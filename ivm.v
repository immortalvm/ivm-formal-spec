From Equations Require Import Equations.
Require Import Coq.Bool.Bvector.
Require Import Nat.
Require Vector.
Require Import Arith Omega List.

Set Implicit Arguments.

Notation "x |> f" := (f x) (at level 150, left associativity, only parsing).
Notation "x >>= f" := (option_map f x) (at level 150, left associativity, only parsing).

Arguments Vector.cons : default implicits.
Arguments Bcons : default implicits.
Arguments Bneg : default implicits.

Definition Bits8 := Bvector 8.
Definition Bits16 := Bvector 16.
Definition Bits32 := Bvector 32.
Definition Bits64 := Bvector 64.

Equations fromBits {n} (v: Bvector n) : nat :=
  fromBits Vector.nil := 0 ;
  fromBits (Vector.cons b r) := 2 * fromBits r + (if b then 1 else 0).

Equations toBits n (k: nat) : Bvector n :=
  toBits 0 _ := Bnil ;
  toBits (S n) k :=
    Bcons (eqb 1 (modulo k 2)) (toBits n (div k 2)).

(* Compute (fromBits (toBits 8 (213 + 65536))). *)

Equations fromLittleEndian {n} (v: Vector.t Bits8 n): nat :=
  fromLittleEndian Vector.nil := 0;
  fromLittleEndian (Vector.cons x r) := 256 * (fromLittleEndian r) + (fromBits x).

Equations toLittleEndian n (k: nat) : Vector.t Bits8 n :=
  toLittleEndian 0 _ := Vector.nil Bits8;
  toLittleEndian (S n) k := Vector.cons (toBits 8 k) (toLittleEndian n (k / 256)).

(* Compute (fromLittleEndian (toLittleEndian 2 12345)). *)

Definition addNat64 k (x: Bits64) : Bits64 := k + (fromBits x) |> toBits 64.
Definition neg64 (x: Bits64) : Bits64 := Bneg x |> addNat64 1.
Definition add64 (x y: Bits64) : Bits64 := (fromBits x) + (fromBits y) |> toBits 64.
Definition subNat64 k (x: Bits64) : Bits64 := add64 (neg64 (toBits 64 k)) x.

Equations addresses (start: Bits64) n : Vector.t Bits64 n :=
  addresses _ 0 := Vector.nil Bits64;
  addresses start (S n) := Vector.cons start (addresses (addNat64 1 start) n).

Definition Gray := Bits8.
Definition Color := (Bits16 * Bits16 * Bits16)%type.


(* Inspired by the 'sigma' type of Equations. *)

Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Record InputFrame :=
  mkInputFrame {
      iWidth: nat;
      iHeight: nat;
      iPixel: nat -> nat -> option Gray;
      iDef: forall x y, x < iWidth -> y < iHeight -> iPixel x y <> None;
    }.

Record OutputImage :=
  mkOutputImage {
      oWidth: nat;
      oHeight: nat;
      oPixel: nat -> nat -> option Color;
      oDef: forall x y, x < oWidth -> y < oHeight -> oPixel x y <> None;
    }.

Record OutputSound := mkOutputSound { rate: Bits32; samples: list (Bits16 * Bits16) }.

Record State :=
  mkState {
      terminated: bool;
      PC: Bits64; (* Program counter *)
      SP: Bits64; (* Stack pointer *)
      input: list InputFrame;
      output: list (OutputImage * OutputSound);
      memory: Bits64 -> option Bits8;
      allocation: Bits64 -> nat;

      allocationsDefined:
        forall (a: Bits64),
          memory a <> None <->
          exists start, Vector.Exists (eq a) (addresses start (allocation start));

      allocationsDisjoint:
        forall start0 start1,
          (Vector.Exists
             (fun a => Vector.Exists (eq a) (addresses start0 (allocation start0)))
             (addresses start1 (allocation start1))) ->
          start0 = start1;
    }.

Unset Primitive Projections.


Equations options {A} {n} (v: Vector.t (option A) n): option (Vector.t A n) :=
  options Vector.nil := Some (Vector.nil A);
  options (Vector.cons _ v) with options v := {
    options (Vector.cons (Some x) _) (Some v) => Some (Vector.cons x v);
    options _ _ := None
  }.

Definition load n (s: State) (start: Bits64) : option nat :=
  addresses start n |> Vector.map s.(memory) |> options >>= fromLittleEndian.

Definition top (s: State): option Bits64 := load 8 s s.(SP) >>= toBits 64.


Definition ioAndTerminationUnchanged (s0 s1: State) : Prop :=
  s1.(terminated) = s0.(terminated)
  /\ s1.(input) = s0.(input)
  /\ s1.(output) = s0.(output).

Definition zero8 := toBits 8 0.

Definition memChangeRel start n (pred: option Bits8 -> option Bits8 -> Prop) (s0 s1: State) : Prop :=
  let addrs := addresses start n in
  Vector.Forall (fun a => pred (s0.(memory) a) (s1.(memory) a)) addrs
  /\ forall (a: Bits64), Vector.Forall (fun x => x <> a) addrs -> s0.(memory) a = s1.(memory) a.

Definition allocateRel (n: nat) (s0 s1: State) : Prop :=
  ioAndTerminationUnchanged s0 s1
  /\ s1.(PC) = s0.(PC)
  /\ s1.(SP) = subNat64 8 s0.(SP)
  /\ match top s1 with
    | None => False
    | Some start =>
      memChangeRel start n (fun _ x1 => x1 = Some zero8) s0 s1
      /\ s0.(allocation) start = 0
      /\ s1.(allocation) start = n
      /\ forall a, a <> start -> s1.(allocation) a = s0.(allocation) a
    end.


Definition deallocateRel (s0 s1: State) : Prop :=
  ioAndTerminationUnchanged s0 s1
  /\ s1.(PC) = s0.(PC)
  /\ s1.(SP) = addNat64 8 s0.(SP)
  /\ match top s0 with
    | None => False
    | Some start =>
      memChangeRel start (s0.(allocation) start) (fun _ x1 => x1 = None) s0 s1
      /\ s1.(allocation) start = 0
      /\ forall a, a <> start -> s1.(allocation) a = s0.(allocation) a
    end.


(* Notice that it makes sense to allocate 0 bytes or deallocate an address
which was never allocated! *)
