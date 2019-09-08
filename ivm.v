From Equations Require Import Equations.
Set Equations With UIP.

Require Import Coq.Bool.Bvector.
Require Import Nat.
Require Vector.
Require Import Arith Omega List.

Set Implicit Arguments.


Arguments Vector.cons : default implicits.
Arguments Bcons : default implicits.
Arguments Bneg : default implicits.


(**** Monad basics *)


(* Special notation for the identity monad *)

(* Bind *)
Notation "x |> f" := (f x) (at level 98, left associativity, only parsing).


(* Based on https://github.com/coq/coq/wiki/AUGER_Monad. *)
Class Monad (m: Type -> Type): Type :=
{
  ret: forall A, A -> m A;
  bind: forall A, m A -> forall B, (A -> m B) -> m B;

  monad_right: forall A (a: m A), a = bind a (@ret A);
  monad_left: forall A (a: A) B (f: A -> m B), f a = bind (ret a) f;
  monad_assoc: forall A (ma: m A) B f C (g: B -> m C),
      bind ma (fun x => bind (f x) g) = bind (bind ma f) g
}.
Notation "ma >>= f" := (bind ma _ f) (at level 98, left associativity).

Section monadic_functions.
  Context {m: Type -> Type} `{M: Monad m}.

  Definition wbind {A: Type} (ma: m A) {B: Type} (mb: m B) :=
    ma >>= fun _ => mb.

  Definition join {A: Type} (mma: m (m A)): m A :=
    mma >>= id.

  Definition liftM {A B: Type} (f: A -> B) (ma: m A): m B :=
    ma >>= fun a => ret (f a).

  Definition liftM2 {A B C: Type} (f: A -> B -> C) (ma: m A) (mb: m B): m C :=
    ma >>= (fun a => mb >>= (fun b => ret (f a b))).

  Definition traverse {A B: Type} (f: A -> m B) (lst: list A) : m (list B) :=
    fold_right (liftM2 cons) (ret nil) (map f lst).

  Equations traverse_vector {A B: Type} (f: A -> m B) {n} (vec: Vector.t A n) : m (Vector.t B n) :=
    traverse_vector _ Vector.nil := ret (Vector.nil B);
    traverse_vector f (Vector.cons x v) with f x, traverse_vector f v := {
      traverse_vector _ _ mb mvb := mb >>= (fun b => mvb >>= (fun vb => ret (Vector.cons b vb)))
    }.

End monadic_functions.

Notation "ma >> mb" := (wbind ma mb) (at level 98, left associativity).
Notation "c ;; d" := (c >> d) (at level 60, right associativity).
Notation "a ::= e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

Instance Maybe: Monad option :=
{
  ret := @Some;
  bind A ma B f := match ma with None => None | Some a => f a end
}.
Proof.
  - abstract (intros A a; case a; split).
  - abstract (split).
  - abstract (intros A x B f C g; case x; split).
Defined.



(**** Bit vectors. TODO: Should we use BinNat instead of nat as well? *)

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


(**** State *)

Equations addresses (start: Bits64) n : Vector.t Bits64 n :=
  addresses _ 0 := Vector.nil Bits64;
  addresses start (S n) := Vector.cons start (addresses (addNat64 1 start) n).

Definition Gray := Bits8.
Definition Color := (Bits16 * Bits16 * Bits16)%type.

(* Record types inspired by the 'sigma' type of Equations. *)

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

      allocations_defined:
        forall (a: Bits64),
          memory a <> None <->
          exists start, Vector.Exists (eq a) (addresses start (allocation start));

      allocations_disjoint:
        forall start0 start1,
          (Vector.Exists
             (fun a => Vector.Exists (eq a) (addresses start0 (allocation start0)))
             (addresses start1 (allocation start1))) ->
          start0 = start1;
    }.

Unset Primitive Projections.


(* Since State is completely finite, this should be provable even without
PropExtensionality or Functionalextensionality, but this will have to wait. *)
Lemma State_extensionality : forall (s0 s1: State),
    s0.(terminated) = s1.(terminated)
    -> s0.(PC) = s1.(PC)
    -> s0.(SP) = s1.(SP)
    -> s0.(input) = s1.(input)
    -> s0.(output) = s1.(output)
    -> s0.(memory) = s1.(memory)
    -> s0.(allocation) = s1.(allocation)
    -> s0 = s1.
Proof.
Admitted. (* TODO *)



(**** Relational state monad *)

Definition ST (A: Type) := State -> A -> State -> Prop.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

(* Extensionality is needed since A is an arbitrary type.
   This can be avoided if we define monads in terms of a setoid.
 *)
Lemma ST_extensionality {A} (st0 st1: ST A):
  (forall s0 x1 s1, st0 s0 x1 s1 <-> st1 s0 x1 s1) -> st0 = st1.
Proof.
  intro H.
  repeat (intro || apply functional_extensionality).
  apply propositional_extensionality.
  apply H.
Qed.

Require Import Coq.Program.Tactics.

Instance StateMonad: Monad ST :=
{
  ret A x0 s0 x1 s1 := x1 = x0 /\ s0 = s1;
  bind A ma B f s0 b s2 := exists a s1, ma s0 a s1 /\ f a s1 b s2;
}.
Proof. (* TODO: Automate! Or use 'admit' for now? *)
  - intros; apply ST_extensionality; intros; split.
    + eauto.
    + intros [? [? [? [? ?]]]].
      subst.
      assumption.
  - intros; apply ST_extensionality; intros; split.
    + eauto.
    + intros [? [? [[? ?] ?]]].
      subst.
      assumption.
  - intros; apply ST_extensionality; intros; split.
    + intros [? [? [? [? [? [? ?]]]]]].
      exists x2, x3; split.
      * exists x, x0; split; assumption.
      * assumption.
    + intros [? [? [[? [? [? ?]]] ?]]].
      exists x2, x3; split.
      * assumption.
      * exists x, x0; split; assumption.
Defined.


(**** Change management *)

Definition intersect {A} (st1 st2: ST A): ST A :=
  fun s0 x1 s1 => st1 s0 x1 s1 /\ st2 s0 x1 s1.

Notation "st1 ⩀ st2" := (intersect st1 st2) (at level 50, left associativity).

Definition stateUnchangedST {A} : ST A :=
  fun s0 _ s1 => s0 = s1.

Lemma ret_characterized {A} (x: A) :
  stateUnchangedST ⩀ (fun _ x1 _ => x = x1) = ret x.
Proof.
  unfold stateUnchangedST, intersect.
  apply ST_extensionality.
  firstorder.
Qed.

Definition registersUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    s0.(terminated) = s1.(terminated)
    /\ s0.(PC) = s1.(PC)
    /\ s0.(SP) = s1.(SP).

Definition memoryUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    s0.(allocation) = s1.(allocation)
    /\ s0.(memory) = s1.(memory).

Definition ioUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    s0.(input) = s1.(input)
    /\ s0.(output) = s1.(output).

Lemma stateUnchanged_characterized {A} :
  @registersUnchangedST A ⩀ memoryUnchangedST ⩀ ioUnchangedST = stateUnchangedST.
Proof.
  unfold registersUnchangedST, memoryUnchangedST, ioUnchangedST, stateUnchangedST.
  repeat (unfold intersect).
  apply ST_extensionality.
  intros; firstorder; subst; try (reflexivity || assumption).
  apply State_extensionality; assumption.
Qed.


(**** Building blocks *)

Definition valueST {A} (p: State -> A -> Prop): ST A :=
  stateUnchangedST ⩀ (fun s0 x1 _ => p s0 x1).

Definition extractST {A} (f: State -> A): ST A :=
  valueST (fun s0 x1 => f s0 = x1).

Definition getPcST : ST Bits64 := extractST PC.

Definition getSpST : ST Bits64 := extractST SP.

(* Get the value at the n bytes starting at start. *)
Definition tryGetST (start: Bits64) (n: nat) : ST (option nat) :=
  extractST (fun s => addresses start n
                   |> traverse_vector s.(memory)
                   |> liftM fromLittleEndian).

Definition undefinedST {A}: ST A :=
  fun _ _ _ => True.

Definition valueOrUndefinedST {A} (oa: option A) : ST A :=
  match oa with Some a => ret a | _ => undefinedST end.

(* NB: The behavior is completely undefined if there is an access violation! *)
Definition getST (start: Bits64) (n: nat) : ST nat :=
  tryGetST start n >>= valueOrUndefinedST.

Definition otherMemoryUnchangedST (start: Bits64) (n: nat): ST unit :=
  fun s0 _ s1 =>
    let other a := Vector.Forall (fun x => x <> a) (addresses start n) in
    forall a, other a -> s0.(memory) a = s1.(memory) a.

(* Observe that if (setST start n value s0 x1 s1), then we know that the
   addresses were allocated because of s1.(allocations_defined).
   Formally:
   Vector.Forall (fun a => s0.(memory) a <> None) (addresses start n)
 *)
Definition setST (start: Bits64) (n: nat) (value: nat) : ST unit :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ otherMemoryUnchangedST start n
    ⩀ fun s0 _ s1 =>
        s0.(allocation) = s1.(allocation)
        /\ getST start n s1 value s1.

Definition setPcST (a: Bits64): ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
        s0.(terminated) = s1.(terminated)
        /\ s0.(SP) = s1.(SP)
        /\ a = s1.(PC).

Definition setSpST (a: Bits64): ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
        (* Is this more readable? *)
        terminated s0 = terminated s1
        /\ PC s0 = PC s1
        /\ a = SP s1.

Definition nextST (n: nat) : ST nat :=
  a ::= getPcST;
  setSpST (addNat64 n a);;
  getST a n.

Definition popST: ST nat :=
  a ::= getSpST;
  setSpST (addNat64 8 a);;
  getST a 8.

Definition pushST (value: nat): ST unit :=
  a0 ::= getSpST;
  let a1 := subNat64 8 a0 in
  setSpST a1;;
  setST a1 8 value.


(**** Memory allocation *)

Definition otherAllocationsUnchanged (start: Bits64) : ST unit :=
  fun s0 _ s1 =>
    forall a, a <> start -> s0.(allocation) a = s1.(allocation) a.

Definition allocateST (n: nat) : ST Bits64 :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 start s1 =>
        s0.(allocation) start = 0
        /\ s1.(allocation) start = n
        /\ otherAllocationsUnchanged start s0 tt s1
        /\ otherMemoryUnchangedST start n s0 tt s1
        /\ getST start n s1 0 s1. (* Memory initialized to 0. *)

Definition deallocateST (start: Bits64) : ST unit :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ otherAllocationsUnchanged start
    ⩀ fun s0 _ s1 =>
        s1.(allocation) start = 0
        /\ otherMemoryUnchangedST start (s0.(allocation) start) s0 tt s1.

(* Observe that allocations_defined ensures that unallocated memory is
None and that it makes sense to allocate 0 bytes or deallocate an address
which was never allocated! *)

(* To be continued... *)
