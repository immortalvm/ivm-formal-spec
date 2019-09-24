From Equations Require Import Equations.
Set Equations With UIP.

Require Import Coq.Bool.Bvector.
Require Import Nat.
Require Vector.
Require Import Arith Omega List.
Require Import Coq.Program.Tactics.

Set Implicit Arguments.


Arguments Vector.cons : default implicits.
Arguments Bcons : default implicits.
Arguments Bneg : default implicits.
Arguments Bsign : default implicits.
Arguments BVand : default implicits.
Arguments BVor : default implicits.
Arguments BVxor : default implicits.

Import ListNotations.


(** * Monad basics *)

(* Based on https://github.com/coq/coq/wiki/AUGER_Monad. *)
Class Monad (m: Type -> Type): Type :=
{
  ret: forall A, A -> m A;
  bind: forall A, m A -> forall B, (A -> m B) -> m B;

  monad_right: forall A (ma: m A), ma = bind ma (@ret A);
  monad_left: forall A (a: A) B (f: A -> m B), f a = bind (ret a) f;
  monad_assoc: forall A (ma: m A) B f C (g: B -> m C),
      bind ma (fun a => bind (f a) g) = bind (bind ma f) g
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
    fold_right (liftM2 cons) (ret []) (map f lst).

  Equations traverse_vector {A B: Type} (f: A -> m B) {n} (vec: Vector.t A n) : m (Vector.t B n) :=
    traverse_vector _ Vector.nil := ret (Vector.nil B);
    traverse_vector f (Vector.cons x v) with f x, traverse_vector f v := {
      traverse_vector _ _ mb mvb := mb >>= (fun b => mvb >>= (fun vb => ret (Vector.cons b vb)))
    }.

End monadic_functions.

Notation "ma ;; mb" := (wbind ma mb) (at level 60, right associativity).
Notation "a ::= ma ; mb" := (ma >>= (fun a => mb)) (at level 60, right associativity, only parsing).

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



(** * Bit vectors. *)

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

Definition fromBits8 : Bits8 -> nat := fromBits. Coercion fromBits8 : Bits8 >-> nat.
Definition fromBits16 : Bits16 -> nat := fromBits. Coercion fromBits16 : Bits16 >-> nat.
Definition fromBits32 : Bits32 -> nat := fromBits. Coercion fromBits32 : Bits32 >-> nat.
Definition fromBits64 : Bits64 -> nat := fromBits. Coercion fromBits64 : Bits64 >-> nat.

Equations fromLittleEndian {n} (v: Vector.t Bits8 n): nat :=
  fromLittleEndian Vector.nil := 0;
  fromLittleEndian (Vector.cons x r) := 256 * (fromLittleEndian r) + x. (* Implicit coercion *)

Equations toLittleEndian n (k: nat) : Vector.t Bits8 n :=
  toLittleEndian 0 _ := Vector.nil Bits8;
  toLittleEndian (S n) k := Vector.cons (toBits 8 k) (toLittleEndian n (k / 256)).

(* Compute (fromLittleEndian (toLittleEndian 2 12345)). *)

Definition addNat64 k (x: Bits64) : Bits64 := toBits 64 (k + x). (* Implicit coercion *)
Definition neg64 (x: Bits64) : Bits64 := addNat64 1 (Bneg x).
Definition add64 (x y: Bits64) : Bits64 := toBits 64 (x + y). (* Implicit coercion *)
Definition subNat64 k (x: Bits64) : Bits64 := add64 (neg64 (toBits 64 k)) x.

Definition signExtend {n} (v: Bvector (S n)) : Bits64.
  refine (
      let sign := Bsign v in
      let extra := nat_rect Bvector Bnil (Bcons sign) (64 - n) in
      let bits := Vector.append v extra in
      Vector.take 64 _ bits). (* in case n > 64 *)
  omega.
Defined.

Definition zero16 : Bits16 := toBits 16 0.
Definition zero32 : Bits32 := toBits 32 0.
Definition zero64 : Bits64 := toBits 64 0.
Definition true64 : Bits64 := Bneg zero64.

(* TODO: Generalize from 0 to x < 2^n. *)
Lemma zeroBits_zero: forall n, fromBits (toBits n 0) = 0.
Proof.
  intro n.
  induction n as [|n IH].
  simp toBits.
  simp fromBits.
  reflexivity.

  simp toBits.
  simpl.
  simp fromBits.
  rewrite IH.
  simpl.
  reflexivity.
Qed.


(** * State *)

Equations addresses n (start: Bits64) : Vector.t Bits64 n :=
  addresses 0 _ := Vector.nil Bits64;
  addresses (S n) start := Vector.cons start (addresses n (addNat64 1 start)).

Definition Gray := Bits8.
Definition Color := (Bits16 * Bits16 * Bits16)%type.

(* Record types inspired by the 'sigma' type of Equations. *)

Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Record Image A :=
  mkImage {
      iWidth: Bits16;
      iHeight: Bits16;
      iPixel: forall (x: nat) (Hx: x < iWidth) (y: nat) (Hy: y < iHeight), A;
    }.

Definition noImage {A} : Image A.
  refine ({|
             iWidth := zero16;
             iHeight := zero16;
             iPixel := _;
           |}).
  unfold fromBits16.
  rewrite zeroBits_zero.
  intros x Hx.
  contradiction (Nat.nlt_0_r x Hx).
Defined.

Record Sound :=
  mkSound {
      sRate: Bits32;
      sSamples: list (Bits16 * Bits16);
      sDef: sRate = zero32 -> sSamples = [];
    }.

Definition noSound : Sound.
  refine ({|
             sRate := zero32;
             sSamples := [];
             sDef := _;
           |}).
  trivial.
Defined.

Definition OutputText := list Bits32.

Definition consistent (memory: Bits64 -> option Bits8) (allocation: Bits64 -> nat) :=
  (forall (a: Bits64),
      memory a <> None <->
      exists start, Vector.Exists (eq a) (addresses (allocation start) start))
  /\
  (forall start0 start1,
      (Vector.Exists
         (fun a => Vector.Exists (eq a) (addresses (allocation start0) start0))
         (addresses (allocation start1) start1)) ->
      start0 = start1).

Record State :=
  mkState {
      terminated: bool;
      PC: Bits64; (* Program counter *)
      SP: Bits64; (* Stack pointer *)
      input: list (Image Gray);
      output: list ((Image Color) * Sound * OutputText);
      memory: Bits64 -> option Bits8;
      allocation: Bits64 -> nat;
      consistency: consistent memory allocation;
      always_output: output <> []
    }.

Unset Primitive Projections.

Lemma State_expansion (s: State) :
  s = {|
    terminated := terminated s;
    PC := PC s;
    SP := SP s;
    input := input s;
    output := output s;
    memory := memory s;
    consistency := consistency s;
    always_output := always_output s;
  |}.
Proof.
  reflexivity.
Qed.

Require Import Coq.Logic.PropExtensionality.

(* Since State is finite, this might be provable even without
   PropExtensionality, but that will have to wait. *)
Lemma State_injectivity
      t0 p0 s0 i0 o0 m0 a0 (c0: consistent m0 a0) ao0
      t1 p1 s1 i1 o1 m1 a1 (c1: consistent m1 a1) ao1:
  t0=t1 -> p0=p1 -> s0=s1 -> i0=i1 -> o0=o1 -> m0=m1 -> a0=a1
  -> {|terminated:=t0; PC:=p0; SP:=s0; input:=i0; output:=o0; memory:=m0; consistency:=c0; always_output:=ao0|}
  = {|terminated:=t1; PC:=p1; SP:=s1; input:=i1; output:=o1; memory:=m1; consistency:=c1; always_output:=ao1|}.
Proof.
  repeat (intro e; destruct e).
  destruct (proof_irrelevance (consistent m0 a0) c0 c1).
  destruct (proof_irrelevance (o0 <> []) ao0 ao1).
  reflexivity.
Qed.

Lemma State_extensionality : forall (s0 s1: State),
    terminated s0 = terminated s1
    -> PC s0 = PC s1
    -> SP s0 = SP s1
    -> input s0 = input s1
    -> output s0 = output s1
    -> memory s0 = memory s1
    -> allocation s0 = allocation s1
    -> s0 = s1.
Proof.
  intros.
  rewrite (State_expansion s0).
  rewrite (State_expansion s1).
  apply State_injectivity; assumption.
Qed.


(** * Relational state monad *)

Definition ST (A: Type) := State -> A -> State -> Prop.

Require Import Coq.Logic.FunctionalExtensionality.

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


Module st_tactics.
  Ltac destr :=
    match goal with
    | H:_ /\ _ |- _ => destruct H
    | H:_ * _ |- _ => destruct H
    | H:_ \/ _ |- _ => destruct H
    | H: exists _, _ |- _ => destruct H
    | H: option _ |- _ => destruct H
    | H: False |- _ => destruct H
    end.
  Ltac exS :=
    match goal with
    | [ |- exists x s, x = ?x' /\ s = ?s' /\ _] => exists x; exists s
    | [x:?X, s:State, _:context H[_ ?x ?s] |- exists _: ?X, exists _: State, _ ] => exists x; exists s
    end.
  Ltac crush := repeat (
                    intro || split || assumption || discriminate || subst
                    || apply State_extensionality
                    || apply ST_extensionality
                    || simpl in *
                    || destr || exS).
End st_tactics.

Instance StateMonad: Monad ST :=
  {
    ret A x0 s0 x1 s1 := x0 = x1 /\ s0 = s1;
    bind A st B f s0 x2 s2 := exists x1 s1, st s0 x1 s1 /\ f x1 s1 x2 s2
  }.
Proof.
  - abstract (st_tactics.crush).
  - abstract (st_tactics.crush).
  - abstract (st_tactics.crush).
Defined.


(** * Change management *)

Definition intersectST {A} (st1 st2: ST A): ST A :=
  fun s0 x1 s1 => st1 s0 x1 s1 /\ st2 s0 x1 s1.

Notation "st1 ⩀ st2" := (intersectST st1 st2) (at level 50, left associativity).

Definition stateUnchangedST {A} : ST A :=
  fun s0 _ s1 => s0 = s1.

Lemma ret_characterized {A} (x: A) :
  stateUnchangedST ⩀ (fun _ x1 _ => x = x1) = ret x.
Proof.
  unfold stateUnchangedST, intersectST.
  st_tactics.crush.
Qed.

Definition registersUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    terminated s0 = terminated s1
    /\ PC s0 = PC s1
    /\ SP s0 = SP s1.

Definition memoryUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    allocation s0 = allocation s1
    /\ memory s0 = memory s1.

Definition ioUnchangedST {A} : ST A :=
  fun s0 _ s1 =>
    input s0 = input s1
    /\ output s0 = output s1.

Lemma stateUnchanged_characterized {A} :
  registersUnchangedST ⩀ memoryUnchangedST ⩀ ioUnchangedST = @stateUnchangedST A.
Proof.
  unfold registersUnchangedST, memoryUnchangedST, ioUnchangedST, stateUnchangedST.
  repeat (unfold intersectST).
  st_tactics.crush.
Qed.


(** * Building blocks *)

Definition extractST {A} (f: State -> A): ST A :=
  stateUnchangedST ⩀ (fun s0 x1 _ => f s0 = x1).

(* Get the value at the n bytes starting at start. *)
Definition tryGetST (n: nat) (start: Bits64) : ST (option nat) :=
  extractST (fun s => liftM fromLittleEndian
                         (traverse_vector (memory s)
                                          (addresses n start))).

Definition failST {A}: ST A :=
  fun _ _ _ => False.

Definition valueOrFailST {A} (oa: option A) : ST A :=
  match oa with Some a => ret a | _ => failST end.

(* Undefined if there is an access violation. *)
Definition getST (n: nat) (start: Bits64) : ST nat :=
  tryGetST n start >>= valueOrFailST.

Definition otherMemoryUnchangedST (start: Bits64) (n: nat): ST unit :=
  fun s0 _ s1 =>
    let other a := Vector.Forall (fun x => x <> a) (addresses n start) in
    forall a, other a -> memory s0 a = memory s1 a.

(* Observe that if (setST n start value s0 x1 s1), then we know that the
   addresses were allocated because of allocations_defined s1.
   Formally:
   Vector.Forall (fun a => memory s0 a <> None) (addresses n start)
 *)
Definition setST (n: nat) (start: Bits64) (value: nat) : ST unit :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ otherMemoryUnchangedST start n
    ⩀ fun s0 _ s1 =>
        allocation s0 = allocation s1
        /\ getST n start s1 value s1.

Definition setPcST (a: Bits64): ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
         terminated s0 = terminated s1
         /\ SP s0 = SP s1
         /\ a = PC s1.

Definition setSpST (a: Bits64): ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
        (* Is this more readable? *)
        terminated s0 = terminated s1
        /\ PC s0 = PC s1
        /\ a = SP s1.

Definition nextST (n: nat) : ST nat :=
  a ::= extractST PC;
  setPcST (addNat64 n a);;
  getST n a.

Definition popST: ST Bits64 :=
  a ::= extractST SP;
  v ::= getST 8 a;
  setSpST (addNat64 8 a);;
  ret (toBits 64 v).

(* Push lower 64 bits of value. *)
Definition pushST (value: nat): ST unit :=
  a0 ::= extractST SP;
  let a1 := subNat64 8 a0 in
  setSpST a1;;
  setST 8 a1 value.


(** * Memory allocation *)

Definition otherAllocationsUnchangedST (start: Bits64) : ST unit :=
  fun s0 _ s1 =>
    forall a, a <> start -> allocation s0 a = allocation s1 a.

Definition allocateST (n: nat) : ST Bits64 :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 start s1 =>
        allocation s0 start = 0
        /\ allocation s1 start = n
        /\ otherAllocationsUnchangedST start s0 tt s1
        /\ otherMemoryUnchangedST start n s0 tt s1
        /\ getST n start s1 0 s1.        (* memory initialized to 0 *)

Definition deallocateST (start: Bits64) : ST unit :=
  registersUnchangedST
    ⩀ ioUnchangedST
    ⩀ otherAllocationsUnchangedST start
    ⩀ fun s0 _ s1 =>
        allocation s1 start = 0
        /\ otherMemoryUnchangedST start (allocation s0 start) s0 tt s1.

(* Observe that allocations_defined ensures that unallocated memory is
None, and that it makes sense to allocate 0 bytes or deallocate an address
which was never allocated. *)


(**** Input and output *)

Definition readFrameST : ST (Bits16 * Bits16) :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 wh s1 =>
        output s0 = output s1
        /\ match input s1 with
          | [] | [_] => wh = (zero16, zero16)
          | _ :: hd :: tl =>
            wh = (iWidth hd, iHeight hd)
            /\ input s1 = hd :: tl
          end.

Definition readPixelST (x y: nat) : ST Bits8 :=
  stateUnchangedST
    ⩀ fun s0 x1 _ =>
        match input s0 with
        | [] => False
        | frame :: _ =>
          exists (Hx: x < iWidth frame)
            (Hy: y < iHeight frame), x1 = iPixel frame Hx Hy
        end.

(* Initial frame pixels: undefined. *)
Definition newFrameST (width height sampleRate: nat) : ST unit :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 _ s1 =>
        input s0 = input s1
        /\ match output s1 with
          | [] => False
          | (image, sound, text) :: rest =>
            output s0 = rest
            /\ width = iWidth image
            /\ height = iHeight image
            /\ sampleRate = sRate sound
            /\ sSamples sound = []
            /\ text = []
          end.

Definition setPixelST (x y r g b : nat) : ST unit :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 _ s1 =>
        input s0 = input s1
        /\ match output s0, output s1 with
          | (i0, s0, t0) :: r0, (i1, s1, t1) :: r1 =>
            r0 = r1
            /\ t0 = t1
            /\ s0 = s1
            (* Needed since iPixel is undefined outside width*height. *)
            /\ iWidth i0 = iWidth i1
            /\ iHeight i0 = iHeight i1
            (* Otherwise undefined *)
            /\ x < iWidth i0
            /\ y < iHeight i0

            /\ forall xx Hx0 Hx1 yy Hy0 Hy1, @iPixel _ i1 xx Hx0 yy Hy0 =
                                       if (xx =? x) && (yy =? y)
                                       then (toBits 16 r, toBits 16 g, toBits 16 b)
                                       else @iPixel _ i0 xx Hx1 yy Hy1
          | _, _ => False
          end.

Definition addSampleST (left right : nat) : ST unit :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 _ s1 =>
        input s0 = input s1
        /\ match output s0, output s1 with
          | (i0, s0, t0) :: r0, (i1, s1, t1) :: r1 =>
            r0 = r1
            /\ t0 = t1
            /\ i0 = i1
            /\ sRate s0 = sRate s1
            /\ sRate s0 <> zero32 (* Otherwise undefined *)
            /\ (toBits 16 left, toBits 16 right) :: sSamples s0 = sSamples s1
          | _, _ => False
          end.

Definition putCharST (c: nat) : ST unit :=
  registersUnchangedST
    ⩀ memoryUnchangedST
    ⩀ fun s0 _ s1 =>
        input s0 = input s1
        /\ match output s0, output s1 with
          | (i0, s0, t0) :: r0, (i1, s1, t1) :: r1 =>
            r0 = r1
            /\ s0 = s1
            /\ i0 = i1
            /\ (toBits 32 c) :: t0 = t1
          | _, _ => False
          end.

(** * Execution *)

Definition exitST : ST unit :=
  memoryUnchangedST
    ⩀ ioUnchangedST
    ⩀ fun s0 _ s1 =>
        terminated s1 = true
        /\ PC s0 = PC s1
        /\ SP s0 = SP s1.

Module Instructions.
  Notation "'EXIT'" := 0.
  Notation "'NOP'" := 1.
  Notation "'JUMP'" := 2.
  Notation "'JUMP_ZERO'" := 3.
  Notation "'SET_SP'" := 4.
  Notation "'GET_PC'" := 5.
  Notation "'GET_SP'" := 6.
  Notation "'PUSH0'" := 7.
  Notation "'PUSH1'" := 8.
  Notation "'PUSH2'" := 9.
  Notation "'PUSH4'" := 10.
  Notation "'PUSH8'" := 11.
  Notation "'SIGX1'" := 12.
  Notation "'SIGX2'" := 13.
  Notation "'SIGX4'" := 14.
  Notation "'LOAD1'" := 16.
  Notation "'LOAD2'" := 17.
  Notation "'LOAD4'" := 18.
  Notation "'LOAD8'" := 19.
  Notation "'STORE1'" := 20.
  Notation "'STORE2'" := 21.
  Notation "'STORE4'" := 22.
  Notation "'STORE8'" := 23.
  Notation "'ALLOCATE'" := 24.
  Notation "'DEALLOCATE'" := 25.
  Notation "'ADD'" := 32.
  Notation "'MULT'" := 33.
  Notation "'DIV'" := 34.
  Notation "'REM'" := 35.
  Notation "'LT'" := 36.
  Notation "'AND'" := 40.
  Notation "'OR'" := 41.
  Notation "'NOT'" := 42.
  Notation "'XOR'" := 43.
  Notation "'POW2'" := 44.
  Notation "'NEW_FRAME'" := 48.
  Notation "'SET_PIXEL'" := 49.
  Notation "'ADD_SAMPLE'" := 50.
  Notation "'PUT_CHAR'" := 52.
  Notation "'READ_FRAME'" := 56.
  Notation "'READ_PIXEL'" := 57.
End Instructions.

Section step_definition.
Import Instructions.

Definition stepST : ST unit :=
  t ::= extractST terminated;
  if t then failST
  else
    op ::= nextST 1;
    match op with
    | EXIT => exitST
    | NOP => stateUnchangedST

    | JUMP => popST >>= setPcST
    | JUMP_ZERO =>
        offset ::= nextST 1;
        v ::= popST;
        if v =? 0
        then pc ::= extractST PC;
             setPcST (add64 pc (signExtend (toBits 8 offset)))
        else stateUnchangedST

    | SET_SP => popST >>= setSpST
    | GET_PC => extractST PC >>= pushST
    | GET_SP => extractST SP >>= pushST

    | PUSH0 => pushST 0
    | PUSH1 => nextST 1 >>= pushST
    | PUSH2 => nextST 2 >>= pushST
    | PUSH4 => nextST 4 >>= pushST
    | PUSH8 => nextST 8 >>= pushST

    (* Detour via nat. *)
    | SIGX1 => v ::= popST; pushST (signExtend (toBits 8 v))
    | SIGX2 => v ::= popST; pushST (signExtend (toBits 16 v))
    | SIGX4 => v ::= popST; pushST (signExtend (toBits 32 v))

    | LOAD1 => popST >>= getST 1 >>= pushST
    | LOAD2 => popST >>= getST 2 >>= pushST
    | LOAD4 => popST >>= getST 4 >>= pushST
    | LOAD8 => popST >>= getST 8 >>= pushST

    | STORE1 => a ::= popST; v ::= popST; setST 1 a v
    | STORE2 => a ::= popST; v ::= popST; setST 2 a v
    | STORE4 => a ::= popST; v ::= popST; setST 4 a v
    | STORE8 => a ::= popST; v ::= popST; setST 8 a v

    | ALLOCATE => popST >>= allocateST >>= pushST
    | DEALLOCATE => popST >>= deallocateST

    (* Only the lower 64 bits of the result ends up on the stack. *)
    | ADD => x ::= popST; y ::= popST; pushST (x + y)
    | MULT => x ::= popST; y ::= popST; pushST (x * y)
    | DIV =>
        x ::= popST;
        y ::= popST;
        pushST (if x =? 0 then 0 else y / x)
    | REM =>
        x ::= popST;
        y ::= popST;
        pushST (if x =? 0 then 0 else modulo y x)
    | LT =>
        x ::= popST;
        y ::= popST;
        pushST (if y <? x then true64 else zero64) (* multiple coercions *)
    | AND =>
        x ::= popST;
        y ::= popST;
        pushST (BVand x y : Bits64)
    | OR =>
        x ::= popST;
        y ::= popST;
        pushST (BVor x y : Bits64)
    | XOR =>
        x ::= popST;
        y ::= popST;
        pushST (BVxor x y : Bits64)
    | NOT =>
        x ::= popST;
        pushST (Bneg x : Bits64)
    | POW2 =>
        n ::= popST;
        pushST (2 ^ n)

    | NEW_FRAME =>
        rate ::= popST;
        height ::= popST;
        width ::= popST;
        newFrameST width height rate
    | SET_PIXEL =>
        b ::= popST;
        g ::= popST;
        r ::= popST;
        y ::= popST;
        x ::= popST;
        setPixelST x y r g b
    | ADD_SAMPLE =>
        right ::= popST;
        left ::= popST;
        addSampleST left right
    | PUT_CHAR =>
        popST >>= putCharST

    | READ_FRAME =>
        wh ::= readFrameST;
        pushST (fst wh);;
        pushST (snd wh)
    | READ_PIXEL =>
        x ::= popST;
        y ::= popST;
        readPixelST x y >>= pushST

    | _ => failST
    end.

End step_definition. (* This limits the scope of the instruction constants. *)

Equations nStepsST (n: nat): ST unit :=
  nStepsST 0 := stateUnchangedST;
  nStepsST (S n) := stepST ;; nStepsST n.

(* Transitive closure *)
Definition multiStepST: ST unit :=
  fun s0 _ s1 => exists n, nStepsST n s0 tt s1.

Definition runST: ST unit:=
  fun s0 _ s1 =>
    multiStepST s0 tt s1
    /\ terminated s1 = true.

(* Avoid complaints from Equations when using depelim. *)
Derive Signature for Vector.Exists.

Definition protoState (inputList: list (Image Gray)) : State.
  refine ({|
             terminated := false;
             PC := zero64;
             SP := zero64;
             input := noImage :: inputList;
             output := [(noImage, noSound, [])];
             memory := fun _ => None;
             allocation := fun _ => 0;
           |}).
  (* TODO: Automate *)
  - split.
    + firstorder.
      exfalso.
      revert_last.
      funelim (addresses 0 x).
      simpl.
      intro H.
      depelim H.
    + intros x y.
      funelim (addresses 0 x).
      simpl.
      intro H.
      exfalso.
      depelim H.
  - congruence.
Defined.

Equations fillST (start: Bits64) (bytes: list Bits8) : ST unit :=
  fillST _ [] := stateUnchangedST;
  fillST a (x :: r) := setST 1 a x ;; fillST (addNat64 1 a) r.

Definition loadProgramST
           (prog: list Bits8)
           (arg: list Bits8) : ST unit :=
  prog_start ::= allocateST (length prog);
  fillST prog_start prog;;
  setPcST prog_start;;
  let restSize := length arg + 3 * 8 in
  arg_start ::= allocateST restSize;
  fillST arg_start arg;;
  setSpST (addNat64 restSize arg_start).

(* Because of non-determinism and Coq's lack of general recursion, this
   must be defined as a predicate rather than a (partial) function. *)
Definition execution
           prog arg
           (inputList: list (Image Gray))
           (outputList: list ((Image Color) * Sound * OutputText)) : Prop :=
  let s0 := protoState inputList in
  let st := (loadProgramST prog arg) ;; runST ;; (extractST output) in
  (* Observe that we reverse the output list. *)
  exists s1, st s0 (rev outputList) s1.


(** * Certification *)

Definition memoryUsed (s: State): nat :=
  (fix used_below (a: nat): nat :=
     match a with
     | 0 => 0
     | S a' => match memory s (toBits 64 a') with
              | Some _ => 1
              | None => 0
              end + used_below a'
     end)
    (2^64).

(* Rather trivial. *)
Lemma max_memoryUsed (s: State): memoryUsed s <= 2^64.
Proof.
  unfold memoryUsed.
  generalize (2^64).
  induction n.
  - trivial.
  - destruct (memory s (toBits 64 n));
      auto with arith.
Qed.

Definition small (s: State) := memoryUsed s <= 2 ^ 34. (* 16 GiB *)

Definition valueOr {A: Type} (default: A) (o: option A) : A :=
  match o with Some a => a | _ => default end.

Class CertifiedMachine (C: Type) :=
  {
    cm_step: C -> C -> Prop;
    cm_meaning: C -> State -> Prop;
    cm_unique_meaning: forall c s s', cm_meaning c s -> cm_meaning c s' -> s = s';

    cm_after_load: list Bits8 -> list Bits8 -> list (Image Gray) -> C -> Prop;

    cm_after_load_ok: forall prog arg inputList c (s: State),
        cm_after_load prog arg inputList c ->
        exists s, cm_meaning c s /\ loadProgramST prog arg (protoState inputList) tt s;

    cm_after_load_exists: forall prog arg inputList,
        (exists s, small s /\ loadProgramST prog arg (protoState inputList) tt s)
        -> exists c s, cm_after_load prog arg inputList c /\ cm_meaning c s;

    cm_correctness: forall c s (_: cm_meaning c s) c' (_: cm_step c c'),
                    (exists s', stepST s tt s')
                    -> exists s', stepST s tt s' /\ cm_meaning c' s';

    cm_progress: forall c s, cm_meaning c s
                        -> (exists s', small s' /\ stepST s tt s')
                        -> exists c' s', cm_step c c' /\ cm_meaning c' s';

    cm_termination: forall c s c', cm_meaning c s -> cm_step c c' -> terminated s = false;
  }.

Inductive Safe (s: State) : Prop :=
| SafeEnd: terminated s = true -> Safe s
| SafeStep: (exists s', small s' /\ stepST s tt s') -> (* NB: small *)
            (forall s', stepST s tt s' -> Safe s') ->
            Safe s.

Definition cm_terminated {C} `{CertifiedMachine C} (c: C) : Prop :=
  exists s, cm_meaning c s /\ terminated s = true.

Inductive CertSafe {C} `{CertifiedMachine C} (c: C) : Prop :=
  | CertSafeEnd: cm_terminated c -> CertSafe c
  | CertSafeStep: (exists c', cm_step c c') -> (forall c', cm_step c c' -> CertSafe c') -> CertSafe c.

Theorem safe_safe {C} `{CertifiedMachine C} (c: C) s :
  cm_meaning c s -> Safe s -> CertSafe c.
Proof.
  intros Hm H_safe.
  revert c Hm.
  induction H_safe as [s H_term | s H0 H_safe H_cs]; intros c Hc.
  - apply CertSafeEnd.
    unfold cm_terminated.
    exists s.
    auto.
  - set (H_prog := cm_progress c Hc).
    specialize (H_prog H0).
    destruct H_prog as [c' [s' [H1 H2]]].
    apply (CertSafeStep c (ex_intro _ c' H1)).
    intros c'' H3.
    set (H_corr := cm_correctness c Hc c'' H3).
    destruct H0 as [s0 [_ H4]].
    specialize (H_corr (ex_intro _ s0 H4)).
    destruct H_corr as [s'' [H5 H6]].
    apply (H_cs s'' H5 _ H6).
Qed.
