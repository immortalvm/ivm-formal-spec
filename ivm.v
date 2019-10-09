From Equations Require Import Equations.
Set Equations With UIP.

Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Psatz.
Require Import Coq.Program.Tactics.

Require Import Coq.Setoids.Setoid.

Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

(** printing )-> $){\rightarrow}$ *)
(** printing >>= $>\!\!>=$ *)
(** printing not $\neg$ *)

(** printing fun $\lambda$ #fun# *)
(** printing nat $\mathbb{N}$ #nat# *)
(** printing bool $\mathbb{B}$ #bool# *)
(** printing Prop $\mathbb{P}$ #Prop# *)
(** printing unit $\mathbbm{1}$ #unit# *)
(** printing tt $\bullet$ #tt# *)

(** printing Z $\mathbb{Z}$ #Z# *)
(** printing True $\top$ #True# *)
(** printing False $\bot$ #False# *)

(** printing Bits8 $\mathbb{B}^8$ #Bits8# *)
(** printing Bits16 $\mathbb{B}^{16}$ #Bits16# *)
(** printing Bits32 $\mathbb{B}^{32}$ #Bits32# *)
(** printing Bits64 $\mathbb{B}^{64}$ #Bits64# *)

(** printing s0 $\coqdocvar{s}_0$ *)
(** printing s1 $\coqdocvar{s}_1$ *)
(** printing s2 $\coqdocvar{s}_2$ *)
(** printing st1 $\coqdocvar{st}_1$ *)
(** printing st2 $\coqdocvar{st}_2$ *)

(** * Formal virtual machine specification

This section contains a formal specification of the virtual machine used
to interpret the contents of this film. It does not describe how to
implement this machine. Instead, this sections contains the requirements
such an implementation must satisfy. The requirements have been formalized
in a system for formal mathematics called Coq, which is based on
higher-order type theory. The text below is based on this formalization.
It involves some formal logic and type theory (where for simplicity we
assume the principles of propositional and functional extensionality), but
we have not included the formal proofs here. *)


(** ** Basic types

We will be using some simple inductive types from the Coq library.

%\begin{center}\begin{tabular}{p{13em}|p{13em}|p{13em}}%
[[
Inductive unit :=
  | tt : unit.
]]
%\vspace{-3ex}&%
[[
Inductive bool :=
  | true : bool
  | false : bool.
]]
%\vspace{-3ex}&%
[[
Inductive nat :=
  | O : nat
  | S : nat -> nat.
]]
%\vspace{-3ex}\end{tabular}\end{center}%

We use decimal numbers as shortcuts. For instance, [3] is an abbreviation
for [S (S (S O))]. [nat] is considered a subtype [Z], the type of (positive
and negative) integers. Furthermore, [if x then y else z]
%\;\;%means%\;\;% [match x with true => y | false => z].

We also need some "generic" types:

%\begin{center}\begin{tabular}{p{17em}|p{20em}}%
[[
Inductive option A :=
  | Some : A -> option A
  | None : option A.
]]
%\vspace{-3ex}&%
[[
Inductive list A :=
 | nil : list A
 | cons : A -> list A -> list A.
]]
%\vspace{-3ex}\end{tabular}\end{center}%

Here [A] is an arbitrary type. We use [ [ ] ] and [x :: y] as shortcuts for
[nil] and [cons x y], respectively.

We will also be using some "dependent" types, such as lists with length
$n$, known as _vectors_:

[[
Definition vector A n := { u : list A | length u = n }.
]]

For technical reasons, [vector] is not actually defined like this, but we
still have implicit inclusions [vector A n] $↪$ [list A], and for every
[u: list A] there is a corresponding vector in [Vector A (length u)]. *)

(* begin hide *)
Open Scope Z_scope.
Coercion Z.of_nat : nat >-> Z.
Notation "'vector'" := t.
Coercion to_list: t >-> list.
(* end hide *)


(** *** Binary numbers

A list or vector of Booleans can be seen as a binary number in the
interval $[0, 2^n)$ when [n = length u]. *)

(* begin hide *)
Definition boolToNat (x: bool) : nat := if x then 1 else 0.
Coercion boolToNat : bool >-> nat.
(* end hide *)

Equations fromBits (_: list bool) : nat :=
  fromBits [] := 0;
  fromBits (x :: u) := 2 * fromBits u + x.

(** This definition is formulated using the Equations extension to Coq.
Observe that we interpret [true] and [false] as 1 and 0, and that the
least significant bit comes first. Below, we shall mostly leave [fromBits]
implicit, using elements of [list bool] and [vector bool n] as if they were
natural numbers.

Conversely, we can extract the $n$ least significant bits of any integer:
*)

(* begin hide *)
Section limit_scope.
Open Scope vector_scope.
(* end hide *)

Equations toBits (n: nat) (_: Z) : vector bool n :=
  toBits 0 _ := [] ;
  toBits (S n) z := (z mod 2 =? 1) :: toBits n (z / 2).

(* begin hide *)
End limit_scope.
(* end hide *)

(* Compute (fromBits (toBits 8 (213 + 1024))). *)

(** Here [z mod 2 =? 1] is [true] if the equality holds, otherwise
[false]. Moreover, [/] and [mod] are defined so that [z mod 2] is either 0
or 1 and [z = 2 * (z / 2) + z mod 2] for every [z]. In particular, all the
bits in [toBits n -1] are [true]. [toBits n] is essentially the ring
homomorphism from [Z] to $\mathbb{Z}/2^n\mathbb{Z}$.
 *)

(* begin hide *)

Arguments Vector.nil {A}.
Arguments Vector.cons : default implicits.

Lemma toBits_equation_3: forall n z (x: bool), toBits (S n) (2 * z + x) = Vector.cons x (toBits n z).
Proof.
  intros n z x.
  simp toBits.
  f_equal.
  - destruct x;
      [apply Z.eqb_eq | apply Z.eqb_neq];
      rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full;
      [reflexivity | easy ].
  - f_equal.
    rewrite Z.add_comm, Z.mul_comm, Z_div_plus.
    + destruct x; simpl; reflexivity.
    + lia.
Qed.

(* end hide *)

Lemma toBits_fromBits: forall {n} (u: vector bool n), toBits n (fromBits u) = u.
Proof.
  induction u as [|x n u IH].
  - reflexivity.
  - assert (to_list (Vector.cons x u) = (x :: u)) as H;
      [reflexivity
      |rewrite H; clear H].
    rewrite fromBits_equation_2.
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_mul.
    rewrite toBits_equation_3 at 1.
    rewrite IH.
    reflexivity.
Qed.



(** In some situations, we want bit vectors to represent both positive and
negative numbers:

[[
Equations signed (_: list bool) : Z :=
  signed [] := 0;
  signed [x] := -x;
  signed (x :: u) := 2 * signed u + x.
]]
*)

(* begin hide *)

(* Presumably we can switch to the simpler definition above at some point. *)
Equations signed (_: list bool) : Z :=
  signed [] := 0;
  signed (x :: u) := match u with
                    | [] => -x
                    | _ => 2 * signed u + x
                    end.

Lemma signed_equation_3: forall (x : bool) (u : list bool), u <> [] -> signed (x :: u) = 2 * signed u + x.
Proof.
  intros x [|y u] H; simp signed; [contradict H|]; reflexivity.
Qed.

Lemma toBits_signed: forall {n} (u: vector bool n), toBits n (signed u) = u.
Proof.
  induction u as [|x n u IH].
  - reflexivity.
  - destruct u as [|y n u].
    + simp signed toBits.
      destruct x; reflexivity.
    + assert (to_list (Vector.cons x (Vector.cons y u)) = (x :: (Vector.cons y u))) as H;
        [reflexivity
        |rewrite H; clear H].
      rewrite signed_equation_3; [|easy].
      rewrite toBits_equation_3 at 1.
      rewrite IH.
      reflexivity.
Qed.

(* end hide *)

(** The most significant bit determines if the [signed u] is negative, and
[signed u] $\equiv$ [fromBits u] $\pmod{2^n}$ for every [u: vector bool n].
*)



(** *** Bytes and words

In this text we shall mainly be concerned with bit vectors consisting of
8, 16, 32 and 64 bits: *)

Definition Bits8  := vector bool  8.
Definition Bits16 := vector bool 16.
Definition Bits32 := vector bool 32.
Definition Bits64 := vector bool 64.

(* begin hide *)
(* The limitations of the Coq coercion mechanism means that it is not
enough to define fromBits to be a coercion from [list bool] to [nat]. *)
Definition fromBits8  (u: Bits8)  := fromBits (to_list u). Coercion fromBits8  : Bits8  >-> nat.
Definition fromBits16 (u: Bits16) := fromBits (to_list u). Coercion fromBits16 : Bits16 >-> nat.
Definition fromBits32 (u: Bits32) := fromBits (to_list u). Coercion fromBits32 : Bits32 >-> nat.
Definition fromBits64 (u: Bits64) := fromBits (to_list u). Coercion fromBits64 : Bits64 >-> nat.
(* end hide *)

(** The elements of [Bits8] are called _bytes_. If we concatenate a list
of bytes, we get a bit vector which represents a natural number. More
precisely: *)

Equations fromLittleEndian (_: list Bits8): nat :=
  fromLittleEndian [] := 0;
  fromLittleEndian (x :: r) := 256 * (fromLittleEndian r) + x.

(* begin hide *)
Section limit_scope.
Open Scope vector_scope.
(* end hide *)

Equations toLittleEndian n (_: Z) : vector Bits8 n :=
  toLittleEndian 0 _ := [];
  toLittleEndian (S n) z := (toBits 8 z) :: (toLittleEndian n (z / 256)).

(** Observe that the "least significant byte" comes first. *)

(* begin hide *)
End limit_scope.

(* TODO: Is this a good idea to avoid switching between [nat_scope] and [Z_scope]? *)
Notation "'0'" := O.
Notation "x < y" := (Nat.lt x y).

(* This could be generalized to all $x < 2^n$. *)
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

(* end hide *)


(** ** Monads

A _monad_ consist of a generic type [m] and two operations that satisfy
three axioms. In Coq this can be expressed as a "type class": *)

(* Based on https://github.com/coq/coq/wiki/AUGER_Monad. *)
Class Monad (m: Type -> Type): Type :=
{
  ret: forall A, A -> m A;
  bind: forall A, m A -> forall B, (A -> m B) -> m B;

  monad_right: forall A (ma: m A), ma = bind ma (@ret A);
  monad_left: forall A (a: A) B (f: A -> m B), f a = bind (ret a) f;
  monad_assoc: forall A (ma: m A) B f C (g: B -> m C),
      bind ma (fun a => bind (f a) g) = bind (bind ma f) g;
}.

(* begin hide *)
Notation "ma >>= f" := (bind ma _ f) (at level 98, left associativity).
Notation "a ::= ma ; mb" := (bind ma _ (fun a => mb)) (at level 60, right associativity, only parsing).
Notation "ma ;; mb" := (bind ma _ (fun _ => mb)) (at level 60, right associativity).
(* end hide *)

(** Working with monads, we use the following notation:
%
\begin{center}
\begin{tabular}{l@{$\qquad$ means $\qquad$}l}
%
[ma >>= f]      %&% [bind ma f] %\\%
[a ::= ma ; mb] %&% [bind ma (fun a => mb)] %\\%
[ma ;; mb]      %&% [bind ma (fun _ => mb)]
%
\end{tabular}
\end{center}
%
The type arguments ([A] and [B]) are most of the time left implicit. *)

Definition lift {m} `{Monad m} {A B: Type} (f: A -> B) (ma: m A): m B :=
  a ::= ma;
  ret (f a).

Equations traverse {m} `{Monad m} {A B: Type} (_: A -> m B) (_: list A) : m (list B) :=
  traverse _ [] := ret [];
  traverse f (x :: u) := y ::= f x; v ::= traverse f u; ret (y :: v).

(** Many generic types have operations that satisfy the monad axioms, but
in this text we shall use only two. The simplest of these is the "Maybe
monad": *)

Instance Maybe: Monad option :=
{
  ret A x := Some x;
  bind A ma B f := match ma with None => None | Some a => f a end
}.
Proof.
  - abstract (intros A a; case a; split).
  - abstract (split).
  - abstract (intros A x B f C g; case x; split).
Defined.

(** We leave the proofs of the monad axioms to the reader. *)


(** ** State and the state monad

As discovered by Eugenio Moggi in 1989, monads can be used to represent
computations with "side-effects" such as input and output; and below we
shall specify the behaviour of our virtual machine in terms of a
non-deterministic state monad. First we define types representing the
state of the machine at a given moment. *)

Record Image (C: Type) :=
  mkImage {
      iWidth: Bits16;
      iHeight: Bits16;
      iPixel: forall (x: nat) (Hx: x < iWidth) (y: nat) (Hy: y < iHeight), C;
    }.

(** In Coq a record is an inductive type with a single constructor
([mkImage]), where we projections "for free". For example, if [im: Image
Bits8], then [iWidth im: Bits16]. The arguments to iWidth and iHeight are
implicit in the type of iPixel. The type [C] represents the color of a
single pixel.

The simplest image consists of [0 * 0] pixels:

[[
Definition noImage {C} : Image C :=
  {|
     iWidth := toBits 16 0;
     iHeight := toBits 16 0;
     iPixel := _;
  |}.
]]
*)

(* begin hide *)
Definition noImage {C} : Image C.
  refine ({|
             iWidth := toBits 16 0;
             iHeight := toBits 16 0;
             iPixel := _;
           |}).
  unfold fromBits16.
  rewrite zeroBits_zero.
  intros x Hx.
  contradiction (Nat.nlt_0_r x Hx).
Defined.
(* end hide *)

(** The [Sound] type represents a clip of stereo sound in LPCM encoding.
Both channels have the same sample rate, and each pair of 16-bit words
[(left, right)] contains one sample for each channel. For convenience,
[sSamples] contains samples in reverse order. *)

Record Sound :=
  mkSound {
      sRate: Bits32;
      sSamples: list (Bits16 * Bits16);
      sDef: 0 = sRate -> sSamples = [];
    }.

(**
[[
Definition noSound : Sound :=
  {|
    sRate := toBits 32 0;
    sSamples := [];
    sDef := _;
  |}.
]]
*)

(* begin hide *)
Definition noSound : Sound.
  refine ({|
             sRate := toBits 32 0;
             sSamples := [];
             sDef := _;
           |}).
  trivial.
Defined.
(* end hide *)

(** Textual output from the machine uses the encoding UTF-32. Again, we
use reverse ordering. *)

Definition OutputText := list Bits32.

(* begin hide *)
Section limit_scope.
Open Scope vector_scope.
(* end hide *)

(** The virtual machine uses 64-bit memory addresses. *)

Equations addresses n (_: Bits64) : vector Bits64 n :=
  addresses 0 _ := [];
  addresses (S n) start := start :: (addresses n (toBits 64 (start + 1))).

(** We keep track of all memory allocations and the contents of the
allocated memory. The contents of unallocated memory is not relevant. *)

Definition consistent (memory: Bits64 -> option Bits8) (allocation: Bits64 -> nat) :=
  (forall (a: Bits64),
      memory a <> None <->
      exists start, In a (addresses (allocation start) start))
  /\
  (forall start0 start1,
      (Exists
         (fun a => In a (addresses (allocation start0) start0))
         (addresses (allocation start1) start1)) ->
      start0 = start1).

(** In this definition [Exists: forall A, (A->Prop)->list A->Prop] as expected, and [In
a = Exists (fun x => x=a)]. *)

(* begin hide *)
Open Scope type_scope.
(* end hide *)
Definition Gray := Bits8.
Definition Color := Bits16 * Bits16 * Bits16.
(* begin hide *)
End limit_scope.
(* end hide *)

(** [Gray] represents the gray scale of the input images (where 0 is
black), whereas [Color] represents the ACES encoded colors of the output
images. The [State] type can now be formulated as follows: *)

Record State :=
  mkState {
      terminated: bool;
      PC: Bits64;
      SP: Bits64;
      input: list (Image Gray);
      output: list ((Image Color) * Sound * OutputText);
      memory: Bits64 -> option Bits8;
      allocation: Bits64 -> nat;
      consistency: consistent memory allocation;
      always_output: output <> []
    }.

(** [PC] and [SP] are known as the "program counter" and the "stack
pointer", respectively. Each elements of [output] consists of an image,
the sound clip to be played while this image is displayed, and an
associated piece of text. Any of these elements may be empty; and the list
is reversed in the sense that the first triple in the list should be
rendered last. The list [input] will only be decreasing as the machine
processes the input. Conversely, [output] will only be increasing, except
that the first element in this list should be considered "in progress"
until the machine terminates. *)


(* begin hide *)

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

(* end hide *)


(** The non-deterministic state monad can now be defined as follows: *)

Definition ST (A: Type) := State -> A -> State -> Prop.

(* begin hide *)

(* Extensionality is needed since A is an arbitrary type.
   This can be avoided if we define monads in terms of a setoid.
 *)
Lemma ST_extensionality {A} (st0 st1: ST A):
  (forall s0 x s1, st0 s0 x s1 <-> st1 s0 x s1) -> st0 = st1.
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

(* end hide *)

Instance StateMonad: Monad ST :=
  {
    ret A x := fun s0 y s1 => x = y /\ s0 = s1;
    bind A st B f := fun s0 y s2 => exists x s1, st s0 x s1 /\ f x s1 y s2
  }.
Proof.
  - abstract (st_tactics.crush).
  - abstract (st_tactics.crush).
  - abstract (st_tactics.crush).
Defined.

(** The proof of the monad axioms is straightforward using propositional
and functional extensionality. An element [st: ST A] represents a
computation with possible side-effect which produces a value of type [A].
More precisely:

- [st s0 x s1] means that a result of executing [st] from state [s0] may
  be that [x] is produced and that the machine transitions to state [s1].

- If [terminated s0 = false] and [not exists s1 x, st s0 x s1], then the result
  of executing [st] at [s0] is undefined.

See also the definition of [ConformingTransitions] below. [ST unit]
represents computations that do not produce any values. (They may,
however, produce _output_.) *)


(** ** Building blocks

Since [ST A] represents non-deterministic computations, it is closed under
intersection. We mainly use this to express that computations leave most
of the state unchanged. *)

Definition intersect' {A} (st1 st2: ST A): ST A :=
  fun s0 x s1 => st1 s0 x s1 /\ st2 s0 x s1.

(** We use [st1 ∩ st2] as an abbreviation for [intersect' st1 st2]; and we
follow the convention (that functions producing) computations have names
ending with an apostrophe. *)

(* begin hide *)
Notation "st1 ∩ st2" := (intersect' st1 st2) (at level 50, left associativity).
(* end hide *)

Definition fail' {A}: ST A := fun _ _ _ => False.

Lemma intersect_fail: forall {A} (st: ST A), st ∩ fail' = fail'.
Proof.
  intros.
  unfold fail', intersect'.
  st_tactics.crush.
Qed.


(** *** Unchanged and mostly unchanged state *)

Definition stateUnchanged' {A} : ST A :=
  fun s0 _ s1 => s0 = s1.

(* begin hide *)

Lemma ret_characterized {A} (x: A) :
  stateUnchanged' ∩ (fun _ y _ => x = y) = ret x.
Proof.
  unfold stateUnchanged', intersect'.
  st_tactics.crush.
Qed.

(* end hide *)

Definition registersUnchanged' {A} : ST A :=
  fun s0 _ s1 =>
    terminated s0 = terminated s1
    /\ PC s0 = PC s1
    /\ SP s0 = SP s1.

Definition memoryUnchanged' {A} : ST A :=
  fun s0 _ s1 => memory s0 = memory s1.

Definition allocationsUnchanged' {A} : ST A :=
  fun s0 _ s1 => allocation s0 = allocation s1.

Definition otherMemoryUnchanged' (n: nat) (start: Bits64): ST unit :=
  fun s0 _ s1 =>
    let other a := Forall (fun x => x <> a) (addresses n start) in
    forall a, other a -> memory s0 a = memory s1 a.

(** This means that the memory is unchanged except possibly for the [n]
bytes starting at address [start]. *)

Definition otherAllocationsUnchanged' (start: Bits64) : ST unit :=
  fun s0 _ s1 =>
    forall a, a <> start -> allocation s0 a = allocation s1 a.

Definition ioUnchanged' {A} : ST A :=
  fun s0 _ s1 =>
    input s0 = input s1
    /\ output s0 = output s1.

(* begin hide *)

Lemma stateUnchanged_characterized {A} :
  registersUnchanged' ∩ memoryUnchanged' ∩ allocationsUnchanged' ∩ ioUnchanged' = @stateUnchanged' A.
Proof.
  unfold registersUnchanged', memoryUnchanged', allocationsUnchanged', ioUnchanged', stateUnchanged'.
  repeat (unfold intersect').
  st_tactics.crush.
Qed.

(* end hide *)

(** Now the [EXIT] instruction can be specified as follows. *)

Definition exit' : ST unit :=
  memoryUnchanged'
    ∩ allocationsUnchanged'
    ∩ ioUnchanged'
    ∩ fun s0 _ s1 =>
        terminated s1 = true
        /\ PC s0 = PC s1
        /\ SP s0 = SP s1.


(** *** Memory access *)

(** Here is how we specify the [LOAD] instructions: *)

Definition load' (n: nat) (start: Bits64) : ST nat :=
  stateUnchanged'
    ∩ fun s x _ => lift fromLittleEndian
                     (traverse (memory s) (addresses n start)) = Some x.

(** In words, [load' n a s0 x s1] means that [s0 = s1] and that the [n]
bytes starting at [a] represents the natural number [x] $<2^n$. The
computation fails unless the addresses [start], ..., [start+n-1] have all
been allocated. *)

(* Observe that if (store' n start value s0 x s1), then we know that the
   addresses were allocated because of [consistency s1].
   Formally:
   Vector.Forall (fun a => memory s0 a <> None) (addresses n start)
 *)
Definition store' (n: nat) (start: Bits64) (value: nat) : ST unit :=
  registersUnchanged'
    ∩ ioUnchanged'
    ∩ otherMemoryUnchanged' n start
    ∩ allocationsUnchanged'
    ∩ fun s0 _ s1 => load' n start s1 value s1.

(**

Therefore, we also have [load' n start s0 y s1] for every [y] such that
[x] $\equiv$ [y] $\pmod{2^n}$.
*)

(** *** Stack and program counter *)

Definition setPC' (a: Bits64): ST unit :=
  memoryUnchanged'
    ∩ allocationsUnchanged'
    ∩ ioUnchanged'
    ∩ fun s0 _ s1 =>
         terminated s0 = terminated s1
         /\ SP s0 = SP s1
         /\ a = PC s1.

Definition setSP' (a: Bits64): ST unit :=
  memoryUnchanged'
    ∩ allocationsUnchanged'
    ∩ ioUnchanged'
    ∩ fun s0 _ s1 =>
        terminated s0 = terminated s1
        /\ PC s0 = PC s1
        /\ a = SP s1.

(** The corresponding "get" computations are simple instances of
[extract']. *)

Definition extract' {A} (f: State -> A): ST A :=
  stateUnchanged' ∩ (fun s x _ => f s = x).

Definition next' (n: nat) : ST nat :=
  a ::= extract' PC;
  setPC' (toBits 64 (a + n));;
  load' n a.

Definition possiblyModifyMemory' n a :=
  registersUnchanged'
    ∩ ioUnchanged'
    ∩ otherMemoryUnchanged' n a
    ∩ allocationsUnchanged'.

Definition pop': ST Bits64 :=
  a ::= extract' SP;
  v ::= load' 8 a;
  setSP' (toBits 64 (a + 8));;
  possiblyModifyMemory' 8 a;;
  ret (toBits 64 v).

(** Observe that an implementation of 'pop' may modify the freed stack. *)

(* begin hide*)
Definition push' (value: Z): ST unit :=
  a0 ::= extract' SP;
  let a1 := toBits 64 (a0 - 8) in
  setSP' a1;;
  store' 8 a1 (toBits 64 value : Bits64).
(* end hide *)

(**
[[
Definition push' (value: Z): ST unit :=
  a0 ::= extract' SP;
  let a1 := toBits 64 (a0 - 8) in
  setSP' a1;;
  store' 8 a1 (toBits 64 value).
]]
*)


(** *** Memory allocation *)

Definition allocate' (n: nat) : ST Bits64 :=
  registersUnchanged'
    ∩ ioUnchanged'
    ∩ fun s0 start s1 =>
        allocation s0 start = 0
        /\ allocation s1 start = n
        /\ otherAllocationsUnchanged' start s0 tt s1
        /\ otherMemoryUnchanged' n start s0 tt s1
        /\ load' n start s1 0 s1.

(** Observe that newly allocated memory will be initialized to zero.

TODO: Do we have to disallow that [allocate'] returns (address) 0 to avoid
confusion with C's NULL pointer? *)

Definition deallocate' (start: Bits64) : ST unit :=
  registersUnchanged'
    ∩ ioUnchanged'
    ∩ otherAllocationsUnchanged' start
    ∩ fun s0 _ s1 =>
        allocation s1 start = 0
        /\ otherMemoryUnchanged' (allocation s0 start) start s0 tt s1.

(** Memory [consistency] ensures that deallocated memory is None. TODO: it
makes sense to allocate 0 bytes or deallocate an address which is not
allocated. This is not compatible with free() in C! *)


(** *** Input and output *)

Definition nonIoUnchanged' {A} : ST A :=
  registersUnchanged'
    ∩ memoryUnchanged'
    ∩ allocationsUnchanged'.

Definition readFrame' : ST (Bits16 * Bits16) :=
  nonIoUnchanged'
    ∩ fun s0 wh s1 =>
        output s0 = output s1
        /\ match input s1 with
          | [] | [_] => wh = (toBits 16 0, toBits 16 0)
          | _ :: hd :: tl =>
            wh = (iWidth hd, iHeight hd)
            /\ input s1 = hd :: tl
          end.

Definition readPixel' (x y: nat) : ST Bits8 :=
  stateUnchanged'
    ∩ fun s0 z _ =>
        match input s0 with
        | [] => False
        | frame :: _ =>
          exists (Hx: x < iWidth frame)
            (Hy: y < iHeight frame), z = iPixel frame Hx Hy
        end.

(* Initial frame pixels: undefined. *)
Definition newFrame' (width height sampleRate: nat) : ST unit :=
  nonIoUnchanged'
    ∩ fun s0 _ s1 =>
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

Definition setPixel' (x y r g b : nat) : ST unit :=
  nonIoUnchanged'
    ∩ fun s0 _ s1 =>
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
                                       if (if xx =? x then yy =? y else false)
                                       then (toBits 16 r, toBits 16 g, toBits 16 b)
                                       else @iPixel _ i0 xx Hx1 yy Hy1
          | _, _ => False
          end.

Definition addSample' (left right : nat) : ST unit :=
  nonIoUnchanged'
    ∩ fun s0 _ s1 =>
        input s0 = input s1
        /\ match output s0, output s1 with
          | (i0, s0, t0) :: r0, (i1, s1, t1) :: r1 =>
            r0 = r1
            /\ t0 = t1
            /\ i0 = i1
            /\ sRate s0 = sRate s1
            /\ 0 <> sRate s0 (* Otherwise undefined *)
            /\ (toBits 16 left, toBits 16 right) :: sSamples s0 = sSamples s1
          | _, _ => False
          end.

Definition putChar' (c: nat) : ST unit :=
  nonIoUnchanged'
    ∩ fun s0 _ s1 =>
        input s0 = input s1
        /\ match output s0, output s1 with
          | (i0, s0, t0) :: r0, (i1, s1, t1) :: r1 =>
            r0 = r1
            /\ s0 = s1
            /\ i0 = i1
            /\ (toBits 32 c) :: t0 = t1
          | _, _ => False
          end.


(** ** Single execution step

The virtual machine has the following "opcodes":

%
\newcommand\col[1]{\begin{tabular}[t]{rl}#1\end{tabular}}
\begin{center}
\col{
 0 & \coqdocvar{EXIT}\\
 1 & \coqdocvar{NOP}\\
 2 & \coqdocvar{JUMP}\\
 3 & \coqdocvar{JUMP\_ZERO}\\
 4 & \coqdocvar{SET\_SP}\\
 5 & \coqdocvar{GET\_PC}\\
 6 & \coqdocvar{GET\_SP}\\
 7 & \coqdocvar{PUSH0}\\
 8 & \coqdocvar{PUSH1}\\
 9 & \coqdocvar{PUSH2}\\
10 & \coqdocvar{PUSH4}\\
11 & \coqdocvar{PUSH8}
}
\col{
12 & \coqdocvar{SIGX1}\\
13 & \coqdocvar{SIGX2}\\
14 & \coqdocvar{SIGX4}\\
16 & \coqdocvar{LOAD1}\\
17 & \coqdocvar{LOAD2}\\
18 & \coqdocvar{LOAD4}\\
19 & \coqdocvar{LOAD8}\\
20 & \coqdocvar{STORE1}\\
21 & \coqdocvar{STORE2}\\
22 & \coqdocvar{STORE4}\\
23 & \coqdocvar{STORE8}\\
24 & \coqdocvar{ALLOCATE}\\
}
\col{
25 & \coqdocvar{DEALLOCATE}\\
32 & \coqdocvar{ADD}\\
33 & \coqdocvar{MULT}\\
34 & \coqdocvar{DIV}\\
35 & \coqdocvar{REM}\\
36 & \coqdocvar{LT}\\
40 & \coqdocvar{AND}\\
41 & \coqdocvar{OR}\\
42 & \coqdocvar{NOT}\\
43 & \coqdocvar{XOR}\\
44 & \coqdocvar{POW2}\\
48 & \coqdocvar{NEW\_FRAME}\\
}
\col{
49 & \coqdocvar{SET\_PIXEL}\\
50 & \coqdocvar{ADD\_SAMPLE}\\
52 & \coqdocvar{PUT\_CHAR}\\
56 & \coqdocvar{READ\_FRAME}\\
57 & \coqdocvar{READ\_PIXEL}\\
}
\end{center}
%
*)

(* begin hide *)

Module Instructions.
  Open Scope nat_scope.
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

Section limit_scope.
Import Instructions.
Let map (f: bool->bool) (u: Bits64) : Bits64 := Vector.map f u.
Let map2 (f: bool->bool->bool) (u: Bits64) (v: Bits64) : Bits64 := Vector.map2 f u v.
(* end hide *)

(** %\vspace{1ex}% The following definition specifies what it means for
the VM to perform a single execution step. We shall have more to say about
this after the definition. *)

Definition step' : ST unit :=
  stopped ::= extract' terminated;
  if stopped then fail'
  else
    opcode ::= next' 1;
    match opcode with
    | EXIT => exit'
    | NOP => stateUnchanged'

    | JUMP => pop' >>= setPC'
    | JUMP_ZERO =>
        offset ::= next' 1;
        v ::= pop';
        if v =? 0
        then pc ::= extract' PC;
             setPC' (toBits 64 (pc + (signed (toBits 8 offset))))
        else stateUnchanged'

    | SET_SP => pop' >>= setSP'
    | GET_PC => extract' PC >>= push'
    | GET_SP => extract' SP >>= push'

    | PUSH0 => push' 0
    | PUSH1 => next' 1 >>= push'
    | PUSH2 => next' 2 >>= push'
    | PUSH4 => next' 4 >>= push'
    | PUSH8 => next' 8 >>= push'

    | SIGX1 => v ::= pop'; push' (signed (toBits 8 v))
    | SIGX2 => v ::= pop'; push' (signed (toBits 16 v))
    | SIGX4 => v ::= pop'; push' (signed (toBits 32 v))

    | LOAD1 => pop' >>= load' 1 >>= push'
    | LOAD2 => pop' >>= load' 2 >>= push'
    | LOAD4 => pop' >>= load' 4 >>= push'
    | LOAD8 => pop' >>= load' 8 >>= push'

    | STORE1 => a ::= pop'; v ::= pop'; store' 1 a v
    | STORE2 => a ::= pop'; v ::= pop'; store' 2 a v
    | STORE4 => a ::= pop'; v ::= pop'; store' 4 a v
    | STORE8 => a ::= pop'; v ::= pop'; store' 8 a v

    | ALLOCATE => pop' >>= allocate' >>= push'
    | DEALLOCATE => pop' >>= deallocate'

    | ADD => x ::= pop'; y ::= pop'; push' (x + y)
    | MULT => x ::= pop'; y ::= pop'; push' (x * y)
    | DIV =>
        x ::= pop';
        y ::= pop';
        push' (if x =? 0 then 0 else y / x)
    | REM =>
        x ::= pop';
        y ::= pop';
        push' (if x =? 0 then 0 else y mod x)
    | LT =>
        x ::= pop';
        y ::= pop';
        push' (if y <? x then -1 else 0)
    | AND =>
        u ::= pop';
        v ::= pop';
        push' (map2 (fun x y => if x then y else false) u v)
    | OR =>
        u ::= pop';
        v ::= pop';
        push' (map2 (fun x y => if x then true else y) u v)
    | XOR =>
        u ::= pop';
        v ::= pop';
        push' (map2 (fun x y => if x then (if y then false else true) else y) u v)
    | NOT =>
        u ::= pop';
        push' (map (fun x => if x then false else true) u)
    | POW2 =>
        n ::= pop';
        push' (2 ^ n)

    | NEW_FRAME =>
        rate ::= pop';
        height ::= pop';
        width ::= pop';
        newFrame' width height rate
    | SET_PIXEL =>
        b ::= pop';
        g ::= pop';
        r ::= pop';
        y ::= pop';
        x ::= pop';
        setPixel' x y r g b
    | ADD_SAMPLE =>
        right ::= pop';
        left ::= pop';
        addSample' left right
    | PUT_CHAR =>
        pop' >>= putChar'

    | READ_FRAME =>
        wh ::= readFrame';
        push' (fst wh);;
        push' (snd wh)
    | READ_PIXEL =>
        x ::= pop';
        y ::= pop';
        readPixel' x y >>= push'

    | _ => fail'
    end.

(* begin hide *)
End limit_scope.
(*end hide *)
(** In this definition %\,%[map: (bool->bool)->Bits64->Bits64] and %\,%[map2:
(bool->bool->bool)->Bits64->Bits64->Bits64] denote the obvious "bitwise"
transformations. *)

Lemma no_progress_after_termination: forall s t, step' s tt t -> terminated s = false.
Proof.
  (* TODO: automate *)
  intros s t H.
  enough (terminated s = true -> False); [destruct (terminated s); easy | intro Ht].
  revert H.
  unfold step'.
  Set Warnings "-variable-collision".
  match goal with [ |- context [stopped ::= extract' terminated;
                               if stopped then fail' else ?R]] => generalize R end.
  Set Warnings "variable-collision".
  intro st_else.
  unfold extract', intersect'.
  simpl.
  rewrite Ht; clear Ht.
  intros [x [s1 [[H1 H2] H3]]].
  revert H3.
  subst.
  unfold fail'.
  trivial.
Qed.

(** A conforming implementation must have the following properties: *)

Class ConformingTransitions (trans: State -> State -> Prop) :=
  {
    ct_termination: forall s t, trans s t -> terminated s = false;
    ct_progress: forall s, (exists t, step' s tt t) -> exists t, trans s t;
    ct_correctness: forall s, (exists t, step' s tt t) -> forall t, (trans s t -> step' s tt t);
  }.

(** In other words, an implementation is a transition system [trans] with
the following properties:

- If [terminated s = true], then [not exists t, trans s t]%\,%.

- If [terminated s = false] and [exists t, step' s tt t], then
  [exists t, trans s t]%\:% and [step' s tt t]%\,% for all such [t].

- If [terminated s = false] and [not exists t, step' s tt t],
  then the behaviour is undefined.

Observe that [trans] does not have to be completely deterministic e.g.%\ %
with regards to the addresses of newly allocated memory.


** The initial state

Before the machine can start, we must put a program in the memory and set
the program counter ([PC]) to its start position. We must also initialize
the stack and stack pointer ([SP]). Moreover, the initial state should
contain the full list of input frames and no output frames.

[[
Definition protoState (inputList: list (Image Gray)) : State :=
  {|
    terminated := false;
    PC := toBits 64 0;
    SP := toBits 64 0;
    input := noImage :: inputList;
    output := [(noImage, noSound, [])];
    memory := fun _ => None;
    allocation := fun _ => 0;
  |}.
]]
*)

(* begin hide *)

Definition protoState (inputList: list (Image Gray)) : State.
  refine ({|
             terminated := false;
             PC := toBits 64 0;
             SP := toBits 64 0;
             input := noImage :: inputList;
             output := [(noImage, noSound, [])];
             memory := fun _ => None;
             allocation := fun _ => 0;
           |}).
  (* TODO: Automate *)
  - split.
    + firstorder.
    + intros x y.
      funelim (addresses 0 x).
      simpl.
      intro H.
      exfalso.
      induction H; assumption.
  - congruence.
Defined.

Section limit_scope.
Open Scope nat_scope.

(* end hide *)

Equations fillMemory' (_: Bits64) (_: list Bits8) : ST unit :=
  fillMemory' _ [] := stateUnchanged';
  fillMemory' start (x :: u) := store' 1 start x ;; fillMemory' (toBits 64 (start + 1)) u.

Definition loadProgram' (program: list Bits8) (argument: list Bits8) : ST unit :=
  program_start ::= allocate' (length program);
  fillMemory' program_start program;;
  setPC' program_start;;
  let len := length argument in
  let restSize := len + 4 * 8 in
  argument_start ::= allocate' restSize;
  fillMemory' argument_start argument;;
  store' 8 (toBits 64 (argument_start + len)) len;;
  setSP' (toBits 64 (argument_start + restSize)).

(* begin hide *)
End limit_scope.
(* end hide *)

Definition conformingInitialState inputList program argument : State -> Prop :=
  loadProgram' program argument (protoState inputList) tt.

(** In other words, a conforming implementation must start the machine in
a state which satisfies this predicate. This completes our specification.
It is somewhat idealized. For example, our programs never need more than
$2^{34}$ bytes of allocated memory. *)
