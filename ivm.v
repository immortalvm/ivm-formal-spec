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
(** printing sn $\coqdocvar{s}_n$ *)
(** printing st1 $\coqdocvar{st}_1$ *)
(** printing st2 $\coqdocvar{st}_2$ *)
(** printing x1 $\coqdocvar{x}_1$ *)
(** printing xn $\coqdocvar{x}_n$ *)


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


(** ** State and state monad

As discovered by Eugenio Moggi in 1989, monads can be used to represent
computations with "side-effects" such as input and output. Below we shall
specify the behaviour of our virtual machine in terms of a partial
computational monad, but first we define types representing the state of
the machine at a given moment.

*** VM state *)

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
      PC: Bits64;
      SP: Bits64;
      input: list (Image Gray);
      output: list ((Image Color) * Sound * OutputText);
      memory: Bits64 -> option Bits8;
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
    PC := PC s;
    SP := SP s;
    input := input s;
    output := output s;
    memory := memory s;
    always_output := always_output s;
  |}.
Proof.
  reflexivity.
Qed.

(* Since State is finite, this might be provable even without
   PropExtensionality, but that will have to wait. *)
Lemma State_injectivity
      p0 s0 i0 o0 m0 ao0
      p1 s1 i1 o1 m1 ao1:
  p0=p1 -> s0=s1 -> i0=i1 -> o0=o1 -> m0=m1
  -> {|PC:=p0; SP:=s0; input:=i0; output:=o0; memory:=m0; always_output:=ao0|}
  = {|PC:=p1; SP:=s1; input:=i1; output:=o1; memory:=m1; always_output:=ao1|}.
Proof.
  repeat (intro e; destruct e).
  destruct (proof_irrelevance (o0 <> []) ao0 ao1).
  reflexivity.
Qed.

Lemma State_extensionality : forall (s0 s1: State),
    PC s0 = PC s1
    -> SP s0 = SP s1
    -> input s0 = input s1
    -> output s0 = output s1
    -> memory s0 = memory s1
    -> s0 = s1.
Proof.
  intros.
  rewrite (State_expansion s0).
  rewrite (State_expansion s1).
  apply State_injectivity; assumption.
Qed.

(* end hide *)


(** *** State monads *)

(** A "computation specification monad" can now be defined as follows: *)

Definition ST (A: Type) := State -> A -> State -> Prop.

(* begin hide *)

(* Extensionality is needed since A is an arbitrary type.
   This can be avoided if we define monads in terms of setoids. *)
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

  Ltac ex_tac := fail.
  Ltac crush := repeat (
                    intro || split || assumption || discriminate || subst
                    || apply State_extensionality
                    || apply ST_extensionality
                    || simpl in * || destr || ex_tac).
  Ltac ex_tac ::=
    match goal with
    | [ |- exists x s, x = ?x' /\ s = ?s' /\ _] => exists x; exists s; solve[crush]
    | [x:?X, s:State, _:context H[_ ?x ?s] |- exists _: ?X, exists _: State, _ ] => exists x; exists s; solve[crush]
    end.

  Ltac special :=
    match goal with
    | [ H1: forall x (s: State), ?st x s -> ?R, H2: ?st ?x ?s  |- _ ] =>
      let h := fresh in
      specialize (H1 _ _ H2) as h;
      try exact h;
      try destruct h as [? [? h]]
    end.
End st_tactics.

(* end hide *)

Instance SpecificationMonad: Monad ST :=
  {
    ret A x := fun s0 y s1 => x = y /\ s0 = s1;
    bind A st B f := fun s0 y s2 => exists x s1, st s0 x s1 /\ f x s1 y s2;
  }.
Proof.
  - abstract (st_tactics.crush).
  - abstract (st_tactics.crush).
  - abstract (st_tactics.crush).
Defined.

(** TODO: Rewrite

The proof of the monad axioms is easy assuming propositional and
functional extensionality.

Informally, an element [st: ST A] specifies a computation with possible
side-effects which should produce a value of type [A]. Suppose we execute
an implementation of [st] starting in state [s0].

- If [exists s1 x, st s0 x s1], then the implementation should produce an
  element [x] and lead to a state [s1] such that [st s0 x s1].

- Otherwise, the result of executing the implementation is undefined.

In other words, if [st s0 x s <-> (x = x1 /\ s = s1) \/ ... \/ (x = xn /\ s =
sn)], then the implementation must produce one of [n] results if [n > 0].
If [n = 0], the implementation is unconstrained since this should never
happen in a correct program. Furthermore, our definition of [bind] ensures
that if running [st] from state [s0] is undefined and [f: A -> ST B], then
running [st >>= f] from [s0] is undefined as well. *)


(** ** Primitive computations

[ST unit] represents computations that do not produce any value. They may,
however, produce output and have other side-effects. In the next section
we shall specify one execution step of our virtual machine as a term
[step': ST unit], but first we need some more building blocks.


*** Lattice structure

A specification [st: ST A] is often "non-deterministic" in the sense that
[st s0 x1 s1] and [st s0 x2 s2] does not imply [x1 = x2] or [s1 = s2]. It
simply means that both [(x1, s1)] and [(x2, s2)] are possible outcomes.
Thus, it makes sense to define the intersection of two such specifications
as follows: *)

Definition intersect' {A} (st1 st2: ST A): ST A :=
  fun s0 x s1 => st1 s0 x s1 /\ st2 s0 x s1.

(* begin hide *)
Notation "st1 ∩ st2" := (intersect' st1 st2) (at level 50, left associativity).
(* end hide *)

(** We use [st1 ∩ st2] as an abbreviation for [intersect' st1 st2]. [ST A]
clearly inherits a full lattice structure from the type of propositions,
but we shall only use [∩] and the least element: *)

Definition stop' {A}: ST A := fun _ _ _ => False.

(* begin hide *)

Lemma intersect_stop: forall {A} (st: ST A), st ∩ stop' = stop'.
Proof.
  intros.
  unfold stop', intersect'.
  st_tactics.crush.
Qed.

Lemma bind_stop: forall {A B} (st: ST A), (st ;; stop') = stop' :> ST B.
Proof.
  unfold stop'.
  st_tactics.crush.
Qed.

(* end hide *)

(** We follow the convention that specifications (and functions returning
specifications) have names ending with an apostrophe. For this reason we
also define: *)

Definition return' {A} (x: A) : ST A := ret x.


(** *** Unchanged and mostly unchanged state

Many computations leave the state unchanged or mostly unchanged. This can
be expressed this using intersection and the following specifications. *)

Definition stateUnchanged' {A} : ST A :=
  fun s0 _ s1 => s1 = s0.

(* begin hide *)

Lemma ret_characterized {A} (x: A) :
  stateUnchanged' ∩ (fun _ y _ => y = x) = ret x.
Proof.
  unfold stateUnchanged', intersect'.
  st_tactics.crush.
Qed.

(* end hide *)

Definition registersUnchanged' {A} : ST A :=
  fun s0 _ s1 =>
    PC s1 = PC s0
    /\ SP s1 = SP s0.

Definition memoryUnchanged' {A} : ST A :=
  fun s0 _ s1 => memory s1 = memory s0.

Definition otherMemoryUnchanged' (n: nat) (start: Bits64): ST unit :=
  fun s0 _ s1 =>
    let other a := Forall (fun x => x <> a) (addresses n start) in
    forall a, other a -> memory s1 a = memory s0 a.

(** This means that the memory is unchanged except possibly for the [n]
bytes starting at address [start]. *)

Definition ioUnchanged' {A} : ST A :=
  fun s0 _ s1 =>
    input s1 = input s0
    /\ output s1 = output s0.

(* begin hide *)

Lemma stateUnchanged_characterized {A} :
  registersUnchanged' ∩ memoryUnchanged' ∩ ioUnchanged' = @stateUnchanged' A.
Proof.
  unfold registersUnchanged', memoryUnchanged', ioUnchanged', stateUnchanged'.
  repeat (unfold intersect').
  st_tactics.crush.
Qed.

(* end hide *)


(** *** Memory access *)

(** Here is how we specify the [LOAD] instructions: *)

Definition load' (n: nat) (start: Bits64) : ST nat :=
  stateUnchanged'
    ∩ fun s x _ => Some x = lift fromLittleEndian
                              (traverse (memory s) (addresses n start)).

(** In words, [load' n a s0 x s1] means that [s0 = s1] and that the [n]
bytes starting at [a] represents the natural number [x] $<2^n$. If not all
the addresses [start], ..., [start+n-1] are available, the machine stops.
*)

Definition memoryAvailable' {A} (n: nat) (start: Bits64): ST A :=
  fun s0 _ _ => Forall (fun a => memory s0 a <> None) (addresses n start).

Definition store' (n: nat) (start: Bits64) (value: nat) : ST unit :=
  registersUnchanged'
    ∩ ioUnchanged'
    ∩ memoryAvailable' n start
    ∩ otherMemoryUnchanged' n start
    ∩ fun s0 _ s1 => load' n start s1 value s1.


(** *** Stack and program counter *)

Definition setPC' (a: Bits64): ST unit :=
  memoryUnchanged'
    ∩ ioUnchanged'
    ∩ fun s0 _ s1 =>
        SP s1 = SP s0
         /\ PC s1 = a.

Definition setSP' (a: Bits64): ST unit :=
  memoryUnchanged'
    ∩ ioUnchanged'
    ∩ fun s0 _ s1 =>
        PC s1 = PC s0
        /\ SP s1 = a.

(** The corresponding "get" computations are simple instances of
[extract']. *)

Definition extract' {A} (f: State -> A): ST A :=
  stateUnchanged' ∩ (fun s x _ => f s = x).

Definition next' (n: nat) : ST nat :=
  a ::= extract' PC;
  setPC' (toBits 64 (a + n));;
  load' n a.

Definition pop': ST Bits64 :=
  a ::= extract' SP;
  v ::= load' 8 a;
  setSP' (toBits 64 (a + 8));;
  return' (toBits 64 v).

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


(** *** Input and output *)

Definition nonIoUnchanged' {A} : ST A :=
  registersUnchanged' ∩ memoryUnchanged'.

Definition readFrame' : ST (Bits16 * Bits16) :=
  nonIoUnchanged'
    ∩ fun s0 wh s1 =>
        output s1 = output s0
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
        input s1 = input s0
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
            r1 = r0
            /\ t1 = t0
            /\ s1 = s0
            (* Needed since iPixel is undefined outside width*height. *)
            /\ iWidth i1 = iWidth i0
            /\ iHeight i1 = iHeight i0
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
            r1 = r0
            /\ t1 = t0
            /\ i1 = i0
            /\ sRate s1 = sRate s0
            /\ 0 <> sRate s0 (* Otherwise undefined *)
            /\ sSamples s1 = (toBits 16 left, toBits 16 right) :: sSamples s0
          | _, _ => False
          end.

Definition putChar' (c: nat) : ST unit :=
  nonIoUnchanged'
    ∩ fun s0 _ s1 =>
        input s0 = input s1
        /\ match output s0, output s1 with
          | (i0, s0, t0) :: r0, (i1, s1, t1) :: r1 =>
            r1 = r0
            /\ s1 = s0
            /\ i1 = i0
            /\ t1 = (toBits 32 c) :: t0
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
}
\col{
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
}
\col{
48 & \coqdocvar{NEW\_FRAME}\\
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
  opcode ::= next' 1;
  match opcode with
  | EXIT => stop'
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

  | _ => stop'
  end.

(* begin hide *)
End limit_scope.
(*end hide *)
(** In this definition %\,%[map: (bool->bool)->Bits64->Bits64] and %\,%[map2:
(bool->bool->bool)->Bits64->Bits64->Bits64] denote the obvious "bitwise"
transformations. *)


(** ** The initial state

Before the machine can start, we must put a program in the memory and set
the program counter to its start position. We must also initialize the
stack and stack pointer; and the initial state should contain the full
list of input frames and no output frames.

[[
Definition protoState (inputList: list (Image Gray)) : State :=
  {|
    PC := toBits 64 0;
    SP := toBits 64 0;
    input := noImage :: inputList;
    output := [(noImage, noSound, [])];
    memory := fun a => if a <? memorySize then Some (toBits 8 0) else None;
  |}.
]]
*)

(* begin hide *)

Definition protoState (memorySize: nat) (inputList: list (Image Gray)) : State.
  refine ({|
             PC := toBits 64 0;
             SP := toBits 64 0;
             input := noImage :: inputList;
             output := [(noImage, noSound, [])];
             memory := fun a => if a <? memorySize then Some (toBits 8 0) else None;
           |}).
  discriminate.
Defined.

Section limit_scope.
Open Scope nat_scope.

(* end hide *)

Equations fillMemory' (_: Bits64) (_: list Bits8) : ST unit :=
  fillMemory' _ [] := stateUnchanged';
  fillMemory' start (x :: u) := store' 1 start x ;; fillMemory' (toBits 64 (start + 1)) u.

Definition loadProgram' (program: list Bits8) (argument: list Bits8) : ST unit :=
  let program_start := toBits 64 0 in
  let argument_start := toBits 64 (length program) in
  fillMemory' program_start program;;
  fillMemory' argument_start argument;;
  setPC' program_start.

(* begin hide *)
End limit_scope.
(* end hide *)

Definition conformingInitialState memorySize inputList program argument : State -> Prop :=
  loadProgram' program argument (protoState memorySize inputList) tt.

(** In other words, a conforming implementation must start the machine in
a state which satisfies this predicate. This completes our specification.
*)

Definition terminalState s : Prop := not (exists s1, step' s tt s1).

Lemma terminalState_decidable: forall s, terminalState s \/ not (terminalState s).
Proof.
Admitted.

Lemma step_deterministic: forall s0 s1 s2, step' s0 tt s1 -> step' s0 tt s2 -> s1 = s2.
Proof.
Admitted.

Equations stepN' (_: nat) : ST unit :=
  stepN' 0 := stateUnchanged';
  stepN' (S n) := step';; stepN' n.

Definition run (s0: State) (s: State) : Prop :=
  terminalState s /\ exists n, stepN' n s0 tt s.

Corollary run_deterministic: forall s0 s1 s2, run s0 s1 -> run s0 s2 -> s1 = s2.
Proof.
  unfold run.
  intros s0 s1 s2 [H11 [n1 H12]] [H21 H22].
  revert s0 H12 s2 H21 H22.
  induction n1 as [|n1 IH];
    simp stepN';
    intros s0 H12 s2 H21 [n2 H22];
    destruct n2.

  - congruence.
  - unfold stateUnchanged' in H12.
    subst.
    simp stepN' in H22.
    destruct H22 as [[] [s [H221 H222]]].
    exfalso.
    apply H11.
    exact (ex_intro _ _ H221).

  - simp stepN' in H22.
    unfold stateUnchanged' in H22.
    subst.
    destruct H12 as [[] [s [H121 H122]]].
    exfalso.
    apply H21.
    exact (ex_intro _ _ H121).

  - destruct H12 as [[] [s [H121 H122]]].
    simp stepN' in H22.
    destruct H22 as [[] [s' [H221 H222]]].
    assert (s' = s); [exact (step_deterministic H221 H121) |].
    subst.
    exact (IH s H122 _ H21 (ex_intro _ n2 H222)).
Qed.
