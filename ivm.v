From Equations Require Import Equations.
Set Equations With UIP.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

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
(** printing map2 $\coqdocvar{map}_2$ *)


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
Open Scope bool_scope.
Open Scope Z_scope.
Coercion Z.of_nat : nat >-> Z.
Notation "'vector'" := t.
Coercion to_list: t >-> list.
(* end hide *)


(** *** Binary numbers

If we interpret [true] and [false] as 1 and 0, then a list or vector of
Booleans can be considered a binary in the interval $[0, 2^n)$ where [n =
length u]. *)

(* begin hide *)
Definition boolToNat (x: bool) : nat := if x then 1 else 0.
Coercion boolToNat : bool >-> nat.
(* end hide *)

Equations fromBits (_: list bool) : nat :=
  fromBits [] := 0;
  fromBits (x :: u) := 2 * fromBits u + x.

(** This definition is formulated using the Equations extension to Coq.
Observe that the least significant bit comes first. We usually leave
[fromBits] implicit, using elements of [list bool] and [vector bool n] as if
they were natural numbers.

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
bits in [toBits n (-1)] are [true]. [toBits n] is essentially the ring
homomorphism $\mathbb{Z}\rightarrow\mathbb{Z}/2^n\mathbb{Z}$. *)

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

(* end hide *)

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

(** Observe that the least significant byte comes first. *)

(* begin hide *)
End limit_scope.

(* TODO: Is this a good idea to avoid switching between [nat_scope] and [Z_scope]? *)
Notation "'0'" := O.
Notation "x < y" := (Nat.lt x y).
Notation "x <? y" := (Nat.ltb x y).
Notation "x =? y" := (Nat.eqb x y).

(* This could be generalized to all $x < 2^n$. *)
Lemma zeroBits_zero: forall n, fromBits (toBits n 0) = 0.
Proof.
  intro n.
  induction n as [|n IH];
    repeat (simp toBits || simp fromBits || simpl).
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* end hide *)



(** ** Monads

A monad consist of a generic type [m] and two operations that satisfy
three axioms. In Coq this can be expressed as a type class: *)

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
[a ::= ma; mb]  %&% [bind ma (fun a => mb)] %\\%
[ma;; mb]       %&% [bind ma (fun _ => mb)]
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
in this text we shall use only two. The simplest of these is the option
monad: *)

Instance OptionMonad: Monad option :=
{
  ret A x := Some x;
  bind A ma B f := match ma with None => None | Some a => f a end
}.
Proof.
  - abstract (intros A a; case a; split).
  - abstract (split).
  - abstract (intros A x B f C g; case x; split).
Defined.

(** The monad axioms are easy to prove. *)


(** ** State and state monad

As discovered by Eugenio Moggi in 1989, monads can be used to represent
computations with side-effects such as input and output. Below we shall
define a virtual machine in terms of a partial computational monad, but
first we define types representing the state of the machine at a given
moment.

*** VM state

An image is a two-dimensional matrix of pixels. *)

Record Image (C: Type) :=
  mkImage {
      iWidth: Bits16;
      iHeight: Bits16;
      iPixel: nat -> nat -> option C;
      iDef: forall x y, iPixel x y <> None <-> x < iWidth /\ y < iHeight;
    }.

(** A record is an inductive type with a single constructor ([mkImage]),
where we get projections for free. For example, if [im: Image Bits8], then
[iWidth im: Bits16]. The arguments to [iWidth] and [iHeight] are implicit
in the type of iDef. The type [C] represents the color of a single pixel.
The simplest image consists of 0 pixels:

[[
Definition noImage {C} : Image C :=
  {|
     iWidth := toBits 16 0;
     iHeight := toBits 16 0;
     iPixel := fun _ _ => None;
     iDef := _;
  |}.
]]
*)

(* begin hide *)
Definition noImage {C} : Image C.
  refine ({|
             iWidth := toBits 16 0;
             iHeight := toBits 16 0;
             iPixel := fun _ _ => None;
             iDef := _;
           |}).
  unfold fromBits16.
  rewrite zeroBits_zero.
  intros x y.
  split.
  - congruence.
  - intros [Hx Hy].
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
  |}.
]]
*)

(* begin hide *)
Definition emptySound (rate: Bits32) : Sound.
  refine ({|
             sRate := rate;
             sSamples := [];
           |}).
  trivial.
Defined.

(* end hide *)

Definition noSound := emptySound (toBits 32 0).

Definition addSample (s: Sound) (H: 0 <> sRate s) (l: Bits16) (r: Bits16) :=
  {|
    sRate := sRate s;
    sSamples := (l, r) :: (sSamples s);
    sDef := fun H0 => False_ind _ (H H0);
  |}.

(** Textual output from the machine uses the encoding UTF-32. Again, we
use reverse ordering. *)

Definition OutputText := list Bits32.

(* begin hide *)
Section limit_scope.
Open Scope type_scope.
(* end hide *)

Definition Gray := Bits8.
Definition Color := Bits16 * Bits16 * Bits16.
Definition Black : Color := (toBits 16 0, toBits 16 0, toBits 16 0).

(* begin hide *)
End limit_scope.
(* end hide *)

(** [Gray] represents the gray scale of the input images (where 0 is
black), whereas [Color] represents the ACES encoded colors of the output
images. The [State] type can now be formulated as follows: *)

(* begin hide *)
Ltac derive name term :=
  let H := fresh in
  let A := type of term in
  assert A as H;
  [ exact term | ];
  clear name;
  rename H into name.

Lemma reflect_it P b: Bool.reflect P b -> (Bool.Is_true b <-> P).
Proof.
  intros [Ht|Hf]; easy.
Qed.
(* end hide *)

Definition allBlack (width: Bits16) (height: Bits16): Image Color.
  refine (
      {|
        iWidth := width;
        iHeight := height;
        iPixel x y := if (x <? width) && (y <? height) then Some Black else None;
        iDef := _;
      |}
    ).
  intros x y.
  split.
  - intro H.
    remember ((x <? width) && (y <? height)) as H_lt eqn:Hxy.
    destruct H_lt; [|congruence].
    clear H.
    derive Hxy (Bool.Is_true_eq_right _ Hxy).
    derive Hxy (Bool.andb_prop_elim _ _ Hxy).
    split;
      [ destruct Hxy as [H _]
      | destruct Hxy as [_ H] ];
      derive H (proj1 (reflect_it (Nat.ltb_spec0 _ _)) H);
      exact H.
  - intros [Hx Hy].
    derive Hx (proj2 (reflect_it (Nat.ltb_spec0 _ _)) Hx).
    derive Hy (proj2 (reflect_it (Nat.ltb_spec0 _ _)) Hy).
    set (H := Bool.andb_prop_intro _ _ (conj Hx Hy)).
    derive H (Bool.Is_true_eq_true _ H).
    rewrite H.
    discriminate.
Defined.

Definition Output : Type := (Image Color) * Sound * OutputText.

Record State :=
  mkState {
      PC: Bits64;
      SP: Bits64;
      memory: Bits64 -> option Bits8;
      input: list (Image Gray);
      output: list Output;
      always_output: [] <> output;
    }.

(** [PC] and [SP] are known as the "program counter" and the "stack
pointer", respectively. Each elements of [output] consists of an image,
the sound clip to be played while this image is displayed, and an
associated piece of text. Any of these elements may be empty; and the list
is reversed in the sense that the first triple in the list should be
rendered last. The list [input] will only be decreasing as the machine
processes the input. Conversely, [output] will only be increasing, except
that the first element in this list should be considered "in progress"
until the machine terminates.

TODO: Mention output <> []
*)

(* begin hide *)

Instance etaState : Settable _ := settable! mkState < PC; SP; memory; input; output; always_output >.

Lemma State_expansion (s: State) :
  s = {|
    PC := PC s;
    SP := SP s;
    memory := memory s;
    input := input s;
    output := output s;
    always_output := always_output s;
  |}.
Proof.
  reflexivity.
Qed.

(* Since State is finite, this might be provable even without
   PropExtensionality, but that will have to wait. *)
Lemma State_injectivity
      p0 s0 m0 i0 o0 ao0
      p1 s1 m1 i1 o1 ao1:
  p0=p1 -> s0=s1 -> m0=m1 -> i0=i1 -> o0=o1
  -> {|PC:=p0; SP:=s0; memory:=m0; input:=i0; output:=o0; always_output:=ao0|}
  = {|PC:=p1; SP:=s1; memory:=m1; input:=i1; output:=o1; always_output:=ao1|}.
Proof.
  repeat (intro e; destruct e).
  destruct (proof_irrelevance ([] <> o0) ao0 ao1).
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


(** *** State monad *)

(** Our computation monad can now be defined as follows: *)

Definition Comp (A: Type) := State -> option (A) * State.

(* begin hide *)

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
                    || apply functional_extensionality
                    || f_equal
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

Instance ComputationMonad: Monad Comp :=
  {
    ret A x := fun s0 => (Some x, s0);
    bind A st B f := fun s => match st s with
                           | (Some x, s1) => f x s1
                           | (None, s1) => (None, s1)
                           end;
  }.
Proof.
  - st_tactics.crush.
    destruct (ma x) as [[?|]?]; reflexivity.
  - st_tactics.crush.
  - st_tactics.crush.
    destruct (ma x) as [[?|]?]; reflexivity.
Defined.

(** It is easy to prove the monad axioms assuming propositional and
functional extensionality. Some readers may recognize this as the result
of applying an option monad transformer to a state monad. Informally, each
[st: Comp A] is a computation that should produce a value of type [A],
perhaps with some side-effects:

- If [st s0 = (Some x, s1)], then executing [st] from state [s0] produces
  [x] and changes the state to [s1].

- If [st s0 = (None, s1)], then the computation halts in state [s1].


** Primitive computations

[Comp unit] represents computations that do not produce any value. They
may, however, produce output and have other side-effects. In the next
section we define one execution step of our virtual machine as a term
[oneStep': Comp unit], but first we need some more building blocks. *)

Definition stop' {A}: Comp A := fun s => (None, s).

(** In other words, [stop'] never completes normally. We use the
convention that computations (and functions returning computations) have
names ending with an apostrophe. For this reason we also define: *)

Definition return' {A} (x: A) : Comp A := ret x.



(** *** Memory access *)

(** The virtual machine uses 64-bit memory addresses. *)

(* begin hide *)
Section limit_scope.
Open Scope vector_scope.
(* end hide *)

Equations addresses n (start: Z) : vector Bits64 n :=
  addresses 0 _ := [];
  addresses (S n) start := toBits 64 start :: (addresses n (start + 1)).

(* begin hide *)
End limit_scope.
(* end hide *)

Definition tryExtract' {A} (f: State -> option A) : Comp A :=
  fun s => (f s, s).

Definition load' (n: nat) (az: Z) : Comp nat :=
  tryExtract'
    (fun s => lift fromLittleEndian
                (traverse (memory s) (addresses n az))).

(** In words, [load' n az s0 = (Some x, s1)] if [s0 = s1] and the [n]
bytes starting at [az] represent the natural number [x] $<2^n$. If not all
the addresses [az], ..., [az+n-1] are available, the machine stops. *)

Definition store1' (az: Z) (value: Bits8) : Comp unit :=
  let a: Bits64 := toBits 64 az in
  fun s =>
    match memory s a with
    | None => (None, s)
    | Some _ =>
      let m (a': Bits64) := if a' =? a then Some value else memory s a' in
      (Some tt, s <| memory := m |>)
    end.

(** [store1'] tries to update the value at a given memory address, and
stops if the address is not availble. *)

Equations fillMemory' (_: Z) (_: list Bits8) : Comp unit :=
  fillMemory' _ [] := return' tt;
  fillMemory' start (x :: u) := store1' start x;; fillMemory' (start + 1) u.

Definition store' (n: nat) (start: Z) (value: Z) : Comp unit :=
  fillMemory' start (toLittleEndian n value).


(** *** Stack and program counter *)

Definition setPC' (az: Z): Comp unit :=
  fun s => (Some tt, s <| PC := toBits 64 az |>).

Definition setSP' (az: Z): Comp unit :=
  fun s => (Some tt, s <| SP := toBits 64 az |>).

(** The corresponding "get" computations are simple instances of
[extract']. *)

Definition extract' {A} (f: State -> A): Comp A :=
  fun s => (Some (f s), s).

Definition next' (n: nat) : Comp nat :=
  a ::= extract' PC;
  setPC' (a + n);;
  load' n a.

Definition pop': Comp Bits64 :=
  a ::= extract' SP;
  v ::= load' 8 a;
  setSP' (a + 8);;
  return' (toBits 64 v).

(* begin hide*)
Definition push' (value: Z): Comp unit :=
  a0 ::= extract' SP;
  let a1 := a0 - 8 in
  setSP' a1;;
  store' 8 a1 value.
(* end hide *)

(**
[[
Definition push' (value: Z): Comp unit :=
  a0 ::= extract' SP;
  let a1 := a0 - 8 in
  setSP' a1;;
  store' 8 a1 value.
]]
*)


(** *** Input and output *)

Definition readFrame' : Comp (Bits16 * Bits16) :=
  fun s =>
    let s' := set input (@tail _) s in
    let x := match input s' with
             | hd :: tl => (iWidth hd, iHeight hd)
             | _ => (toBits 16 0, toBits 16 0)
             end in
    (Some x, s').

Definition readPixel' (x y: nat) : Comp Bits8 :=
  tryExtract'
    (fun s =>
       match input s with
       | frame :: _ => iPixel frame x y
       | [] => None
       end).

(* TODO: Hide *)
Definition addOutput s o : State :=
  ({|
      PC := PC s;
      SP := SP s;
      memory := memory s;
      input := input s;
      output := o :: output s;
      always_output:= fun H => nil_cons H
    |}).

(* TODO: Hide *)
Definition replaceOutput s o : State :=
  ({|
      PC := PC s;
      SP := SP s;
      memory := memory s;
      input := input s;
      output := o :: tail (output s);
      always_output:= fun H => nil_cons H
    |}).

Definition newFrame' (width height rate: nat) : Comp unit :=
  let o := (allBlack (toBits 16 width) (toBits 16 height), emptySound (toBits 32 rate), []) in
  fun s => (Some tt, addOutput s o).

(* TODO: Simplify presentation *)
Definition trySetPixel {C} (image: Image C) (x y: nat) (c: C): option (Image C).
  refine (if Sumbool.sumbool_of_bool ((x <? iWidth image) && (y <? iHeight image))
          then Some
                 {|
                   iWidth := iWidth image;
                   iHeight := iHeight image;
                   iPixel := fun xx yy => if (xx =? x) && (yy =? y) then Some c else iPixel image xx yy;
                   iDef := _
                 |}
          else None).
  intros xx yy.
  split;
    remember ((xx =? x) && (yy =? y)) as exy eqn:H;
    destruct exy.
  - intros _.
    derive e (Bool.Is_true_eq_left _ e).
    derive e (Bool.andb_prop_elim _ _ e).
    derive H (Bool.Is_true_eq_right _ H).
    derive H (Bool.andb_prop_elim _ _ H).
    split;
      [ destruct e as [e _] | destruct e as [_ e] ];
      [ destruct H as [H _] | destruct H as [_ H] ];
      derive e (proj1 (reflect_it (Nat.ltb_spec0 _ _)) e);
      derive H (proj1 (reflect_it (Nat.eqb_spec _ _)) H);
      subst;
      exact e.
  - apply (iDef image).
  - discriminate.
  - apply (iDef image).
Defined.

Definition getCurrentOutput' : Comp Output :=
  fun s => match output s with
        | o :: _ => (Some o, s)
        | [] => (None, s)
        end.

(** TODO: Mention impossible case? *)

Definition setPixel' (x y r g b : nat) : Comp unit :=
  o ::= getCurrentOutput';
  match o with
  | (image, sound, text) =>
    match trySetPixel image x y (toBits 16 r, toBits 16 g, toBits 16 b) with
    | None => stop'
    | Some newImage => fun s => (Some tt, replaceOutput s (newImage, sound, text))
    end
  end.

Definition addSample' (l r : nat) : Comp unit :=
  o ::= getCurrentOutput';
  match o with
  | (image, sound, text) =>
    match Sumbool.sumbool_of_bool (0 =? sRate sound) with
    | right H =>
      let newSound := addSample sound (beq_nat_false _ _ H) (toBits 16 l) (toBits 16 r) in
      fun s => (Some tt, replaceOutput s (image, newSound, text))
    | _ => stop'
    end
  end.

Definition putChar' (c: nat) : Comp unit :=
  o ::= getCurrentOutput';
  match o with
  | (image, sound, text) =>
    fun s => (Some tt, replaceOutput s (image, sound, (toBits 32 c) :: text))
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

(** %\vspace{1ex}% Now we can define what it means for our virtual machine
to perform one execution step. *)

Definition oneStep' : Comp unit :=
  opcode ::= next' 1;
  match opcode with
  | EXIT => stop'
  | NOP => return' tt

  | JUMP => pop' >>= setPC'
  | JUMP_ZERO =>
      offset ::= next' 1;
      v ::= pop';
      if v =? 0
      then pc ::= extract' PC;
           setPC' (pc + (signed (toBits 8 offset)))
      else return' tt

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
  | DIV => x ::= pop'; y ::= pop'; push' (if x =? 0 then 0 else y / x)
  | REM => x ::= pop'; y ::= pop'; push' (if x =? 0 then 0 else y mod x)
  | LT => x ::= pop'; y ::= pop'; push' (if y <? x then -1 else 0)
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
  | NOT => u ::= pop'; push' (map (fun x => if x then false else true) u)
  | POW2 => n ::= pop'; push' (2 ^ n)

  | NEW_FRAME =>
      rate ::= pop'; height ::= pop'; width ::= pop';
      newFrame' width height rate
  | SET_PIXEL =>
      b ::= pop'; g ::= pop'; r ::= pop';
      y ::= pop'; x ::= pop';
      setPixel' x y r g b
  | ADD_SAMPLE => r ::= pop'; l ::= pop'; addSample' l r
  | PUT_CHAR => pop' >>= putChar'

  | READ_FRAME => wh ::= readFrame'; push' (fst wh);; push' (snd wh)
  | READ_PIXEL => x ::= pop'; y ::= pop'; readPixel' x y >>= push'

  | _ => stop'
  end.

(* begin hide *)
End limit_scope.
(*end hide *)
(** In this definition [map] and [map2] denote the obvious "bitwise" transformations:

%\begin{center}%
[map : (bool -> bool) -> Bits64 -> Bits64] %$\qquad\qquad$%
[map2 : (bool -> bool -> bool) -> Bits64 -> Bits64 -> Bits64]
%\end{center}%

In general, we want to run the machine until it stops: *)

Equations run' (limit: nat) : Comp unit :=
  run' 0 := stop';
  run' (S n) := oneStep';; run' n.

(** Since we are working in a framework without general recursion, we must
limit the number of steps in order to guarantee termination.


** Running a program

Before the machine can start, we must load a program into the memory and
set the program counter to its start position. We must also initialize the
stack and stack pointer; and the initial state should contain the full
list of input frames and no output frames.

[[
Definition protoState (memorySize: nat) (inputList: list (Image Gray)) : State :=
  {|
    PC := toBits 64 0;
    SP := toBits 64 (min memorySize (2 ^ 64));
    memory := fun a => if a <? memorySize then Some (toBits 8 0) else None;
    input := noImage :: inputList;
    output := [(noImage, noSound, [])];
  |}.
]]
*)

(* begin hide *)
Definition protoState (memorySize: nat) (inputList: list (Image Gray)) : State.
  refine ({|
             PC := toBits 64 0;
             SP := toBits 64 (min memorySize (2 ^ 64));
             memory := fun a => if a <? memorySize then Some (toBits 8 0) else None;
             input := noImage :: inputList;
             output := [(noImage, noSound, [])];
           |}).
  discriminate.
Defined.
(* end hide *)

(** Initially, the memory is 0 at every address below [memorySize], and
[SP] points to the first address after this segment. If [memorySize >=]
$2^{64}$, then [SP=0]. *)

Definition loadProgram' (program: list Bits8) (argument: list Bits8) : Comp unit :=
  let program_start := 0 in
  let argument_start := length program in
  fillMemory' program_start program;;
  store' 8 argument_start (length argument);;
  fillMemory' (argument_start + 8) argument;;
  setPC' program_start.

(** Thus, the final state after running a program is characterized as
follows: *)

Definition finalState memorySize inputList program argument : State -> Prop :=
  fun s1 =>
    let s0 := protoState memorySize inputList in
    exists n, (loadProgram' program argument;; run' n) s0 = (Some tt, s1).
