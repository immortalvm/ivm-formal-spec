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
(** printing <| $\langle|$ *)
(** printing |> $|\rangle$ *)
(** printing |>) $|\rangle)$ *)
(** printing )|>) $)|\rangle)$ *)
(** printing )|>);; %$)|\rangle)$;;% *)

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

(** printing m0 $\coqdocvar{m}_0$ *)
(** printing m1 $\coqdocvar{m}_1$ *)
(** printing m2 $\coqdocvar{m}_2$ *)
(** printing s0 $\coqdocvar{s}_0$ *)
(** printing s1 $\coqdocvar{s}_1$ *)
(** printing s2 $\coqdocvar{s}_2$ *)
(** printing sn $\coqdocvar{s}_n$ *)
(** printing st1 $\coqdocvar{st}_1$ *)
(** printing st2 $\coqdocvar{st}_2$ *)
(** printing x1 $\coqdocvar{x}_1$ *)
(** printing xn $\coqdocvar{x}_n$ *)
(** printing IO0 $\coqdocvar{IO}_0$ *)
(** printing map2 $\coqdocvar{map}_2$ *)


(** * Formal specification of the iVM abstract machine%\label{sec:formal}%

This section contains a mathematical definition of the abstract machine
used to interpret the contents of this film. It has been formalized in a
system for formal mathematics called Coq, which is based on higher-order
type theory. The text below was extracted from the Coq description. It
involves some formal logic and type theory (where for simplicity we assume
the principles of propositional and functional extensionality), but we do
not include the actual proofs here.


** Basic types

We will be using three simple inductive types from the Coq library (a.k.a.
%\coqdocvar{unit}%, %\coqdocvar{bool}% and %\coqdocvar{nat}%):

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
$n$, known as "vectors":

[[
Definition vector A n := { u : list A | length u = n }.
]]

For technical reasons, [vector] is not actually defined like this.
However, we do have implicit inclusions [vector A n] $↪$ [list A] for
every [n] known as "coercions", and for every [u: list A] there is a
corresponding element in [vector A (length u)]. *)

(* begin hide *)
Open Scope bool_scope.
Open Scope Z_scope.
Coercion Z.of_nat : nat >-> Z.
Notation "'vector'" := t.
Coercion to_list: t >-> list.
(* end hide *)


(** *** Binary numbers

If we interpret [true] and [false] as 1 and 0, then a list or vector of
Booleans can be considered a binary number in the interval $[0, 2^n)$
where [n = length u]. *)

(* begin hide *)
Definition boolToNat (x: bool) : nat := if x then 1 else 0.
Coercion boolToNat : bool >-> nat.
(* end hide *)

Equations fromBits (_: list bool) : nat :=
  fromBits [] := 0;
  fromBits (x :: u) := 2 * fromBits u + x.

(** This definition is formulated using the Equations extension to Coq.
Observe that the least significant bit comes first. Taking [fromBits] as a
coercion, we will often be using elements of [list bool] and [vector bool n] as
if they were natural numbers.

Conversely, we can extract the $n$ least significant bits of any integer:
*)

(* begin hide *)
Section limit_scope.
Open Scope vector_scope.
(* end hide *)

Equations toBits (n: nat) (_: Z) : vector bool n :=
  toBits O _ := [] ;
  toBits (S n) z := (z mod 2 =? 1) :: toBits n (z / 2).
(* begin hide *)
End limit_scope.
(* end hide *)
(* Compute (fromBits (toBits 8 (213 + 1024))). *)

(** Here [z mod 2 =? 1] is [true] if the equality holds, otherwise
[false]. Moreover, [/] and [mod] are defined so that [z mod 2] is either 0
or 1 and [z = 2 * (z / 2) + z mod 2] for every [z]. In particular, all the
bits in [toBits n (-1)] are [true]. Thus, [toBits n] is essentially the
ring homomorphism $\mathbb{Z}\rightarrow\mathbb{Z}/2^n\mathbb{Z}$. *)

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

(** In some situations we want bit vectors to represent both positive and
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
[signed u] $\equiv$ [fromBits u] $\pmod{2^n}$ for every [u: vector bool n]. *)


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

(** The elements of [Bits8] are called "bytes". If we concatenate a list
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

(** The least significant byte comes first, and we have the following (not
entirely commutative) diagram:

%
\begin{center}
  \begin{tikzcd}[row sep=normal, column sep=6em]
    \coqdocvar{list}\;\mathbb{B}
    \arrow[r, "\coqdocvar{fromBits}"]
    \arrow[dr, dashed, "\coqdocvar{signed}" sloped] &
    \mathbb{N}
    \arrow[d, hook] &
    \coqdocvar{list}\;\mathbb{B}^8
    \arrow[l, dashed, swap, "\coqdocvar{fromLittleEndian}"]
    \\
    \coqdocvar{vector}\;\mathbb{B}\; n
    \arrow[u, hook] &
    \mathbb{Z}
    \arrow[l, dashed, "\coqdocvar{toBits}\;\coqdocvar{n}"]
    \arrow[r, dashed, swap, "\coqdocvar{toLittleEndian}\;\coqdocvar{n}"] &
    \coqdocvar{vector}\;\mathbb{B}^8\; n
    \arrow[u, hook]
  \end{tikzcd}
\end{center}
%

 *)

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


(** *** Monads

In this text a "monad" is a structure consisting of one generic type [m:
Type -> Type] and two operations that satisfy three axioms. We express
this as a "type class": *)

(* Loosely based on https://github.com/coq/coq/wiki/AUGER_Monad. *)
Class Monad (m: Type -> Type): Type :=
{
  ret: forall {A}, A -> m A;
  bind: forall {A}, m A -> forall {B}, (A -> m B) -> m B;

  monad_right: forall A (ma: m A), bind ma ret = ma;
  monad_left: forall A (a: A) B (f: A -> m B), bind (ret a) f = f a;
  monad_assoc: forall A (ma: m A) B f C (g: B -> m C),
      bind ma (fun a => bind (f a) g) = bind (bind ma f) g;
}.

(** Writing the type parameters as [{A}] and [{B}] means that when we
apply [ret] and [bind], the type arguments should be left implicit.
Moreover, we use the following notation:
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
*)

(* begin hide *)
Notation "ma >>= f" := (bind ma f) (at level 69, left associativity).
Notation "a ::= ma ; mb" := (bind ma (fun a => mb)) (at level 60, right associativity, only parsing).
Notation "ma ;; mb" := (bind ma (fun _ => mb)) (at level 60, right associativity).
(* end hide *)

(** The simplest monad is the "identity monad", were [m A = A] for every [A]: *)

(* TODO: Place in module? *)
Program Instance IdMonad: Monad id :=
{
  ret A x := x;
  bind A ma B f := f ma;
}.

(** We shall often say that a function [Type -> Type] is a monad if the
rest of the monad structure is clear from the context. *)


(** *** Monad transformers

A "morphism" between monads is a structure preserving family of functions
[m0 A -> m1 A] : *)

Class Morphism m0 `{Monad m0} m1 `{Monad m1} (F: forall {A}, m0 A -> m1 A) :=
{
  morph_ret: forall A (x: A), F (ret x) = ret x;
  morph_bind: forall A (ma: m0 A) B (f: A -> m0 B),
      F (ma >>= f) = (F ma) >>= (fun x => F (f x));
}.

Arguments Morphism: clear implicits.
Arguments Morphism _ {_} _ {_} _.

(** Here [`{Monad m0}] means that that [m0: Type -> Type] must have a
(usually implicit) monad structure, similarly for [m1]. A "monad
transformer" constructs a new monad from an existing monad [m] such that
there is a morphism from [m] to the new monad: *)

Class Transformer (t: forall (m: Type -> Type) `{Monad m}, Type -> Type): Type :=
{
  transformer_monad: forall m `{Monad m}, Monad (t m);
  lift: forall {m} `{Monad m} A, m A -> (t m) A;
  lift_morphism: forall {m} `{Monad m}, Morphism _ _ lift;
}.

(* begin hide*)

Existing Instance transformer_monad.
Existing Instance lift_morphism.

(* end hide *)

(** We get a simple transformer by composing [m] with [option] (as defined
above): *)

Definition Opt m `{Monad m} A := m (option A).

(* begin hide *)

Arguments Opt: clear implicits.
Arguments Opt _ {_}.

(* end hide *)

Program Instance OptionTransformer: Transformer Opt :=
{
  transformer_monad m _ :=
    {|
      ret _ x := ret (Some x);
      bind _ ma _ f := a ::= (ma: m _);
                       match a with None => ret None | Some x => f x end;
    |};
  lift _ _ _ ma := x ::= ma; ret (Some x);
}.
Next Obligation.
  match goal with
    |- ma >>= ?f = ma => assert (f = ret) as Hf
  end.
   - apply functional_extensionality.
     intros [?|]; reflexivity.
   - rewrite Hf.
     apply (monad_right (m:=m)).
Defined.
Next Obligation.
  rewrite monad_left.
  reflexivity.
Defined.
Next Obligation.
  rewrite <- monad_assoc.
  f_equal.
  apply functional_extensionality.
  intros [a|].
  + reflexivity.
  + rewrite monad_left.
    reflexivity.
Defined.
Next Obligation.
  split.
  - intros.
    rewrite monad_left.
    reflexivity.
  - intros.
    rewrite <- monad_assoc at 1.
    simpl.
    rewrite <- monad_assoc.
    f_equal.
    apply functional_extensionality.
    intro x.
    rewrite monad_left.
    reflexivity.
Defined.

(** Here we define [ret] and [bind] in terms of the corresponding
operations of [m]. The axioms are easy to verify. Monads of the form [Opt
m] can represent computations that may stop before producing a value: *)

Definition stop' {m} `{Monad m} {A}: Opt m A := ret None.

(** Observe that [stop' >>= f = stop'] for every [f]. *)

(* begin hide *)

Lemma stop_bind : forall m `(M: Monad m) A B (f: A -> Opt m B), stop' >>= f = stop'.
Proof.
  intros.
  unfold stop'.
  simpl.
  rewrite monad_left.
  reflexivity.
Qed.

Instance opt_morphism: forall m0 `(Monad m0) m1 `(Monad m1) (F: forall A, m0 A -> m1 A) `(Morphism m0 m1 F),
    Morphism (Opt m0) (Opt m1) (fun A => F (option A)).
Proof.
  intros.
  split.
  - intros.
    apply (morph_ret (F:=F)).
  - intros.
    rewrite (morph_bind (F:=F)).
    simpl.
    f_equal.
    apply functional_extensionality.
    intros [x|].
    + reflexivity.
    + apply (morph_ret (F:=F)).
Qed.

(* end hide *)


(** *** State monad transformer

As discovered by Eugenio Moggi in 1989, monads can be used to represent
computations with side-effects such as input and output. In particular, we
can define a transformer which extends and existing monad with the ability
to access and modify a value referred to as the "current state": *)

(* begin hide *)
Section limit_scope.
Open Scope type_scope.
(* end hide *)

Definition ST S m `{Monad m} A := S -> m (A * S).

(* begin hide *)

End limit_scope.

Arguments ST: clear implicits.
Arguments ST _ _ {_} _.

(* end hide *)

Program Instance StateTransformer S: Transformer (ST S) :=
{
  transformer_monad m _ :=
    {|
      ret _ x := fun s => ret (x, s);
      bind _ ma _ f := fun s => p ::= ma s; f (fst p) (snd p);
    |};
  lift _ _ _ ma := fun s => x ::= ma; ret (x, s);
}.
Next Obligation.
  (* TODO: The proofs are virtually identical to those of the option transformer. *)
  apply functional_extensionality.
  intro s.
  rewrite <- monad_right.
  f_equal.
  apply functional_extensionality.
  intro p.
  rewrite <- surjective_pairing.
  reflexivity.
Defined.
Next Obligation.
  apply functional_extensionality.
  intro s.
  rewrite monad_left.
  reflexivity.
Defined.
Next Obligation.
  apply functional_extensionality.
  intro s.
  rewrite <- monad_assoc.
  reflexivity.
Defined.
Next Obligation.
  split.
  + intros.
    apply functional_extensionality.
    intro s.
    rewrite monad_left.
    reflexivity.
  + intros.
    apply functional_extensionality.
    intro s.
    rewrite <- monad_assoc at 1.
    simpl.
    rewrite <- monad_assoc.
    f_equal.
    apply functional_extensionality.
    intro x.
    rewrite monad_left.
    reflexivity.
Defined.

(** In other words, [ST S] is a monad transformer for every type [S]. We
shall be especially interested in monads of the form [Opt (ST S m)] where
the elements represent "computations": *)

Section opt_st_section.

  Context {m} `{Monad m} {S: Type}.

  Let C := Opt (ST S m).

  Definition tryGet' {A} (f: S -> option A) : C A :=
    fun s => ret (f s, s).

  Definition get' {A} (f: S -> A) : C A :=
    fun s => ret (Some (f s), s).

  Definition update' (f: S -> S): C unit :=
    fun s => ret (Some tt, f s).

  (** These definitions were simplified by placing them inside a "section"
      with a list of shared [Context] parameters and a local abbreviation,
      [C]. In this text computations (and functions returning
      computations) have names ending with an apostrophe. For this reason
      we also define: *)

  Definition return' {A} (x: A) : C A := ret x.

End opt_st_section.


(** ** Generic abstract machine%\label{sec:generic}%

We have split specification of the machine in three parts. In
section%~\ref{sec:io}% we specify the I/O operations in terms of a
separate monad, [IO], whereas in the current section we describe the parts
of the machine that are independent of the I/O operations. Finally, we put
the pieces together in section%\ref{sec:integration}%. *)

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
End Instructions.

(* end hide *)

(** The current state of the generic virtual machine has three components:
a program counter ([PC]), a stack pointer ([SP]), and the memory contents.
The memory is a collection of memory cells. Each cell has a unique address
of type [Bits64] and stores one byte of data. In practice, the addresses
of the memory cells will form a subset $[0,\coqdocvar{memorySize})$ for
some $\coqdocvar{memorySize}\leq 2^{64}$, see [initialCoreState] below.
*)

Record CoreState :=
  mkCoreState {
      PC: Bits64;
      SP: Bits64;
      memory: Bits64 -> option Bits8;
    }.

(** A record is an inductive type with a single constructor
([mkCoreState]), where we get projections for free. For example, [PC s :
Bits64] for every [s : CoreState]. *)

(* begin hide *)

Instance etaCoreState : Settable _ := settable! mkCoreState < PC; SP; memory >.

(* end hide *)

Definition initialCoreState
           (program: list Bits8)
           (argument: list Bits8)
           (start: Bits64)
           (memorySize: nat)
           (_: start + memorySize <= 2^64)
           (_: length program + 8 + length argument <= memorySize) : CoreState :=
  let stop := (start + memorySize)%nat in
  let mem := program ++ toLittleEndian 8 (length argument) ++ argument in
  {|
    PC := toBits 64 start;
    SP := toBits 64 stop;
    memory a :=
      if (start <=? a) && (a <? stop)
      then Some (nth (a - start) mem (toBits 8 0))
      else None
  |}.

(** In other words, before the machine is started, the available memory
will be initialized to 0, except for a "program" and an "argument", both
sequenced of bytes. Also, the length of the argument is stored in 64 bits
between the program and the argument, the program counter is set to 0, and
the stack pointer is set to the first address after the available memory.
*)


Section generic_machine_section.

  (** We assume an I/O monad of form [Opt m] (to be defined later). *)

  Context m `{Monad m}.

  Let IO := Opt m.

  Definition Comp := Opt (ST CoreState m).

  Definition fromIO {A} : IO A -> Comp A := lift (option A).

  (* begin hide *)
  Arguments fromIO [A].
  (* end hide *)

  Instance fromIO_morphism: Morphism IO Comp fromIO.
  Proof.
    (* intros. apply opt_morphism, lift_morphism. *)
    typeclasses eauto.
  Qed.

  (** Also observe that [fromIO stop' = stop']. *)

  (* begin hide *)

  Proposition fromIO_characterization : forall A (ma: IO A),
      fromIO ma = fun s => (ma : m (option A)) >>= (fun x => ret (x, s)).
  Proof.
    reflexivity.
  Qed.

  (* end hide *)


  (** *** Memory access

  The machine stops if it is asked to access an unavailable memory address: *)

  Definition loadByte' (a: Z) : Comp Bits8 :=
    mem ::= get' memory;
    match mem (toBits 64 a) with
    | None => stop'
    | Some value => return' value
    end.

  (* begin hide *)
  Section limit_scope.
  Open Scope vector_scope.
  (* end hide *)

  Equations loadBytes' (n: nat) (a: Z) : Comp (vector Bits8 n) :=
    loadBytes' 0 _ := return' [];
    loadBytes' (S n) start :=
      x ::= loadByte' start;
      u ::= loadBytes' n (start + 1);
      return' (x :: u).

  (* begin hide *)
  End limit_scope.
  (* end hide *)

  Definition load' (n: nat) (a: Z) : Comp nat :=
    bytes ::= loadBytes' n a;
    return' (fromLittleEndian bytes).

  (** That is, [load' n a s0 = (Some x, s1)] if [s0 = s1] and the [n]
  bytes at addresses [a], ..., [a+n-1] represent the natural number [x]
  $<2^n$. [storeByte'] also stops if the address is not available: *)

  Definition storeByte' (a: Z) (value: Bits8) : Comp unit :=
    mem ::= get' memory;
    let u: Bits64 := toBits 64 a in
    match mem u with
    | None => stop'
    | _ => let newMem (v: Bits64) := if v =? u then Some value else mem v in
          update' (fun s => s<|memory := newMem|>)
    end.

  (** Here [s<|memory := newMem|>] is identical to [s], except that the
  field [memory] has been changed to [newMem]. *)

  Equations storeBytes' (_: Z) (_: list Bits8) : Comp unit :=
    storeBytes' _ [] := return' tt;
    storeBytes' start (x :: u) :=
      storeByte' start x;;
      storeBytes' (start + 1) u.

  Definition store' (n: nat) (start: Z) (value: Z) : Comp unit :=
    storeBytes' start (toLittleEndian n value).


  (** *** Program counter *)

  Definition setPC' (az: Z): Comp unit :=
    update' (fun s => s<|PC := toBits 64 az|>).

  Definition next' (n: nat) : Comp nat :=
    a ::= get' PC;
    setPC' (a + n);;
    load' n a.

  (** In other words, [next' n] loads the next [n] bytes and advances [PC]
  accordingly. *)


  (** *** Stack

  A stack is a LIFO (last in, first out) queue. The elements on our stack
  are 64 bits long, and [SP] points to the next element that can be
  popped. The stack grows "downwards" in the sense that [SP] is decreased
  when new elements are pushed. *)

  Definition setSP' (az: Z): Comp unit :=
    update' (fun s => s<|SP := toBits 64 az|>).

  Definition pop': Comp Bits64 :=
    a ::= get' SP;
    v ::= load' 8 a;
    setSP' (a + 8);;
    return' (toBits 64 v).

  (* begin hide *)
  Section limit_scope.
  Open Scope vector_scope.
  (* end hide *)

  Equations popN' (n: nat) : Comp (vector Bits64 n) :=
    popN' 0 := return' [];
    popN' (S n) := u ::= popN' n; x ::= pop'; return' (x :: u).

  (* begin hide *)
  End limit_scope.
  (* end hide *)

  Definition push' (value: Z): Comp unit :=
    a0 ::= get' SP;
    let a1 := a0 - 8 in
    setSP' a1;;
    store' 8 a1 value.

  Equations pushList' (_: list Z) : Comp unit :=
    pushList' [] := return' tt;
    pushList' (x :: u) := push' x;; pushList' u.

  (** Since [popN'] returns elements in the order they were pushed, it is
  essentially a left inverse to [pushList']. *)


  (** *** Generic I/O interface

  In the generic machine an I/O operation is simply an element [io: vector
  Bits64 n -> IO (list Bits64)] for some [n]. When a corresponding
  operation is encountered, the machine will pop [n] elements from the
  stack, execute [io] on these elements and place the push the result onto
  the stack. *)

  Record IO_operation :=
    mkIO_operation {
        ioArgs: nat;
        operation: vector Bits64 ioArgs -> IO (list Z);
      }.

  Definition from_IO_operation (op: IO_operation) : Comp unit :=
    arguments ::= popN' (ioArgs op);
    results ::= fromIO (operation op arguments);
    pushList' results.

  Context (IO_operations: list IO_operation).

  Definition ioStep' (n: nat) : Comp unit :=
    nth (255 - n) (map from_IO_operation IO_operations) stop'.

  (** In other words, we assume a list of I/O operations that will be
  mapped to "opcodes" 255, 254, ...*)


  (** *** Single execution step

  The other opcodes of the machine are as follows:

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
  }
  \col{
   7 & \coqdocvar{PUSH0}\\
   8 & \coqdocvar{PUSH1}\\
   9 & \coqdocvar{PUSH2}\\
  10 & \coqdocvar{PUSH4}\\
  11 & \coqdocvar{PUSH8}\\
  12 & \coqdocvar{SIGX1}\\
  13 & \coqdocvar{SIGX2}\\
  14 & \coqdocvar{SIGX4}\\
  }
  \col{
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
  }
  \col{
  40 & \coqdocvar{AND}\\
  41 & \coqdocvar{OR}\\
  42 & \coqdocvar{NOT}\\
  43 & \coqdocvar{XOR}\\
  44 & \coqdocvar{POW2}\\
  }
  \end{center}
  %
  *)

  (* begin hide *)
  Section limit_scope.
  Import Instructions.
  Let map (f: bool->bool) (u: Bits64) : Bits64 := Vector.map f u.
  Let map2 (f: bool->bool->bool) (u: Bits64) (v: Bits64) : Bits64 := Vector.map2 f u v.
  (* end hide *)

  (** %\vspace{1ex}% Now we can define what it means for our abstract machine
  to perform one execution step: *)

  Definition oneStep' : Comp unit :=
    opcode ::= next' 1;
    match opcode with
    | EXIT => stop'
    | NOP => return' tt

    | JUMP => pop' >>= setPC'
    | JUMP_ZERO =>
        offset ::= next' 1;
        x ::= pop';
        if x =? 0
        then pc ::= get' PC;
             setPC' (pc + (signed (toBits 8 offset)))
        else return' tt
    | SET_SP => pop' >>= setSP'
    | GET_PC => get' PC >>= push'
    | GET_SP => get' SP >>= push'

    | PUSH0 => push' 0
    | PUSH1 => next' 1 >>= push'
    | PUSH2 => next' 2 >>= push'
    | PUSH4 => next' 4 >>= push'
    | PUSH8 => next' 8 >>= push'
    | SIGX1 => x ::= pop'; push' (signed (toBits 8 x))
    | SIGX2 => x ::= pop'; push' (signed (toBits 16 x))
    | SIGX4 => x ::= pop'; push' (signed (toBits 32 x))

    | LOAD1 => pop' >>= load' 1 >>= push'
    | LOAD2 => pop' >>= load' 2 >>= push'
    | LOAD4 => pop' >>= load' 4 >>= push'
    | LOAD8 => pop' >>= load' 8 >>= push'
    | STORE1 => a ::= pop'; x ::= pop'; store' 1 a x
    | STORE2 => a ::= pop'; x ::= pop'; store' 2 a x
    | STORE4 => a ::= pop'; x ::= pop'; store' 4 a x
    | STORE8 => a ::= pop'; x ::= pop'; store' 8 a x

    | ADD => x ::= pop'; y ::= pop'; push' (x + y)
    | MULT => x ::= pop'; y ::= pop'; push' (x * y)
    | DIV => x ::= pop'; y ::= pop'; push' (if x =? 0 then 0 else y / x)
    | REM => x ::= pop'; y ::= pop'; push' (if x =? 0 then 0 else y mod x)
    | LT => x ::= pop'; y ::= pop'; push' (if y <? x then -1 else 0)
    | AND =>
        u ::= pop';
        v ::= pop';
        push' (map2 (fun x y => x && y) u v)
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

    | n => ioStep' n
    end.

  (* begin hide *)
  End limit_scope.
  (*end hide *)
  (** In this definition [map] and [map2] denote the obvious "bitwise" transformations:

  %\begin{center}%
  [map : (bool -> bool) -> Bits64 -> Bits64] %$\qquad\qquad$%
  [map2 : (bool -> bool -> bool) -> Bits64 -> Bits64 -> Bits64]
  %\end{center}%

  We can also run the machine for [n] steps or until it stops: *)

  Equations nSteps' (_: nat) : Comp unit :=
    nSteps' 0 := return' tt;
    nSteps' (S n) := oneStep';; nSteps' n.

  (* begin hide *)

  Lemma nSteps_succ: forall n, nSteps' (S n) = nSteps' n;; oneStep'.
  Proof.
    intro n.
    induction n.
    - simp nSteps'.
      rewrite monad_left.
      rewrite <- monad_right.
      f_equal.
      apply functional_extensionality.
      intros [].
      reflexivity.
    - simp nSteps' in *.
      rewrite <- monad_assoc.
      rewrite IHn.
      reflexivity.
  Qed.

  Lemma nSteps_stop: forall (init: Comp unit) n,
      init;; nSteps' n;; stop' = init;; nSteps' n -> init;; nSteps' (S n) = init;; nSteps' n.
  Proof.
    intros init n HH.
    rewrite nSteps_succ.
    rewrite monad_assoc.
    rewrite <- HH.
    repeat rewrite <- monad_assoc.
    rewrite stop_bind.
    reflexivity.
  Qed.

  Lemma nSteps_stop_k: forall (init: Comp unit) n k,
      init;; nSteps' n;; stop' = init;; nSteps' n -> init;; nSteps' (k + n) = init;; nSteps' n.
  Proof.
    intros init n k HH.
    induction k as [|k IH].
    - reflexivity.
    - rewrite plus_Sn_m.
      rewrite <- IH.
      apply nSteps_stop.
      rewrite monad_assoc.
      rewrite IH.
      rewrite <- monad_assoc.
      exact HH.
  Qed.

  (* end hide *)

End generic_machine_section.


(** ** Actual input and output%\label{sec:io}%

In this section we shall define the I/O operations in terms of a
corresponding monad. For simplicity, we will again use a monad of the form
[Opt (ST S m)]; but whereas a concrete implementation of the iVM machine
would typically reflect [CoreState] in its program state, the I/O state
might be distributed across the system as a whole. For instance,
[readFrame'] (defined below) might trigger a scan the next frame of the
film roll on the fly. It is not necessary to perform a complete scan
before starting the machine.

*** Bitmap images

The I/O state has several components. First, an image is a two-dimensional
matrix of square pixels, counting from left to right and from top to
bottom. *)

Record Image (C: Type) :=
  mkImage {
      iWidth: Bits16;
      iHeight: Bits16;
      iPixel: nat -> nat -> option C;
      iDefined: forall x y, iPixel x y <> None <-> x < iWidth /\ y < iHeight;
    }.

(** Here [C] represents the color of a single pixel. The arguments to
[iWidth] and [iHeight] (of type [Image C]) are implicit in the type of
[iDefined]. The simplest image consists of [0 * 0] pixels:

[[
Definition noImage {C} : Image C :=
  {|
     iWidth := toBits 16 0;
     iHeight := toBits 16 0;
     iPixel := fun _ _ => None;
     iDefined := _;
  |}.
]]
*)

(* begin hide *)

Definition noImage {C} : Image C.
  refine ({|
             iWidth := toBits 16 0;
             iHeight := toBits 16 0;
             iPixel := fun _ _ => None;
             iDefined := _;
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

(** [Gray] represents the gray scale of the input images, and [Color] the
colors of the output images: *)

(* begin hide *)

Section limit_scope.
Open Scope type_scope.

(* end hide *)

Definition Gray := Bits8.
Definition Color := Bits64 * Bits64 * Bits64.

(** *** Sound and text

[Sound] represents a clip of stereo sound. Both channels have the same
sample rate, and each pair of 16-bit words $(\coqdocvar{left},
\coqdocvar{right})$ contains one sample for each channel. For convenience,
[sSamples] lists the samples in reverse order. *)

Record Sound :=
  mkSound {
      sRate: Bits32;
      sSamples: list (Bits16 * Bits16);
      sDefined: 0 = sRate -> sSamples = [];
    }.

(**
[[
Definition emptySound (rate: Bits32) : Sound :=
  {|
    sRate := rate;
    sSamples := [];
  |}.
]]
*)

(* begin hide *)

Definition emptySound (rate: nat) : Sound.
  refine ({|
             sRate := (toBits 32 rate);
             sSamples := [];
           |}).
  trivial.
Defined.

(* end hide *)

Definition noSound := emptySound 0.

(** Textual output from the machine uses the encoding UTF-32. Again, we
use reverse ordering. *)

Definition OutputText := list Bits32.

Definition OneOutput := (Image Color) * Sound * OutputText.


(** *** The I/O monad

The complete I/O state of our machine can now be defined as: *)

Record IoState :=
  mkIoState {
      input: list (Image Gray);
      output: list OneOutput;
    }.

(* begin hide *)

End limit_scope.

Instance etaIoState : Settable _ := settable! mkIoState < input; output >.

(* end hide *)

(** When the machine starts, [input] contains all the frames of the film
plus an initial empty frame, and [output] is empty exept for an empty
triple. *)

Definition initialIoState (inputList: list (Image Gray)) :=
  {|
    input := noImage :: inputList;
    output := [(noImage, noSound, [])]
  |}.

(** As the machine executes, [input] will decrease in size, whereas
[output] will increase. The first element in each list represents the
frame currently being processed/produced. In other words, we use a reverse
ordering for [output] as well. The I/O monad is based on the identity
monad: *)

Definition IO0 := ST IoState id.

Definition IO := Opt IO0.


(** *** Input operations *)

Definition readFrame' : IO (Bits16 * Bits16) :=
  update' (fun s => s<|input := tail (input s)|>);;
  i ::= get' input;
  return' (match i with
           | frame :: _ => (iWidth frame, iHeight frame)
           | [] => (toBits 16 0, toBits 16 0)
           end).

(** Here [tail (_ :: tl) := tl] %\:and\:% [tail [] := []]. *)

Definition readPixel' (x y: nat) : IO Bits8 :=
  i ::= get' input;
  match i with
  | [] => stop'
  | frame :: _ =>
    match iPixel frame x y with
    | None => stop'
    | Some c => return' c
    end
  end.


(** *** Output operations *)

Definition defaultColor: Color := let z := toBits 64 0 in (z, z, z).
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

Definition blank (width: Bits16) (height: Bits16): Image Color.
  refine (
      {|
        iWidth := width;
        iHeight := height;
        iPixel x y := if (x <? width) && (y <? height) then Some defaultColor else None;
        iDefined := _;
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

(* end hide *)
(**
[[
Definition blank (width: Bits16) (height: Bits16): Image Color :=
  {|
    iWidth := width;
    iHeight := height;
    iPixel x y := if (x <? width) && (y <? height) then Some defaultColor else None;
    iDefined := _;
  |}.
]]

Here %\:%[p && q = if p then q else false]. *)

Definition newFrame' (width height rate: nat) : IO unit :=
  let o := (blank (toBits 16 width) (toBits 16 height), emptySound rate, []) in
  update' (fun s => s<|output := o :: output s|>).

Definition getCurrentOutput' : IO OneOutput :=
  oList ::= get' output;
  match oList with
  | o :: _ => return' o
  | [] => stop'
  end.

(** In practice, [getCurrentOutput'] will not stop since we start the
machine with a non-empty output list. *)

Definition replaceOutput o s : IoState := s<|output := o :: tail (output s)|>.

(**
[[
Definition trySetPixel (image: Image Color) (x y: nat) (c: Color): option (Image Color) :=
  if (x <? iWidth image) && (y <? iHeight image)
  then let p xx yy := if (xx =? x) && (yy =? y)
                     then Some c
                     else iPixel image xx yy in
       Some (image <| iPixel := p |>)
  else None).
]]
*)

(* begin hide *)

Definition trySetPixel (image: Image Color) (x y: nat) (c: Color): option (Image Color).
  refine (let newPix xx yy := if (xx =? x) && (yy =? y) then Some c else iPixel image xx yy in
          if Sumbool.sumbool_of_bool ((x <? iWidth image) && (y <? iHeight image))
          then Some
                 {|
                   iWidth := iWidth image;
                   iHeight := iHeight image;
                   iPixel := newPix;
                   iDefined := _
                 |}
          else None).
  subst newPix.
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
  - apply (iDefined image).
  - discriminate.
  - apply (iDefined image).
Defined.

(* end hide *)

Definition setPixel' (x y r g b : nat) : IO unit :=
  o ::= getCurrentOutput';
  match o with (image, sound, text) =>
    match trySetPixel image x y (toBits 64 r, toBits 64 g, toBits 64 b) with
    | None => stop'
    | Some newImage => update' (replaceOutput (newImage, sound, text))
    end
  end.


(**
[[
Definition addSample' (l r : nat) : Comp unit :=
  o ::= getCurrentOutput';
  match o with (image, sound, text) =>
    if sRate sound =? 0
    then stop'
    else let ns := sound <| sSamples := (toBits 16 l, toBits 16 r) :: sSamples sound |> in
         update' (replaceOutput (image, ns, text))
  end.
]]
*)

(* begin hide *)

Definition addSample (s: Sound) (H: 0 <> sRate s) (l: Bits16) (r: Bits16) :=
  {|
    sRate := sRate s;
    sSamples := (l, r) :: (sSamples s);
    sDefined := fun H0 => False_ind _ (H H0);
  |}.

Definition addSample' (l r : nat) : IO unit :=
  o ::= getCurrentOutput';
  match o with (image, sound, text) =>
    match Sumbool.sumbool_of_bool (0 =? sRate sound) with
    | left _ => stop'
    | right H =>
      let newSound := addSample sound (beq_nat_false _ _ H) (toBits 16 l) (toBits 16 r) in
      update' (replaceOutput (image, newSound, text))
    end
  end.

(* end hide *)

Definition putChar' (c: nat) : IO unit :=
  o ::= getCurrentOutput';
  match o with (image, sound, text) =>
    update' (replaceOutput (image, sound, (toBits 32 c) :: text))
  end.


(** *** List of I/O operations

The generic machine defined in section%~\ref{sec:generic}% expects I/O
operations of a certain form. *)

Equations nFun (n: nat) (A B: Type): Type :=
  nFun O _ B := B;
  nFun (S n) A B := A -> (nFun n A B).

(** In other words, [nFun n A B = ]$\underbrace{A\rightarrow A\rightarrow ...}_n$[ -> B]. *)

(* begin hide *)
Open Scope vector_scope.
(* end hide *)

Equations nApp {n A B} (f: nFun n A B) (v: vector A n): B :=
  nApp y [] := y;
  nApp f (x :: v) := nApp (f x) v.

(* begin hide *)
Close Scope vector_scope.
(* end hide *)

(* For some reason, I can't make this a "let" in the next definition. *)
Definition io_operation n f := {| operation := nApp (f: nFun n Bits64 (IO (list Z))) |}.

Definition IO_operations :=
  [
    io_operation 0 (wh ::= readFrame'; return' [fst wh : Z; snd wh : Z]);
    io_operation 2 (fun x y => p ::= readPixel' x y; return' [p:Z]);
    io_operation 3 (fun w h r => newFrame' w h r;; return' []);
    io_operation 5 (fun x y r g b => setPixel' x y r g b;; return' []);
    io_operation 2 (fun l r => addSample' l r;; return' []);
    io_operation 1 (fun c => putChar' c;; return' [])
  ].



(** ** Integration%\label{sec:integration}%

Putting everthing together, we can say what it means to run the machine
from start to finish. *)

(* begin hide *)
(* Why is this needed?*)
Instance CompMonad: Monad (Comp (m:=IO0)).
Proof.
  unfold Comp.
  typeclasses eauto.
Defined.
(* end hide *)

Lemma characterize_stopped: forall (c: Comp (m:=IO0) unit) (cs: CoreState) (ios: IoState),
    let init := update' (fun _ => cs);; fromIO (update' (fun _ => ios)) in
    init;; c;; stop' = init;; c  <->  fst (fst (c cs ios)) = None.
Proof. (* TODO: Improve proof *)
  intros.
  split; intro H.
  - assert ((init;; c;; stop') cs ios = (init;; c) cs ios) as HH;
      [congruence|]; clear H; rename HH into H.
    subst init.
    simpl in H.
    rewrite <- H.
    clear H.
    destruct (fst (fst (c cs ios))); reflexivity.
  - apply functional_extensionality. intro cs2.
    apply functional_extensionality. intro iso2.
    simpl.
    rewrite H.
    clear cs2 iso2.
    destruct (c cs ios) as [[opt cs2] ios2].
    simpl. simpl in H.
    rewrite H.
    reflexivity.
Qed.

(* begin hide *)
Section limit_scope.
Open Scope type_scope.
(* end hide *)

Definition State := CoreState * IoState.

(* begin hide *)
End limit_scope.
(* end hide *)

Definition finalState
           program argument (start: Bits64) (memorySize: nat) inputList
           (Ha: start + memorySize <= 2^64)
           (Hb: length program + 8 + length argument <= memorySize): State -> Prop :=
  let cs := initialCoreState program argument start memorySize Ha Hb in
  let ios := initialIoState inputList in
  fun s => exists n, nSteps' IO_operations n cs ios = ((None, fst s), snd s).

(** This is a partial function in the following sense: *)

Lemma finalState_unique: forall p a st ms i Ha Hb s1 s2,
    finalState p a st ms i Ha Hb s1 -> finalState p a st ms i Ha Hb s2 -> s1 = s2.
Proof. (* TODO: simplify *)
  intros p a st ms i Ha Hb s1 s2 H1 H2.
  destruct H1 as [n1 H1].
  destruct H2 as [n2 H2].
  revert H1 H2.
  generalize (initialCoreState p a st ms Ha Hb).
  generalize (initialIoState i).
  intros ios cs H1 H2.
  set (g := nSteps' IO_operations) in *.
  enough (g n1 cs ios = g n2 cs ios) as HH.
  - rewrite H1, H2 in HH.
    inversion HH.
    destruct s1.
    destruct s2.
    f_equal; assumption.
  - set (init := update' (fun _ => cs);; fromIO (update' (fun _ => ios))).
    assert (init;; g n1;; stop' = init;; g n1) as Hs1; [apply characterize_stopped; rewrite H1; reflexivity|].
    assert (init;; g n2;; stop' = init;; g n2) as Hs2; [apply characterize_stopped; rewrite H2; reflexivity|].

    set (n3 := max n1 n2).
    enough (g n3 cs ios = g n1 cs ios /\ g n3 cs ios = g n2 cs ios) as [HH1 HH2].
    + rewrite HH2 in HH1.
      rewrite H1, H2 in HH1.
      inversion HH1.
      destruct  s1; destruct s2.
      simpl in *.
      congruence.
    + split.
      * set (k1 := (n3 - n1)%nat).
        assert (n3 = (k1 + n1)%nat) as Hn1; [lia|].
        assert (init;; g (k1 + n1)%nat = init;; g n1) as Hi1; [apply nSteps_stop_k; exact Hs1|].
        rewrite <- Hn1 in Hi1.
        assert ((init;; g n3) cs ios = (init;; g n1) cs ios) as HH1; [congruence|].
        exact HH1.
      * set (k2 := (n3 - n2)%nat).
        assert (n3 = (k2 + n2)%nat) as Hn2; [lia|].
        assert (init;; g (k2 + n2)%nat = init;; g n2) as Hi2; [apply nSteps_stop_k; exact Hs2|].
        rewrite <- Hn2 in Hi2.
        assert ((init;; g n3) cs ios = (init;; g n2) cs ios) as HH2; [congruence|].
        exact HH2.
Qed.

(** In a framework with general recursion we could have defined this
partial function directly. *)
