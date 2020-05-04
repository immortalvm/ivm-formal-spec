Require Import Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.


(** ** Error monad *)

Reserved Notation "ma >>= f" (at level 69, left associativity).

Class EMonad (m: Type -> Type): Type :=
{
  ret {A} : A -> m A;
  bind {A} (_: m A) {B} : (A -> m B) -> m B
    where "ma >>= f" := (bind ma f);

  monad_right A (ma: m A) : ma >>= ret = ma;
  monad_left A (a: A) B (f: A -> m B) : ret a >>= f = f a;
  monad_assoc A (ma: m A) B f C (g: B -> m C) : (ma >>= f) >>= g = ma >>= (fun a => f a >>= g);

  err {A} : m A;
  err_terminal A B (f: A -> m B) : err >>= f = err;
}.

Declare Scope monad_scope.
Notation "ma >>= f" := (bind ma f) : monad_scope.
Open Scope monad_scope.

(* Note to self: Order of associativity switched since ivm.v. *)

Class EMorphism m0 `{EMonad m0} m1 `{EMonad m1} (F: forall {A}, m0 A -> m1 A) :=
{
  morph_ret A (x: A) : F (ret x) = ret x;
  morph_bind A (ma: m0 A) B (f: A -> m0 B) : F (ma >>= f) = (F ma) >>= (fun x => F (f x));
  morph_err A : F (err : m0 A) = err;
}.

Class SMonad (S: Type) (m: Type -> Type): Type :=
{
  emonad :> EMonad m;
  get : m S;
  put (s: S) : m unit;
}.

(** NB. Observe that [SMonad] is not fully axiomatized. *)

Class SMorphism S m0 `{SMonad S m0} m1 `{SMonad S m1} (F: forall {A}, m0 A -> m1 A) :=
{
  emorphism :> EMorphism m0 m1 (@F);
  morph_get : F get = get;
  morph_put s : F (put s) = put s;
}.


(** Error/State monad *)

Definition EST S A : Type := S -> option (A * S).

#[refine]
Instance est_emonad S : EMonad (EST S) :=
{
  ret A a s := Some (a, s);
  bind A ma _ f s :=
    match ma s with
    | None => None
    | Some (a, s') => f a s'
    end;
    err _ _ := None;
}.
Proof.
  - intros A ma.
    apply functional_extensionality. intro s.
    destruct (ma s) as [[a s']|]; reflexivity.
  - intros A a B f.
    apply functional_extensionality. intro s.
    reflexivity.
  - intros A ma B f C g.
    apply functional_extensionality. intro s.
    destruct (ma s) as [[a s']|]; reflexivity.
  - reflexivity.
Defined.

Instance est_smonad S : SMonad S (EST S) :=
{
  emonad := est_emonad S;
  get s := Some (s, s);
  put s _ := Some (tt, s);
}.


(** Abstract syntax *)

(* Inspired by FreeSpec's [impure].*)
Inductive EST0 (S: Type) : Type -> Type :=
| ret0 {A} : A -> EST0 S A
| err0 {A} : EST0 S A
| get0 {A} : (S -> EST0 S A) -> EST0 S A
| put0 : S -> forall {A}, EST0 S A -> EST0 S A.

Equations bind0 S {A} (ma: EST0 S A) {B} (_: A -> EST0 S B) : EST0 S B :=
  bind0 _ (ret0 S a) g := g a;
  bind0 _ (err0 S) _ := err0 S;
  bind0 _ (get0 S f) g := get0 S (fun a => bind0 S (f a) g);
  bind0 _ (put0 S s ma) g := put0 S s (bind0 S ma g).

#[refine]
Instance est0_emonad S : EMonad (EST0 S) :=
  {
  ret _ a := ret0 S a;
  bind _ ma _ f := bind0 S ma f;
  err _ := err0 S;
  }.
Proof.
  - intros A ma.
    induction ma as [A a|A|A g IH|s A ma IH]; simp bind0.
    + reflexivity.
    + reflexivity.
    + f_equal. apply functional_extensionality. exact IH.
    + f_equal. exact IH.

  - intros A a B f. simp bind0. reflexivity.

  - intros A ma B f C g.
    induction ma as [A a|A|A h IH|s A ma IH]; simp bind0.
    + reflexivity.
    + reflexivity.
    + f_equal.
      apply functional_extensionality. intro s. apply IH.
    + f_equal. apply IH.

  - intros A B f. simp bind0. reflexivity.
Defined.

Instance est0_smonad S : SMonad S (EST0 S) :=
{
  emonad := est0_emonad S;
  get := get0 S (ret0 S);
  put s := put0 S s (ret0 S tt);
}.

(* We prefer a notation which does not require do-end blocks. *)
Notation "let* a := ma 'in' mb" := (bind ma (fun a => mb)) (at level 60, right associativity) : monad_scope.
Notation "ma ;; mb" := (bind ma (fun _ => mb)) (at level 60, right associativity) : monad_scope.

Equations interp {S M} `{_: SMonad S M} {A} (_: EST0 S A) : M A :=
  interp (ret0 S a) := ret a;
  interp (err0 S) := err;
  interp (get0 S f) := let* s := get in interp (f s);
  interp (put0 S s ma) := put s;; interp ma.

#[refine]
Instance interp_smorphism S M `(_: SMonad S M) : SMorphism S (EST0 S) M (@interp S M _) := {}.
Proof.
  - split.
    + intros A x. reflexivity.
    + intros A ma B f. simpl.
      induction ma as [A a|A|A h IH|s A ma IH]; simp bind0.
      * simp interp. rewrite monad_left. reflexivity.
      * simp interp. rewrite err_terminal. reflexivity.
      * simp interp. rewrite monad_assoc. f_equal.
        apply functional_extensionality. intro s. apply IH.
      * simp interp. rewrite monad_assoc. f_equal.
        apply functional_extensionality. rewrite IH. intros _. reflexivity.
    + intro A. reflexivity.

  - simpl. simp interp.
    rewrite <- monad_right. (* Hack since, rewrite does not work under fun binder. *)
    reflexivity.
  - intro s. simpl. simp interp. rewrite <- monad_right. (* Similar hack. *)
    f_equal.
    apply functional_extensionality. intros []. reflexivity.
Defined.


(** Product state *)

Definition prod_morph
           S1 M1 `{SMonad S1}
           S2 M2 `{SMonad (S1 * S2) M2}
           {A} (ma: M1 A) : M2 A.
{A} (ma: SMonad
