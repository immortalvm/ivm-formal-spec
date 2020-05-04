Require Import Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.


(** ** Error/state monad *)

Declare Scope monad_scope.

Reserved Notation "ma >>= f" (at level 69, left associativity).

Class SMonad (S: Type) (m: Type -> Type): Type :=
{
  ret {A} : A -> m A;
  bind {A} (_: m A) {B} : (A -> m B) -> m B
    where "ma >>= f" := (bind ma f);

  monad_right A (ma: m A) : ma >>= ret = ma;
  monad_left A (a: A) B (f: A -> m B) : ret a >>= f = f a;
  monad_assoc A (ma: m A) B f C (g: B -> m C) : (ma >>= f) >>= g = ma >>= (fun a => f a >>= g);

  err {A} : m A;
  err_right A (ma: m A) B : ma >>= (fun _ => err) = (err : m B);
  err_left A B (f: A -> m B) : err >>= f = err;

  get : m S;
  put (s: S) : m unit;
  put_put s s' : put s >>= (fun _ => put s') = put s';
  put_get s B (f: S -> m B) : put s >>= (fun _ => get >>= f) = put s >>= fun _ => f s;
  get_put B (f: S -> m B) : get >>= (fun s => put s >>= (fun _ => f s)) = get >>= f;
  get_ret B (mb: m B) : get >>= (fun _ => mb) = mb;
  get_get B (f: S -> S -> m B) : get >>= (fun s => get >>= (fun s' => f s s')) = get >>= (fun s => f s s);
}.

(* Note to self: Order of associativity switched since ivm.v. *)

Notation "ma >>= f" := (bind ma f) : monad_scope.

(* We prefer a notation which does not require do-end blocks. *)
Notation "'let*' a := ma 'in' mb" := (bind ma (fun a => mb))
                                       (at level 60, right associativity,
                                        format "'[hv' let*  a  :=  ma  'in'  '//' mb ']'") : monad_scope.
Notation "ma ;; mb" := (bind ma (fun _ => mb))
                         (at level 60, right associativity,
                          format "'[hv' ma ;;  '//' mb ']'") : monad_scope.


Section state_section.

  Context (S: Type).

  Open Scope monad_scope.

  Global Instance bind_proper m `{SM: SMonad S m} {A} (ma: m A) {B}:
    Proper ( pointwise_relation A (@eq (m B)) ==> (@eq (m B)) ) (@bind S m SM A ma B).
  Proof.
    intros f f' H_f. f_equal.
    apply functional_extensionality. intros a. f_equal.
  Qed.

  (* TODO: Is this really needed (or even useful)? *)
  Global Instance put_proper m `{SM: SMonad S m} : Proper ( (@eq S) ==> (@eq (m unit)) ) (@put S m SM).
  Proof.
    intros s s' Hs. f_equal. exact Hs.
  Qed.


  Class SMorphism m0 `{SM0: SMonad S m0} m1 `{SM1: SMonad S m1} (F: forall {A}, m0 A -> m1 A) :=
  {
    morph_ret A (a: A) : F (ret a) = ret a;
    morph_bind A (ma: m0 A) B (f: A -> m0 B) : F (ma >>= f) = (F ma) >>= (fun x => F (f x));
    morph_err A : F (err : m0 A) = err;
    morph_get : F get = get;
    morph_put s : F (put s) = put s;
  }.


  (** Initial SMonad *)

  Definition EST A : Type := S -> option (S * A).

  #[refine]
  Instance est_smonad : SMonad S EST :=
  {
    ret A a s := Some (s, a);
    bind A ma B f s :=
      match ma s with
      | None => None
      | Some (s', a) => f a s'
      end;
    err _ _ := None;
    get s := Some (s, s);
    put s _ := Some (s, tt);
  }.
  Proof.
    - intros A ma.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - intros A a B f.
      apply functional_extensionality. intros s.
      reflexivity.
    - intros A ma B f C g.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - intros A ma B.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Defined.

  Definition from_est {m} `{SMonad S m} {A} (ma: EST A) : m A :=
    let* s := get in
    match ma s with
    | None => err
    | Some (s', a) => put s';; ret a
    end.

  Lemma est_characterization A (ma: EST A) : from_est ma = ma.
  Proof.
    unfold from_est.
    simpl.
    apply functional_extensionality. intros s.
    destruct (ma s) as [[s' a]|]; reflexivity.
  Qed.

  Lemma est_unique m `{SMonad S m} F `{SMorphism EST (SM0:=est_smonad) m F} A (ma: EST A) : F A ma = from_est ma.
  Proof.
    rewrite <- est_characterization at 1.
    unfold from_est at 1.
    rewrite morph_bind, morph_get. unfold from_est. f_equal.
    apply functional_extensionality. intros s.
    destruct (ma s) as [[s' a]|].
    - rewrite morph_bind, morph_put. f_equal.
      apply functional_extensionality. intros [].
      rewrite morph_ret. reflexivity.
    - rewrite morph_err. reflexivity.
  Qed.

  Instance est_morphism m `{SMonad S m}: SMorphism EST m (@from_est m _).
  Proof.
    split.
    - intros A a. unfold from_est. simpl.
      rewrite get_put, get_ret. reflexivity.
    - intros A ma B f.
      unfold from_est.
      simpl.
      rewrite monad_assoc.
      f_equal.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|].
      + rewrite -> monad_assoc, monad_left, put_get.
        destruct (f a s') as [[s'' b]|].
        * rewrite <- monad_assoc, put_put. reflexivity.
        * rewrite err_right. reflexivity.
      + rewrite err_left. reflexivity.
    - intros A.
      unfold from_est. simpl. rewrite err_right. reflexivity.
    - unfold from_est. simpl.
      rewrite get_put, monad_right. reflexivity.
    - intros s.
      unfold from_est. simpl.
      rewrite get_ret, <- monad_right. f_equal.
      apply functional_extensionality. intros []. reflexivity.
  Qed.

End state_section.

Section proj_section.

  Open Scope monad_scope.

  (** ** Projections *)

  Context (S: Type)
          {X: Type}
          (proj: S -> X)
          (update: S -> X -> S).

  Class Proj :=
  {
    proj_update (s: S) (x: X) : proj (update s x) = x;
    update_proj (s: S) : update s (proj s) = s;
    update_update (s: S) (x: X) (x': X) : update (update s x) x' = update s x';
  }.

  Context `{H_proj: Proj}
          (MS: Type -> Type)
          `{H_ms: SMonad S MS}.

  #[refine]
  Instance proj_smonad: SMonad X MS :=
  {
    ret := @ret S MS H_ms;
    bind := @bind S MS H_ms;
    err := @err S MS H_ms;
    get := let* s := get in ret (proj s);
    put x := let* s := get in put (update s x);
  }.
  Proof.
    (* Trivial *)
    - intros A ma. rewrite monad_right. reflexivity.
    - intros A a B f. rewrite monad_left. reflexivity.
    - intros A ma B f C g. rewrite monad_assoc. reflexivity.
    - intros A ma B. rewrite err_right. reflexivity.
    - intros A ma B. rewrite err_left. reflexivity.

    (* Almost trivial *)
    - intros x x'.
      rewrite monad_assoc.
      f_equal. apply functional_extensionality. intros s.
      rewrite put_get, put_put, update_update. reflexivity.
    - intros x B f.
      repeat rewrite monad_assoc.
      f_equal. apply functional_extensionality. intros s.
      rewrite put_get, proj_update, monad_left.
      reflexivity.
    - intros B f.
      repeat setoid_rewrite monad_assoc.
      setoid_rewrite monad_left.
      rewrite get_get.
Set Typeclasses Debug.

      setoid_rewrite update_proj.


      rewrite_strat (innermost update_proj).

      Print Instances Proper.

      setoid_rewrite update_proj.
      Set Printing All.


      setoid_rewrite update_proj.


      f_equal. apply functional_extensionality. intros s.




      setoid_rewrite <- monad_assoc at 2.


      transitivity (let* s := get in f (proj (update s (proj s)))).


      transitivity (let* s := get in f (proj s)).


      +



      match goal with
        [ |- _ = ?rhs ] => assert (rhs = let* s := get in f (proj s)) as H_rhs
      end.
      + f_equal. apply functional_extensionality. intros s.
        rewrite monad_left. reflexivity.
      +
        match goal with

        rewrite H_rhs. clear H_rhs.
        rewrite monad_left.


        f_equal. apply functional_extensionality. intros s.
        rewrite monad_left.
        rewrite

rewrite <- monad_assoc.

      rewrite <- monad_assoc at 1.

      rewrite monad_left.

      simpl.
      f_equal. apply functional_extensionality. intros s.
