Require Import Utf8.

Require Import Equations.Equations.
Set Equations With UIP.

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.


(** ** Error/state monad *)

Declare Scope monad_scope.

Reserved Notation "ma >>= f" (at level 69, left associativity).

Class SMonad (S: Type) (m: Type -> Type): Type :=
{
  ret {A} : A -> m A;
  bind {A B} (_: m A) : (A -> m B) -> m B
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

(* Note to self:
* Order of associativity switched since ivm.v.
* I had to move the [B] argument to [bind] to make it an instance of [Proper] (see below).
*)

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

  Section m_section.

    Context m `{SM: SMonad S m}.

    Global Instance bind_proper {A B}:
      Proper ( eq ==> pointwise_relation A eq ==> eq ) (@bind S m SM A B).
    Proof.
      intros ma ma' H_ma f f' H_f. f_equal.
      - exact H_ma.
      - apply functional_extensionality. intros a. f_equal.
    Qed.

    (* TODO: Is this really needed (or even useful)? *)
    Global Instance put_proper : Proper ( eq ==> eq ) (@put S m SM).
    Proof.
      intros s s' Hs. f_equal. exact Hs.
    Qed.

    Global Instance ret_proper A : Proper ( eq ==> eq ) (@ret S m SM A).
    Proof.
      intros a a' Ha. f_equal. exact Ha.
    Qed.

  End m_section.


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
  Global Instance est_smonad : SMonad S EST :=
  {
    ret A a s := Some (s, a);
    bind A B ma f s :=
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

  Global Instance est_morphism m `{SMonad S m}: SMorphism EST m (@from_est m _).
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


(** ** Projections *)

Class Proj (S: Type) (X: Type) :=
{
  proj: S -> X;
  update: S -> X -> S;
  proj_update (s: S) (x: X) : proj (update s x) = x;
  update_proj (s: S) : update s (proj s) = s;
  update_update (s: S) (x: X) (x': X) : update (update s x) x' = update s x';
}.

Section proj_section.

  Open Scope monad_scope.

  Context {S: Type}
          (m: Type -> Type) `{SM: SMonad S m}
          {X: Type} `(PM: Proj S X).

  #[refine]
  Global Instance proj_smonad: SMonad X m :=
  {
    ret := @ret S m SM;
    bind := @bind S m SM;
    err := @err S m SM;
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
      setoid_rewrite update_proj.
      setoid_rewrite get_put.
      reflexivity.
    - intros B mb.
      rewrite monad_assoc.
      setoid_rewrite monad_left.
      rewrite get_ret.
      reflexivity.
    - intros B f.
      repeat setoid_rewrite monad_assoc.
      repeat setoid_rewrite monad_left.
      rewrite get_get.
      reflexivity.
  Defined.

End proj_section.

Class Independent {S: Type}
      {X: Type} (PX: Proj S X)
      {Y: Type} (PY: Proj S Y) : Prop :=
{
  projY_updateX (s: S) (x: X) : proj (update s x) = proj s :> Y;
  projX_updateY (s: S) (y: Y) : proj (update s y) = proj s :> X;
  independent_commute (s: S) (x: X) (y: Y) :
    update (update s x) y = update (update s y) x;
}.

(** To see that [independent_commute] does not follow from the other
    properties, consider a square staircase. *)

Section product_section.

  Context {X Y: Type}.

  (* Since this instance is in a section and not marked global,
     it is removed from the instance database below. *)

  Program Instance proj_fst : Proj (X * Y) X :=
  {
    proj := fst;
    update s x := (x, snd s);
  }.

  Program Instance proj_snd : Proj (X * Y) Y :=
  {
    proj := snd;
    update s y := (fst s, y);
  }.

  Program Instance independent_projs : Independent proj_fst proj_snd.

  Context {S} (Hx: Proj S X) (Hy: Proj S Y) {Hd: Independent Hx Hy}.

  Instance independent_symm : Independent Hy Hx.
  Proof.
    split.
    - apply projX_updateY.
    - apply projY_updateX.
    - symmetry. apply independent_commute.
  Qed.

  #[refine]
  Instance proj_prod : Proj S (X * Y) :=
  {
    proj s := (proj s, proj s);
    update s pair := update (update s (fst pair)) (snd pair);
  }.
  Proof.
    - intros s [x y]. simpl.
      rewrite projX_updateY, proj_update, proj_update.
      reflexivity.
    - intros. simpl.
      do 2 rewrite update_proj.
      reflexivity.
    - intros s [x y] [x' y']. simpl.
      do 2 (rewrite independent_commute, update_update).
      reflexivity.
  Defined.

  Context Z (Hz: Proj S Z) (Hdx: Independent Hx Hz) (Hdy: Independent Hy Hz).

  Instance independent_prod : Independent proj_prod Hz.
  Proof.
    split.
    - intros s [x y].
      simpl.
      transitivity (proj (update s x)).
      + rewrite projY_updateX. reflexivity.
      + rewrite projY_updateX. reflexivity.
    - intros s z. simpl. f_equal.
      + rewrite projX_updateY. reflexivity.
      + rewrite projX_updateY. reflexivity.
    - intros s [x y] z. simpl.
      rewrite independent_commute, (independent_commute (Independent:=Hdx)). reflexivity.
  Qed.

End product_section.

(** The projections from a record type have the same property. *)

Section relation_section.

  Context {S X} (HX: Proj S X).

  Definition aligned (s s' : S) :=
    update s (proj s') = s'.

  (** Thus, [aligned s s'] means that [s] and [s'] are equal except for
  their projections onto [X]. *)

  Instance aligned_equivalence : Equivalence aligned.
  Proof.
    split.
    - intros s. unfold aligned. rewrite update_proj. reflexivity.
    - intros s s'. unfold aligned. intros H. rewrite <- H.
      rewrite update_update, update_proj. reflexivity.
    - intros s1 s2 s3. unfold aligned. intros H12 H23.
      rewrite <- H12 in H23.
      rewrite update_update in H23.
      exact H23.
  Qed.

  Context (R: relation X).

  Definition proj_relation : relation S :=
    fun s s' => aligned s s' /\ R (proj s) (proj s').

  Global Instance proj_relation_reflexive {H_reflexive: Reflexive R} : Reflexive proj_relation.
  Proof.
    unfold proj_relation. intros s. split; reflexivity.
  Qed.

  Global Instance proj_relation_symmetric {H_symmetric: Symmetric R} : Symmetric proj_relation.
  Proof.
    unfold proj_relation. intros s s' [? ?].
    split; symmetry; assumption.
  Qed.

  Global Instance proj_relation_transitive {H_transitive: Transitive R} : Transitive proj_relation.
  Proof.
    unfold proj_relation. intros s1 s2 s3 [? ?] [? ?].
    split.
    - transitivity s2; assumption.
    - transitivity (proj s2); assumption.
  Qed.

End relation_section.

Require Import Assembly.Convenience.

Section proper_section.

  Context {S} (RS: relation S).

  Local Notation M := (EST S).

  Definition est_relation {A} (RA: relation A) : relation (M A) :=
    (RS ==> option_relation (prod_relation RS RA))%signature.

  Local Notation RM := (est_relation).

  Global Instance ret_propR {A} {RA: relation A} : Proper (RA ==> RM RA) (@ret _ M _ A).
  Proof.
    intros a a' Ha.
    intros s s' Hs.
    simpl.
    split; assumption.
  Qed.

  Global Instance bind_propR {A B} {RA: relation A} {RB: relation B} :
    Proper (RM RA ==> (RA ==> RM RB) ==> RM RB) (@bind _ M _ A B).
  Proof.
    intros ma ma' Hma f f' Hf.
    intros s s' Hs. simpl.
    specialize (Hma s s' Hs).
    destruct (ma s) as [(t,a)|]; destruct (ma' s') as [(t',a')|].
    - destruct Hma as [Ht Ha].
      exact (Hf _ _ Ha _ _ Ht).
    - contradict Hma.
    - exact I.
    - exact I.
  Qed.

  Global Instance get_propR : Proper (RM RS) get.
  Proof.
    intros s s' Hs.
    split; assumption.
  Qed.

  Global Instance put_propR : Proper (RS ==> RM eq) put.
  Proof.
    intros s s' Hs.
    intros t t' Ht.
    split.
    - assumption.
    - reflexivity.
  Qed.

End proper_section.
