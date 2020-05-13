Require Import Utf8.

Require Import Assembly.Mon.


(** The results in this file are not used elsehwere, but they can be
useful for the understanding of the subject.*)


(** ** The trivial [SMonad] *)

Section trivial_smonad_section.

  Context (S: Type).

  Local Ltac crush :=
    repeat (match goal with
            | [|- unit] => exact tt
            | [|- forall (_:unit),_] => intros []
            | [|- ?x = ?y :> unit] => destruct x; destruct y
            end
            || intro
            || reflexivity
            || assumption).

  #[refine]
  Instance trivial_smonad : SMonad S (fun _ => unit) := { }.
  all: crush.
  Defined.

  (** Clearly, this is the terminal [SMonad]. Moreover, this means that
      there are non-trivial "termination properties" that hold in all
      [SMonads]. Thus, we shall express and prove such properties only for
      the initial [SMonad]. *)

End trivial_smonad_section.


(** ** No side-effects *)

Section no_side_effects_section.

  Open Scope monad_scope.

  Context (S: Type)
          (m: Type -> Type)
          {M: SMonad S m}.

  Class NoSideEffects {A} (ma: m A) : Prop :=
    noSideEffects: forall B (mb: m B), ma;; mb = mb.

  Global Instance noEff_unit {A} (ma: m A) (H: ma;; ret tt = ret tt): NoSideEffects ma.
  Proof.
    intros B mb.
    transitivity (ma;; ret tt;; mb).
    - setoid_rewrite monad_left. reflexivity.
    - rewrite <- monad_assoc, H, monad_left. reflexivity.
  Qed.

  Global Instance noEff_ret {A} (x: A) : NoSideEffects (ret x).
  Proof.
    apply noEff_unit. rewrite monad_left. reflexivity.
  Qed.

  Global Instance noEff_bind
           {A B} (ma: m A) (f: A -> m B)
           {Ha: NoSideEffects ma}
           {Hb: forall x, NoSideEffects (f x)} : NoSideEffects (bind ma f).
  Proof.
    intros C mc.
    rewrite monad_assoc.
    setoid_rewrite Hb.
    rewrite Ha.
    reflexivity.
  Qed.

End no_side_effects_section.

Existing Instance est_smonad.

(** [NoSideEffects get] does not hold in general.
    (Think about logging/monitoring.) *)

Instance noEff_get {S} : NoSideEffects S (EST S) get.
Proof.
  intros B mb.
  simpl.
  apply functional_extensionality.
  intros s.
  reflexivity.
Qed.


(** ** Every projection is a product projection

Assuming functional extensionality and proof irrelevance, we have a
converse of [proj_fst]: If [Proj S X], then [S ≅ X * S'] for some S'. *)

Require Coq.Logic.ProofIrrelevance.

Section inv_proj_section.

  Import Coq.Logic.ProofIrrelevance.

  Context S X (PX: Proj S X).

  Definition S' := { f: X -> S | forall x y, update (f x) y = f y }.

  #[refine]
  Instance inv_proj : Proj S S' :=
  {
    proj s := exist _ (update s) _;
    update s f := proj1_sig f (proj s);
  }.
  Proof.
    - intros x y. rewrite update_update. reflexivity.
    - intros s [f H].
      simpl.
      apply eq_sig_hprop.
      + intros. apply proof_irrelevance.
      + simpl. apply functional_extensionality. intros x.
        rewrite H. reflexivity.
    - intro s. simpl.
      rewrite update_proj. reflexivity.
    - intros s [f Hf] [g Hg]. simpl.
      rewrite <- (Hf (proj s)), proj_update. reflexivity.
  Defined.

  Instance inv_proj_independent : Independent inv_proj PX.
  Proof.
    split.
    - intros s [f Hf]. simpl.
      rewrite <- (Hf (proj s)), proj_update. reflexivity.
    - intros s x. simpl.
      apply eq_sig_hprop.
      + intros. apply proof_irrelevance.
      + simpl. apply functional_extensionality. intros x'.
        rewrite update_update. reflexivity.
    - intros s [f Hf] x. simpl.
      rewrite proj_update, Hf. reflexivity.
  Qed.

  Lemma inv_proj_inv (s: S) :
    let (fH, x) := proj (Proj:=proj_prod _ _) s in
    proj1_sig fH x = s.
  Proof.
    simpl. rewrite update_proj. reflexivity.
  Qed.

End inv_proj_section.
