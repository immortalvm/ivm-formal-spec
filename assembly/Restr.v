From Assembly Require Import Lens DSet.

Unset Suggest Proof Using.


(** ** Restriction lenses *)

Import DSetNotations.

Section restriction_section.

  Context {A : Type} {F : A -> Type}.

  Definition restr u : Type := forall (a: A), a ∈ u -> F a.

  Local Notation S := (forall a, F a).

  #[refine] Instance fullLens : Lens S (restr Ω) :=
  {
    proj f a _ := f a;
    update _ g a := g a I;
  }.
  Proof.
    all: unfold restr; try reflexivity.
    cbn. intros f g.
    extensionality a.
    extensionality t.
    destruct t. reflexivity.
  Defined.

  #[refine] Instance subsetLens {u v} (Huv: u ⊆ v) : Lens (restr v) (restr u) :=
  {
    proj f a Ha := f a (Huv a Ha);
    update f g a Hv := match decide (a ∈ u) with
                       | left Hu => g a Hu
                       | _ => f a Hv
                       end;
  }.
  Proof.
    - abstract (intros f g;
                extensionality a;
                extensionality Ha;
                decided Ha;
                reflexivity).
    - abstract (intros f;
                extensionality a;
                extensionality Hv;
                destruct (decide _) as [Hu|_];
                [ f_equal; apply is_true_unique
                | reflexivity ]).
    - abstract (intros f g g';
                extensionality a;
                extensionality Hv;
                destruct (decide _);
                reflexivity).
  Defined.

  Instance restrLens u : Lens S (restr u) :=
    subsetLens full_terminal ∘ fullLens.

  (** By construction *)
  Instance full_sublens u : (restrLens u | fullLens).
  Proof.
    apply sublens_comp'.
  Qed.

  Global Instance restrLens_proper_sub :
    Proper (@subset A ==> @Submixer S) restrLens.
  Proof.
    intros u v Huv.
    intros f g h. extensionality a. cbn.
    destruct (decide (a ∈ u)) as [Hu|Hu];
      destruct (decide (a ∈ v)) as [Hv|Hv];
      try reflexivity.
    exfalso.
    apply Hv, Huv, Hu.
  Qed.

  (* TODO: Useful? *)
  Instance submixer_subset {u v} (Huv: u ⊆ v) : (restrLens u | restrLens v).
  Proof.
    (* Does not work in 8.12: [rewrite Huv.]
       cf. Coq issue #4175. *)
    apply restrLens_proper_sub. exact Huv.
  Qed.

  Instance separate_independent u v (Huv: u # v) :
    Independent (restrLens u) (restrLens v).
  Proof.
    intros f g h. extensionality a. cbn.
    destruct (decide (a ∈ v)) as [Hv|Hv];
      destruct (decide (a ∈ u)) as [Hu|Hu];
      try reflexivity.
    exfalso.
    apply (Huv a).
    split; assumption.
  Qed.


  (** ** Point lenses, [restrLens {a}] simplified *)

  Context {H_eqdec: EqDec A}.

  #[refine] Instance pointLens' {a u} (Ha: a ∈ u) : Lens (restr u) (F a) :=
  {
    proj f := f a Ha;
    update f x a' Hu := match decide (a = a') with
                        | left H => rew H in x
                        | _ => f a' Hu
                        end;
  }.
  Proof.
    - abstract (intros f x;
                decided (@eq_refl _ a);
                revert H;
                apply EqDec.UIP_K;
                reflexivity).
    - intros f;
        extensionality a';
        extensionality Hu;
        destruct (decide (a = a')) as [H|H];
        [ subst a; cbn; f_equal; apply is_true_unique
        | reflexivity ].
    - abstract (intros f x x';
                extensionality a';
                extensionality Hu;
                destruct (decide (a = a')) as [H|H];
                reflexivity).
  Defined.

  Instance pointLens a : Lens S (F a) := pointLens' full_spec ∘ fullLens.

  Instance pointLens_sublens {a u} (Ha: a ∈ u) : (pointLens a | restrLens u).
  Proof.
    intros f g h. extensionality a'. cbn.
    destruct (decide (a = a')) as [H|H].
    - subst a. decided Ha. reflexivity.
    - destruct (decide _); reflexivity.
  Qed.

  Instance pointLens_independent {a a'} (Ha: a <> a') :
    Independent (pointLens a) (pointLens a').
  Proof.
    intros f x x'. cbn.
    extensionality a''.
    destruct (decide (a' = a'')) as [He'|He'];
      destruct (decide (a = a'')) as [He|He];
      congruence.
  Qed.

End restriction_section.
