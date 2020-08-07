From Assembly Require Import Init DSet.

Unset Suggest Proof Using.


(** ** Lenses *)

Class Lens (A: Type) (X: Type) :=
{
  proj: A -> X;
  update: A -> X -> A;
  proj_update (a: A) (x: X) : proj (update a x) = x;
  update_proj (a: A) : update a (proj a) = a;
  update_update (a: A) (x: X) (x': X) : update (update a x) x' = update a x';
}.

Declare Scope lens_scope.
Bind Scope lens_scope with Lens.
Delimit Scope lens_scope with lens.

Hint Rewrite @proj_update : lens.
Hint Rewrite @update_proj : lens.
Hint Rewrite @update_update : lens.

Set Typeclasses Unique Instances.


(** ** Independent lenses *)

Class Independent {A: Type}
      {X: Type} (LX: Lens A X)
      {Y: Type} (LY: Lens A Y) : Prop :=
  independent (a: A) (x: X) (y: Y) :
    update (update a x) y = update (update a y) x.

Section independence_section.

  Context {A X Y} {LX: Lens A X} {LY: Lens A Y} (HI: Independent LX LY).

  Proposition proj2_update1 (a: A) (x: X) : proj (update a x) = proj a :> Y.
  Proof.
    rewrite <- (@update_proj _ _ LY a) at 1.
    rewrite <- independent.
    apply proj_update.
  Qed.

  Proposition proj1_update2 (a: A) (y: Y) : proj (update a y) = proj a :> X.
  Proof.
    rewrite <- (@update_proj _ _ LX a) at 1.
    rewrite independent.
    apply proj_update.
  Qed.

  (** Beware: This may cause loops. *)
  Instance independent_symm : Independent LY LX.
  Proof. intros a y x. symmetry. apply independent. Qed.

End independence_section.

Arguments proj2_update1 {_ _ _ _ _ HI}.
Arguments proj1_update2 {_ _ _ _ _ HI}.

Hint Rewrite @proj2_update1 using (typeclasses eauto) : lens.
Hint Rewrite @proj1_update2 using (typeclasses eauto) : lens.


(** *** Add [independent_symm] hint without loops. *)

CoInductive _independent_type1 {A X Y} (LX: Lens A X) (LY: Lens A Y) : Prop :=
  _independent_ctor1.

Ltac independent_symm_guard LX LY :=
  lazymatch goal with
  | [ _ : _independent_type1 LX LY |- _ ] => fail
  | _ => let iltt := fresh "iltt" in
        assert (iltt:=_independent_ctor1 LX LY)
  end.

Global Hint Extern 20 (Independent ?LX ?LY) =>
  independent_symm_guard LX LY;
  apply independent_symm : typeclass_instances.


(** *** Use [independent] rewrite except for [independent_symm] instances *)

Inductive _independent_type2 {A X Y} (LX: Lens A X) (LY: Lens A Y) : Prop :=
  _independent_ctor2 (HI: Independent LX LY) :
    _independent_type2 LX LY.

Arguments _independent_ctor2 {_ _ _} _ _ {_}.

Ltac rewrite_independent :=
  match goal with
    |- context [ @update _ _ ?LY (@update _ _ ?LX _ _) _ ] =>
    let indeq := fresh "indeq" in
    assert (indeq:=@eq_refl _ (_independent_ctor2 LX LY));
    lazymatch goal with
    | [ _ : _independent_ctor2 _ _ (HI := (let _ := _ in independent_symm _)) = _ |- _ ] =>
      fail
    | [ _ : _independent_ctor2 _ _ (HI := ?HI) = _ |- _ ] =>
      clear indeq;
      setoid_rewrite (@independent _ _ LX _ LY HI)
    end
  end.


(** *** Rewrite tactics *)

Ltac lens_rewrite1 := rewrite_strat (outermost (hints lens))
                      || rewrite_independent.
Ltac lens_rewrite := repeat lens_rewrite1; try reflexivity.


(** ** Lens cateogory *)

Section lens_category_section.

  Context {A: Type}.

  (** Since "unit" shorter than "terminal". *)
  #[refine] Instance unitLens : Lens A unit :=
  {
    proj _ := tt;
    update a _ := a;
  }.
  Proof.
    - intros _ []. reflexivity.
    - reflexivity.
    - reflexivity.
  Defined.

  Program Instance idLens : Lens A A :=
  {
    proj a := a;
    update a x := x;
  }.

  Context {X Y} (LY: Lens X Y) (LX: Lens A X).

  #[refine] Instance compositeLens : Lens A Y :=
  {
    proj := proj ∘ proj;
    update a := update a ∘ update (proj a);
  }.
  Proof.
    all: abstract (unfold compose; intros; lens_rewrite).
  Defined.

  (** Clearly this defined a category up to extensionality. *)

End lens_category_section.

Infix "∘" := compositeLens (at level 40, left associativity) : lens_scope.

Section composite_independent_section.

  Context {A X Y Y'} (LX: Lens A X) (LY: Lens X Y) (LY': Lens X Y')
          {HI: Independent LY LY'}.

  Instance composite_independent : Independent (LY ∘ LX) (LY' ∘ LX).
  Proof.
    intros a y y'. cbn.
    unfold compose. lens_rewrite.
  Qed.

End composite_independent_section.


(** ** Lens equality *)

Section equality_section.

  Local Arguments proj {_ _} _ _.
  Local Arguments update {_ _} _ _ _.

  Context {A X : Type}.

  Section eq_section.

    Context (L1: Lens A X) (L2: Lens A X).


    (** This is equivalent to "L1 = L2" if/when we assume extensionality,
        see LensExtras.v. *)
    Definition lens_eq : Prop :=
      forall a x, update L1 a x = update L2 a x.

    Proposition proj_eq (H: lens_eq) : forall a, proj L1 a = proj L2 a.
    Proof.
      intros a.
      setoid_rewrite <- (update_proj (Lens:=L2)) at 1.
      rewrite <- H.
      apply proj_update.
    Qed.

  End eq_section.

  Global Instance proj_eq_equivalence : Equivalence lens_eq.
  Proof.
    split.
    - intros LX a x. reflexivity.
    - intros L1 L2 H12 a x. rewrite H12. reflexivity.
    - intros L1 L2 L3 H12 H23 a x.
      transitivity (update L2 a x).
      + apply H12.
      + apply H23.
  Qed.

End equality_section.

(* TODO: Define notation scope. *)
Notation "L1 ≅ L2" := (lens_eq L1 L2) (at level 70, no associativity).


(** ** Covers

I don't know if this has an established name. *)

Section cover_section.

  Local Arguments proj {_ _} _ _.
  Local Arguments update {_ _} _ _ _.

  Context {A X Y} (LX: Lens A X) (LY: Lens A Y).

  Class Cover : Prop :=
    cover : exists (c: Lens X Y), LY ≅ c ∘ LX.

End cover_section.

Arguments cover {_ _ _ _ _} _.

Notation "( L2 | L1 )" := (Cover L1 L2) : type_scope.

(** By definition *)
Instance compositionCover {A X Y} (LX: Lens A X) (LY: Lens X Y) :
  (LY ∘ LX | LX).
Proof. exists LY. reflexivity. Qed.


Section cover_ordering_section.

  Context {A X} (LX: Lens A X).

  Instance idCover : (LX | LX).
  Proof.
    exists idLens.
    reflexivity.

 := { cover := idLens; }.


  Context {Y} {LY: Lens A Y} (CXY: Cover LX LY)
          {Z} {LZ: Lens A Z} (CYZ: Cover LY LZ).

  #[refine] Instance compositeCover : Cover LX LZ := { cover := cover CYZ ∘ cover CXY }.
  Proof.
    intros a y.
    cbn.
    rewrite
      (cover_update CYZ),
      (cover_update CXY),
      (cover_proj CXY).
    reflexivity.
  Qed.

End cover_ordering_section.

Arguments compositeCover {_ _ LX _ _} CXY {_ _} CYZ.


(** ** Products and projections *)

Section projection_section.

  Context {X Y: Type}.

  Program Instance lens_fst : Lens (X * Y) X :=
  {
    proj := fst;
    update s x := (x, snd s);
  }.

  Program Instance lens_snd : Lens (X * Y) Y :=
  {
    proj := snd;
    update s y := (fst s, y);
  }.

  Program Instance independent_projs : Independent lens_fst lens_snd.

  Context {A} (LX: Lens A X) (LY: Lens A Y) {IXY: Independent LX LY}.

  #[refine]
  Instance prodLens : Lens A (X * Y) :=
  {
    proj a := (proj a, proj a);
    update a xy := update (update a (fst xy)) (snd xy);
  }.
  Proof.
    all: idestructs; repeat (lens_rewrite || simpl).
  Defined.

  (* TODO: Can we do these two propositions? *)
  Proposition prod_proj_spec (a: A) : proj a = (proj a, proj a).
  Proof. reflexivity. Qed.

  Proposition prod_update_spec (a: A) (xy: X * Y) : update a xy = update (update a (fst xy)) (snd xy).
  Proof. reflexivity. Qed.

  #[refine] Global Instance prod_cover1 : Cover prodLens LX := { cover := lens_fst; }.
  Proof.
    intros a x. cbn. lens_rewrite.
  Qed.

  #[refine] Global Instance prod_cover2 : Cover prodLens LY := { cover := lens_snd; }.
  Proof.
    intros a y. cbn. lens_rewrite.
  Qed.

  Context {X'} (LX': Lens A X') {HC: Cover LX LX'}.

  (** A loop-safe corollary. *)
  Global Instance prod_cover1' : Cover prodLens LX'.
  Proof.
    apply (compositeCover prod_cover1 HC).
  Qed.

  Context Z (LZ: Lens A Z) (IXZ: Independent LX LZ) (IYZ: Independent LY LZ).

  Global Instance independent_prod : Independent prodLens LZ.
  Proof.
    intros s [x y] z. simpl. lens_rewrite.
  Qed.

End projection_section.

(** The projections from a record type have the same property, cf. MachineExtras.v. *)

Infix "*" := prodLens : lens_scope.


(** *** Restriction lenses *)

Import DSetNotations.

Section restriction_section.

  Context {A : Type} {F : A -> Type}.

  Definition restr u : Type := forall (a: A), a ∈ u -> F a.

  #[refine] Instance unrestrLens : Lens (forall a, F a) (restr Ω) :=
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

  Instance restrLens u : Lens (forall a, F a) (restr u) :=
    subsetLens univ_terminal ∘ unrestrLens.

  (** By construction *)
  #[refine] Instance unrestr_cover u : Cover unrestrLens (restrLens u) :=
  {
    cover := subsetLens univ_terminal;
  }.
  Proof.
    reflexivity.
  Qed.

  #[refine] Instance subset_cover {u v} (Huv: u ⊆ v) :
    Cover (restrLens v) (restrLens u) :=
  {
    cover := subsetLens Huv;
  }.
  Proof.
    intros f g. extensionality a. cbn.
    destruct (decide (a ∈ u)) as [Hu|Hu];
      destruct (decide (a ∈ v)) as [Hv|Hv];
      try reflexivity.
    exfalso.
    apply Hv, Huv, Hu.
  Qed.

  (** I.e. [subsetLength] respects the transitivity of [⊆]. *)

  Instance separate_independent u v (Huv: u # v) :
    Independent (restrLens u) (restrLens v).
  Proof.
    intros f g h.
    extensionality a.
    cbn.
    destruct (decide (a ∈ v)) as [Hv|Hv];
      destruct (decide (a ∈ u)) as [Hu|Hu];
      try reflexivity.
    exfalso.
    apply (Huv a).
    split; assumption.
  Qed.

End restriction_section.


(** ** Point lenses *)

Section point_section.

  Context {A : Type}
          {F : A -> Type}
          {H_eqdec: EqDec A}
          (a: A).

  #[refine] Instance pointLens' {u} (Ha: a ∈ u) : Lens (restr u) (F a) :=
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

  Instance pointLens : Lens (forall a', F a') (F a) :=
    pointLens' univ_spec ∘ unrestrLens.

  #[refine] Instance pointLens_cover {u} (Ha: a ∈ u) : Cover (restrLens u) pointLens :=
  {
    cover := pointLens' Ha
  }.
  Proof.
    intros f x. extensionality a'. cbn.
    destruct (decide (a = a')) as [H|H].
    - subst a. decided Ha. reflexivity.
    - destruct (decide _); reflexivity.
  Qed.

End point_section.
