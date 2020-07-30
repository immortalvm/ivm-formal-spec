From Assembly Require Import Init.

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


(** ** Unit and false lenses

Instances placed in a section to avoid confusing [typeclasses eauto].
Are these observations ever useful? *)

Section unit_and_false_section.

  #[refine] Instance lens_unit {A} : Lens A unit :=
  {
    proj _ := tt;
    update a _ := a;
  }.
  Proof.
    all: intro a; repeat intros []; reflexivity.
  Defined.

  Program Instance independent_unit {A X} {LX: Lens A X} : Independent lens_unit LX.

  #[refine] Instance lens_false {X} : Lens False X :=
  {
    proj a := False_rect X a;
    update a x := a;
  }.
  Proof.
    all: intros [].
  Defined.

  Instance independent_False {X Y} {LY: Lens False Y} : Independent (@lens_false X) LY.
  Proof.
    split; intros [].
  Qed.

End unit_and_false_section.


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
  Instance prodlens : Lens A (X * Y) :=
  {
    proj a := (proj a, proj a);
    update a xy := update (update a (fst xy)) (snd xy);
  }.
  Proof.
    all: idestructs; repeat (lens_rewrite || simpl).
  Defined.

  Proposition prod_proj_spec (a: A) : proj a = (proj a, proj a).
  Proof. reflexivity. Qed.

  Proposition prod_update_spec (a: A) (xy: X * Y) : update a xy = update (update a (fst xy)) (snd xy).
  Proof. reflexivity. Qed.

  Context Z (LZ: Lens A Z) (IXZ: Independent LX LZ) (IYZ: Independent LY LZ).

  Global Instance independent_prod : Independent prodlens LZ.
  Proof.
    intros s [x y] z. simpl. lens_rewrite.
  Qed.

End projection_section.

(** The projections from a record type have the same property, cf. MachineExtras.v. *)

Infix "*" := prodlens : lens_scope.


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


(** ** Covers
    I don't know if this has an established name. *)

Local Arguments proj {_ _} _ _.
Local Arguments update {_ _} _ _ _.

(** This can be simplified if we assume extensionality, cf. LensExtras.v. *)
Proposition update_characterizes_proj
            {A X} (LX: Lens A X) (LX': Lens A X)
            (H: forall a x, update LX a x = update LX' a x) :
  forall a, proj LX a = proj LX' a.
Proof.
  intros a.
  setoid_rewrite <- (update_proj (Lens:=LX')) at 1.
  rewrite <- H.
  apply proj_update.
Qed.

Section cover_section.

  Context {A X Y} (LX: Lens A X) (LY: Lens A Y).

  Class Cover :=
  {
    cover : Lens X Y;
    cover_update a y : update LY a y = update LX a (update cover (proj LX a) y);
  }.

  Proposition cover_proj {HC: Cover} a : proj LY a = proj cover (proj LX a).
  Proof.
    transitivity (proj (cover ∘ LX) a).
    - apply update_characterizes_proj, HC.
    - reflexivity.
  Qed.

End cover_section.

Arguments cover {_ _ _ _ _} _.
Arguments cover_update {_ _ _ _ _} _.
Arguments cover_proj {_ _ _ _ _} _.

Section cover_category_section.

  Context {A X} (LX: Lens A X).

  Program Instance idCover : Cover LX LX := { cover := idLens; }.

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
  Defined.

End cover_category_section.

Arguments compositeCover {_ _ LX _ _} CXY {_ _} CYZ.

Section prod_cover_section.

  Context {A X Y} (LX: Lens A X) (LY: Lens A Y) {HI: Independent LX LY}.

  #[refine] Global Instance prod_cover1 : Cover (LX * LY) LX := { cover := lens_fst; }.
  Proof.
    intros a x. cbn. lens_rewrite.
  Defined.

  #[refine] Global Instance prod_cover2 : Cover (LX * LY) LY := { cover := lens_snd; }.
  Proof.
    intros a y. cbn. lens_rewrite.
  Defined.

  Context {X'} (LX': Lens A X') {HC: Cover LX LX'}.

  (** A loop-safe corollary. *)
  Global Instance prod_cover1' : Cover (LX * LY) LX'.
  Proof.
    apply (compositeCover prod_cover1 HC).
  Defined.

End prod_cover_section.
