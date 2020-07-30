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

Create HintDb proj discriminated.
Hint Rewrite @proj_update : proj.
Hint Rewrite @update_proj : proj.
Hint Rewrite @update_update : proj.
Ltac lens_rewrite1 := rewrite_strat (outermost (hints proj)).
Ltac lens_rewrite := repeat lens_rewrite1.


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

  (** I have not found a way to make this global with causing loops. *)
  Instance independent_symm : Independent LY LX.
  Proof.
    intros a y x.
    symmetry.
    apply independent.
  Qed.

End independence_section.

Arguments proj2_update1 {_ _ _ _ _ HI}.
Arguments proj1_update2 {_ _ _ _ _ HI}.

Create HintDb independent discriminated.
Hint Rewrite @proj2_update1 using (typeclasses eauto) : independent.
Hint Rewrite @proj1_update2 using (typeclasses eauto) : independent.
(** Beware: The rewrite order is somewhat arbitrary. *)
Hint Rewrite @independent using (typeclasses eauto) : independent.
Ltac independent_rewrite1 := rewrite_strat (outermost (hints independent)).
Ltac independent_rewrite := repeat independent_rewrite1.


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
    all: idestructs; now repeat (independent_rewrite1 || lens_rewrite || simpl).
  Defined.

  Proposition prod_proj_spec (a: A) : proj a = (proj a, proj a).
  Proof. reflexivity. Qed.

  Proposition prod_update_spec (a: A) (xy: X * Y) : update a xy = update (update a (fst xy)) (snd xy).
  Proof. reflexivity. Qed.

  Context Z (LZ: Lens A Z) (IXZ: Independent LX LZ) (IYZ: Independent LY LZ).

  Global Instance independent_prod : Independent prodlens LZ.
  Proof.
    intros s [x y] z. simpl. now independent_rewrite.
  Qed.

End projection_section.

(** The projections from a record type have the same property, cf. MachineExtras.v. *)

Infix "*" := prodlens : lens_scope.


(** ** Lens monoid

This is not something we actually use.
TODO: Remove? *)

Section lens_monoid_section.

  (** [id] is a bijection and therefore a lens. *)

  Context {A X Y} (LY: Lens X Y) (LX: Lens A X).

  #[refine] Instance composeLenses : Lens A Y :=
  {
    proj a := proj (proj a);
    update a y := update a (update (proj a) y);
  }.
  Proof.
    all: abstract (intros; lens_rewrite; reflexivity).
  Defined.

  (** This is clearly a monoid up to funcitonal extensionality. *)

End lens_monoid_section.

Infix "∘" := composeLenses (at level 40, left associativity) : lens_scope.


(** ** Various *)

Local Arguments proj {_ _} _ _.
Local Arguments update {_ _} _ _ _.

Section characterization_section.

  Context {A X} (LX: Lens A X) (LX': Lens A X).

  Proposition update_characterizes_proj
              (H: forall a x, update LX a x = update LX' a x) a :
    proj LX a = proj LX' a.
  Proof.
    setoid_rewrite <- (update_proj (Lens:=LX')) at 1.
    rewrite <- H.
    apply proj_update.
  Qed.

  (** This can be simplified if we assume functional extensionality. *)

  Proposition update_characterizes_proj'
              (H: update LX = update LX') : proj LX = proj LX'.
  Proof.
    extensionality a.
    apply update_characterizes_proj.
    rewrite H.
    reflexivity.
  Qed.

End characterization_section.

Section cover_section.

  Context {A X Y} (LX: Lens A X) (LY: Lens A Y).

  Class Cover :=
  {
    cover: Lens X Y;
    cover_update a y: update LY a y = update LX a (update cover (proj LX a) y);
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

Section prod_cover_section.

  Context {A X Y} (LX: Lens A X) (LY: Lens A Y) (HI: Independent LX LY).

  #[refine] Global Instance prod_cover1 : Cover (LX * LY) LX := { cover := lens_fst; }.
  Proof.
    intros a x. cbn.
    repeat (lens_rewrite1 || independent_rewrite1).
    reflexivity.
  Defined.

  #[refine] Global Instance prod_cover2 : Cover (LX * LY) LY := { cover := lens_snd; }.
  Proof.
    intros a y. cbn.
    repeat (lens_rewrite1 || independent_rewrite1).
    reflexivity.
  Defined.

End prod_cover_section.
