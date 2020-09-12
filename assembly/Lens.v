From Assembly Require Export Mixer.

Unset Suggest Proof Using.

Ltac lens_rewrite0 := rewrite_strat (repeat (outermost (hints lens))).
Tactic Notation "lens_rewrite0" "in" hyp(H) :=
  rewrite_strat (repeat (outermost (hints lens))) in H.


(** * Lenses *)

Class Lens (A: Type) (X: Type) :=
{
  proj: A -> X;
  update: A -> X -> A;
  proj_update (a: A) (x: X) : proj (update a x) = x;
  update_proj (a: A) : update a (proj a) = a;
  update_update (a: A) (x: X) (x': X) : update (update a x) x' = update a x';
}.

Hint Rewrite @proj_update : lens.
Hint Rewrite @update_proj : lens.
Hint Rewrite @update_update : lens.

Bind Scope lens_scope with Lens.


(** ** Lens equality *)

Section equality_section.

  Arguments proj {_ _} _ _.
  Arguments update {_ _} _ _ _.

  Context {A X : Type}.

  (** Equivalent to "L = L'" if we assume extensionality and proof irrelevance. *)
  Definition lensEq (L L': Lens A X) :=
    forall a (x: X), update L a x = update L' a x.

  (** Useful to have as separate fact. *)
  Proposition lens_refl {Lx: Lens A X} : lensEq Lx Lx.
  Proof.
    intros a x. reflexivity.
  Qed.

  Global Instance lensEq_equivalence : Equivalence lensEq.
  Proof.
    split.
    - intro L1. exact lens_refl.
    - intros L1 L2 H12 a x. rewrite H12. reflexivity.
    - intros L1 L2 L3 H12 H23 a x.
      transitivity (update L2 a x).
      + apply H12.
      + apply H23.
  Qed.

  Global Instance update_proper :
    Proper (lensEq ==> eq ==> eq ==> eq) (@update A X).
  Proof.
    repeat intro. subst. intuition.
  Qed.

  Global Instance proj_proper :
    Proper (lensEq ==> eq ==> eq) (@proj A X).
  Proof.
    intros L L' Hl.
    repeat intro. subst.
    setoid_rewrite <- (update_proj (Lens:=L')) at 1.
    rewrite <- Hl.
    apply proj_update.
  Qed.

End equality_section.

Notation "L ≅ L'" := (lensEq L L') (at level 70, no associativity) : type_scope.


(** ** Lenses to mixers *)

#[refine] Instance compositeMixer {A X} (f: Mixer X) (L: Lens A X) : Mixer A :=
{
  mixer a a' := update a (f (proj a) (proj a'));
}.
Proof.
  all: intros; repeat (lens_rewrite0 || mixer_rewrite).
Defined.

Instance proper_compositeMixer {A X} :
  Proper (@mixerEq X ==> @lensEq A X ==> @mixerEq A) compositeMixer.
Proof.
  intros f f' Hf
         L L' Hl
         x y.
  cbn. rewrite Hf, Hl. reflexivity.
Qed.

Instance proper_compositeMixer_sub {A X} :
  Proper (@Submixer X ==> @lensEq A X ==> @Submixer A) compositeMixer.
Proof.
  intros f f' Hf
         L L' Hl
         x y z.
  cbn. rewrite Hl.
  repeat (lens_rewrite0 || mixer_rewrite).
Qed.

Instance lens2mixer {A X} (L: Lens A X) : Mixer A := compositeMixer sndMixer L.

Instance lens2mixer_proper {A X} : Proper (@lensEq A X ==> @mixerEq A) lens2mixer.
Proof.
  intros L L' Hl.
  unfold lens2mixer.
  rewrite Hl.
  reflexivity.
Qed.

Coercion lens2mixer : Lens >-> Mixer.


(** ** Independent lenses *)

(** This is a trivial consequence of [Mixer.independent_proper] and
[lens2mixer_proper]. I am not sure what it would take for [typeclasses
eauto] to solve such goals automatically.*)

(* Shadows [Mixer.independence_proper] *)
Instance independent_proper {A X Y : Type} :
  Proper (@lensEq A X ==> @lensEq A Y ==> iff) Independent.
Proof.
  intros ? ? Hx ? ? Hy.
  rewrite Hx, Hy.
  reflexivity.
Qed.

Section independence_section.

  Context {A X Y : Type}
          {Lx: Lens A X}
          {Ly: Lens A Y}.

  Instance independent_update
           (H: forall a (x: X) (y: Y), update (update a x) y = update (update a y) x) :
    Independent Lx Ly.
  Proof.
    intros a ax ay. cbn. rewrite H. reflexivity.
  Qed.

  Context {Hi: Independent Lx Ly}.

  (* Shadows [Mixer.independent] *)
  Proposition independent a (x: X) (y: Y):
    update (update a x) y = update (update a y) x.
  Proof.
    specialize (Hi a (update a x) (update a y)).
    cbn in Hi. lens_rewrite0 in Hi.
    symmetry. (* TODO: Swap order in Mixer to match? *)
    exact Hi.
  Qed.

  Proposition proj2_update1 (a: A) (x: X) : proj (update a x) = proj a :> Y.
  Proof.
    rewrite <- (@update_proj _ _ Ly a) at 1.
    rewrite <- independent.
    apply proj_update.
  Qed.

  Proposition proj1_update2 (a: A) (y: Y) : proj (update a y) = proj a :> X.
  Proof.
    rewrite <- (@update_proj _ _ Lx a) at 1.
    rewrite independent.
    apply proj_update.
  Qed.

End independence_section.

Hint Rewrite @proj2_update1 using (typeclasses eauto) : lens.
Hint Rewrite @proj1_update2 using (typeclasses eauto) : lens.
Hint Rewrite @independent using (typeclasses eauto) : lens.

(** *** Rewrite tactics *)

Ltac lens_rewrite1 := unfold compose;
                      lens_rewrite0
                      || mixer_rewrite1.
Ltac lens_rewrite := repeat lens_rewrite1;
                     try reflexivity.


(** ** Lens composition *)

Section category_section.

  Context {A: Type}.

  Program Instance idLens : Lens A A :=
  {
    proj a := a;
    update _ x := x;
  }.

  Proposition idLens_spec : idLens ≃ sndMixer.
  Proof.
    intros a a'. reflexivity.
  Qed.

  Context {X Y} (Ly: Lens X Y) (Lx: Lens A X).

  #[refine] Instance compositeLens : Lens A Y :=
  {
    proj := proj ∘ proj;
    update a := update a ∘ update (proj a);
  }.
  Proof.
    all: abstract (intros; lens_rewrite).
  Defined.

End category_section.

Infix "∘" := compositeLens (at level 40, left associativity) : lens_scope.

Section category_facts_section.

  Arguments proj {_ _} _ _.
  Arguments update {_ _} _ _ _.

  Context {A X Y : Type}.

  Instance compositeLens_proper :
    Proper (lensEq ==> lensEq ==> lensEq) (@compositeLens A X Y).
  Proof.
    intros Lx Lx' Hx
           Ly Ly' Hy
           a y.
    cbn.
    rewrite Hx.
    rewrite Hy.
    reflexivity.
  Qed.

  Proposition compositeLens_associative {Z}
        (Lx : Lens A X)
        (Ly : Lens X Y)
        (Lz : Lens Y Z) : Lz ∘ (Ly ∘ Lx) ≅ (Lz ∘ Ly) ∘ Lx.
  Proof.
    intros a z. reflexivity.
  Qed.

  Context (Lx: Lens A X).

  Proposition idLens_composite : idLens ∘ Lx ≅ Lx.
  Proof.
    intros a x. reflexivity.
  Qed.

  Proposition composite_idLens: Lx ∘ idLens ≅ Lx.
  Proof.
    intros a x. reflexivity.
  Qed.

  Global Instance composite_independent_r
           (Ly: Lens X Y) {Y'} (Ly': Lens X Y')
           {Hi: Independent Ly Ly'} : Independent (Ly ∘ Lx) (Ly' ∘ Lx).
  Proof.
    intros a y y'. cbn. lens_rewrite.
  Qed.

  Global Instance composite_independent_l
         (Ly: Lens A Y) {Hi: Independent Lx Ly}
         {Z} (Lz: Lens X Z) : Independent (Lz ∘ Lx) Ly.
  Proof.
    intros a z y. cbn. lens_rewrite.
  Qed.

  (** By symmetry, we also get [Independent Lx (Lz' ∘ Ly)]. *)

End category_facts_section.

(* TODO: Is this really necessary? *)
Arguments compositeLens_proper {_ _ _ _ _} Hlx {_ _} Hly.

Proposition composite_compositeMixer {X Y} (Ly: Lens X Y) {A} (Lx: Lens A X) :
  Ly ∘ Lx ≃ compositeMixer Ly Lx.
Proof.
  intros a a'. lens_rewrite.
Qed.


(** ** Sublenses *)

Section sublens_ordering_section.

  Context {A X} (Lx: Lens A X).

  Global Instance sublens_comp
         {Y} {Ly: Lens X Y}
         {Z} {Lz: Lens X Z}
         (Syz: (Ly | Lz)) : (Ly ∘ Lx | Lz ∘ Lx).
  Proof.
    setoid_rewrite composite_compositeMixer.
    apply proper_compositeMixer_sub.
    - exact Syz.
    - reflexivity.
  Qed.

  (** This is a corollary but even simpler to prove directly.
      Making this global may cause loops. Instead we use the
      restricted hint below. *)
  Instance sublens_comp' {Y} (Ly: Lens X Y) : (Ly ∘ Lx | Lx).
  Proof.
    intros a b c. cbn. lens_rewrite.
  Qed.

End sublens_ordering_section.

Hint Extern 2 (?Ly ∘ ?Lx | ?Lx) =>
  apply sublens_comp' : typeclass_instances.


(** ** Products and projections *)

Section projection_section.

  Context {A X Y: Type}.

  Program Instance fstLens : Lens (X * Y) X :=
  {
    proj := fst;
    update s x := (x, snd s);
  }.

  Program Instance sndLens : Lens (X * Y) Y :=
  {
    proj := snd;
    update s y := (fst s, y);
  }.

  Global Program Instance independent_projs : Independent fstLens sndLens.

  Context (Lx: Lens A X) (Ly: Lens A Y) {Hi: Independent Lx Ly}.

  #[refine] Global Instance prodLens : Lens A (X * Y) :=
  {
    proj a := (proj a, proj a);
    update a xy := update (update a (fst xy)) (snd xy);
  }.
  Proof.
    all: idestructs; repeat (lens_rewrite || simpl).
  Defined.

  Proposition prodLens_prodMixer : prodLens ≃ Lx × Ly.
  Proof.
    intros a a'. cbn. lens_rewrite.
  Qed.

End projection_section.

Infix "*" := prodLens : lens_scope.

Hint Extern 5 => setoid_rewrite prodLens_prodMixer : typeclass_instances.

Goal forall {A X Y: Type} (Lx: Lens A X) (Ly: Lens A Y) {Hi: Independent Lx Ly},
    (Lx | Lx * Ly).
Proof.
  typeclasses eauto.
Qed.

(** Cf. [prodMixer_proper]. *)
Lemma prodLens_proper {A X Y}
      {Lx Lx' : Lens A X} (Hx: Lx ≅ Lx')
      {Ly Ly' : Lens A Y} (Hy: Ly ≅ Ly')
      {Hi: Independent Lx Ly}
      {Hi': Independent Lx' Ly'} : (* Follows from [Hi] *)
  Lx * Ly ≅ Lx' * Ly'.
Proof.
  intros a [x y]. cbn.
  rewrite Hx, Hy. reflexivity.
Qed.
