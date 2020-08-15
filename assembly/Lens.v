From Assembly Require Import Init DSet.

Unset Suggest Proof Using.

Declare Scope lens_scope.
Delimit Scope lens_scope with lens.

Ltac lens_rewrite0 := rewrite_strat (repeat (outermost (hints lens))).
Tactic Notation "lens_rewrite0" "in" hyp(H) :=
  rewrite_strat (repeat (outermost (hints lens))) in H.


(** * Pseudo-lenses

[Lens'] represents lenses with the target type abstracted away.
I don't know if this has an established name. *)

Class Lens' A :=
{
  mix: A -> A -> A;
  mix_id a : mix a a = a;
  mix_left a b c : mix (mix a b) c = mix a c;
  mix_right a b c : mix a (mix b c) = mix a c;
}.

Hint Rewrite @mix_id : lens.
Hint Rewrite @mix_left : lens.
Hint Rewrite @mix_right : lens.

Bind Scope lens_scope with Lens'.
Arguments mix {_} _ _ _.


(** ** Preudo-lens equality *)

Section equality_section.

  Context {A : Type}.

  (** Equivalent to "L = L'" if we assume extensionality and proof irrelevance. *)
  Definition lensEq' (L L': Lens' A) : Prop :=
    forall a b, mix L a b = mix L' a b.

  (** Useful to have as separate fact. *)
  Proposition lens_refl' {L: Lens' A} : lensEq' L L.
  Proof.
    intros a x. reflexivity.
  Qed.

  Global Instance lensEq_equivalence' : Equivalence lensEq'.
  Proof.
    split.
    - intro L1. exact lens_refl'.
    - intros L1 L2 H12 a x. rewrite H12. reflexivity.
    - intros L1 L2 L3 H12 H23 a a'.
      transitivity (mix L2 a a').
      + apply H12.
      + apply H23.
  Qed.

  Instance mix_proper :
    Proper (lensEq' ==> eq ==> eq ==> eq) (@mix A).
  Proof.
    repeat intro.
    repeat subst.
    intuition.
  Qed.

End equality_section.

Notation "L ≃ L'" := (lensEq' L L') (at level 70, no associativity) : type_scope.


(** ** Sub(pseudo)lenses *)

Set Typeclasses Unique Instances.

Class Sublens {A} (L L': Lens' A) : Prop :=
  sublens a b c : mix L (mix L' a b) c = mix L' a (mix L b c).

Unset Typeclasses Unique Instances.

Notation "( L | L' )" := (Sublens L L') : type_scope.

(* TODO: Is it safe to add [sublens] as a rewrite hint? *)

Instance sublens_proper {A} :
  Proper (@lensEq' A ==> @lensEq' A ==> iff) Sublens.
Proof.
  intros L1 L1' H1 L2 L2' H2.
  split; intros H a b c.
  - repeat rewrite <- H1. repeat rewrite <- H2. rewrite sublens. reflexivity.
  - repeat rewrite H1. repeat rewrite H2. rewrite sublens. reflexivity.
Qed.

Instance sublens_reflexive {A} : Reflexive (@Sublens A).
Proof.
  intros L a b c.
  rewrite mix_left, mix_right.
  reflexivity.
Qed.

Proposition sublens_left {A} {L L': Lens' A} {Hs: (L|L')} a b c :
  mix L' (mix L a b) c = mix L' a c.
Proof.
  transitivity (mix L' (mix L' a (mix L a b)) c).
  - rewrite <- sublens, mix_id. reflexivity.
  - rewrite mix_left. reflexivity.
Qed.

Corollary sublens_left' {A} {L L': Lens' A} {Hs: (L|L')} a b :
  mix L' (mix L a b) a = a.
Proof.
  rewrite sublens_left. apply mix_id.
Qed.

Proposition sublens_right {A} {L L': Lens' A} {Hs: (L|L')} a b c :
  mix L a (mix L' b c) = mix L a c.
Proof.
  transitivity (mix L a (mix L (mix L' b c) c)).
  - rewrite sublens, mix_id. reflexivity.
  - rewrite mix_right. reflexivity.
Qed.

Corollary sublens_right' {A} {L L': Lens' A} {Hs: (L|L')} a b :
  mix L a (mix L' b a) = a.
Proof.
  rewrite sublens_right.
  apply mix_id.
Qed.

Lemma sublens_antisymm {A} {L L': Lens' A} (S: (L|L')) (S': (L'|L)) : L ≃ L'.
Proof.
  intros a a'.
  transitivity (mix L' (mix L a a') (mix L a a')).
  - rewrite mix_id; reflexivity.
  - rewrite sublens_left, sublens_right. reflexivity.
Qed.

Instance sublens_transitive {A} : Transitive (@Sublens A).
Proof.
  intros Lx Ly Lz Hxy Hyz a b c.
  transitivity (mix Lx (mix Ly (mix Lz a b) (mix Lz a b)) c).
  - rewrite mix_id. reflexivity.
  - rewrite Hxy.
    rewrite Hyz.
    rewrite <- Hxy.
    rewrite sublens_right'.
    reflexivity.
Qed.

(* TODO: Is this useful? *)
Instance eq_sublens_subrelation {A} : subrelation (@lensEq' A) (@Sublens A).
Proof.
  intros L L' H.
  rewrite H.
  reflexivity.
Qed.


(** ** Independent pseudo-lenses *)

Set Typeclasses Unique Instances.

Class Independent {A} (L1 L2: Lens' A) : Prop :=
  independent' a a1 a2 : mix L2 (mix L1 a a1) a2 =
                         mix L1 (mix L2 a a2) a1.

Unset Typeclasses Unique Instances.

(** Not declared an instance to avoid loops. *)
Proposition independent_symm {A} (L L': Lens' A) : Independent L L' <-> Independent L' L.
Proof.
  split; intros H a a1 a2; symmetry; apply H.
Qed.


(** *** Add symmetry hint while avoiding loops. *)

Local Corollary independent_symm_imp {A} (L L': Lens' A) : Independent L L' -> Independent L' L.
Proof.
  apply independent_symm.
Qed.

CoInductive _independent_type1 {A} (L: Lens' A) (L': Lens' A) : Prop :=
  _independent_ctor1.

Ltac independent_symm_guard L L' :=
  lazymatch goal with
  | [ _ : _independent_type1 L L' |- _ ] => fail
  | _ => let iltt := fresh "iltt" in
        assert (iltt:=_independent_ctor1 L L')
  end.

Global Hint Extern 20 (Independent ?L ?L') =>
  independent_symm_guard L L';
  apply independent_symm_imp : typeclass_instances.

(** **** Tests *)

Goal forall {A} (L L': Lens' A) (H: Independent L L'), Independent L' L.
  (* Symmetry found *)
  typeclasses eauto.
Qed.

Goal forall {A} (L L': Lens' A), Independent L L'.
  (* Loop avoided. *)
  assert_fails (typeclasses eauto).
Abort.


(** *** Use [independent'] rewrite in one direction only *)

Inductive _independent_type2 {A} (L: Lens' A) (L': Lens' A) : Prop :=
  _independent_ctor2 (Hi: Independent L L') :
    _independent_type2 L L'.

Arguments _independent_ctor2 {_} _ _ {_}.

(* TODO: Not very elegant (see also [rewrite_independent] below) *)
Ltac rewrite_independent' :=
  match goal with
    |- context [ @mix _ ?L' (@mix _ ?L _ _) _ ] =>
    let indeq := fresh "indeq" in
    assert (indeq:=@eq_refl _ (_independent_ctor2 L L'));
    lazymatch goal with
    | [ _ : _independent_ctor2 _ _ (Hi := (let _ := _ in @independent_symm_imp _ _ _ _)) = _ |- _ ] =>
      fail
    | [ _ : _independent_ctor2 _ _ (Hi := ?Hi) = _ |- _ ] =>
      clear indeq;
      setoid_rewrite (@independent' _ L L' Hi)
    end
  end.

(** [Rewrite_independent'] only works if the lenses are not bound variables.
    This restriction can probably be avoided, but it does not matter to us. *)

(** **** Test *)

Goal forall {A} (L L': Lens' A) (H: Independent L L') a x y, mix L (mix L' a y) x = mix L' (mix L a x) y.
  intros.
  (* Rewrites once, but not twice (back to the original). *)
  progress rewrite_independent'.
  assert_fails (progress rewrite_independent').
  reflexivity.
Qed.


(** ** [Independent] is proper *)

Section scope_section.

  (* TODO: Is this a good idea in general? *)
  Coercion mix : Lens' >-> Funclass.

  Instance independent_proper_sub0 {A} {f: Lens' A} :
    Proper (@Sublens A ==> flip impl) (Independent f).
  Proof.
    intros g g' Hg
           H a x y.
    rewrite <- (mix_id (Lens':=g') a) at 2.
    rewrite Hg.
    rewrite <- H.
    rewrite <- Hg.
    rewrite H.
    rewrite mix_id.
    reflexivity.
  Qed.

  Global Instance independent_proper_sub {A} :
    Proper (@Sublens A ==> @Sublens A ==> flip impl) (@Independent A).
  Proof.
    intros f f' Hf
           g g' Hg.
    rewrite Hg. setoid_rewrite independent_symm.
    rewrite Hf. reflexivity.
  Qed.

End scope_section.

Instance independent_proper' {A} :
  Proper (@lensEq' A ==> @lensEq' A ==> iff) (@Independent A).
Proof.
  (* The direct proof is much longer. *)
  intros L1 L1' H1
         L2 L2' H2.
  split; intro H.
  - rewrite <- H1, <- H2. exact H.
  - rewrite H1, H2. exact H.
Qed.


(** * Acutal lenses *)

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


(** ** Lenses to pseudo-lenses *)

#[refine] Instance Lens2Lens' {A X} (Lx: Lens A X) : Lens' A :=
{
  mix a b := update a (proj b);
}.
Proof.
  all:
    (rewrite_strat (repeat (outermost (hints lens))));
    reflexivity.
Defined.

Instance lens2lens_proper {A X} :
  Proper (lensEq ==> lensEq') (@Lens2Lens' A X).
Proof.
  intros L L' Hl a a'.
  cbn. rewrite Hl. reflexivity.
Qed.

Coercion Lens2Lens' : Lens >-> Lens'.


(** ** Independent lenses *)

Instance independent_proper {A X Y : Type} :
  Proper (@lensEq A X ==> @lensEq A Y ==> iff) (fun Lx Ly => Independent Lx Ly).
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

  Context (Hi: Independent Lx Ly).

  Proposition independent a (x: X) (y: Y):
    update (update a x) y = update (update a y) x.
  Proof.
    specialize (Hi a (update a x) (update a y)).
    cbn in Hi. lens_rewrite0  in Hi.
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

Arguments proj2_update1 {_ _ _ _ _ Hi}.
Arguments proj1_update2 {_ _ _ _ _ Hi}.

Hint Rewrite @proj2_update1 using (typeclasses eauto) : lens.
Hint Rewrite @proj1_update2 using (typeclasses eauto) : lens.


(** *** Use [independent] in one direction only, cf. [rewrite_independent'] *)

Ltac rewrite_independent :=
  match goal with
    |- context [ @update _ _ ?Ly (@update _ _ ?Lx _ _) _ ] =>
    let indeq := fresh "indeq" in
    assert (indeq:=@eq_refl _ (_independent_ctor2 Lx Ly));
    lazymatch goal with
    | [ _ : _independent_ctor2 _ _ (Hi := (let _ := _ in @independent_symm_imp _ _ _ _)) = _ |- _ ] =>
      fail
    | [ _ : _independent_ctor2 _ _ (Hi := ?Hi) = _ |- _ ] =>
      clear indeq;
      setoid_rewrite (@independent _ _ _ Lx Ly Hi)
    end
  end.

(** **** Test *)

Goal forall {A X Y} (L: Lens A X) (L':Lens A Y) (H: Independent L L')
       a (x:X) (y:Y), update (update a x) y = update (update a y) x.
  intros.
  (* Rewrites once, but not twice (back to the original). *)
  progress rewrite_independent.
  assert_fails (progress rewrite_independent).
  reflexivity.
Qed.


(** *** Rewrite tactics *)

Ltac lens_rewrite1 := unfold compose;
                      lens_rewrite0
                      || rewrite_independent
                      || rewrite_independent'.
Ltac lens_rewrite := repeat lens_rewrite1;
                     try reflexivity.


(** ** Lens category *)

Section category_section.

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

  (* TODO: Useful? *)
  Proposition idLens_composite : idLens ∘ Lx ≅ Lx.
  Proof.
    intros a x. reflexivity.
  Qed.

  (* TODO: Useful? *)
  Proposition composite_idLens: Lx ∘ idLens ≅ Lx.
  Proof.
    intros a x. reflexivity.
  Qed.

  (** Independent lenses are stable under prefixing. *)

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

End category_facts_section.

Arguments compositeLens_proper {_ _ _ _ _} Hlx {_ _} Hly.


(** ** Pseudo-lens composition *)

#[refine] Instance compositeLens' {X A} (L: Lens' X) (Lab: Lens A X) : Lens' A :=
{
  mix a a' := update a (mix L (proj a) (proj a'));
}.
Proof.
  all: lens_rewrite.
Defined.

Proposition composite_compositeLens' {X Y} (Ly: Lens X Y) {A} (Lx: Lens A X) :
  Ly ∘ Lx ≃ compositeLens' Ly Lx.
Proof.
  intros a a'.
  lens_rewrite.
Qed.

Instance proper_compositeLens' {A X} :
  Proper (@lensEq' X ==> @lensEq A X ==> @lensEq' A) compositeLens'.
Proof.
  intros L1 L1' H1
         L2 L2' H2
         a a'.
  cbn. rewrite H1, H2. reflexivity.
Qed.

Instance proper_compositeLens'_sub {A X} :
  Proper (@Sublens X ==> @lensEq A X ==> @Sublens A) compositeLens'.
Proof.
  intros L1 L1' H1
         L2 L2' H2
         a a1 a2.
  cbn. rewrite H2. lens_rewrite.
  rewrite H1. reflexivity.
Qed.

Section sublens_ordering_section.

  Context {A X} (Lx: Lens A X).

  Instance sublens_comp {Y} (Ly: Lens X Y) : (Ly ∘ Lx | Lx).
  Proof.
    intros a b c. cbn. lens_rewrite.
  Qed.

  Global Instance sublens_comp'
         {Y} {Ly: Lens X Y}
         {Z} {Lz: Lens X Z}
         (Syz: (Ly | Lz)) : (Ly ∘ Lx | Lz ∘ Lx).
  Proof.
    setoid_rewrite composite_compositeLens'.
    apply proper_compositeLens'_sub.
    - exact Syz.
    - reflexivity.
  Qed.

End sublens_ordering_section.


(** ** Products and projections *)

Section projection_section.

  Context {A X Y: Type}.

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

  Global Program Instance independent_projs : Independent lens_fst lens_snd.

  Context (Lx: Lens A X) (Ly: Lens A Y) {Hi: Independent Lx Ly}.

  #[refine]
  Instance prodLens : Lens A (X * Y) :=
  {
    proj a := (proj a, proj a);
    update a xy := update (update a (fst xy)) (snd xy);
  }.
  Proof.
    all: idestructs; repeat (lens_rewrite || simpl).
  Defined.

  Global Instance prod_sublens1 : (Lx | prodLens).
  Proof.
    intros a b. cbn. lens_rewrite.
  Qed.

  Global Instance prod_sublens2 : (Ly | prodLens).
  Proof.
    intros a b. cbn. lens_rewrite.
  Qed.

  (** Loop-safe corollary
      TODO: Still needed? *)
  Global Instance prod_sublens1'
         (Lx': Lens' A) {Sx: (Lx' | Lx)} : (Lx' | prodLens).
  Proof.
    transitivity Lx.
    - exact Sx.
    - exact prod_sublens1.
  Qed.

  Global Instance independent_prod
         {Z} {Lz: Lens A Z}
         (Ixz: Independent Lx Lz)
         (Iyz: Independent Ly Lz) : Independent prodLens Lz.
  Proof.
    intros a b c. cbn. lens_rewrite.
  Qed.

End projection_section.

(** The projections from a record type have the same property, cf. MachineExtras.v. *)

Infix "*" := prodLens : lens_scope.

Section flip_section.

  Context {A X Y} (Lx: Lens A X) (Ly: Lens A Y) {Hi: Independent Lx Ly}.

  (** TODO: Will this cause loops? *)
  Instance prod_sublens_symm : (Lx * Ly | Ly * Lx).
  Proof.
    intros a b. cbn. lens_rewrite.
  Qed.

  Context {X'} (Lx': Lens A X') {Sx: (Lx'|Lx)}.

  (* TODO: Still needed? *)
  (* Beware: This may cause loops. *)
  Instance independent_sublens1 : Independent Lx' Ly.
  Proof.
    rewrite Sx. exact Hi.
  Qed.


(************** Continue from here ***************)


  (* TODO: Think of a better name (similarly for the symmetric case below. *)
  Global Instance prod_sublens11 : (Lx' * Ly | Lx * Ly).
  Proof.
    destruct Sx as [L H].
    cbn in L.
    exists ((L∘lens_fst) * lens_snd)%lens.
    intros a xy'.
    cbn. rewrite H. lens_rewrite.
  Qed.

  Context {Y'} (Ly': Lens A Y') {Sy: (Ly'|Ly)}.

  (* Beware: This may cause loops. *)
  Instance independent_sublens2 : Independent Lx Ly'.
  Proof.
    intros a x y'.
    destruct Sy as [L H].
    rewrite H.
    lens_rewrite.
  Qed.

  Global Instance prod_sublens22 : (Lx * Ly' | Lx * Ly).
  Proof.
    destruct Sy as [L H].
    cbn in L.
    exists (lens_fst * (L∘lens_snd))%lens.
    intros a xy'.
    cbn. rewrite H. lens_rewrite.
  Qed.

End flip_section.

(* TODO: Are there more elegant ways to do this? *)
Lemma prodLens_proper {A X Y}
      {LX LX' : Lens A X} (Hx: LX ≅ LX')
      {LY LY' : Lens A Y} (Hy: LY ≅ LY')
      {Hi: Independent LX LY} :
  LX * LY ≅ prodLens _ _ (Hi:=proj1 (independent_proper _ _ Hx _ _ Hy) Hi).
Proof.
  intros a [x y]. cbn.
  rewrite Hx, Hy. reflexivity.
Qed.


(** *** Restriction lenses *)

Import DSetNotations.

Section restriction_section.

  Context {A : Type} {F : A -> Type}.

  Definition restr u : Type := forall (a: A), a ∈ u -> F a.

  #[refine] Instance fullLens : Lens (forall a, F a) (restr Ω) :=
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
    subsetLens full_terminal ∘ fullLens.

  (** By construction *)
  Instance full_sublens u : (restrLens u | fullLens).
  Proof.
    apply sublens_comp.
  Qed.

  (** [restrLens] is essentially "proper", i.e. respects [⊆]. *)
  Instance subsetSublens {u v} (Huv: u ⊆ v) : (restrLens u | restrLens v).
  Proof.
    exists (subsetLens Huv).
    intros f g. extensionality a. cbn.
    destruct (decide (a ∈ u)) as [Hu|Hu];
      destruct (decide (a ∈ v)) as [Hv|Hv];
      try reflexivity.
    exfalso.
    apply Hv, Huv, Hu.
  Qed.

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


(** ** Point lenses

[restrLens {a}] can be simplified. *)

Section point_section.

  Context {A : Type}
          {F : A -> Type}
          {H_eqdec: EqDec A}.

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

  Instance pointLens a : Lens (forall a', F a') (F a) := pointLens' full_spec ∘ fullLens.

  Instance pointLens_sublens {a u} (Ha: a ∈ u) : (pointLens a | restrLens u).
  Proof.
    exists (pointLens' Ha).
    intros f x. extensionality a'. cbn.
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

End point_section.
