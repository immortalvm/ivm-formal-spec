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

Hint Rewrite @proj_update : lens.
Hint Rewrite @update_proj : lens.
Hint Rewrite @update_update : lens.

Declare Scope lens_scope.
Bind Scope lens_scope with Lens.
Delimit Scope lens_scope with lens.

(** This applies to the remaining class declarations in this file,
    i.e. [Independent] and [Sublens]. *)
Set Typeclasses Unique Instances.


(** ** Independent lenses *)

Class Independent {A X Y: Type}
      (Lx: Lens A X) (Ly: Lens A Y) : Prop :=
  independent (a: A) (x: X) (y: Y) :
    update (update a x) y = update (update a y) x.

Section independence_section.

  Context {A X Y : Type}
          {Lx: Lens A X} {Ly: Lens A Y}
          (Hi: Independent Lx Ly).

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

  (** Beware: This may cause loops. *)
  Instance independent_symm : Independent Ly Lx.
  Proof. intros a y x. symmetry. apply independent. Qed.

End independence_section.

Arguments proj2_update1 {_ _ _ _ _ Hi}.
Arguments proj1_update2 {_ _ _ _ _ Hi}.

Hint Rewrite @proj2_update1 using (typeclasses eauto) : lens.
Hint Rewrite @proj1_update2 using (typeclasses eauto) : lens.


(** *** Add [independent_symm] hint without loops. *)

CoInductive _independent_type1 {A X Y} (Lx: Lens A X) (Ly: Lens A Y) : Prop :=
  _independent_ctor1.

Ltac independent_symm_guard Lx Ly :=
  lazymatch goal with
  | [ _ : _independent_type1 Lx Ly |- _ ] => fail
  | _ => let iltt := fresh "iltt" in
        assert (iltt:=_independent_ctor1 Lx Ly)
  end.

Global Hint Extern 20 (Independent ?Lx ?Ly) =>
  independent_symm_guard Lx Ly;
  apply independent_symm : typeclass_instances.


(** *** Use [independent] rewrite except for [independent_symm] instances *)

Inductive _independent_type2 {A X Y} (Lx: Lens A X) (Ly: Lens A Y) : Prop :=
  _independent_ctor2 (Hi: Independent Lx Ly) :
    _independent_type2 Lx Ly.

Arguments _independent_ctor2 {_ _ _} _ _ {_}.

Ltac rewrite_independent :=
  match goal with
    |- context [ @update _ _ ?Ly (@update _ _ ?Lx _ _) _ ] =>
    let indeq := fresh "indeq" in
    assert (indeq:=@eq_refl _ (_independent_ctor2 Lx Ly));
    lazymatch goal with
    | [ _ : _independent_ctor2 _ _ (Hi := (let _ := _ in independent_symm _)) = _ |- _ ] =>
      fail
    | [ _ : _independent_ctor2 _ _ (Hi := ?Hi) = _ |- _ ] =>
      clear indeq;
      setoid_rewrite (@independent _ _ _ Lx Ly Hi)
    end
  end.


(** *** Rewrite tactics *)

Ltac lens_rewrite1 := rewrite_strat (outermost (hints lens))
                      || rewrite_independent.
Ltac lens_rewrite := repeat lens_rewrite1; try reflexivity.


(** ** Lens equality *)

Section equality_section.

  Arguments proj {_ _} _ _.
  Arguments update {_ _} _ _ _.

  Context {A X : Type}.

  Section eq_section.

    Context (L1: Lens A X) (L2: Lens A X).

    (** This is equivalent to "L1 = L2" if/when we assume extensionality,
        see LensExtras.v. *)
    Definition lensEq : Prop := forall a x, update L1 a x = update L2 a x.

  End eq_section.

  (** Useful to have as separate fact. *)
  Proposition lens_refl {Lx} : lensEq Lx Lx.
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

End equality_section.

(* TODO: Define notation scope. *)
Notation "L1 ≅ L2" := (lensEq L1 L2) (at level 70, no associativity) : type_scope. (* ! *)

Section proper_section.

  Context {A X Y : Type}.

  Global Instance update_proper :
    Proper (lensEq ==> eq ==> eq ==> eq) (@update A X).
  Proof.
    repeat intro. subst. intuition.
  Qed.

  Global Instance proj_proper :
    Proper (lensEq ==> eq ==> eq) (@proj A X).
  Proof.
    intros Lx Lx' Hlx.
    repeat intro. subst.
    setoid_rewrite <- (update_proj (Lens:=Lx')) at 1.
    rewrite <- Hlx.
    apply proj_update.
  Qed.

  Global Instance independent_proper :
    Proper (lensEq ==> lensEq ==> iff) (@Independent A X Y).
  Proof.
    (* Not sure why [setoid_rewrite] works with [Hx]
       and [rewrite] with [Hy], but not vice versa. *)
    intros Lx Lx' Hx
           Ly Ly' Hy.
    split; intros H a x y.
    - setoid_rewrite <- Hx.
      do 2 rewrite <- Hy.
      apply H.
    - setoid_rewrite Hx.
      do 2 rewrite Hy.
      apply H.
  Qed.

End proper_section.


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
    all: abstract (unfold compose; intros; lens_rewrite).
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

  (** Independent lenses are stable under prefixing. *)

  Global Instance composite_independent_r
           (Ly: Lens X Y) {Y'} (Ly': Lens X Y')
           {Hi: Independent Ly Ly'} : Independent (Ly ∘ Lx) (Ly' ∘ Lx).
  Proof.
    intros a y y'. cbn.
    unfold compose. cbn.
    lens_rewrite.
  Qed.

  Global Instance composite_independent_l
         (Ly: Lens A Y) {Hi: Independent Lx Ly}
         {Z} (Lz: Lens X Z) : Independent (Lz ∘ Lx) Ly.
  Proof.
    intros a z y. cbn.
    unfold compose. lens_rewrite.
  Qed.

End category_facts_section.

Arguments compositeLens_proper {_ _ _ _ _} Hlx {_ _} Hly.


(** ** Implicit targets *)

Class Lens' A :=
{
  target: Type;
  lens: Lens A target;
}.

Arguments target {_} _.
Arguments lens {_} _.

Instance Lens2Lens' {A X} (Lx: Lens A X) : Lens' A :=
{
  target := X;
  lens := Lx;
}.

Coercion Lens2Lens' : Lens >-> Lens'.

Bind Scope lens_scope with Lens'.


(** ** Sublenses *)

Section sublens_section.

  Context {A : Type}.

  (** This is analogous to [Z.divide], but beware that information is lost
  here, since [L21] is not unique. *)

  Class Sublens (L1 L2: Lens' A) : Prop :=
    sublens : exists (L21: Lens (target L2) (target L1)),
              lens L1 ≅ lens L21 ∘ lens L2.

  Global Instance sublens_reflexive : Reflexive Sublens.
  Proof.
    intros L. exists idLens.
    rewrite idLens_composite. reflexivity.
  Qed.

  Arguments proj {_ _} _ _.
  Arguments update {_ _} _ _ _.

  Global Instance sublens_transitive : Transitive Sublens.
  Proof.
    intros Lx Ly Lz Sxy Syz.
    destruct Sxy as [Lyx Hx].
    destruct Syz as [Lzy Hy].
    exists (Lyx ∘ Lzy)%lens.
    intros a x.
    cbn. rewrite Hx.
    cbn. rewrite Hy.
    reflexivity.
  Qed.

  Global Instance sublens_proper {X} :
    Proper (lensEq ==> lensEq ==> iff)
           (fun (L1 L2 : Lens A X) => Sublens L1 L2).
  Proof.
    intros Lx Lx' Hlx
           Ly Ly' Hly.
    unfold Sublens. cbn.
    setoid_rewrite Hlx.
    (* Hangs for some reason: setoid_rewrite Hly. *)
    setoid_rewrite (compositeLens_proper lens_refl Hly).
    reflexivity.
  Qed.

End sublens_section.

Notation "( Lx | Ly )" := (Sublens Lx Ly) : type_scope.

Section sublens_ordering_section.

  Context {A X} (Lx: Lens A X).

  Global Instance sublens_comp {Y} (Ly: Lens X Y) : (Ly ∘ Lx | Lx).
  Proof.
    exists Ly. reflexivity.
  Qed.

  (** [_ ∘ Lx ] is essentially proper. *)
  Global Instance sublens_comp'
         {Y} {Ly: Lens X Y}
         {Z} {Lz: Lens X Z}
         (Syz: (Ly | Lz)) : (Ly ∘ Lx | Lz ∘ Lx).
  Proof.
    destruct Syz as [Lzy Hyz].
    exists Lzy. cbn in *.
    rewrite compositeLens_associative.
    apply (compositeLens_proper Hyz lens_refl).
  Qed.

  (* TODO: Useful? *)
  Global Instance sublens_comp'' :
    Proper (@Sublens X ==> @Sublens A) (fun L => lens L ∘ Lx)%lens.
  Proof.
    intros L1 L2 [L21 H1].
    exists L21. cbn in *.
    rewrite compositeLens_associative.
    apply (compositeLens_proper H1 lens_refl).
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
    exists lens_fst. intros a x. cbn. lens_rewrite.
  Qed.

  Global Instance prod_sublens2 : (Ly | prodLens).
  Proof.
    exists lens_snd. intros a y. cbn. lens_rewrite.
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
    intros s [x y] z. simpl. lens_rewrite.
  Qed.

End projection_section.

(** The projections from a record type have the same property, cf. MachineExtras.v. *)

Infix "*" := prodLens : lens_scope.

Section flip_section.

  Context {A X Y} (Lx: Lens A X) (Ly: Lens A Y) {Hi: Independent Lx Ly}.

  (** TODO: Will this cause loops? *)
  Global Instance prod_sublens_symm : (Lx * Ly | Ly * Lx).
  Proof.
    exists (prodLens lens_snd lens_fst).
    intros a (x, y).
    cbn. lens_rewrite.
  Qed.

  Context {X'} (Lx': Lens A X') {Sx: (Lx'|Lx)}.

  Global Instance independent_sublens1 : Independent Lx' Ly.
  Proof.
    intros a x' y.
    destruct Sx as [L H].
    rewrite H.
    lens_rewrite.
  Qed.

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

  Global Instance independent_sublens2 : Independent Lx Ly'.
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
