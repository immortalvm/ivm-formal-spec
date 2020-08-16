From Assembly Require Import Init DSet Lens.

Require Import Coq.Logic.ProofIrrelevance.

Unset Suggest Proof Using.


(** ** Extensionality *)

Section char_section.

  Local Arguments proj {_ _} _ _.
  Local Arguments update {_ _} _ _ _.

  Context {A X} (L1 L2: Lens A X).

  Lemma lensEq_eq (H: L1 ≅ L2) : L1 = L2.
  Proof.
    destruct L1 as [p1 u1 pu1 up1 uu1].
    destruct L2 as [p2 u2 pu2 up2 uu2].
    cbn in H.

    assert (u1 = u2) as Hu;
      [ extensionality a; extensionality x; apply H
      | subst u1 ].

    assert (p1 = p2) as Hp;
      [ extensionality a;
        setoid_rewrite <- up2 at 1;
        apply pu1
      | subst p1 ].

    f_equal; apply proof_irrelevance.
   Qed.

End char_section.


(** ** Elementary *)

Section elementary_section.

  (** Since "unit" shorter than "terminal". *)
  #[refine] Instance unitLens {A} : Lens A unit :=
  {
    proj _ := tt;
    update a _ := a;
  }.
  Proof.
    1: intros _ [].
    all: reflexivity.
  Defined.

  Program Instance independent_unit {A X} {Lx: Lens A X} : Independent unitLens Lx.

  Instance unitSublens {A X} (Lx: Lens A X) : (Lx | idLens).
  Proof.
    intros a b c. reflexivity.
  Qed.

  #[refine] Instance falseLens {X} : Lens False X :=
  {
    proj a := False_rect X a;
    update a x := a;
  }.
  Proof.
    all: intros [].
  Defined.

  Instance independent_False {X Y} {Ly: Lens False Y} : Independent (@falseLens X) Ly.
  Proof.
    split; intros [].
  Qed.

  Context {A X} (Lx: Lens A X).

  Instance terminal_sublens : (Lx | idLens ).
  Proof.
    intros a b c. reflexivity.
  Qed.

  Instance initial_sublens : (unitLens | Lx).
  Proof.
    intros a b c. reflexivity.
  Qed.

  Context {Y} (Ly: Lens A Y) {Hi: Independent Lx Ly}.

  Arguments proj {_ _} _ _.
  Arguments update {_ _} _ _ _.

  (* TODO: Can we manage without these two propositions? *)
  Proposition prod_proj_spec (a: A) : proj (Lx * Ly) a = (proj Lx a, proj Ly a).
  Proof. reflexivity. Qed.

  Proposition prod_update_spec (a: A) (xy: X * Y) :
    update (Lx * Ly) a xy = update Ly (update Lx a (fst xy)) (snd xy).
  Proof. reflexivity. Qed.

End elementary_section.


(** ** Bijections *)

Class Bijection {X Y: Type} (f: X -> Y) :=
{
  inverse : Y -> X;
  inverse_f x : inverse (f x) = x;
  f_inverse y : f (inverse y) = y;
}.

Definition bijection {X Y: Type} (f: X -> Y) (g: Y -> X) : Prop :=
  forall x y, f x = y <-> g y = x.

Section bijection_section.

  Context {X: Type}.

  Program Instance Bijection_id : Bijection (@id X).

  Context {Y} {f: X -> Y}.

  #[refine] Instance Bijection_b (g: Y -> X) (Hb: bijection f g) : Bijection f :=
  {
    inverse := g;
    inverse_f x := _;
    f_inverse y := _;
  }.
  Proof.
    all: apply Hb; reflexivity.
  Defined.

  Context {Bf: Bijection f}.

  Lemma B_bijection : bijection f inverse.
  Proof.
    intros x y. split; intro; subst.
    - apply inverse_f.
    - apply f_inverse.
  Qed.

  Lemma B_injective x x' : f x = f x' -> x = x'.
    intros H.
    rewrite <- (proj1 (B_bijection x (f x')) H).
    apply inverse_f.
  Qed.

  (** Not global on purpose! *)
  Instance Bijection_symmetry : Bijection inverse :=
  {
    inverse := f;
    inverse_f := f_inverse;
    f_inverse := inverse_f;
  }.

  Context {Z} {g: Y -> Z} {Bg: Bijection g}.

  #[refine] Instance Bijection_composite : Bijection (g ∘ f) :=
  {
    inverse z := inverse (inverse z);
  }.
  Proof.
    all: intro; unfold compose.
    - do 2 rewrite inverse_f. reflexivity.
    -  do 2 rewrite f_inverse. reflexivity.
  Defined.

End bijection_section.

Arguments Bijection_b : clear implicits.
Arguments Bijection_b {_ _ _} _ _.

Arguments Bijection_composite : clear implicits.
Arguments Bijection_composite {_ _ _} _ {_ _}.


(** ** Bijection lenses *)

Notation Bijection_lens L := (Bijection (proj (Lens:=L))).

Section bijection_lens_section.

  Context {A X} {f: A -> X} (Bf: Bijection f).

  #[refine] Instance lens_bijection : Lens A X :=
  {
    proj x := f x;
    update _ x := inverse x;
  }.
  Proof.
    - intros _ x. apply f_inverse.
    - intros a. apply inverse_f.
    - reflexivity.
  Defined.

End bijection_lens_section.

Section lens_bijection_section.

  Context {A X} {Lx: Lens A X}.

  Proposition proj_characterized a x : proj a = x <-> update a x = a.
  Proof.
    split; intros H; rewrite <- H.
    - apply update_proj.
    - apply proj_update.
  Qed.

  Proposition update_as_inverse {Bp: Bijection proj} a x :
    update a x = inverse x.
  Proof.
    symmetry. apply B_bijection, proj_update.
  Qed.

  (** Conversely: *)

  #[refine] Instance bijection_lens (g: X -> A)
            (Hup: forall a x, update a x = g x) : Bijection_lens Lx :=
  {
    inverse := g;
  }.
  Proof.
    - intro a. rewrite <- (Hup a). apply proj_characterized. reflexivity.
    - intro x. rewrite <- (Hup (g x)). rewrite proj_update. reflexivity.
  Defined.

End lens_bijection_section.


(** ** Products and projections *)

Section projection_section.

  Context {X Y: Type}
          {A} (Lx: Lens A X) (Ly: Lens A Y) {IXY: Independent Lx Ly}
          {Bp: Bijection_lens (Lx * Ly)}.

  Local Ltac update_prod_tac a :=
    apply (B_injective (Bf:=Bp));
    rewrite <- (update_as_inverse a);
    rewrite proj_update;
    simpl;
    lens_rewrite.

  Proposition update_prodX (a: A) (x: X) : update a x = inverse (x, proj a).
  Proof. update_prod_tac a. Qed.

  Proposition update_prodY (a: A) (y: Y) : update a y = inverse (proj a, y).
  Proof. update_prod_tac a. Qed.

  (* TODO: Is this ever useful? *)
  Lemma update_proj_swap (a a' : A) :
    update a' (proj a : X) = update a (proj a' : Y).
  Proof. rewrite update_prodX, update_prodY. reflexivity. Qed.

  Proposition projX_inverse xy : proj (inverse xy) = fst xy.
  Proof.
    rewrite
      <- (update_as_inverse (inverse xy)),
      prod_update_spec,
      proj1_update2,
      proj_update.
    reflexivity.
  Qed.

  Proposition projY_inverse xy : proj (inverse xy) = snd xy.
  Proof.
    rewrite
      <- (update_as_inverse (inverse xy)),
      prod_update_spec,
      proj_update.
    reflexivity.
  Qed.

End projection_section.


(** ** Sum lenses *)

Section sum_section.

  Context {A B X : Type} {Lx : Lens A X} {Ly : Lens B X}.

  #[refine] Instance lens_sum : Lens (A + B) X :=
  {
    proj ab := match ab with inl a => proj a | inr b => proj b end;
    update ab x := match ab with inl a => inl (update a x) | inr b => inr (update b x) end;
  }.
  Proof.
    - intros [a|b] x; lens_rewrite.
    - intros [a|b]; f_equal; lens_rewrite.
    - intros [a|b] x x'; f_equal; lens_rewrite.
  Defined.

End sum_section.


(** ** Prisms

This is essentially a formalization of "prisms" in funcitonal programming.
I am not sure if our axiomatization is optimal. *)

Class Prism (X: Type) (A: Type) :=
{
  inj : X -> A;
  injected : A -> option X;
  injected_inj x : injected (inj x) = Some x;
  injected_some a x : injected a = Some x -> inj x = a;
}.

Arguments injected_some {_ _ _ _ _}.

Import DSetNotations.

Definition prism_dset {X A} (P: Prism X A) : DSet A :=
  DSet.def (fun a => injected a).

#[refine] Instance dset_prism {A} (u: DSet A) : Prism { a: A | a ∈ u } A :=
{
  inj x := proj1_sig x;
  injected a := match decide (a ∈ u) with
                | left Ha => Some (exist _ a Ha)
                | right _ => None
                end;
}.
Proof.
  - intros [a Ha]. cbn.
    decided Ha. reflexivity.
  - intros a [a' Ha'] H.
    cbn.
    destruct (decide (a ∈ u)) as [Ha|Ha]; [ | discriminate H ].
    derive H (noConfusion_inv H).
    cbn in H.
    derive H (f_equal (@proj1_sig A _) H).
    symmetry.
    exact H.
Defined.

Notation Bijection_prism P := (Bijection (inj (Prism:=P))).

Section bijection_prism_section.

  Context {X A} {f: X -> A} (Bf: Bijection f).

  #[refine] Instance prism_bijection : Prism X A :=
  {
    inj := f;
    injected a := Some (inverse a);
  }.
  Proof.
    - intros x. f_equal. apply inverse_f.
    - intros a x H. injection H. intro. subst x. apply f_inverse.
  Qed.

End bijection_prism_section.

Section prism_basics_section.

  Context A {X} (PX: Prism X A).

  Lemma inj_extract a (H: injected a) : inj (extract H) = a.
  Proof.
    destruct (injected a) as [x|] eqn:Ha.
    - apply injected_some. exact Ha.
    - exact (none_rect H).
  Qed.

  Proposition inj_is_injected (x: X) : injected (inj x).
  Proof. apply (is_some_eq (injected_inj x)). Defined.

  Proposition extract_inj (x: X) : extract (inj_is_injected x) = x.
  Proof.
    unfold inj_is_injected.
    rewrite extract_is_some_eq.
    reflexivity.
  Qed.

  Opaque inj_is_injected.

  Lemma inj_injective (x x': X) : inj x = inj x' -> x = x'.
  Proof. (* Not sure if this is the best proof of this fact. *)
    intros H.
    derive H (f_equal injected H).
    do 2 rewrite injected_inj in H.
    exact (noConfusion_inv H).
  Qed.

  Context {Y} (PY: Prism Y X).

  #[refine] Instance inj_composition : Prism Y A :=
  {
    inj y := inj (inj y);
    injected a := match injected a with
                  | Some x => injected x
                  | None => None
                  end;
  }.
  Proof.
    - intros y. do 2 rewrite injected_inj. reflexivity.
    - intros a y H.
      destruct (injected a) as [x|] eqn:Ha.
      + rewrite (injected_some H).
        rewrite (injected_some Ha).
        reflexivity.
      + destruct (noConfusion_inv H).
  Defined.

  (** [id] is a bijection and therefore a prism. Hence, we clearly have a
      monoid up to functional extensionality here as well. *)

End prism_basics_section.

Arguments inj_extract {_ _ _ _} _.
Arguments inj_is_injected {_ _ _} _.
Arguments extract_inj {_ _ _} _.
Arguments inj_injective {_ _ _ _ _} _.
Arguments inj_composition {_ _} _ {_} _.

(** From now on, make [X] explicit for clarity. *)
Arguments injected : clear implicits.
Arguments injected _ {_ _} _.


(** ** Disjoint prisms *)

Class Disjoint {X Y A} (PX: Prism X A) (PY: Prism Y A) : Prop :=
{
  injectedY_injX (x: X) : injected Y (inj x) = None;
  injectedX_injY (y: Y) : injected X (inj y) = None;
}.

Arguments injectedY_injX {_ _ _ _ _ _} _.
Arguments injectedX_injY {_ _ _ _ _ _} _.

Section disjoint_basics_section.

  Context {X Y A} {PX: Prism X A} {PY: Prism Y A}.

  (** Not global to avoid infinite loops. *)
  Instance disjoint_symm (D: Disjoint PX PY) :
    Disjoint PY PX.
  Proof.
    split.
    - apply injectedX_injY.
    - apply injectedY_injX.
  Qed.

  Lemma disjoint_spec : Disjoint PX PY <-> forall a, (injected X a) -> (injected Y a) -> False.
  Proof.
    split.
    - intros [Hyx Hxy].
      intros a Hx Hy.
      specialize (Hyx (extract Hx)).
      rewrite inj_extract in Hyx.
      rewrite Hyx in Hy.
      exact (none_is_false Hy).
    - intros H.
      split.
      + intros x.
        specialize (H (inj x)).
        destruct (injected Y (inj x)).
        exfalso.
        apply H.
        * apply inj_is_injected.
        * apply some_is_some.
        * reflexivity.
      + intros y.
        specialize (H (inj y)).
        destruct (injected X (inj y)).
        exfalso.
        apply H.
        * apply some_is_some.
        * apply inj_is_injected.
        * reflexivity.
  Qed.

End disjoint_basics_section.


(** ** Injection prisms *)

Section injection_section.

  Context {X Y : Type}.

  #[refine] Instance inj_inl: Prism X (X + Y) :=
  {
    inj := inl;
    injected a := match a with inl x => Some x | _ => None end;
  }.
  Proof.
    - intro x. reflexivity.
    - intros [x|y] x' H; destruct (noConfusion_inv H).
      reflexivity.
  Defined.

  #[refine] Instance inj_inr: Prism Y (X + Y) :=
  {
    inj := inr;
    injected a := match a with inr y => Some y | _ => None end;
  }.
  Proof.
    - intro y. reflexivity.
    - intros [x|y] y' H; destruct (noConfusion_inv H).
      reflexivity.
  Defined.

  Program Instance disjoint_ins : Disjoint inj_inl inj_inr.

  Context (A: Type).

  Context (PX: Prism X A) (PY: Prism Y A).

  #[refine] Instance inj_false : Prism False A :=
  {
    inj H := False_rect A H;
    injected _ := None;
  }.
  Proof.
    - intros [].
    - intros a x. destruct x.
  Defined.

  Instance inj_false_disjoint: Disjoint inj_false PX.
  Proof.
    split.
    - intros [].
    - intros y. reflexivity.
  Defined.

End injection_section.


(** ** Sum prisms *)

Section sum_section.

  Derive NoConfusion for sum.

  Context {A X Y} {PX: Prism X A} {PY: Prism Y A} (DXY: Disjoint PX PY).

  #[refine] Instance inj_sum : Prism (X + Y) A :=
  {
    inj xy := match xy with
              | inl x => inj x
              | inr y => inj y
              end;
    injected a := match injected X a, injected Y a with
                  | Some x, _ => Some (inl x)
                  | _, Some y => Some (inr y)
                  | _, _ => None
                  end;
  }.
  Proof.
    - intros [x|y]; rewrite injected_inj.
      + reflexivity.
      + rewrite injectedX_injY. reflexivity.
    - intros a [x|y] H; destruct (injected X a) as [x'|] eqn:Ha.
      + repeat derive H (noConfusion_inv H).
        simpl in H. subst x'.
        exact (injected_some Ha).
      + destruct (injected Y a) as [y|];
          exfalso; repeat derive H (noConfusion_inv H); exact H.
      + exfalso; repeat derive H (noConfusion_inv H); exact H.
      + destruct (injected Y a) as [y'|] eqn:Ha'.
        * repeat derive H (noConfusion_inv H).
          simpl in H. subst y'.
          exact (injected_some Ha').
        * exfalso; repeat derive H (noConfusion_inv H); exact H.
  Defined.

  Context Z {PZ: Prism Z A} (DXZ: Disjoint PX PZ) (DYZ: Disjoint PY PZ).

  Instance sum_disjoint : Disjoint inj_sum PZ.
  Proof. (* TODO: shorten? *)
    split.
    - intros [x|y].
      + apply (injectedY_injX (Disjoint:=DXZ)).
      + apply (injectedY_injX (Disjoint:=DYZ)).
    - intros z.
      simpl.
      destruct (injected X (inj z)) as [x|] eqn:Hi.
      + rewrite injectedX_injY in Hi.
        exfalso; exact (noConfusion_inv Hi).
      + destruct (injected Z (inj z)) as [y|] eqn:Hi';
          rewrite injectedX_injY;
          reflexivity.
  Qed.

End sum_section.


(** ** [N -> Z] prism *)

Tactic Notation "decide" "as" ident(H) :=
  match goal with
    [|- context [decide ?P]] =>
    let H := fresh H in (* Not sure why this is needed *)
    let HH := fresh in
    assert P as HH;
    [ | destruct (decide P) as [H|H];
        [ clear HH | exfalso; exact (H HH) ]]
end.

#[refine] Instance prism_N : Prism N Z :=
{
  inj x := Z.of_N x;
  injected z := if decide (0 <= z)%Z
                then Some (Z.to_N z)
                else None;
}.
Proof.
  - intros x.
    decide as H; [apply N2Z.is_nonneg|].
    f_equal.
    apply N2Z.id.
  - intros z x.
    destruct (decide _) as [H|H];
      [|intros HH; exfalso; exact (noConfusion_inv HH)].
    injection 1. intro. subst x.
    apply Z2N.id.
    exact H.
Defined.

Proposition injected_N {z: Z} : injected N z <-> (0 <= z)%Z.
Proof.
  simpl.
  destruct (decide _) as [H|H]; unfold is_some; simpl; tauto.
Qed.


(** ** Sublenses *)

Section sublens_section.

  Context {X A Y} {PX: Prism X A} {Ly: Lens A Y}.

  Context (H: forall x y, injected X (update (inj x) y)).

  #[refine] Instance sublens : Lens X Y :=
  {
    proj x := proj (inj x);
    update x y := extract (H x y);
  }.
  Proof.
    - intros x y. rewrite inj_extract, proj_update. reflexivity.
    - intros x. apply inj_injective.
      rewrite inj_extract, update_proj. reflexivity.
    - intros x y y'.
      apply inj_injective.
      repeat rewrite inj_extract.
      rewrite update_update.
      reflexivity.
  Defined.

  Proposition prism_proj_spec x : proj x = proj (inj x).
  Proof. reflexivity. Qed.

  Proposition prism_update_spec x y : update x y = extract (H x y).
  Proof. reflexivity. Qed.

  Proposition inj_prism_update x y : inj (update x y) = update (inj x) y.
  Proof. simpl. rewrite inj_extract. reflexivity. Qed.

End sublens_section.


(** ** Every lens is a product lens

Assuming functional extensionality and proof irrelevance, we have a
converse of [fstLens]: If [Lens S X], then [S ≅ X * S'] for some S'. *)

Section Inv_lens.

  Context S X (PX: Lens S X).

  Definition S' := { f: X -> S | forall x y, update (f x) y = f y }.

  Arguments exist {_} {_} _.

  #[refine]
  Instance inv_lens : Lens S S' :=
  {
    proj s := exist (update s) _;
    update s f := proj1_sig f (proj s);
  }.
  Proof.
    - intros x y. rewrite update_update. reflexivity.
    - intros s [f H].
      simpl.
      apply eq_sig_hprop.
      + intros. apply proof_irrelevance.
      + simpl. extensionality x.
        rewrite H. reflexivity.
    - intro s. simpl.
      rewrite update_proj. reflexivity.
    - intros s [f Hf] [g Hg]. simpl.
      rewrite <- (Hf (proj s)), proj_update. reflexivity.
  Defined.

  Instance inv_lens_independent : Independent inv_lens PX.
  Proof.
    intros a b c. cbn. lens_rewrite.
  Qed.

  Lemma inv_lens_inv (s: S) :
    let (fH, x) := proj (Lens:=_*_) s in
    proj1_sig fH x = s.
  Proof.
    simpl. rewrite update_proj. reflexivity.
  Qed.

End Inv_lens.
