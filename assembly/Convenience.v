Require Import Equations.Equations.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.micromega.Lia.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Vectors.Vector. (** Does not open [vector_scope]. *)
Require Export Coq.Bool.Bvector.
Require Export Coq.Lists.List. (** Opens [list_scope]. *)
Require Export Coq.Program.Basics.
Require Coq.Init.Byte.

Export EqNotations.

(* This is a mixed blessing *)
Set Implicit Arguments.

(** This clearly does not work properly at the moment. *)
Unset Suggest Proof Using.


(** ** Tactics *)

Tactic Notation "by_lia" constr(P) "as" ident(H) := assert P as H; [lia|].

Ltac derive name term :=
  let H := fresh in
  let A := type of term in
  assert A as H;
  [ exact term | ];
  clear name;
  rename H into name.

(** From http://ropas.snu.ac.kr/gmeta/source/html/LibTactics.html. *)
Ltac destructs H :=
  let X := fresh in
  let Y := fresh in
  first [ destruct H as [X Y]; destructs X; destructs Y | idtac ].

Ltac idestructs := repeat (let X := fresh in intro X; destructs X).


(** ** Booleans *)

Derive NoConfusion for bool.

Goal true <> false.
Proof.
  intro H.
  exact (noConfusion_inv H).
Qed.

Coercion Is_true : bool >-> Sortclass.

Proposition true_is_true : true.
Proof. exact I. Qed.

Proposition false_is_false : not false.
Proof. exact id. Qed.

Proposition false_if_not_true {b: bool} : not b -> b = false.
Proof.
  destruct b.
  - intros H. contradict H. exact true_is_true.
  - intros _. reflexivity.
Qed.

(** See also [Is_true_eq_left], [Is_true_eq_right] and [Is_true_eq_true]. *)

Notation as_bool x := (if x then true else false).


(** ** Decidable *)

Class Decidable (P: Prop) : Type :=
  decide : { P } + { not P }.

Arguments decide P {_}.

Instance True_decidable : Decidable True := left I.
Instance False_decidable : Decidable False := right (@id False).
Instance equality_decidable {A} `{dec: EqDec A} (x y: A) : Decidable (x = y) := dec x y.
Instance is_true_decidable (x: bool) : Decidable (x) :=
  if x return (Decidable x)
  then left true_is_true
  else right false_is_false.

Section decidable_connectives.

  Context P `(DP: Decidable P).

  Global Instance not_decidable : Decidable (not P) :=
    match DP with
    | left H => right (fun f => f H)
    | right H => left H
    end.

  Context Q `(DQ: Decidable Q).

  Local Ltac cases := destruct DP; destruct DQ; constructor; tauto.

  Global Instance and_decidable : Decidable (P /\ Q). cases. Defined.
  Global Instance or_decidable : Decidable (P \/ Q). cases. Defined.
  Global Instance impl_decidable : Decidable (P -> Q). cases. Defined.

End decidable_connectives.

Instance nat_lt_decidable (x y: nat) : Decidable (x < y) := lt_dec x y.
Instance nat_le_decidable (x y: nat) : Decidable (x <= y) := le_dec x y.

Instance Z_lt_decidable (x y: Z) : Decidable (x < y)%Z := Z_lt_dec x y.
Instance Z_le_decidable (x y: Z) : Decidable (x <= y)%Z := Z_le_dec x y.
Instance Z_ge_decidable (x y: Z) : Decidable (x >= y)%Z := Z_ge_dec x y.
Instance Z_gt_decidable (x y: Z) : Decidable (x > y)%Z := Z_gt_dec x y.


(** ** Options *)

Derive NoConfusion for option.

Goal forall {X} (x y: X) (H: Some x = Some y), x = y.
Proof. intros ? ? ?. exact noConfusion_inv. Qed.

Instance option_eqdec {A} {Ha: EqDec A} : EqDec (option A).
Proof.
  eqdec_proof. (* Tactic in Coq-Equations *)
Defined.

Definition is_some {X} (ox: option X) : bool := as_bool ox.

Coercion is_some : option >-> bool.

Instance is_some_decidable {X} (ox: option X) : Decidable ox.
Proof. apply is_true_decidable. Defined.

Instance is_none_decidable {X} (ox: option X) : Decidable (ox = None).
Proof. destruct ox as [x|]; [right|left]; congruence. Defined.

Proposition some_is_some {X} (x: X) : Some x.
Proof. exact true_is_true. Qed.

Proposition none_is_false {X} : @None X -> False.
Proof. exact false_is_false. Qed.

(** Shortcut *)
Definition none_rect {X Y} (H: @None X) : Y :=
  False_rect Y (none_is_false H).

Definition extract {X} {ox: option X} : ox -> X :=
  match ox return ox -> X with
  | Some x => fun _ => x
  | None => fun H => none_rect H
  end.

Proposition extract_some {X} (x: X) : extract (some_is_some x) = x.
Proof. reflexivity. Qed.

Lemma some_extract {X} {ox: option X} (H: ox) : Some (extract H) = ox.
Proof.
  destruct ox as [x|].
  - simpl. reflexivity.
  - exact (none_rect H).
Qed.

Proposition is_some_eq {X} {ox: option X} {x: X} : ox = Some x -> ox.
Proof. intro H. rewrite H. reflexivity. Qed.

Proposition extract_is_some_eq {X} {ox: option X} {x: X} (H: ox = Some x) : extract (is_some_eq H) = x.
Proof. subst ox. reflexivity. Qed.

Proposition extract_unique {X} {ox: option X} (H H': ox) : extract H = extract H'.
Proof.
  destruct ox as [x|].
  - reflexivity.
  - exact (none_rect H).
Qed.


(** ** Bijections *)

Class Bijection {X Y: Type} (f: X -> Y) :=
{
  inverse : Y -> X;
  inverse_f x : inverse (f x) = x;
  f_inverse y : f (inverse y) = y;
}.

Definition bijection {X Y: Type} (f: X -> Y) (g: Y -> X) : Prop :=
  forall {x y}, f x = y <-> g y = x.

Section bijection_section.

  Open Scope program_scope.

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

(** * Lenses *)

Class Lens (A: Type) (X: Type) :=
{
  proj: A -> X;
  update: A -> X -> A;
  proj_update (a: A) (x: X) : proj (update a x) = x;
  update_proj (a: A) : update a (proj a) = a;
  update_update (a: A) (x: X) (x': X) : update (update a x) x' = update a x';
}.

Create HintDb proj discriminated.
Hint Rewrite @proj_update using (typeclasses eauto) : proj.
Hint Rewrite @update_proj using (typeclasses eauto) : proj.
Hint Rewrite @update_update using (typeclasses eauto) : proj.
Ltac lens_rewrite1 := rewrite_strat (outermost (hints proj)).
Ltac lens_rewrite := repeat lens_rewrite1.


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

  Context {A X} {LX: Lens A X}.

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
            (Hup: forall a x, update a x = g x) : Bijection_lens LX :=
  {
    inverse := g;
  }.
  Proof.
    - intro a. rewrite <- (Hup a). apply proj_characterized. reflexivity.
    - intro x. rewrite <- (Hup (g x)). rewrite proj_update. reflexivity.
  Defined.

End lens_bijection_section.


(** ** Lens monoid

This is not something we actually use.
TODO: Remove? *)

Section lens_monoid_section.

  (** [id] is a bijection and therefore a lens. *)

  Context {A X} (PX: Lens A X).
  Context {Y} (PY: Lens X Y).

  #[refine] Instance lens_composite : Lens A Y :=
  {
    proj a := proj (proj a);
    update a y := update a (update (proj a) y);
  }.
  Proof.
    all: intros; lens_rewrite; reflexivity.
  Defined.

  (** This is clearly a monoid up to funcitonal extensionality. *)

End lens_monoid_section.


(** ** Independent lenses *)

Class Independent {S: Type}
      {X: Type} (LX: Lens S X)
      {Y: Type} (LY: Lens S Y) : Prop :=
{
  projY_updateX (s: S) (x: X) : proj (update s x) = proj s :> Y;
  projX_updateY (s: S) (y: Y) : proj (update s y) = proj s :> X;
  independent_commute (s: S) (x: X) (y: Y) :
    update (update s x) y = update (update s y) x;
}.

(** To see that [independent_commute] does not follow from the other
    properties, consider a square staircase. *)

Create HintDb independent discriminated.
Hint Rewrite @projY_updateX using (typeclasses eauto) : independent.
Hint Rewrite @projX_updateY using (typeclasses eauto) : independent.
Hint Rewrite @independent_commute using (typeclasses eauto) : independent.
Ltac independent_rewrite1 := rewrite_strat (outermost (hints independent)).
Ltac independent_rewrite := repeat independent_rewrite1.

Section independence_section.

  Context {A X Y} {LX: Lens A X} {LY: Lens A Y} (HI: Independent LX LY).

  (** Not gloal on purpose. *)
  Instance independent_symm : Independent LY LX.
  Proof.
    split; intros; now independent_rewrite.
  Qed.

End independence_section.


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


(** ** Projection lenses *)

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

  Context {A} {LX: Lens A X} {LY: Lens A Y} (IXY: Independent LX LY).

  #[refine]
  Instance lens_prod : Lens A (X * Y) :=
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


  Context {Bp: Bijection_lens lens_prod}.

  Local Ltac update_prod_tac a :=
    apply (B_injective (Bf:=Bp));
    rewrite <- (update_as_inverse a);
    rewrite proj_update;
    simpl;
    rewrite proj_update;
    independent_rewrite1;
    reflexivity.

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
      projX_updateY,
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


  Context Z (LZ: Lens A Z) (IXZ: Independent LX LZ) (IYZ: Independent LY LZ).

  Global Instance independent_prod : Independent lens_prod LZ.
  Proof.
    split.
    - intros s [x y]. simpl.
      transitivity (proj (update s x)); now independent_rewrite.
    - intros s z. simpl. f_equal; now independent_rewrite.
    - intros s [x y] z. simpl. now independent_rewrite.
  Qed.

End projection_section.

(** The projections from a record type have the same property, cf. Concrete.v. *)


(** ** Sum lenses *)

Section sum_section.

  Context {A B X : Type} {LX : Lens A X} {LY : Lens B X}.

  #[refine] Instance lens_sum : Lens (A + B) X :=
  {
    proj ab := match ab with inl a => proj a | inr b => proj b end;
    update ab x := match ab with inl a => inl (update a x) | inr b => inr (update b x) end;
  }.
  Proof.
    - intros [a|b] x; now lens_rewrite.
    - intros [a|b]; f_equal; now lens_rewrite.
    - intros [a|b] x x'; f_equal; now lens_rewrite.
  Defined.

End sum_section.


(** ** Vectors and lists *)

Close Scope list_scope.
(** This opens [vector_scope]. *)
Export VectorNotations.

Export ListNotations.
Open Scope list_scope. (* Partly shadows vector_scope. *)

Notation vector := (Vector.t).

Derive Signature NoConfusion NoConfusionHom for vector.

Instance vector_eqdec {A} {Ha: EqDec A} {n} : EqDec (vector A n).
Proof. eqdec_proof. Defined.

Arguments Vector.nil {A}.
Arguments Vector.cons : default implicits.

Lemma to_list_equation_1 {A} : to_list []%vector = [] :> list A.
Proof. reflexivity. Qed.

Lemma to_list_equation_2 {A n} (x: A) (u: vector A n) : to_list (x :: u)%vector = x :: (to_list u).
Proof. reflexivity. Qed.

Hint Rewrite
     @to_list_equation_1
     @to_list_equation_2 : to_list.

Lemma to_list_injective {A n} (u v: vector A n) : to_list u = to_list v -> u = v.
Proof.
  induction n as [|n IH]; depelim u; depelim v.
  - easy.
  - simp to_list. intro Heq.
    f_equal; [|apply (IH u v)]; congruence.
Qed.

Lemma length_to_list {A n} (v: vector A n) : length (to_list v) = n.
Proof.
  depind v.
  - reflexivity.
  - simp to_list. simpl length. rewrite IHv. reflexivity.
Qed.

(* Coercion Vector.to_list : vector >-> list. *)


(** ** Vector lenses *)

Section lens_vector_section.

  Open Scope vector.

  Context {A X: Type} {LX: Lens A X} {LA: Lens A A}.

  Equations projN n (_: A) : vector X n :=
    projN 0 _ := [];
    projN (S n) a := (proj a :: projN n (proj a)).

  Equations projN' `(nat) `(A) : A :=
    projN' 0 a := a;
    projN' (S n) a := (projN' n (proj a)).

  Arguments update : clear implicits.
  Arguments update {_ _} _ _ _.

  Equations updateN {n} `(A) `(vector X n) : A :=
    updateN (n:=S n) a (x :: r) := (update LX (update LA a (updateN (proj a) r)) x);
    updateN a _ := a.

  Equations updateN' (n:nat) `(A) `(A) : A :=
    updateN' (S n) a a' := update LA a (updateN' n (proj a) a');
    updateN' _ _ a' := a'.

  Context {IXA: Independent LX LA}.

  #[refine] Instance lens_vector n : Lens A (vector X n) :=
  {
    proj a := projN n a;
    update a x := updateN a x;
  }.
  Proof.
    - induction n as [|n IH]; intros a x; depelim x.
      + reflexivity.
      + simp projN updateN.
        rewrite proj_update. f_equal.
        rewrite <- (IH (proj a)). f_equal.
        rewrite projY_updateX, proj_update.
        reflexivity.
    - induction n as [|n IH]; intros a.
      + reflexivity.
      + simp projN updateN.
        rewrite IH. lens_rewrite. reflexivity.
    - induction n as [|n IH]; intros a x x'; depelim x; depelim x'.
      + reflexivity.
      + simp projN updateN.
        independent_rewrite.
        lens_rewrite. rewrite IH. reflexivity.
  Defined.

  #[refine] Instance lens_vector' n : Lens A A :=
  {
    proj a := projN' n a;
    update a x := updateN' n a x;
  }.
  Proof.
    - induction n as [|n IH]; intros a x.
      + reflexivity.
      + simp projN' updateN'.
        rewrite proj_update, IH.
        reflexivity.
    - induction n as [|n IH]; intros a.
      + reflexivity.
      + simp projN' updateN'.
        rewrite IH. lens_rewrite. reflexivity.
    - induction n as [|n IH]; intros a x x'.
      + reflexivity.
      + simp updateN'.
        lens_rewrite. rewrite IH. reflexivity.
  Defined.

  Instance independent_vector n : Independent (lens_vector n) (lens_vector' n).
  Proof.
    induction n as [|n IH]; [split; reflexivity|].
    destruct IH as [IH1 IH2 IH3].
    simpl in IH1, IH2, IH3.
    split.
    - intros a x. depelim x. simpl.
      simp projN' updateN.
      independent_rewrite.
      lens_rewrite.
      rewrite IH1.
      reflexivity.
    - intros a y. simpl.
      simp projN updateN'.
      lens_rewrite.
      rewrite IH2.
      f_equal.
      independent_rewrite.
      reflexivity.
    - intros a x y.
      simpl.
      depelim x.
      simp updateN updateN'.
      independent_rewrite.
      lens_rewrite.
      rewrite IH3.
      reflexivity.
  Qed.

  Context (Bp: Bijection_lens (lens_prod IXA)).
  Existing Instance lens_prod.

  Equations inverseN {n} `(vector X n) `(A) : A :=
    inverseN (n:=S n) (x :: r) a := inverse (x, inverseN r a);
    inverseN _ a := a.

  #[refine] Instance bijection_vector n : Bijection_lens (lens_prod (independent_vector n)) :=
    bijection_lens (fun va => inverseN (fst va) (snd va)) _.
  Proof.
    intros a [v a']. simpl. revert a v a'.
    induction n as [|n IH]; intros a v a'; depelim v; simp inverseN.
    - reflexivity.
    - simp updateN' updateN.
      independent_rewrite.
      lens_rewrite.
      rewrite IH.
      rewrite <- (update_as_inverse a).
      simpl.
      independent_rewrite1.
      reflexivity.
  Defined.

End lens_vector_section.

Arguments lens_vector : clear implicits.
Arguments lens_vector {_ _} _ _ {_} _.

Arguments lens_vector' : clear implicits.
Arguments lens_vector' {_} _ _.


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

  Context {X A Y} {PX: Prism X A} {LY: Lens A Y}.

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


(** * Bits *)

Section bits_section.

  Open Scope Z.

  (** ** Basics *)

  Lemma pos_pred_double_z (x: positive) : Zpos (Pos.pred_double x) = 2 * (Zpos x) - 1.
  Proof.
    destruct x as [ x | x | ]; simpl; reflexivity.
  Qed.

  Lemma pos_pred_n_z (x: positive): Z.of_N (Pos.pred_N x) = Z.pred (Zpos x).
  Proof.
    destruct x as [ x | x | ]; reflexivity.
  Qed.

  Lemma pos_pred_n_injective : forall x y, Pos.pred_N x = Pos.pred_N y -> x = y.
  Proof.
    intros x y H.
    enough (Zpos x = Zpos y) as Hz.
    - injection Hz. tauto.
    - set (HH := f_equal Z.of_N H).
      do 2 rewrite pos_pred_n_z in HH.
      apply Z.pred_inj.
      exact HH.
  Qed.

  Lemma odd_double {z b} : Z.odd (Z.double z + Z.b2z b) = b.
  Proof.
    rewrite Z.add_comm, Z.odd_add_mul_2.
    destruct b; reflexivity.
  Qed.

  Proposition div2_double z : Z.div2 (Z.double z) = z.
  Proof.
    rewrite Z.div2_div, Z.double_spec, Z.mul_comm, Z_div_mult;
      auto with zarith.
  Qed.

  Proposition div2_double1 z : Z.div2 (Z.double z + 1) = z.
  Proof.
    rewrite Z.div2_div, Z.double_spec, Z.mul_comm, Z_div_plus_full_l;
      auto with zarith.
  Qed.

  Corollary div2_double2 z b : Z.div2 (Z.double z + Z.b2z b) = z.
  Proof.
    destruct b; simpl.
    - apply div2_double1.
    - rewrite Z.add_0_r. apply div2_double.
  Qed.


  (** ** Lenses *)

  #[refine] Instance lens_odd : Lens Z bool :=
  {
    proj z := Z.odd z;
    update z b := Z.double (Z.div2 z) + Z.b2z b;
  }.
  Proof.
    - intros z x.
      rewrite Z.add_comm.
      rewrite Z.odd_add_mul_2.
      destruct x; reflexivity.
    - intros z.
      symmetry.
      apply Z.div2_odd.
    - intros z x x'.
      rewrite div2_double2.
      reflexivity.
  Defined.

  #[refine] Instance lens_div2 : Lens Z Z :=
  {
    proj z := Z.div2 z;
    update z x := Z.double x + Z.b2z (Z.odd z);
  }.
  Proof.
    - intros z x. apply div2_double2.
    - intros z. symmetry. apply Z.div2_odd.
    - intros z x x'. do 2 f_equal. apply odd_double.
  Defined.

  Instance independent_odd_div2 : Independent lens_odd lens_div2.
  Proof.
    split.
    - intros z b. apply div2_double2.
    - intros z x. apply odd_double.
    - intros z b y. simpl.
      rewrite odd_double, div2_double2.
      reflexivity.
  Qed.

  #[refine] Instance bijection_odd_div2 : Bijection_lens (lens_prod independent_odd_div2) :=
    bijection_lens (fun oz => Z.double (snd oz) + Z.b2z (fst oz)) _.
  Proof.
    intros z [o x]. simpl.
    do 2 f_equal.
    rewrite Z.add_comm.
    rewrite Z.double_spec.
    rewrite Z.odd_add_mul_2.
    destruct o; reflexivity.
  Defined.

  Context (n: nat).

  Global Instance lens_bits : Lens Z (Bvector n).
  Proof.
    apply (lens_vector lens_odd lens_div2 n).
  Defined.

  Instance lens_bits' : Lens Z Z.
  Proof.
    apply (lens_vector' lens_div2 n).
  Defined.

  Global Instance independent_bits : Independent lens_bits lens_bits'.
  Proof.
    apply (independent_vector n).
  (** This must be transparent for the definition
      of [bijection_bits] to go through. *)
  Defined.

  Global Instance bijection_bits : Bijection_lens (lens_prod independent_bits).
  Proof.
    apply (bijection_vector bijection_odd_div2).
  Defined.

End bits_section.

Arguments Bsign {_} _.

Section bit_facts_section.

  Open Scope Z.
  Coercion Z.of_nat : nat >-> Z.
  Coercion N.of_nat : nat >-> N.
  Open Scope vector.


  (** ** Helpers *)

  Lemma pow2_equation_0 : 2^0 = 1.
  Proof. reflexivity. Qed.

  Lemma pow2_equation_1 : 2 ^ 0%nat = 1.
  Proof. simpl. exact pow2_equation_0. Qed.

  Lemma pow2_equation_2 n : 2^(S n) = 2 * (2^n).
  Proof.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r.
    - reflexivity.
    - apply Nat2Z.is_nonneg.
  Qed.

  Hint Rewrite
       pow2_equation_0
       pow2_equation_1
       pow2_equation_2 : pow2.

  Lemma pow2_pos (n: nat) : 0 < 2^n.
  Proof.
    apply Z.pow_pos_nonneg.
    - lia.
    - apply Nat2Z.is_nonneg.
  Qed.

  Corollary pow2_nonneg (n : nat) : 0 <= 2^n.
  Proof. apply Z.lt_le_incl, pow2_pos. Qed.


  (** ** Characterizations *)

  Definition toBits n : Z -> Bvector n := proj (Lens:=lens_bits n).

  Proposition toBits_equation_1 z : toBits 0 z = [].
  Proof. reflexivity. Qed.

  Proposition toBits_equation_2 n z :
    toBits (S n) z = Z.odd z :: toBits n (Z.div2 z).
  Proof.
    unfold toBits. simpl.
    simp projN. simpl.
    reflexivity.
  Qed.

  Hint Rewrite
       toBits_equation_1
       toBits_equation_2 : toBits.

  Definition toRest n : Z -> Z := proj (Lens:=lens_bits' n).

  Proposition toRest_equation_1 z : toRest 0 z = z.
  Proof. reflexivity. Qed.

  Proposition toRest_equation_2 n z :
    toRest (S n) z = toRest n (Z.div2 z).
  Proof.
    unfold toRest.
    simpl.
    simp projN'.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite
       toRest_equation_1
       toRest_equation_2 : toRest.

  Lemma toRest_spec n z : toRest n z = z / 2 ^ n.
  Proof.
    revert z. induction n; intros z; simp toRest.
    - symmetry. apply Z.div_1_r.
    - rewrite IHn.
      rewrite Z.div2_div.
      simp pow2.
      rewrite Zdiv_Zdiv.
      + reflexivity.
      + lia.
      + apply pow2_nonneg.
  Qed.

  Definition insta {n} (u:Bvector n) (z: Z) : Z :=
    inverse (Bijection:=bijection_bits n) (u, z).

  Proposition toBits_insta {n} (u: Bvector n) z : toBits n (insta u z) = u.
  Proof. apply projX_inverse. Qed.

  Proposition toRest_insta {n} (u: Bvector n) z : toRest n (insta u z) = z.
  Proof. apply projY_inverse. Qed.

  Proposition insta_equation_1 z : insta [] z = z.
  Proof. unfold insta. reflexivity. Qed.

  Arguments inverseN {_ _ _ _ _ _ _}.

  Proposition insta_equation_2 {n} (b:bool) (u:Bvector n) z :
    insta (b::u) z = Z.double (insta u z) + Z.b2z b.
  Proof.
    unfold insta. simpl. simp inverseN.
    reflexivity.
  Qed.

  Hint Rewrite
       insta_equation_1
       @insta_equation_2 : insta.

  Proposition insta_bijection z {n} (u: Bvector n) z' :
    toBits n z = u /\ toRest n z = z' <-> insta u z' = z.
  Proof.
    transitivity (proj (Lens:=lens_prod (independent_bits n)) z = (u, z')).
    - unfold toBits, toRest. simpl. split.
      + intros [H1 H2]. subst. reflexivity.
      + intros H. inversion H. tauto.
    - apply B_bijection.
  Qed.


  (** ** Update *)

  Lemma insta_spec {n} (u: Bvector n) (z: Z) :
    insta u z = 2^n * z + update 0 u.
  Proof.
    revert u z. induction n; intros u z; depelim u; simp insta pow2.
    - simpl update. simp updateN. lia.
    - simpl update. simp updateN.
      rewrite IHn. simpl update.
      set (x := updateN 0 u).
      rewrite Z.add_assoc.
      f_equal.
      setoid_rewrite Z.double_spec.
      rewrite Z.mul_add_distr_l.
      f_equal.
      + lia.
      + rewrite Z.add_0_r, div2_double.
        reflexivity.
  Qed.

  Corollary update_to_insta0 {n} (u: Bvector n) : update 0 u = insta u 0.
  Proof. rewrite insta_spec. lia. Qed.

  Lemma update_spec {n} (u: Bvector n) (z: Z) :
    update z u = 2^n * (z / 2^n) + insta u 0.
  Proof.
    transitivity (insta u (toRest n z)).
    - unfold insta, toRest.
      apply (B_injective (Bf:=bijection_bits n)).
      setoid_rewrite prod_proj_spec.
      f_equal.
      + rewrite proj_update.
        rewrite <- update_prodX.
        rewrite proj_update.
        reflexivity.
      + rewrite projY_updateX.
        rewrite <- (update_as_inverse z).
        rewrite prod_update_spec.
        rewrite proj_update.
        reflexivity.
    - rewrite insta_spec.
      rewrite toRest_spec.
      rewrite update_to_insta0.
      reflexivity.
  Qed.

  Lemma insta0_nonneg {n} (u: Bvector n) : 0 <= insta u 0.
  Proof.
    induction n; depelim u; simp insta; [lia|].
    apply Z.add_nonneg_nonneg; [|destruct h; simpl; lia].
    specialize (IHn u).
    rewrite Z.double_spec.
    lia.
  Qed.

  Corollary update_nonneg {n} (x : N) (u : Bvector n) : injected N (update (inj x) u).
  Proof.
    rewrite update_spec.
    simpl. decide as H.
    - apply Z.add_nonneg_nonneg;
        [| apply insta0_nonneg].
      apply Z.mul_nonneg_nonneg.
      + apply Z.lt_le_incl, pow2_pos.
      + apply Z.div_pos.
        * apply N2Z.is_nonneg.
        * apply pow2_pos.
    - apply some_is_some.
  Qed.


  (** ** Unsigned *)

  Instance lens_bits_N n : Lens N (Bvector n) :=
    sublens (PX:=prism_N) (LY:=lens_bits n) update_nonneg.

  Definition bitsToN {n} (u: Bvector n) : N := update 0%N u.

  Proposition ofN_bitsToN {n} (u: Bvector n) : Z.of_N (bitsToN u) = insta u 0.
  Proof.
    change Z.of_N with inj.
    rewrite <- update_to_insta0.
    change 0 with (inj 0%N).
    apply inj_prism_update.
  Qed.

  Lemma div2_reflects_lt x y : Z.div2 x < Z.div2 y -> x < y.
  Proof.
    intros H.
    setoid_rewrite Z.div2_odd.
    do 2 destruct (Z.odd _); simpl Z.b2z; lia.
  Qed.

  Lemma insta0_limit {n} (u: Bvector n) : insta u 0 < 2 ^ n.
  Proof.
    induction n; depelim u; simp insta pow2.
    - exact Z.lt_0_1.
    - apply div2_reflects_lt.
      rewrite div2_double2, div2_double.
      apply IHn.
  Qed.

  Corollary bitsToN_limit {n} (u: Bvector n) : (bitsToN u < 2 ^ n)%N.
  Proof.
    apply N2Z.inj_lt.
    rewrite ofN_bitsToN, N2Z.inj_pow. simpl.
    rewrite nat_N_Z.
    apply insta0_limit.
  Qed.

  Proposition double_reflects_lt x y : Z.double x < Z.double y -> x < y.
  Proof. destruct x; destruct y; tauto. Qed.

  Lemma insta_toBits {n:nat} z (H0: 0 <= z) (H1: z < 2 ^ n) :
    insta (toBits n z) 0 = z.
  Proof.
    revert z H0 H1.
    induction n;
      simp pow2;
      intros z H0 H1;
      simp toBits;
      simp insta;
      [ lia | ].
    rewrite IHn.
    - symmetry. apply Z.div2_odd.
    - apply Z.div2_nonneg. exact H0.
    - apply double_reflects_lt.
      rewrite (Z.div2_odd z) in H1.
      setoid_rewrite Z.double_spec.
      destruct (Z.odd z); simpl Z.b2z in H1; lia.
  Qed.

 Corollary bitsToN_proj {n:nat} {x} (Hx: (x < 2 ^ n)%N) :
    bitsToN (proj x : Bvector n) = x.
  Proof.
    apply N2Z.inj.
    rewrite ofN_bitsToN.
    unfold lens_bits_N.
    rewrite prism_proj_spec.
    apply insta_toBits.
    - apply N2Z.is_nonneg.
    - change 2 with (Z.of_N 2%N).
      rewrite <- nat_N_Z, <- N2Z.inj_pow.
      apply N2Z.inj_lt.
      exact Hx.
  Qed.


  (** ** Signed *)

  Definition bitsToZ {n} (u: Bvector (S n)) : Z := insta u (if Bsign u then -1 else 0).

  Proposition toBits_bitsToZ {n} (u: Bvector (S n)) : toBits _ (bitsToZ u) = u.
  Proof. apply toBits_insta. Qed.

  (* "101" = -3 *)
  (* Compute bitsToZ [true; false; true]. *)

  Proposition sign_bitsToZ {n} (u: Bvector (S n)) : bitsToZ u < 0 <-> Bsign u.
  Proof.
    unfold bitsToZ.
    split.
    - destruct (Bsign u); intro H; [apply true_is_true|].
      exfalso.
      apply (Zlt_not_le _ _ H).
      apply insta0_nonneg.
    - induction n.
      + do 2 depelim u.
        simp insta.
        destruct (_:bool); simpl; intro H; lia.
      + depelim u. simpl Bsign. intros Hs. simp insta.
        apply div2_reflects_lt.
        rewrite div2_double2.
        simpl Z.div2.
        exact (IHn u Hs).
  Qed.

End bit_facts_section.


(** * Bytes *)

Notation byte := (Byte.byte).
Notation B8 := (Bvector 8).

Section bytes_section.

  Open Scope vector.
  Open Scope program_scope.

  Equations bytes_to_bits {n} `(vector byte n) : Bvector (n * 8) :=
    bytes_to_bits [] := [];
    bytes_to_bits (b :: r) :=
      match Byte.to_bits b with
        (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) =>
        b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bytes_to_bits r
      end.

  (** Not understood by Equations 1.2.1:
  [[
  Equations bits_to_bytes {n} `(Bvector (n * 8)) : vector byte n :=
    bits_to_bytes [] := [];
    bits_to_bytes (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r) :=
      Byte.of_bits (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) :: bits_to_bytes r.
   ]]
   *)

  Definition bits_to_bytes {n} (u: Bvector (n * 8)) : vector byte n.
  Proof.
    induction n.
    - exact [].
    - simpl in u.
      do 8 depelim u.
      exact (Byte.of_bits (h, (h0, (h1, (h2, (h3, (h4, (h5, h6))))))) :: IHn u).
  Defined.

  Proposition bits_to_bytes_equation_1 : @bits_to_bytes (0 * 8) [] = [].
  Proof. reflexivity. Qed.

  Proposition bits_to_bytes_equation_2 {n} b0 b1 b2 b3 b4 b5 b6 b7 (u: Bvector (n * 8)) :
    @bits_to_bytes (S n) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u) =
    (Byte.of_bits (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) :: bits_to_bytes u).
  Proof. reflexivity. Qed.

  Hint Rewrite bits_to_bytes_equation_1 @bits_to_bytes_equation_2 : bits_to_bytes.

  #[refine] Instance bytes_bijection n : Bijection (@bits_to_bytes n) := { inverse := (@bytes_to_bits n) }.
  Proof.
    all: induction n; intro u.
    1,3: depelim u; reflexivity.
    - do 8 depelim u. simp bits_to_bytes bytes_to_bits.
      rewrite IHn.
      rewrite Byte.to_bits_of_bits.
      reflexivity.
    - depelim u.
      transitivity ((Byte.of_bits (Byte.to_bits h)) :: u);
        [ | f_equal; apply Byte.of_bits_to_bits].
      simp bytes_to_bits.
      set (v := Byte.to_bits h).
      repeat destruct v as [? v].
      simp bits_to_bytes.
      f_equal.
      apply IHn.
  Defined.

End bytes_section.
