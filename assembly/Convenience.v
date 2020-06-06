Require Import Equations.Equations.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.micromega.Lia.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Vectors.Vector. (** Does not open [vector_scope]. *)
Require Export Coq.Bool.Bvector.
Require Export Coq.Lists.List. (** Opens [list_scope]. *)

Export EqNotations.

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

(** Borrowed from http://ropas.snu.ac.kr/gmeta/source/html/LibTactics.html. *)
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

Coercion is_true : bool >-> Sortclass.

Proposition is_true_true : is_true true.
Proof. exact eq_refl. Qed.

Proposition not_is_true_false : is_true false -> False.
Proof. intro H. exact (noConfusion_inv H). Qed.

Lemma is_true_def (b: bool) : b <-> if b then True else False.
Proof.
  split; intro H.
  - destruct b; exact (noConfusion_inv H).
  - destruct b; [reflexivity|exfalso; exact H].
Qed.

(** Cf. https://github.com/coq/coq/wiki/StandardLibrary#user-content-is_true-vs-true *)
Inductive is_true_prop : bool -> Prop := is_true_prop_true : is_true_prop true.

Lemma is_true_ind (b: bool) : b <-> is_true_prop b.
Proof.
  split; intro H.
  - destruct b.
    + constructor.
    + exfalso. exact (noConfusion_inv H).
  - destruct H. reflexivity.
Qed.

Notation as_bool x := (if x then true else false).


(** ** Decidable *)

Class Decidable (P: Prop) : Type :=
  decide : { P } + { not P }.

Arguments decide P {_}.

Instance True_decidable : Decidable True := left I.
Instance False_decidable : Decidable False := right (@id False).
Instance equality_decidable {A} `{dec: EqDec A} (x y: A) : Decidable (x = y) := dec x y.
Instance is_true_decidable (x: bool) : Decidable (is_true x) := equality_decidable x true.

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

Proposition is_some_true {X} (ox: option X) : ox -> ox = true :> bool.
Proof. exact id. Qed.

Proposition is_some_some {X} (x: X) : Some x.
Proof. exact is_true_true. Qed.

Proposition not_is_some_none {X} : @None X -> False.
Proof. exact not_is_true_false. Qed.

(** Shortcut *)
Definition none_not_some {X Y} (H: @None X) : Y :=
  False_rect Y (not_is_some_none H).

Definition extract {X} {ox: option X} : ox -> X :=
  match ox return ox -> X with
  | Some x => fun _ => x
  | None => fun H => none_not_some H
  end.

Proposition extract_some {X} (x: X) : extract (is_some_some x) = x.
Proof. reflexivity. Qed.

Lemma some_extract {X} {ox: option X} (H: ox) : Some (extract H) = ox.
Proof.
  destruct ox as [x|].
  - simpl. reflexivity.
  - exact (none_not_some H).
Qed.

Proposition is_some_eq {X} {ox: option X} {x: X} : ox = Some x -> ox.
Proof. intro H. rewrite H. reflexivity. Qed.

Proposition extract_is_some_eq {X} {ox: option X} {x: X} (H: ox = Some x) : extract (is_some_eq H) = x.
Proof. subst ox. reflexivity. Qed.

Proposition extract_unique {X} {ox: option X} (H H': ox) : extract H = extract H'.
Proof.
  destruct ox as [x|].
  - reflexivity.
  - exact (none_not_some H).
Qed.


(** * Lenses *)

Class Lens (S: Type) (X: Type) :=
{
  proj: S -> X;
  update: S -> X -> S;
  proj_update (s: S) (x: X) : proj (update s x) = x;
  update_proj (s: S) : update s (proj s) = s;
  update_update (s: S) (x: X) (x': X) : update (update s x) x' = update s x';
}.

Create HintDb proj discriminated.
Hint Rewrite @proj_update using (typeclasses eauto) : proj.
Hint Rewrite @update_proj using (typeclasses eauto) : proj.
Hint Rewrite @update_update using (typeclasses eauto) : proj.
Ltac lens_rewrite1 := rewrite_strat (outermost (hints proj)).
Ltac lens_rewrite := repeat lens_rewrite1.


(** ** Complete lenses

I am not sure if there is an established term for this. *)

Section complete_section.

  Context {A X} (LX: Lens A X).

  Class Complete :=
  {
    install : X -> A;
    update_installs a x : update a x = install x;
  }.

  Context {CX: Complete}.

  Proposition install_proj (a: A) : install (proj a) = a.
  Proof.
    rewrite <- (update_installs a (proj a)).
    apply update_proj.
  Qed.

  Corollary proj_injective (a a': A) : proj a = proj a' -> a = a'.
  Proof.
    intros H.
    setoid_rewrite <- install_proj.
    f_equal.
    exact H.
  Qed.

End complete_section.


(** ** Lens monoid

This is not something we actually use.
TODO: Remove? *)

Section lens_monoid_section.

  Context (A : Type).

  Program Instance lens_id : Lens A A :=
  {
    proj := id;
    update _ := id;
  }.

  Program Instance complete_id : Complete lens_id :=
  {
    install := id;
  }.

  Context {X} (PX: Lens A X).
  Context {Y} (PY: Lens X Y).

  #[refine] Instance lens_composite : Lens A Y :=
  {
    proj a := proj (proj a);
    update a y := update a (update (proj a) y);
  }.
  Proof.
    all: intros; lens_rewrite; reflexivity.
  Defined.

  Context {CX: Complete PX} {CY: Complete PY}.

  #[refine] Instance complete_composite : Complete lens_composite :=
  {
    install x := install (install x);
  }.
  Proof.
    intros a y. simpl.
    do 2 setoid_rewrite update_installs.
    reflexivity.
  Defined.

End lens_monoid_section.

(** This is clearly a monoid up to funcitonal extensionality. *)


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

  (** We do not make this global sine together with [independent_commute]
      it can send [typeclasses eauto] into an infinite loop. *)
  Instance independent_symm {A X Y}
           {LX: Lens A X} {LY: Lens A Y} (HI: Independent LX LY) : Independent LY LX.
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

  Context {CP: Complete lens_prod}.

  Local Ltac update_prod_tac a :=
    apply (proj_injective (CX:=CP));
    rewrite <- (update_installs a);
    rewrite proj_update;
    simpl;
    rewrite proj_update;
    independent_rewrite1;
    reflexivity.

  Let update_prodX (a: A) (x: X) : update a x = install (x, proj a).
  Proof. update_prod_tac a. Qed.

  Let update_prodY (a: A) (y: Y) : update a y = install (proj a, y).
  Proof. update_prod_tac a. Qed.

  Lemma update_proj_swap (a a' : A) :
    update a' (proj a : X) = update a (proj a' : Y).
  Proof. rewrite update_prodX, update_prodY. reflexivity. Qed.

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

Hint Rewrite @to_list_equation_1 : to_list.
Hint Rewrite @to_list_equation_2 : to_list.

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
  Arguments update {_} {_} _ _ _.

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

  Context (CP: Complete (lens_prod IXA)).
  Existing Instance lens_prod.

  Equations installN {n} `(vector X n) `(A) : A :=
    installN (n:=S n) (x :: r) a := install (x, installN r a);
    installN _ a := a.

  #[refine] Global Instance complete_vector n : Complete (lens_prod (independent_vector n)) :=
  {
    install va := installN (fst va) (snd va);
  }.
  Proof.
    intros a [v a']. simpl. revert a v a'.
    induction n as [|n IH]; intros a v a'; depelim v; simp installN.
    - reflexivity.
    - simp updateN' updateN.
      independent_rewrite.
      lens_rewrite.
      rewrite IH.
      rewrite <- (update_installs a).
      simpl.
      independent_rewrite1.
      reflexivity.
  Qed.

End lens_vector_section.

Arguments lens_vector : clear implicits.
Arguments lens_vector {_} {_} _ _ {_} _.

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

Arguments injected_some {_} {_} {_} {_} {_}.

Section prism_basics_section.

  Context A {X} (PX: Prism X A).

  Lemma inj_extract a (H: injected a) : inj (extract H) = a.
  Proof.
    destruct (injected a) as [x|] eqn:Ha.
    - apply injected_some. exact Ha.
    - exact (none_not_some H).
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

  Program Instance inj_id : Prism A A :=
  {
    inj := id;
    injected := Some;
  }.

  (** This, too, is clearly a monoid up to functional extensionality. *)

End prism_basics_section.

Arguments inj_extract {_} {_} {_} {_} _.
Arguments inj_is_injected {_} {_} {_} _.
Arguments extract_inj {_} {_} {_} _.
Arguments inj_injective {_} {_} {_} {_} {_} _.
Arguments inj_composition {_} {_} _ {_} _.

(** From now on make [X] explicit for clarity. *)
Arguments injected : clear implicits.
Arguments injected _ {_} {_} _.


(** ** Disjoint prisms *)

Class Disjoint {X Y A} (PX: Prism X A) (PY: Prism Y A) : Prop :=
{
  injectedY_injX (x: X) : injected Y (inj x) = None;
  injectedX_injY (y: Y) : injected X (inj y) = None;
}.

Arguments injectedY_injX {_} {_} {_} {_} {_} {_} _.
Arguments injectedX_injY {_} {_} {_} {_} {_} {_} _.

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
      exact (not_is_some_none Hy).
    - intros H.
      split.
      + intros x.
        specialize (H (inj x)).
        destruct (injected Y (inj x)).
        exfalso.
        apply H.
        * apply inj_is_injected.
        * apply is_some_some.
        * reflexivity.
      + intros y.
        specialize (H (inj y)).
        destruct (injected X (inj y)).
        exfalso.
        apply H.
        * apply is_some_some.
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
  destruct (decide _) as [H|H]; unfold is_some, is_true.
  - tauto.
  - split; intro HH; exfalso.
    * exact (noConfusion_inv HH).
    * exact (H HH).
Qed.


(** ** Prism lenses *)

Section prism_lens_section.

  Context {X A Y} {PX: Prism X A} {LY: Lens A Y}.

  Context (H: forall x y, injected X (update (inj x) y)).

  #[refine] Instance lens_prism : Lens X Y :=
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

  Proposition inj_prism_update x y : inj (update x y) = update (inj x) y.
  Proof.
    simpl. rewrite inj_extract. reflexivity.
  Qed.

End prism_lens_section.


(** ** Bits *)

Section bits_section.

  Lemma pos_pred_double_z (x: positive) : Zpos (Pos.pred_double x) = (2 * (Zpos x) - 1)%Z.
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

  #[refine] Instance lens_odd : Lens Z bool :=
  {
    proj z := Z.odd z;
    update z b := (Z.double (Z.div2 z) + Z.b2z b)%Z;
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
    update z x := (Z.double x + Z.b2z (Z.odd z))%Z;
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
  Qed.

  Definition toBits z := @proj _ _ lens_bits z.

End bits_section.

(* Compute (toBits 4 7). *)
(* Compute (toBits 4 (-7)). *)


(** ** Signed and unsigned *)

Arguments Bsign {_} _.

Section sign_section.

  Open Scope Z.
  Open Scope vector.
  Opaque Z.mul.


  (** *** Specs *)

  Proposition toBits_equation_1 z : toBits 0 z = [].
  Proof. reflexivity. Qed.

  Proposition toBits_equation_2 n z :
    toBits (S n) z = Z.odd z :: toBits n (Z.div2 z).
  Proof.
    unfold toBits. simpl.
    simp projN. simpl.
    reflexivity.
  Qed.

  Hint Rewrite toBits_equation_1 : toBits.
  Hint Rewrite toBits_equation_2 : toBits.

  Proposition two_power_nat_equation_1 : two_power_nat 0 = 1.
  Proof. reflexivity. Qed.

  Proposition two_power_nat_equation_2 n : two_power_nat (S n) = Z.double (two_power_nat n).
  Proof. reflexivity. Qed.

  Hint Rewrite two_power_nat_equation_1 : two_power_nat.
  Hint Rewrite two_power_nat_equation_2 : two_power_nat.

  Proposition two_power_nat_nonneg n : 0 < two_power_nat n.
  Proof.
    induction n; simp two_power_nat. exact Z.lt_0_1.
  Qed.

  Lemma div2_reflects_lt x y : Z.div2 x < Z.div2 y -> x < y.
  Proof.
    intros H.
    setoid_rewrite Z.div2_odd.
    do 2 destruct (Z.odd _); simpl; lia.
  Qed.

  Definition modPow2 n z := Z.land z (Z.ones (Z.of_nat n)).

  Proposition modPow2_spec n z : modPow2 n z = z mod two_power_nat n.
  Proof.
    unfold modPow2. rewrite Z.land_ones, two_power_nat_equiv.
    - reflexivity.
    - apply Nat2Z.is_nonneg.
  Qed.

  (* TODO: needed? *)
  Proposition double_shiftl z : Z.double z = Z.shiftl z 1.
  Proof. reflexivity. Qed.

  Proposition modPow2_equation_1 z : modPow2 0 z = 0.
  Proof. destruct z; reflexivity. Qed.

  Compute Z.land 8 (-2).

  Lemma itest z : z = Z.lor (Z.land z (-2)) (Z.land z 1).
  Proof.
    apply Z.bits_inj.
    intro n.
    rewrite Z.lor_spec.
    destruct n.
    -
(*******************)


  Proposition modPow2_equation_2 n z :
    modPow2 (S n) z = Z.double (modPow2 n (Z.div2 z)) + Z.b2z (Z.odd z).
  Proof.
    unfold modPow2.
    rewrite <- Z.bit0_odd.
    rewrite double_shiftl.
    rewrite Z.shiftl_land.

    Compute Z.shiftl (-2) 4.


  Lemma modPow2_lemma n z : modPow2 n (Z.div2 z) = Z.div2 (modPow2 (S n) z).
  Proof.
    unfold modPow2.
    simp two_power_nat.
    set (p := two_power_nat n).

    Z_div_mod_eq
    div2_double2

  Proposition modPow2_equation_2 n z :
    modPow2 (S n) z = Z.double (modPow2 n (Z.div2 z)) + Z.b2z (Z.odd z).
  Proof.
    unfold modPow2. simp two_power_nat.
    unfold Z.b2z. rewrite <- Zmod_odd.
    setoid_rewrite Z.double_spec at 2.

    rewrite Z.div2_div.


    set (x := Z.div2 z mod two_power_nat n).
    assert (z mod 2 = x mod 2) as Hx.
    - subst x.


    rewrite Z_div_mod_eq.


  Definition domPow2 n z := two_power_nat n * (z / two_power_nat n).

  (* TODO: change to corollary below *)
  Proposition mod_dom_id n z : z = domPow2 n z + modPow2 n z.
  Proof.
    unfold domPow2, modPow2.
    apply Z_div_mod_eq, Z.lt_gt, two_power_nat_nonneg.
  Qed.

  Lemma update_bits_spec n z z' : update z (toBits n z') = domPow2 n z + modPow2 n z'.
  Proof.
    unfold domPow2, modPow2. simpl.
    revert z z'.
    induction n as [|n IH]; intros z z'; simp toBits updateN two_power_nat.
    - rewrite Z.mul_1_l, Z.div_1_r, Zmod_1_r, Z.add_0_r. reflexivity.
    - rewrite IH. clear IH.
      set (p := two_power_nat n) in *.
      match goal with
        |- update ?x ?y = _ =>
        set (xx:=x); set (yy:=y); simpl update; subst xx; subst yy
      end.
      rewrite

      rewrite Z.mul_add_distr_l.
              Z.mul_assoc,
              <- Z.add_assoc.


      .

      unfold update at 1.
      simpl.

.
      simp projN.


  Local Notation collapse n z := (@proj _ _ (lens_bits' n) z).

  Lemma proj_spec' n z : collapse n z = z / two_power_nat n.
  Proof.
    simpl. revert z. induction n as [|n IH]; intros z; simp projN'.
    - auto with zarith.
    - simpl. rewrite IH. simp two_power_nat.
      rewrite Z.div2_div.
      unfold two_power_nat.
      apply Zdiv_Zdiv; auto with zarith.
  Qed.

  Corollary proj_spec {n z} : collapse n z = z / 2 ^ Z.of_nat n.
  Proof.
    rewrite <- two_power_nat_equiv.
    apply proj_spec'.
  Qed.

  Local Notation upd n z z' := (@update _ _ (lens_bits' n) z z').

  Lemma upd_spec' n z z' : upd n z z' = (two_power_nat n) * z' + z mod (two_power_nat n).
  Proof. (* TODO: Simplify *)
    simpl upd; revert z z'.
    induction n as [|n IH]; intros z z'; simp updateN' two_power_nat.
    - rewrite Zmod_1_r. auto with zarith.
    - rewrite IH. clear IH. simpl update.
      rewrite Z.double_spec,
              Z.mul_add_distr_l,
              Z.mul_assoc,
              <- Z.add_assoc.
      f_equal.
      rewrite <- (Zmod_small (_ + _) (2 * two_power_nat n)).
      + rewrite <- Zmult_mod_distr_l,
                Zplus_mod,
                Zmod_mod,
                <- Zplus_mod,
                <- Z.div2_odd.
        reflexivity.
      + split.
        * apply Ztac.add_le.
          -- apply Z.mul_nonneg_nonneg.
             ++ lia.
             ++ apply Z.mod_pos_bound, two_power_nat_nonneg.
          -- destruct Z.odd; simpl; auto with zarith.
        * apply div2_reflects_lt.
          setoid_rewrite <- Z.double_spec.
          rewrite div2_double, div2_double2.
          apply Z.mod_pos_bound, two_power_nat_nonneg.
  Qed.

  Transparent Z.mul.

  Lemma upd_toBits n z z' : update z (toBits n z') = upd n z' (collapse n z).
  Proof.
    unfold toBits. simpl.
    apply updateX_projY.


  Lemma update_proj_mod {n} {z} {z'}: update z (toBits n z')
                                      = two_power_nat n * (collapse n z)
                                        +
  .


  Definition synthesize {n} (u: Bvector n) (z: Z) : Z :=



  Local Coercion Z.of_nat : nat >-> Z.

  Local Opaque Z.pow.

  Lemma proj_spec {n z} : collapse n z = z / 2 ^ n.
  Proof.
    simpl. revert z. induction n as [|n IH]; intros z; simp projN'.
    - auto with zarith.
    - simpl. rewrite IH.
      rewrite Z.div2_div.
      rewrite Z.pow_add_r.

      , two_power_nat_S.
      apply Zdiv_Zdiv;
        unfold two_power_nat;
        auto with zarith.




Set Printing Implicit.
rewrite IH.


      auto with zarith.
reflexivity.








  (** *** Unsigned *)

  Lemma proj_positive n {z} : 0 <= z -> 0 <= proj (Lens:=lens_bits' n) z.
  Proof.
    simpl.
    revert z.
    induction n as [|n IH].
    - simp projN'.
    - intros z Hz. simp projN'. simpl.
      apply (IH (Z.div2 z)), Z.div2_nonneg.
      exact Hz.
  Qed.

  Lemma update_nonneg {n} (u: Bvector n) {z} : 0 <= z -> 0 <= update z u.
  Proof.
    simpl. revert u z.
    induction n as [|n IH]; intros u; depelim u; intros z Hz; simp updateN.
    remember (proj_positive 1 Hz) as Hz' eqn:Hez'. clear Hez'.
    remember (proj _) as z' eqn:Hez. clear Hez.
    specialize (IH u z' Hz').
    remember (updateN z' _) as z'' eqn:Hez''. clear Hez''.
    simpl.
    rewrite Z.div2_div, Z.double_spec, Z.double_spec at 1.
    clear n u z' Hz Hz'.
    apply Z.add_nonneg_nonneg.
    - destruct (Z.odd z); simpl Z.b2z;
        clear z;
        (apply Ztac.mul_le; [|apply Z.div_pos]; lia).
    - destruct h; simpl Z.b2z; lia.
  Qed.

  Local Opaque update.

  Corollary update_nonneg' {n} (x : N) (u : Bvector n) : injected N (update (inj x) u).
  Proof.
    simpl. decide as H.
    - apply update_nonneg, N2Z.is_nonneg.
    - apply is_some_some.
  Defined.

  Local Transparent update.

  Instance lens_bits_N n : Lens N (Bvector n) :=
    lens_prism (PX:=prism_N) (LY:=lens_bits n) update_nonneg'.

  Definition bitsToN {n} (u: Bvector n) : N := update 0%N u.

  Proposition ofN_bitsToN {n} (u: Bvector n) : Z.of_N (bitsToN u) = update 0 u.
  Proof.
    change Z.of_N with inj.
    change 0 with (inj 0%N).
    apply inj_prism_update.
  Qed.

  Lemma update_upper_limit {n} (u: Bvector n) : update 0 u < two_power_nat n.
  Proof. (* TODO: simplify? *)
    induction n as [|n IH].
    - cbv. simp updateN. reflexivity.
    - depelim u.
      simpl update.
      simp updateN.
      simpl update.
      rewrite Z.div2_div, Z.double_spec, Z.double_spec at 1.
      rewrite Z.add_0_r.
      specialize (IH u).
      simpl in IH.
      set (z := updateN 0 u) in *.
      revert IH.
      generalize z.
      clear u z.
      intros z H.
      rewrite two_power_nat_S.
      destruct h; simpl Z.b2z;
        [apply Z.double_above
        |rewrite Z.add_0_r; apply Zmult_lt_compat_l; [lia|]];
        (rewrite Z.mul_comm, Z_div_mult; [exact H|lia]).
  Qed.

  Corollary bitsToN_limit {n} (u: Bvector n) : (bitsToN u < 2 ^ N.of_nat n)%N.
  Proof.
    apply N2Z.inj_lt.
    rewrite ofN_bitsToN, N2Z.inj_pow. simpl.
    rewrite nat_N_Z, <- two_power_nat_equiv.
    apply update_upper_limit.
  Qed.

  Proposition double_compare z z' : (Z.double z ?= Z.double z') = (z ?= z').
  Proof.
    destruct z; destruct z'; simpl; reflexivity.
  Qed.

  Corollary double_strict z z' : Z.double z < Z.double z' <-> z < z'.
  Proof.
    unfold Z.lt.
    rewrite double_compare.
    tauto.
  Qed.

  Lemma two_power_nat_div2 {n z} : z < two_power_nat (S n)
                                 -> Z.div2 z < two_power_nat n.
  Proof.
    rewrite two_power_nat_S.
    intros H.
    apply double_strict.
    refine (Z.le_lt_trans _ z _ _ H).
    setoid_rewrite Z.div2_odd at 4.
    rewrite <- Z.double_spec at 1.
    destruct (Z.odd z); simpl Z.b2z; lia.
  Qed.

  Local Opaque Z.lt Z.pow.

  Lemma bits_id {n z} (H0: 0 <= z) (H1: z < two_power_nat n) :
    update 0 (proj z : Bvector n) = z.
  Proof.
    simpl. revert z H0 H1.
    induction n as [|n IH]; intros z H0 H1.
    - cbv in H1. by_lia (z = 0) as Hz. subst z. reflexivity.
    - rewrite two_power_nat_S in H1.
      simp projN updateN. simpl.
      change 0 with (Z.b2z false) at 2.
      rewrite div2_double.
      specialize (IH (Z.div2 z)).
      specialize (IH (proj2 (Z.div2_nonneg _) H0)).
      specialize (IH (two_power_nat_div2 H1)).
      rewrite IH.
      symmetry.
      apply Z.div2_odd.
  Qed.

  Local Transparent Z.lt Z.pow.

 Corollary bitsToN_id {n x} (Hx: (x < 2 ^ N.of_nat n)%N) :
    bitsToN (proj x : Bvector n) = x.
  Proof.
    apply N2Z.inj.
    rewrite ofN_bitsToN.
    simpl proj.
    apply bits_id.
    - apply N2Z.is_nonneg.
    - rewrite two_power_nat_equiv.
      change 2 with (Z.of_N 2%N).
      rewrite <- nat_N_Z.
      rewrite <- N2Z.inj_pow.
      apply N2Z.inj_lt.
      exact Hx.
  Qed.


  (** *** Signed *)

  Local Opaque Z.mul Z.add.

  Definition signOffset {n} (u: Bvector (S n)) : Z :=
    update (Lens := lens_bits' n)
           0
           (if (Bsign u) then -1 else 0).

  Open Scope vector.

  Lemma signOffset_equation_1 b : signOffset [b] = - Z.b2z b.
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma signOffset_equation_2 {n} b {u: Bvector (S n)} : signOffset (b :: u) = 2 * signOffset u.
  Proof.
    unfold signOffset.
    simpl.
    generalize (if Bsign u then -1 else 0).
    clear u b.
    intros z.
    simp updateN'.
    simpl.
    rewrite Z.double_spec.
    lia.
  Qed.

  Hint Rewrite signOffset_equation_1 : signOffset.
  Hint Rewrite @signOffset_equation_2 : signOffset.

  Local Opaque Z.opp.

  Corollary signOffset_spec {n} (u: Bvector (S n)) :
    signOffset u = if Bsign u then - two_power_nat n else 0.
  Proof.
    induction n as [|n IH].
    - do 2 depelim u. simpl. simp signOffset.
      destruct h; reflexivity.
    - depelim u. simpl. simp signOffset.
      rewrite two_power_nat_S.
      rewrite (IH u).
      clear h IH.
      destruct (Bsign u); lia.
  Qed.

  Definition bitsToZ {n} (u: Bvector (S n)) : Z := update (signOffset u) u.

  (* "101" = -3 *)
  (* Compute bitsToZ [true; false; true]. *)

  Proposition proj_bitsToZ {n} (u: Bvector (S n)) : proj (bitsToZ u) = u.
  Proof.
    unfold bitsToZ.
    rewrite proj_update.
    reflexivity.
  Qed.

  (* TODO: move up *)
  Proposition not_is_true {b: bool} : not b -> b = false.
  Proof.
    destruct b.
    - intros H. contradict H. exact is_true_true.
    - reflexivity.
  Qed.

  Proposition positive_correspondence {n} (u: Bvector (S n)) :
    not (Bsign u) -> bitsToZ u = Z.of_N (bitsToN u).
  Proof.
    intros H.
    derive H (not_is_true H).
    unfold bitsToZ.
    rewrite signOffset_spec.
    rewrite H.
    symmetry.
    apply ofN_bitsToN.
  Qed.



    unfold bitsToN.


  Proposition sign_bitsToZ {n} (u: Bvector (S n)) : (bitsToZ u) < 0 <-> Bsign u.
  Proof.
    induction n as [|n IH].
    - depelim u. depelim u.
      unfold bitsToZ, signOffset.
      destruct h.

      cbn.

      destruct h; cbv. ; simp updateN updateN'.
      + tauto.
      + split; congruence.

    - depelim u.
      simp signOffset. simpl Bsign.
      rewrite <- IH. lia.


    unfold bitsToZ.
    rewrite <- sign_signOffset.
    destruct (Bsign u).
    - simpl.
      depind u.





End





(*******************)


(** ** Bytes *)

Notation B8 := (Bvector 8).

Section bytes_section.

  Context (n: nat).

  Global Instance lens_bytes : Lens Z (vector B8 n).
  Proof.
    apply (lens_vector (lens_bits 8) (lens_bits' 8) n).
  Defined.

  Instance lens_bytes' : Lens Z Z.
  Proof.
    apply (lens_vector' (lens_bits' 8) n).
  Defined.

  Global Instance independent_bytes : Independent lens_bytes lens_bytes'.
  Proof.
    apply (independent_vector n).
  Qed.

End bytes_section.

Definition toBytes n z := @proj _ _ (lens_bytes n) z.

(* Compute (toBytes 2 8192). *)
