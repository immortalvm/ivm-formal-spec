Require Export Equations.Equations.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Export Coq.micromega.Lia.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Vectors.Vector. (** Does not open [vector_scope]. *)
Require Export Coq.Bool.Bvector.
Require Export Coq.Lists.List. (** Opens [list_scope]. *)
Require Export Coq.Program.Basics.
Require Export Coq.Program.Tactics.

Export EqNotations.

(** This clearly does not work properly at the moment. *)
Unset Suggest Proof Using.


(** ** Basics *)

(** The standard library confuses currying and uncurrying. *)
Notation curry := prod_uncurry.
Notation uncurry := prod_curry.


(** ** Tactics *)

Tactic Notation "by_lia" constr(P) "as" ident(H) := assert P as H; [lia|].

Ltac lia_rewrite P :=
  let H := fresh in
  by_lia P as H;
  setoid_rewrite H;
  clear H.

(* TODO: Replace with [apply ... in ...]. *)
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

(** Introduce abstract provable assumption. *)
Tactic Notation "given" constr(P) "as" ident(H) :=
  let T := type of P in
  cut T; [intro H|exact P].

(** From https://github.com/tchajed/coq-tricks. *)
Local Tactic Notation "unfolded_eq" constr(pf) :=
  let x := (eval red in pf) in
  exact (eq_refl : (pf = x)).
Notation unfolded_eq pf := ltac:(unfolded_eq pf) (only parsing).


(** ** Booleans *)

Derive NoConfusion for bool.

Goal true <> false.
Proof.
  intro H.
  exact (noConfusion_inv H).
Qed.

Coercion Is_true : bool >-> Sortclass.

Proposition bool_extensionality (x y : bool) (H: x <-> y) : x = y.
Proof.
  unfold Is_true in H.
  destruct x, y; tauto.
Qed.

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

Proposition is_true_unique {b: bool} (H H': b) : H = H'.
Proof.
  destruct b.
  - destruct H, H'. reflexivity.
  - contradict H.
Qed.

(** See also [Is_true_eq_left], [Is_true_eq_right] and [Is_true_eq_true]. *)

Notation as_bool x := (if x then true else false).


(** ** Decidable propositions *)

(** We are not interested in Vector.eq_dec. *)
Notation eq_dec := (Classes.eq_dec).

Instance Z_EqDec: EqDec Z := Z.eq_dec.
Instance N_EqDec: EqDec N := N.eq_dec.

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

Proposition asBool_decide P {DP: Decidable P} : as_bool (decide P) <-> P.
Proof.
  destruct (decide P) as [H|H].
  - split; intros _; [ exact H | exact I ].
  - cbv.
    split;
      intros HH;
      [ exfalso | apply H ];
      exact HH.
Qed.

(** Eliminate [decide P] when we already know [P]. *)
Ltac decided H :=
  let P := type of H in
  let HH := fresh in
  destruct (decide P) as [HH|HH];
  [ try (clear HH
         || let HHH := fresh in
           set (HHH := is_true_unique HH H);
           subst HH)
  | exfalso; exact (HH H) ].

Section decidable_connectives.

  Context {P} {DP: Decidable P}.

  Global Instance not_decidable : Decidable (not P) :=
    match DP with
    | left H => right (fun f => f H)
    | right H => left H
    end.

  Proposition decidable_raa : ~ ~ P <-> P.
  Proof.
    split.
    - destruct (decide P) as [H|H]; tauto.
    - tauto.
  Qed.

  Context {Q} {DQ: Decidable Q}.

  Notation cases := ltac:(destruct DP; destruct DQ; constructor; tauto)
                           (only parsing).

  Global Instance and_decidable : Decidable (P /\ Q) := cases.
  Global Instance or_decidable : Decidable (P \/ Q) := cases.
  Global Instance impl_decidable : Decidable (P -> Q) := cases.

End decidable_connectives.

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


(* ** Decidable match statements *)

Instance match_decide_decidable {P: Prop} {DP: Decidable P}
         (f: P -> Prop) {Df: forall H, Decidable (f H)}
         (g: not P -> Prop) {Dg: forall H, Decidable (g H)}:
  Decidable match decide P with
            | left H => f H
            | right H => g H
            end.
Proof.
  destruct (decide P) as [H|H].
  - apply Df.
  - apply Dg.
Defined.

Instance match_option_decidable {X}
         (f: X -> Prop) {Df: forall x, Decidable (f x)}
         (Q: Prop) {DQ: Decidable Q}
         {ox: option X} :
  Decidable match ox with
            | Some x => f x
            | None => Q
            end.
Proof.
  destruct ox as [x|].
  - apply Df.
  - exact DQ.
Defined.


(* ** Decidable predicates on integers *)

Instance nat_lt_decidable (x y: nat) : Decidable (x < y) := lt_dec x y.
Instance nat_le_decidable (x y: nat) : Decidable (x <= y) := le_dec x y.

Derive NoConfusion EqDec for comparison.

(** It follows that the comparison operators are decidable for [Z] and [N]. *)

Lemma bounded_decidable0 (P: nat -> Prop) {DP: forall x, Decidable (P x)} (n: nat) :
  {forall x, x < n -> P x} + {exists x, x < n /\ ~ P x}.
Proof.
  induction n as [|n IH].
  - left. lia.
  - destruct IH as [IH|IH].
    + destruct (DP n) as [H|H].
      * left.
        intros x H'.
        -- by_lia (x < n \/ x = n) as H''.
           destruct H'' as [H''|H''].
           ++ exact (IH x H'').
           ++ subst x. exact H.
      * right. exists n. split; [lia | exact H].
    + right. destruct IH as [x [Hx Hp]]. exists x. split; [lia | exact Hp].
Defined.

Instance bounded_all_decidable0 (P: nat -> Prop) {DP: forall x, Decidable (P x)} (n: nat) :
  Decidable (forall x, x < n -> P x).
Proof.
  destruct (bounded_decidable0 P n) as [H|H].
  - left. exact H.
  - right. intro H'. destruct H as [x [Hx Hp]].
    exact (Hp (H' x Hx)).
Qed.

Instance bounded_ex_decidable0 (P: nat -> Prop) {DP: forall x, Decidable (P x)} (n: nat) :
  Decidable (exists x, x < n /\ P x).
Proof.
  destruct (bounded_decidable0 (fun x => ~ P x) n) as [H|H].
  - right. intros [x [Hx Hp]]. exact (H x Hx Hp).
  - left.
    setoid_rewrite decidable_raa in H.
    exact H.
Qed.

Lemma bounded_ex_succ (P: nat -> Prop) n :
  (exists i, i < S n /\ P i) <-> P n \/ (exists i, i < n /\ P i).
Proof.
  split.
  - intros [i [Hi Hp]].
    by_lia (i = n \/ i < n) as H.
    destruct H.
    + destruct H. left. exact Hp.
    + right. exists i. split; assumption.
  - intros [H | [i [Hi Hp]]].
    + exists n. split.
      * lia.
      * exact H.
    + exists i. split.
      * lia.
      * exact Hp.
Qed.

(** Clearly, [N] has the same properties. *)

Local Open Scope N.

Instance bounded_all_decidable0' (P: forall (x:N), Prop) {DP: forall x, Decidable (P x)} (n: N) :
  Decidable (forall x, x < n -> P x).
Proof.
  (* TODO: Derive from results above instead. *)
  destruct (decide (forall y, (y < N.to_nat n)%nat -> P (N.of_nat y))) as [H|H]; [left|right].
  - intros x Hx. specialize (H (N.to_nat x)).
    rewrite Nnat.N2Nat.id in H.
    apply H, nat_compare_lt.
    rewrite <- Nnat.N2Nat.inj_compare.
    exact Hx.
  - intro H'. apply H. clear H.
    intros y Hy.
    apply H'.
    unfold N.lt.
    rewrite Nnat.N2Nat.inj_compare, Nnat.Nat2N.id.
    apply nat_compare_lt.
    exact Hy.
Defined.

(** We also have a slightly stronger property. *)

Instance bounded_all_decidable1
           (n: N) (P: forall (x: N), x < n -> Prop)
           {DP: forall x (H: x < n), Decidable (P x H)} : Decidable (forall x (H: x < n), P x H).
Proof. (* TODO: simplify? *)
  assert (forall x, Decidable (forall (H: x < n), P x H)) as D.
  - intros x.
    destruct (decide (x < n)) as [H|H].
    + destruct (DP x H) as [Hd|Hd].
      * left. intros H'. rewrite (uip H' H). assumption.
      * right. contradict Hd. apply (Hd H).
    + left. intros H'. contradict H. exact H'.
  - destruct (bounded_all_decidable0' (fun x => forall (H: x < n), P x H) n) as [H|H];
      [left|right]; firstorder.
Qed.

(** In order to prove the corresponding property for [nat], we seem to need
an axiom or a different definition of [nat.le] than the one in the current
standard library, cf. "Definitional Proof-Irrelevance without K" (2019). *)


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
  induction n.
  - dependent elimination u.
    dependent elimination v.
    reflexivity.
  - dependent elimination u as [(x :: u)%vector].
    dependent elimination v as [(y :: v)%vector].
    simp to_list. intro Heq.
    f_equal; [|apply (IHn u v)]; congruence.
Qed.

Lemma length_to_list {A n} (v: vector A n) : length (to_list v) = n.
Proof.
  depind v.
  - reflexivity.
  - simp to_list. simpl length. rewrite IHv. reflexivity.
Qed.

(* Coercion Vector.to_list : vector >-> list. *)


(** ** Relations *)

Section relation_section.

  Context {X} {R: relation X}.

  (* Making this global would likely ruin proof search. *)
  Instance eq_subrelation {HR: Reflexive R} : subrelation eq R.
  Proof. intros x x' Hx. subst x. reflexivity. Qed.

End relation_section.

(** *** Inverse image **)

Section irel_section.

  Context {X Y} (f: X -> Y) (R: relation Y).

  Definition irel : relation X := fun x x' => R (f x) (f x').

  Global Instance irel_reflexive {HR: Reflexive R} : Reflexive irel.
  Proof. unfold irel. intros x. reflexivity. Qed.

  Global Instance irel_symmetric {HR: Symmetric R} : Symmetric irel.
  Proof. unfold irel. intros x y H. symmetry. exact H. Qed.

  Global Instance irel_transitive {HR: Transitive R} : Transitive irel.
  Proof. unfold irel. intros x y z Hxy Hyz. transitivity (f y); assumption. Qed.

  Global Instance irel_equivalence {HR: Equivalence R} : Equivalence irel.
  Proof. split; typeclasses eauto. Qed.

End irel_section.


(** ** Various *)

Coercion N.of_nat : nat >-> N.
Coercion Z.of_N : N >-> Z.

(** Defines [∘] *)
Open Scope program_scope.
