Require Import Utf8.

Require Import Equations.Equations.
Require Export Coq.Lists.List.
Require Export Coq.ZArith.ZArith.
Require Export Coq.micromega.Lia.

Require Import Coq.Bool.Sumbool.


(** ** Decidable propositions *)

Class Decidable (P: Prop) : Type :=
  decision : { P } + { not P }.

Arguments decision P {_}.

Instance True_decidable : Decidable True := left I.
Instance False_decidable : Decidable False := right (@id False).
Instance equality_decidable {A} `{dec: EqDec A} (x y: A) : Decidable (x = y) := dec x y.
Instance is_true_decidable (x: bool) : Decidable (is_true x) := equality_decidable x true.

Section option_section.

  Context {A} (x: option A).

  Instance is_none_decidable : Decidable (x = None).
  Proof.
    destruct x as [y|]; [right|left]; congruence.
  Defined.

  Definition is_some : Prop := if x then True else False.

  Global Instance is_some_decidable : Decidable is_some.
  Proof.
    unfold is_some. destruct x as [y|]; [left|right]; easy.
  Defined.

End option_section.

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


Tactic Notation "by_lia" constr(P) "as" ident(H) := assert P as H; [lia|].

Definition bounded_all_decidable0 (P: forall (x: nat), Prop) `{DP: forall x, Decidable (P x)} (n: nat) : Decidable (forall x, x < n -> P x).
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
      * right. contradict H. apply H. lia.
    + right. contradict IH. intros x H. apply IH. lia.
Defined.

Existing Instance bounded_all_decidable0.

(** Presumably, this instance of proof irrelevance will be provable when
the Coq standard library has been rehauled, cf. the article "Definitional
Proof-Irrelevance without K" (2019). *)
Axiom le_proofs_unique : forall {m n: nat} (H1 H2: m <= n), H1 = H2.

Definition bounded_all_decidable1
           (n: nat) (P: forall (x: nat), x < n -> Prop)
           `{DP: forall x (H: x < n), Decidable (P x H)} : Decidable (forall x (H: x < n), P x H).
Proof.
  assert (forall x, Decidable (forall (H: x < n), P x H)) as D.
  - intros x.
    destruct (decision (x < n)) as [H|H].
    + destruct (DP x H) as [Hd|Hd].
      * left.
        intros H'.
        elim le_proofs_unique with H H'.
        assumption.
      * right.
        contradict Hd.
        apply (Hd H).
    + left.
      intros H'.
      exfalso.
      exact (H H').
  - destruct (bounded_all_decidable0 (fun x => forall (H: x < n), P x H) n) as [H|H];
      [left|right]; firstorder.
Defined.

Existing Instance bounded_all_decidable1.
