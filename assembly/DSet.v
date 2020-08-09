From Assembly Require Import Init.

Unset Suggest Proof Using.


(** Decidable subsets can be represented using Boolean predicates. This is
essentially a simplified formalization of "prisms", i.e. a dual lenses. *)

Section DSet_section.

  (** Alas, the scope and notations must be repeated after the section.*)

  Context {X: Type}.

  Definition DSet := X -> bool.

  Declare Scope DSet_scope.
  Bind Scope DSet_scope with DSet.
  Delimit Scope DSet_scope with DSet.


  (** *** Membership and subsets *)

  Definition member x (u: DSet) : Prop := u x.
  Infix "∈" := member (at level 70) : type_scope.

  (* TODO: Is it better to leave this implicit? *)
  Global Instance member_decidable x u : Decidable (member x u).
  Proof.
    typeclasses eauto.
  Qed.

  Proposition extensionality u v (H: forall x, x ∈ u <-> x ∈ v) : u = v.
  Proof.
    extensionality x.
    apply bool_extensionality, H.
  Qed.

  Definition subset u v := forall x, x ∈ u -> x ∈ v.
  Infix "⊆" := subset (at level 70) : type_scope.

  Instance subset_reflexive : Reflexive subset.
  Proof.
    intros u x. tauto.
  Qed.

  Corollary antisymmetry u v (Huv: u ⊆ v) (Hvu: v ⊆ u) : u = v.
  Proof.
    apply extensionality.
    intros x.
    split.
    - apply Huv.
    - apply Hvu.
  Qed.

  (* TODO: Make global? *)
  Instance subset_transitive : Transitive subset.
  Proof.
    intros u v w Huv Hvw
           x Hu.
    apply Hvw.
    apply Huv.
    exact Hu.
  Qed.

  Instance subset_proper : Proper ( subset --> subset ==> impl) subset.
  Proof.
    intros u u' Hu
           v v' Hv
           H.
    unfold flip in Hu.
    transitivity u; [exact Hu |].
    transitivity v; [| exact Hv].
    exact H.
  Qed.

  Instance member_proper : Proper ( eq ==> subset ==> impl) member.
  Proof.
    intros x x' Hx
           u u' Hu
           H.
    subst x'.
    apply Hu.
    exact H.
  Qed.


  (** *** Basics *)

  Definition def (p: X -> Prop) {dec: forall x, Decidable (p x)} : DSet :=
    fun x => as_bool (decide (p x)).

  (** We have dropped the traditional subset notation for now. *)

  Proposition def_spec x p {dec: forall x', Decidable (p x')} : x ∈ def p <-> p x.
  Proof.
    unfold def, member.
    setoid_rewrite <- (asBool_decide (p x) (DP := dec x)) at 2.
    destruct (decide (p x)) as [H|H]; tauto.
  Qed.

  Definition full : DSet := def (fun _ => True).
  Notation "'Ω'" := full : DSet_scope.
  Proposition full_spec {x} : x ∈ Ω.
  Proof. exact I. Qed.

  Corollary full_terminal {u} : u ⊆ Ω.
  Proof.
    intros x _. apply full_spec.
  Qed.

  Definition empty : DSet := def (fun _ => False).
  Notation "∅" := empty : DSet_scope.
  Proposition empty_spec {x} : not ( x ∈ ∅ ).
  Proof. exact id. Qed.

  Corollary empty_initial {u} : ∅ ⊆ u.
  Proof.
    intros x H. exfalso. apply (empty_spec H).
  Qed.

  (** Required to define singleton sets. *)
  Context {H_eqdec: EqDec X}.

  Definition singleton x := def (eq x).
  (** Since [{x}] collides with the standard notations. *)
  Notation "!{  x  }" := (singleton x) (at level 0, x at level 99) : DSet_scope.
  Proposition singleton_spec x x' : x ∈ !{x'} <-> x = x'.
  Proof.
    unfold singleton. rewrite def_spec.
    split; intro H; symmetry; exact H.
  Qed.

  Corollary refl {x} : x ∈ !{x}.
  Proof.
    apply singleton_spec. reflexivity.
  Qed.

  Proposition singleton_subset x u : !{x} ⊆ u <-> x ∈ u.
  Proof.
    unfold subset.
    split.
    - intros H.
      apply (H x refl).
    - intros H x'.
      rewrite singleton_spec.
      intros Hx. subst x'. exact H.
  Qed.

  Definition union (u v : DSet) := def (fun a => a ∈ u \/ a ∈ v).
  Infix "∪" := union (at level 40, left associativity) : DSet_scope.
  Proposition union_spec u v x : x ∈ u ∪ v <-> x ∈ u \/ x ∈ v.
  Proof.
    unfold union.
    rewrite def_spec.
    reflexivity.
  Qed.

  Instance union_proper : Proper (subset ==> subset ==> subset) union.
  Proof.
    intros u u' Hu
           v v' Hv
           x.
    setoid_rewrite union_spec.
    intros [H|H].
    - left. apply Hu. exact H.
    - right. apply Hv. exact H.
  Qed.

  (* TODO: Prove more union facts here? *)

  Definition disjoint u v := forall x, not (x ∈ u /\ x ∈ v).
  Infix "#" := disjoint (at level 50) : type_scope.

  Instance disjoint_symmetric : Symmetric disjoint.
  Proof.
    intros u v H x [Hu Hv].
    apply (H x).
    split; assumption.
  Qed.

  Instance disjoint_proper : Proper (subset --> subset --> impl) disjoint.
  Proof.
    intros u u' Hu
           v v' Hv
           Huv x [Hxu Hxv].
    apply (Huv x).
    split;
      [apply Hu
      |apply Hv];
      assumption.
  Qed.

  Proposition disjoint_not_member a u : !{a} # u <-> not (a ∈ u).
  Proof.
    unfold disjoint.
    setoid_rewrite singleton_spec.
    intuition.
    congruence.
  Qed.

  Corollary disjoint_singeltons a a' : disjoint !{a} !{a'} <-> a <> a'.
  Proof.
    transitivity (not (a ∈ !{a'}));
      [ rewrite disjoint_not_member
      | rewrite singleton_spec ];
      reflexivity.
  Qed.

End DSet_section.

Arguments DSet : clear implicits.
Declare Scope DSet_scope.
Bind Scope DSet_scope with DSet.
Delimit Scope DSet_scope with DSet.

Module DSetNotations.

  Infix "∈" := member (at level 70) : type_scope.
  Infix "⊆" := subset (at level 70) : type_scope.
  Infix "#" := disjoint (at level 50) : type_scope.

  Notation "'Ω'" := full : DSet_scope.
  Notation "∅" := empty : DSet_scope.
  Notation "!{  x  }" := (singleton x) (at level 0, x at level 99) : DSet_scope.
  Infix "∪" := union (at level 40, left associativity) : DSet_scope.

End DSetNotations.
