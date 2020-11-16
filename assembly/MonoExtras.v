From Assembly Require Export RelExtras MachineExtras StateRel.
Require Import Coq.Logic.ProofIrrelevance.

Instance MP1 : MachineParams1 := concreteParams1.
Instance MP2 : MachineParams2 := concreteParams2.
Include CoreRel.

Definition M := EST State.

Instance RM X {RX: Rel X} : Rel (M X) := est_relation State.

Instance SMP : SMonadPropR State M := est_pmon State.

Proposition err_less_eq {X} {RX: Rel X} (mx: M X) (Hmx: mx ⊑ err) : mx = err.
Proof.
  apply (err_less_eq State).
  exact Hmx.
Qed.

Instance RM_transitive X (RX: Rel X) (RXT: Transitive RX) : Transitive (RM X).
Proof.
  typeclasses eauto.
Qed.

Instance eq_antisymm X : Antisymmetric X eq eq.
Proof.
  congruence.
Qed.

Instance srel_antisymm : Antisymmetric State eq state_relation.
Proof.
  intros s s' Hs Hs'.
  destruct s.
  destruct s'.
  srel_destruct Hs.
  srel_destruct Hs'.
  unfold rel, eq_relation in *.
  cbn in *.
  f_equal.
  all: try assumption.

  - extensionality a.
    extensionality Ha.
    specialize (Hs_mem a Ha).
    specialize (Hs'_mem a Ha).
    apply option_relation_antisymm.
    + typeclasses eauto.
    + assumption.
    + assumption.

  - destruct state_image.
    destruct state_image0.
    f_equal.
    destruct Hs_img as [Hw [Hh Hs_img]].
    destruct Hs'_img as [Hw' [Hh' Hs'_img]].
    cbn in Hs_img, Hs'_img.
    cbn in Hw, Hh, Hw', Hh'.
    destruct Hw, Hh.
    assert (Hw' = eq_refl) as Hw''; [ apply proof_irrelevance | subst Hw' ].
    assert (Hh' = eq_refl) as Hh''; [ apply proof_irrelevance | subst Hh' ].
    f_equal.
    extensionality x. extensionality Hx.
    extensionality y. extensionality Hy.
    specialize (Hs_img x Hx y Hy).
    specialize (Hs'_img x Hx y Hy).
    cbn in Hs_img, Hs'_img.
    apply option_relation_antisymm.
    + apply prod_relation_antisymm; typeclasses eauto.
    + assumption.
    + assumption.
Qed.

Instance RM_antisymmetric X (RX: Rel X) (RXT: Antisymmetric X eq RX) :
    Antisymmetric (M X) eq (RM X).
Proof.
  typeclasses eauto.
Qed.
