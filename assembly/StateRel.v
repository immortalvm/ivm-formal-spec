From Assembly Require Export Machine Rel.
Require Import Coq.Logic.PropExtensionality.

Unset Suggest Proof Using.

Module Type MachineParametersX.
  Declare Instance MP1: MachineParams1.
  Declare Instance MP2: MachineParams2.
End MachineParametersX.

Module CoreRel (MPX: MachineParametersX).

  (** ** State relation *)

  (** *** Memory *)

  (** Observe that [memory_relation] and [img_relation] (defined below)
      are defined in terms of [option_relation] (implicitly). *)

  Instance memory_relation : Rel Memory :=
    fun m m' => forall a Ha, m a Ha ⊑ m' a Ha.

  Instance memory_relation_reflexive : Reflexive memory_relation.
  Proof.
    intros m a Ha. reflexivity.
  Qed.

  Instance memory_relation_transitive : Transitive memory_relation.
  Proof.
    intros m1 m2 m3 H12 H23 a Ha.
    specialize (H12 a Ha).
    specialize (H23 a Ha).
    transitivity (m2 a Ha); assumption.
  Qed.


  (** *** Output image *)

  Import EqNotations.

  Instance img_relation : Rel (Image (option OutputColor)) :=
    fun i i' =>
      exists (Hw: width i = width i')
        (Hh: height i = height i'),
      forall x Hx y Hy,
        @pixel _ i x Hx y Hy ⊑
        @pixel _ i' x (rew Hw in Hx) y (rew Hh in Hy).

  Instance img_relation_reflexive : Reflexive img_relation.
  Proof.
    intros i.
    exists eq_refl, eq_refl.
    intros x Hx y Hy.
    reflexivity.
  Qed.

  Instance img_relation_transitive : Transitive img_relation.
  Proof.
    intros i1 i2 i3 [Hw12 [Hh12 H12]] [Hw23 [Hh23 H23]].
    exists (eq_Transitive _ _ _ Hw12 Hw23).
    exists (eq_Transitive _ _ _ Hh12 Hh23).
    intros x Hx y Hy.
    specialize (H12 x Hx y Hy).
    specialize (H23 x (rew Hw12 in Hx) y (rew Hh12 in Hy)).
    unfold eq_Transitive in H23.
    do 2 rewrite rew_compose in H23.
    transitivity (pixel i2 (rew Hw12 in Hx) (rew  Hh12 in Hy)); assumption.
  Qed.


  (** *** State *)

  Infix "∩" := and_relation (at level 60, right associativity).

  Instance state_relation : Rel State :=
    lens_relation MEM
    ∩ lens_relation OUT_IMAGE
    ∩ lens_relation OUT_BYTES
    ∩ lens_relation OUT_CHARS
    ∩ lens_relation OUT_SOUND
    ∩ lens_relation LOG
    ∩ lens_relation INP
    ∩ lens_relation PC
    ∩ lens_relation SP.

  Ltac srel_destruct H :=
    unfold rel, state_relation, and_relation, lens_relation in H;
    let H0 := fresh H "_mem" in
    let H1 := fresh H "_img" in
    let H2 := fresh H "_byt" in
    let H3 := fresh H "_chr" in
    let H4 := fresh H "_snd" in
    let H5 := fresh H "_log" in
    let H6 := fresh H "_inp" in
    let H7 := fresh H "_pc" in
    let H8 := fresh H "_sp" in
    destruct H as [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]].

  Instance srel_reflexive : Reflexive state_relation.
  Proof.
    intros s. repeat split; reflexivity.
  Qed.

  Instance srel_transitive : Transitive state_relation.
  Proof.
    intros s1 s2 s3 H12 H23.
    srel_destruct H12.
    srel_destruct H23.
    repeat split; transitivity s2; assumption.
  Qed.

End CoreRel.
