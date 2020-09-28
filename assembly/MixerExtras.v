From Assembly Require Export Mixer.

Require Import Coq.Logic.ProofIrrelevance.

Unset Suggest Proof Using.

Ltac collapse p q :=
  let HH := fresh "HH" in
  assert (p = q) as HH; [ apply proof_irrelevance | destruct HH ].

Proposition mixerEq_is_eq {A} (f g: Mixer A) (H: f ≃ g) : f = g.
Proof.
  destruct f as [f f_id f_left f_right].
  destruct g as [g g_id g_left g_right].
  unfold mixerEq in H.
  cbn in H.
  assert (f = g) as HH.
  - extensionality x.
    extensionality y.
    apply H.
  - destruct HH. clear H.
    collapse f_id g_id.
    collapse f_left g_left.
    collapse f_right g_right.
    reflexivity.
Qed.

Section opp_section.

  (** This easily leads to loops. *)
  #[refine] Instance oppMixer {A} (f: Mixer A) : Mixer A :=
  {
    mixer x y := f y x;
  }.
  Proof.
    all: intros; mixer_rewrite0; reflexivity.
  Defined.

End opp_section.

Proposition opp_fstMixer {A} : oppMixer fstMixer ≃ @sndMixer A.
Proof.
  intros x y. reflexivity.
Qed.

Proposition opp_oppMixer {A} (f: Mixer A) : oppMixer (oppMixer f) ≃ f.
Proof.
  intros x y. reflexivity.
Qed.

Proposition submixer_snd {A} (f: Mixer A) : (f | sndMixer).
Proof. mixer_rewrite'. Qed.

Proposition independent_spec {A} (f g: Mixer A) :
  Independent f g <-> (f | oppMixer g).
Proof.
  split; intros H x y z; apply H.
Qed.
