From Assembly Require Export Machine Rel.
Require Import Coq.Logic.PropExtensionality.

Unset Suggest Proof Using.
Set Implicit Arguments.

Arguments proj : clear implicits.
Arguments proj {_} {_}.
Arguments update : clear implicits.
Arguments update {_} {_}.


(** Global parameters from now on for convenience. *)
Context {MP1: MachineParams1}.

(** Focus on the initial smonad from now on. *)
Instance estParams2 : MachineParams2 :=
{
  M := EST State;
  H_mon := est_smonad State;
}.

Existing Instance H_mon.


(** ** Memory relation *)

(** Observe that [memory_relation] and [img_relation] (defined below) are
    (implicitly) defined in terms of [option_relation]. *)

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


(** *** Output image relation *)

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


(** ** Monotonicity *)

Existing Instance independent_MEM_IMAGE.
Existing Instance independent_MEM_BYTES.
Existing Instance independent_MEM_CHARS.
Existing Instance independent_MEM_SOUND.
Existing Instance independent_MEM_LOG.
Existing Instance independent_MEM_INP.
Existing Instance independent_MEM_PC.
Existing Instance independent_MEM_SP.
Existing Instance independent_IMAGE_BYTES.
Existing Instance independent_IMAGE_CHARS.
Existing Instance independent_IMAGE_SOUND.
Existing Instance independent_IMAGE_LOG.
Existing Instance independent_IMAGE_INP.
Existing Instance independent_IMAGE_PC.
Existing Instance independent_IMAGE_SP.
Existing Instance independent_BYTES_CHARS.
Existing Instance independent_BYTES_SOUND.
Existing Instance independent_BYTES_LOG.
Existing Instance independent_BYTES_INP.
Existing Instance independent_BYTES_PC.
Existing Instance independent_BYTES_SP.
Existing Instance independent_CHARS_SOUND.
Existing Instance independent_CHARS_LOG.
Existing Instance independent_CHARS_INP.
Existing Instance independent_CHARS_PC.
Existing Instance independent_CHARS_SP.
Existing Instance independent_SOUND_LOG.
Existing Instance independent_SOUND_INP.
Existing Instance independent_SOUND_PC.
Existing Instance independent_SOUND_SP.
Existing Instance independent_LOG_INP.
Existing Instance independent_LOG_PC.
Existing Instance independent_LOG_SP.
Existing Instance independent_INP_PC.
Existing Instance independent_INP_SP.
Existing Instance independent_PC_SP.

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

Instance sm_relation {A} (RA: Rel A) : Rel (M A).
Proof.
  typeclasses eauto.
Defined.

(** Make sure we got what we want. *)
Goal forall {A} (RA: Rel A), sm_relation RA = @est_relation _ state_relation _ RA.
  reflexivity.
Qed.

Ltac srel_destruct H :=
  unfold rel, state_relation, and_relation, lens_relation in H;
  let H0 := fresh H "_mem" in
  let H1 := fresh H "_img" in
  let H2 := fresh H "_byt" in
  let H2 := fresh H "_chr" in
  let H3 := fresh H "_snd" in
  let H4 := fresh H "_log" in
  let H5 := fresh H "_inp" in
  let H6 := fresh H "_pc" in
  let H7 := fresh H "_sp" in
  destruct H as [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]].

Local Ltac rewr := repeat (independent_rewrite1 || lens_rewrite1 || simpl).


(** *** Get *)

Local Ltac get_tactic :=
  intros s s' Hs; split; [|srel_destruct Hs]; assumption.

Instance getMem_propr : PropR (get' MEM).
Proof. get_tactic. Qed.

Instance getImg_propr : PropR (get' OUT_IMAGE).
Proof. get_tactic. Qed.

Instance getByt_propr: PropR (get' OUT_BYTES).
Proof. get_tactic. Qed.

Instance getChr_propr: PropR (get' OUT_CHARS).
Proof. get_tactic. Qed.

Instance getSnd_propr: PropR (get' OUT_SOUND).
Proof. get_tactic. Qed.

Instance getLog_propr: PropR (get' LOG).
Proof. get_tactic. Qed.

Instance getInp_propr: PropR (get' INP).
Proof. get_tactic. Qed.

Instance getPc_propr: PropR (get' PC).
Proof. get_tactic. Qed.

Instance getSp_propr: PropR (get' SP).
Proof. get_tactic. Qed.


(** *** Put *)

Local Ltac put_tactic :=
  intros x x' Hx;
  (* try (cbv in Hx; subst x); *)
  intros s s' Hs;
  (split; [|reflexivity]);
  srel_destruct Hs;
  repeat split;
  unfold lens_relation;
  rewr;
  try assumption.

Instance putMem_propr : PropR (put' MEM).
Proof. put_tactic. Qed.

Instance putImg_propr : PropR (put' OUT_IMAGE).
Proof. put_tactic. Qed.

Instance putByt_propr: PropR (put' OUT_BYTES).
Proof. put_tactic. Qed.

Instance putChr_propr: PropR (put' OUT_CHARS).
Proof. put_tactic. Qed.

Instance putSnd_propr: PropR (put' OUT_SOUND).
Proof. put_tactic. Qed.

Instance putLog_propr: PropR (put' LOG).
Proof. put_tactic. Qed.

Instance putInp_propr: PropR (put' INP).
Proof. put_tactic. Qed.

Instance putPc_propr: PropR (put' PC).
Proof. put_tactic. Qed.

Instance putSp_propr: PropR (put' SP).
Proof. put_tactic. Qed.


(** Load *)

Ltac crush :=
  match goal with

  (* | [|- ?X] => idtac X; fail *)

  | [|- rel (option_relation _) None _] => exact I
  | [H: rel (option_relation _) (Some _) None |- _] => destruct H
  | [x: _ * _ |- _] => destruct x; simpl fst; simpl snd
  | [H: rel (prod_relation _ _) _ _ |- _] => destruct H


  | [|- put' MEM _ ⊑ put' MEM _] => unshelve eapply putMem_propr
  | [|- put' OUT_IMAGE _ ⊑ put' OUT_IMAGE _] => unshelve eapply putImg_propr
  | [|- put' OUT_BYTES _ ⊑ put' OUT_BYTES _] => unshelve eapply putByt_propr
  | [|- put' OUT_CHARS _ ⊑ put' OUT_CHARS _] => unshelve eapply putChr_propr
  | [|- put' OUT_SOUND _ ⊑ put' OUT_SOUND _] => unshelve eapply putSnd_propr
  | [|- put' LOG _ ⊑ put' LOG _] => unshelve eapply putLog_propr
  | [|- put' INP _ ⊑ put' INP _] => unshelve eapply putInp_propr
  | [|- put' PC _ ⊑ put' PC _] => unshelve eapply putPc_propr
  | [|- put' SP _ ⊑ put' SP _] => unshelve eapply putSp_propr

  | [|- bind _ _ ⊑ bind _ _] => unshelve eapply bind_propr
  | [|- ret _ ⊑ ret _] => unshelve eapply ret_propr
  | [|- err ⊑ _] => unshelve eapply err_propr

  | [|- ?x ⊑ ?x] => try reflexivity;
                  unshelve eapply propR;
                  match goal with [|- PropR x] => fail end

  | [H : rel eq_relation ?x ?x' |- _] => cbv in H; first [subst x|subst x']

  | [|- match ?H with left _ => _ | right _ => _ end ⊑ _] => destruct H as [HL|HR]


  | [|- match ?H with Some _ => _ | None => _ end ⊑ _] =>
    let u := fresh "u" in
    let Hu := fresh "Hu" in
    destruct H as [u|] eqn:Hu

  | [|- _ ⊑ match ?H with Some _ => _ | None => _ end] =>
    let v := fresh "v" in
    let Hv := fresh "Hv" in
    destruct H as [v|] eqn:Hv

  | [|- rel (fun_relation _ _) ?a _] =>
    match type of a with
    | Memory -> _ => (* TODO: Merge with next case *)
      let f := fresh "f" in
      let g := fresh "g" in
      let Hfg := fresh "Hfg" in
      intros f g Hfg
    | (_ -> _) -> _ =>
      let f := fresh "f" in
      let g := fresh "g" in
      let Hfg := fresh "Hfg" in
      intros f g Hfg
    | _ -> _ =>
      let x := fresh "x" in
      let y := fresh "y" in
      let Hxy := fresh "Hxy" in
      intros x y Hxy
    end

  | _ => try (exact eq_refl);
        try assumption;
        try typeclasses eauto;
        unfold PropR, popMany, pushMany (* never fails *)

  end.

Instance load_propr a : PropR (load a).
Proof.
  unfold load.
  repeat crush; specialize (Hfg a HL);
    rewrite Hu, Hv in *.
  - exact Hfg.
  - destruct Hfg.
Qed.

Instance nextB_propr n : PropR (nextB n).
Proof.
  repeat (unfold nextB, next; crush).
  revert y.
  induction n as [|n IH];
    intro a;
    simp loadMany;
    repeat crush.
  apply IH.
Qed.

Instance popN_propr: PropR popN.
Proof.
  repeat (unfold popN, loadMany; crush).
Qed.

Instance pop64_propr: PropR pop64.
Proof.
  unfold pop64. repeat crush.
Qed.

Instance storeMany_propr a lst : PropR (storeMany a lst).
Proof.
  revert a.
  induction lst as [|x r IH]; intro a; repeat (crush || simp storeMany).
  unfold store.
  repeat crush.
  intros a' HL'.
  destruct (eq_dec a a') as [Ha|Ha]; [easy|].
  specialize (Hfg a' HL').
  destruct (f a' HL') as [fa'|] eqn:Hfa; crush.
Qed.

Instance pushZ_propr z: PropR (pushZ z).
Proof.
  unfold pushZ. repeat crush.
Qed.

Instance loadN_propr n a : PropR (loadN n a).
Proof.
  unfold loadN. repeat crush.
  revert a.
  induction n as [|n IH]; intro a; simp loadMany; repeat crush.
  apply IH.
Qed.

Instance storeZ_propr n a z : PropR (storeZ n a z).
Proof.
  unfold storeZ. repeat crush.
Qed.

Open Scope N.

Instance setPixel_propr x y c : PropR (setPixel x y c).
Proof.
  (** Presumably, there is some way to automate more of this,
      but I am not sure whether it is worth the effort.*)
  repeat (unfold setPixel, updatePixel; crush).
  simpl.
  rename x0 into i, y0 into i', Hxy into Hi, HL into Hx.
  destruct (decide (y < height i)) as [Hy|Hy];
    [|repeat crush].
  destruct Hi as [Hw [Hh Hi]].

  destruct (decide (x < width i')) as [Hw'|Hw'];
    [| contradict Hw'; rewrite <- Hw; exact Hx ].
  destruct (decide (y < height i')) as [Hh'|Hh'];
    [| contradict Hh'; rewrite <- Hh; exact Hy ].

  apply putImg_propr. exists Hw. exists Hh.
  intros x' Hx' y' Hy'. simpl.

  destruct (decide (x' = x /\ y' = y)).
  - reflexivity.
  - exact (Hi x' Hx' y' Hy').
Qed.

Instance readPixel_propr x y : PropR (readPixel x y).
Proof.
  unfold readPixel. repeat crush.
  destruct (decide _) as [Hh|Hh];
    repeat crush.
Qed.

Lemma image_complete_lemma
      {i i': Image (option OutputColor)}
      (Hi: i ⊑ i') (Hc: image_complete i) : i = i'.
Proof.
  destruct i as [w h p].
  destruct i' as [w' h' p'].
  destruct Hi as [Hw [Hh Hp]].
  simpl in *. subst w'. subst h'.
  apply f_equal.
  extensionality x.
  extensionality Hx.
  extensionality y.
  extensionality Hy.
  specialize (Hp x Hx y Hy). simpl in Hp.
  specialize (Hc x Hx y Hy). simpl in Hc.
  rewrite <- (some_extract Hc) in *.
  destruct (p' x Hx y Hy) as [c'|].
  - unfold rel in Hp.
    destruct (extract Hc) as [[r g] b].
    destruct c' as [[r' g'] b'].
    cbn in Hp.
    destruct Hp as [[Hr Hg] Hb].
    repeat crush.
  - crush.
Qed.

Instance newFrame_propr w h r: PropR (newFrame w h r).
Proof.
  repeat (unfold newFrame, extractImage; crush).
  simpl.
  clear r y y0 y1.
  rename
    x into i,
    y2 into i',
    Hxy into Hi,
    HL into Hc.

  destruct (image_complete_lemma Hi Hc).
  destruct (decide (image_complete i)) as [Hc'|Hc'];
    [|contradict Hc'; exact Hc].

  intros s s' Hs. split.
  - exact Hs.
  - destruct (proof_irrelevance _ Hc Hc'). reflexivity.
Qed.


(** Putting it all together... *)

Global Instance oneStep_propr : PropR oneStep.
Proof.
  unfold oneStep. repeat crush.
  destruct (y : N) eqn:Hy;
    [ crush; reflexivity | ].

  (* Presumably, there is a more elegant way to do this. *)
  unfold oneStep'.
  repeat (match goal with
            [|- context [match _ with xI _ => _ | xO _ => _ | xH => _ end]] =>
            destruct p end).
  all:
    unfold putByte, putChar, addSample, readFrame; repeat crush.
Qed.

(*
Declare Instance oneStep_propr : PropR oneStep.
 *)
