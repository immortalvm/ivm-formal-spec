Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Operations.
Require Import Assembly.Machine.
Require Import Assembly.Rel.

Require Import Coq.Logic.PropExtensionality.

Arguments proj : clear implicits.
Arguments proj {_} {_}.
Arguments update : clear implicits.
Arguments update {_} {_}.

Notation OI := (OUT_IMAGE).


Section machine_section.

  Context {MP1: @MachineParams1 concreteParams0}.

  Instance estParams2 : @MachineParams2 concreteParams0 MP1 :=
  {
      M := EST State;
      H_mon := est_smonad State;
  }.

  Existing Instance H_mon.


  (** ** Memory relation *)

  (** Observe that [memory_relation] and [oi_relation] (defined below) are
      (implicitly) defined in terms of [option_relation]. *)

  Instance memory_relation : Rel Memory :=
    fun m m' => forall a Ha, m a Ha ⊑ m' a Ha.

  Instance memory_relation_reflexive : Reflexive memory_relation.
  Proof using.
    intros m a Ha. reflexivity.
  Qed.

  Instance memory_relation_transitive : Transitive memory_relation.
  Proof using.
    intros m1 m2 m3 H12 H23 a Ha.
    specialize (H12 a Ha).
    specialize (H23 a Ha).
    transitivity (m2 a Ha); assumption.
  Qed.


  (** *** Output image relation *)

  Import EqNotations.

  Instance oi_relation : Rel (Image (option OutputColor)) :=
    fun i i' =>
      exists (Hw: width i = width i')
        (Hh: height i = height i'),
      forall x Hx y Hy,
        @pixel _ i x Hx y Hy ⊑
        @pixel _ i' x (rew Hw in Hx) y (rew Hh in Hy).

  Instance oi_relation_reflexive : Reflexive oi_relation.
  Proof using.
    intros i.
    exists eq_refl, eq_refl.
    intros x Hx y Hy.
    reflexivity.
  Qed.

  Instance oi_relation_transitive : Transitive oi_relation.
  Proof using.
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

  Instance state_relation : Rel State :=
    proj_relation (proj_prod MEM OI)
                  (prod_relation memory_relation oi_relation).

  Instance sm_relation {A} (RA: Rel A) : Rel (M A).
  Proof.
    typeclasses eauto.
  Defined.

  (** Make sure we got what we want. *)
  Goal forall {A} (RA: Rel A), sm_relation RA = @est_relation _ state_relation _ RA.
    reflexivity.
  Qed.


  Local Ltac rewr := repeat (independent_rewrite1 || proj_rewrite1 || simpl).

  (** *** Get *)

  Instance getMem_propR : PropR (get' MEM).
  Proof using.
    intros s s' Hs. split; [|destruct Hs as [_ [Hs _]]]; exact Hs.
  Qed.

  Instance getOi_propR : PropR (get' OI).
  Proof using.
    intros s s' Hs. split; [|destruct Hs as [_ [_ Hs]]]; exact Hs.
  Qed.

  (** We have ordered the assumptions that the projections are pairwise
      independent so that we won't have to combine the following with
      [independent_symm]. Similarly for [putOther_propR] below. *)

  Instance getOther_propR X
           (PX: Proj State X)
           (Imem: Independent MEM PX)
           (Ioi: Independent OI PX) : PropR (get' PX).
  Proof using.
    intros s s' Hs.
    split; [exact Hs|].
    destruct Hs as [Hs _].
    unfold aligned in Hs.
    simpl in Hs.
    rewrite <- Hs.
    now rewr.
  Qed.


  (** *** Put *)

  Local Ltac putTactic PX :=
    intros x x' Hx;
    try (cbv in Hx; subst x);
    intros s s' Hs;
    (split; [|reflexivity]);
    (split; [|split]);
    [ destruct Hs as [Hs _];
      derive Hs (f_equal (fun t => update PX t x') Hs);
      simpl in Hs;
      simpl;
      rewrite <- Hs;
      unfold aligned;
      now rewr
    | |].

  Instance putMem_PropR : PropR (put' MEM).
  Proof using.
    putTactic MEM.
    - rewr. exact Hx.
    - destruct Hs as [_ [_ Hs]]. rewr. exact Hs.
  Qed.

  Instance putOi_PropR : PropR (put' OI).
  Proof using.
    putTactic OI.
    - destruct Hs as [_ [Hs _]]. rewr. exact Hs.
    - rewr. exact Hx.
  Qed.

  Instance putOther_PropR X
           (PX: Proj State X)
           (Imem: Independent MEM PX)
           (Ioi: Independent OI PX) : PropR (put' PX).
  Proof using.
    putTactic PX.
    - destruct Hs as [_ [Hs _]]. rewr. exact Hs.
    - destruct Hs as [_ [_ Hs]]. rewr. exact Hs.
  Qed.


  (** Load *)

  Ltac crush :=
    match goal with

    (* | [|- ?X] => idtac X; fail *)

    | [|- rel (option_relation _) None _] => exact I
    | [H: rel (option_relation _) (Some _) None |- _] => destruct H
    | [x: _ * _ |- _] => destruct x; simpl fst; simpl snd
    | [H: rel (prod_relation _ _) _ _ |- _] => destruct H


    | [|- put' MEM _ ⊑ put' MEM _] => unshelve eapply putMem_PropR
    | [|- put' OI _ ⊑ put' OI _] => unshelve eapply putOi_PropR
    | [|- put' _ _ ⊑ put' _ _] => unshelve eapply putOther_PropR

    | [|- bind _ _ ⊑ bind _ _] => unshelve eapply bind_propR
    | [|- ret _ ⊑ ret _] => unshelve eapply ret_propR
    | [|- err ⊑ _] => unshelve eapply err_propR

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

  Instance load_propR a : PropR (load a).
  Proof using.
    unfold load.
    repeat crush; specialize (Hfg a HL);
      rewrite Hu, Hv in *.
    - exact Hfg.
    - destruct Hfg.
  Qed.

  Instance nextN_propR n : PropR (nextN n).
  Proof using.
    repeat (unfold nextN, next; crush).
    revert y.
    induction n as [|n IH];
      intro a;
      simp loadMany;
      repeat crush.
    apply IH.
  Qed.

  Instance popN_propR: PropR popN.
  Proof using.
    repeat (unfold popN, loadMany; crush).
  Qed.

  Instance pop64_propR: PropR pop64.
  Proof using.
    unfold pop64. repeat crush.
  Qed.

  Instance storeMany_propR a lst : PropR (storeMany a lst).
  Proof using.
    revert a.
    induction lst as [|x r IH]; intro a; repeat (crush || simp storeMany).
    unfold store.
    repeat crush.
    intros a' HL'.
    destruct (eq_dec a a') as [Ha|Ha]; [easy|].
    specialize (Hfg a' HL').
    destruct (f a' HL') as [fa'|] eqn:Hfa; crush.
  Qed.

  Instance push64_propR z: PropR (push64 z).
  Proof using.
    unfold push64. repeat crush.
  Qed.

  Instance loadN_propR n a : PropR (loadN n a).
  Proof using.
    unfold loadN. repeat crush.
    revert a.
    induction n as [|n IH]; intro a; simp loadMany; repeat crush.
    apply IH.
  Qed.

  Instance storeZ_propR n a z : PropR (storeZ n a z).
  Proof using.
    unfold storeZ. repeat crush.
  Qed.

  Instance setPixel_propR x y c : PropR (setPixel x y c).
  Proof using.
    (** Presumably, there is some way to automate more of this,
        but I am not sure whether it is worth the effort.*)
    repeat (unfold setPixel, updatePixel; crush).
    simpl.
    rename x0 into i, y0 into i', Hxy into Hi, HL into Hx.
    destruct (decision (y < height i)) as [Hy|Hy];
      [|repeat crush].
    destruct Hi as [Hw [Hh Hi]].

    destruct (decision (x < width i')) as [Hw'|Hw'];
      [| contradict Hw'; rewrite <- Hw; exact Hx ].
    destruct (decision (y < height i')) as [Hh'|Hh'];
      [| contradict Hh'; rewrite <- Hh; exact Hy ].

    apply putOi_PropR. exists Hw. exists Hh.
    intros x' Hx' y' Hy'. simpl.

    destruct (decision (x' = x /\ y' = y)).
    - reflexivity.
    - exact (Hi x' Hx' y' Hy').
  Qed.

  Instance readPixel_propR x y : PropR (readPixel x y).
  Proof using.
    unfold readPixel. repeat crush.
    destruct (decision (y < height (nth y0 allInputImages noImage))) as [Hh|Hh];
      repeat crush.
  Qed.

  Lemma image_complete_lemma
        {i i': Image (option OutputColor)}
        (Hi: i ⊑ i') (Hc: image_complete i) : i = i'.
  Proof using.
    destruct i as [w h p].
    destruct i' as [w' h' p'].
    destruct Hi as [Hw [Hh Hp]].
    simpl in *. subst w'. subst h'.
    apply f_equal.
    extensionality x.
    extensionality Hx.
    extensionality y.
    extensionality Hy.
    specialize (Hp x Hx y Hy).
    simpl in Hp.
    specialize (Hc x Hx y Hy).
    derive Hc (some_some Hc).
    destruct Hc as [c Hc].
    simpl in Hc.
    rewrite Hc in *.
    destruct (p' x Hx y Hy) as [c'|].
    - unfold rel in Hp.
      destruct c as [[r g] b].
      destruct c' as [[r' g'] b'].
      cbn in Hp.
      destruct Hp as [[Hr Hg] Hb].
      repeat crush.
    - crush.
  Qed.

  Instance newFrame_propR w h r: PropR (newFrame w h r).
  Proof using.
    repeat (unfold newFrame, extractImage; crush).
    simpl.
    clear r y y0 y1.
    rename
      x into i,
      y2 into i',
      Hxy into Hi,
      HL into Hc.

    destruct (image_complete_lemma Hi Hc).
    destruct (decision (image_complete i)) as [Hc'|Hc'];
      [|contradict Hc'; exact Hc].

    intros s s' Hs. split.
    - exact Hs.
    - destruct (proof_irrelevance _ Hc Hc'). reflexivity.
  Qed.


  (** Putting it all together... *)

  Global Instance oneStep_propR : PropR oneStep.
  Proof using.
    unfold oneStep.
    repeat crush.
    destruct y as [|n]; repeat crush.

    Ltac print := match goal with [|- _ (_ ?i)] => idtac i end.

    Ltac step :=
      print;
      simp oneStep';
      unfold putByte, putChar, addSample, readFrame;
      repeat crush.

    Time do 255 (destruct n as [|n]; [step|]); step.
    (* Beware: This takes a long time!
       This is mostly due to inefficiencies in coq-equations. *)
  Qed.

End machine_section.
