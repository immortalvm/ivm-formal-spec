From Assembly Require Export Machine Rel.
Require Import Coq.Logic.PropExtensionality.

Unset Suggest Proof Using.


(** We leave these assumptions abstract in order improve proof search.
    In Concete.v we have shown that they hold in our standard model. *)
Context {MP1: MachineParams1}
        {MP2: MachineParams2}.


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


(** ** Basic monotonicity *)

(** Additional assumptions *)
Context {RM: forall X (RX: Rel X), Rel (M X)}
        {PM: SMonadPropR State M (RM:=RM)}.

Global Existing Instance PM.

Proposition bind_propr'
            {X Y} {RX: Rel X} {RY: Rel Y}
            {mx mx': M X} (Hmx: mx ⊑ mx')
            {f f': X -> M Y} (Hf: f ⊑ f') : mx >>= f ⊑ mx' >>= f'.
Proof.
  exact (bind_propr State RX RY mx mx' Hmx f f' Hf).
Qed.

Ltac crush0 :=
  match goal with
  | [ |- ret _ ⊑ ret _ ] => unshelve eapply ret_propr; [apply PM|]
  | [|- err ⊑ _] => unshelve eapply err_least, PM
  | [ |- get ⊑ get ] => unshelve eapply get_propr, PM
  | [ |- put _ ⊑ put _ ] => unshelve eapply put_propr; [apply PM|]

  | [|- ?x ⊑ ?x] => try reflexivity;
                  unshelve eapply propR;
                  match goal with [|- PropR x] => fail end

  | [H : rel eq_relation ?x ?y |- _] => cbv in H; first [subst x|subst y]

  | [|- rel (option_relation _) None _] => exact I
  | [H: rel (option_relation _) (Some _) None |- _] => destruct H
  | [x: _ * _ |- _] => destruct x; simpl fst; simpl snd
  | [H: rel (prod_relation _ _) _ _ |- _] => destruct H

  | [|- rel (fun_relation _ _) ?a _] =>
    match type of a with
    | State -> _ =>
      let x := fresh "s" in
      let y := fresh "t" in
      let Hxy := fresh "Hst" in
      intros x y Hxy
    | Image _ -> _ =>
      let x := fresh "i" in
      let y := fresh "j" in
      let Hxy := fresh "Hij" in
      intros x y Hxy
    | Memory -> _ => (* TODO: Merge with next case *)
      let x := fresh "f" in
      let y := fresh "g" in
      let Hxy := fresh "Hfg" in
      intros x y Hxy
    | (_ -> _) -> _ =>
      let x := fresh "f" in
      let y := fresh "g" in
      let Hxy := fresh "Hfg" in
      intros x y Hxy
    | _ -> _ =>
      let x := fresh "x" in
      let y := fresh "y" in
      let Hxy := fresh "Hxy" in
      intros x y Hxy
    end

  | [|- match ?H with left _ => _ | right _ => _ end ⊑ _] =>
    let HL := fresh "HL" in
    let HR := fresh "HR" in
    destruct H as [HL|HR]

  | [|- _ ⊑ match ?H with left _ => _ | right _ => _ end] =>
    let HL := fresh "HL" in
    let HR := fresh "HR" in
    destruct H as [HL|HR]

  | [|- match ?H with Some _ => _ | None => _ end ⊑ _] =>
    let u := fresh "u" in
    let Hu := fresh "Hu" in
    destruct H as [u|] eqn:Hu

  | [|- _ ⊑ match ?H with Some _ => _ | None => _ end] =>
    let v := fresh "v" in
    let Hv := fresh "Hv" in
    destruct H as [v|] eqn:Hv

  | [|- rel memory_relation _ _] =>
    let a := fresh "a" in
    let Ha := fresh "Ha" in
    intros a Ha

  | [ |- (_ >>= _) >>= _ ⊑ _ ] => setoid_rewrite bind_assoc
  | [ |- _ ⊑ (_ >>= _) >>= _ ] => setoid_rewrite bind_assoc
  | [ |- _ >>= _ ⊑ _ >>= _ ] => apply bind_propr'

  | _ => exact eq_refl
  | _ => progress unfold PropR
  end.


(** *** Get *)

Local Ltac get_tactic :=
  rewrite get_spec; simpl; repeat crush0;
  match goal with [ H: _ ⊑ _ |- _ ] => srel_destruct H end;
  try assumption.

Instance getMem_propr : PropR (get' MEM).
Proof. get_tactic. apply Hst_mem. Qed.

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
  rewrite put_spec; simpl; repeat crush0;
  match goal with [ H: _ ⊑ _ |- _ ] => srel_destruct H end;
  repeat split;
  unfold lens_relation;
  repeat (lens_rewrite1 || simpl);
  reflexivity || assumption.

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


(** *** Crush *)

Ltac crush1 :=
  match goal with
  | [|- put' MEM _ ⊑ put' MEM _] => unshelve eapply putMem_propr
  | [|- put' OUT_IMAGE _ ⊑ put' OUT_IMAGE _] => unshelve eapply putImg_propr
  | [|- put' OUT_BYTES _ ⊑ put' OUT_BYTES _] => unshelve eapply putByt_propr
  | [|- put' OUT_CHARS _ ⊑ put' OUT_CHARS _] => unshelve eapply putChr_propr
  | [|- put' OUT_SOUND _ ⊑ put' OUT_SOUND _] => unshelve eapply putSnd_propr
  | [|- put' LOG _ ⊑ put' LOG _] => unshelve eapply putLog_propr
  | [|- put' INP _ ⊑ put' INP _] => unshelve eapply putInp_propr
  | [|- put' PC _ ⊑ put' PC _] => unshelve eapply putPc_propr
  | [|- put' SP _ ⊑ put' SP _] => unshelve eapply putSp_propr

  | _ => crush0
  end.

Ltac crush := repeat crush1.

Instance pointwise_propr {X Y} (f: X -> Y) {RY: Rel Y} (H: forall x, PropR (f x)) : PropR f.
Proof. crush. Qed.

(** In other words, there is no less of generality instatiating
arguments for which the relation is simply [eq]. On the contrary, this
improves proof search. *)


(** ** Monotone operations *)

Instance extr_propr {X} {RX: Rel X} : PropR (extr (X:=X)).
Proof.
  rewrite extr_spec.
  crush.
  exact Hxy.
Qed.

Instance load_propr a : PropR (load a).
Proof.
  rewrite load_spec.
  crush.
  apply extr_propr, Hfg.
Qed.

Instance loadMany_propr n a : PropR (loadMany n a).
Proof.
  revert a; induction n; intros a; simp loadMany; crush.
Qed.

Instance next_propr n : PropR (next n).
Proof. induction n; simp next; crush. Qed.

Instance store_propr a o : PropR (store a o).
Proof.
  rewrite store_spec.
  crush.
  apply Hfg.
Qed.

Instance storeMany_propr a lst : PropR (storeMany a lst).
Proof.
  revert a.
  induction lst as [|x r IH]; intros a;
    simp storeMany; crush.
Qed.

Instance push_propr u : PropR (push u).
Proof.
  rewrite push_spec.
  crush.
Qed.

Instance pushManyR_propr u : PropR (pushManyR u).
Proof.
  induction u; simp pushManyR; crush.
Qed.

Instance pushMany_propr u : PropR (pushMany u).
Proof. crush. Qed.

Instance pop_propr : PropR pop.
Proof.
  rewrite pop_spec. crush.
Qed.

Instance popMany_propr n : PropR (popMany n).
Proof.
  induction n; simp popMany; crush.
Qed.

Instance pop64_propr: PropR pop64.
Proof. unfold pop64. crush. Qed.

Instance pushZ_propr z: PropR (pushZ z).
Proof. unfold pushZ. crush. Qed.

Instance storeZ_propr n a z : PropR (storeZ n a z).
Proof. unfold storeZ. crush. Qed.

Local Open Scope N.

Instance setPixel_propr x y c : PropR (setPixel x y c).
Proof.
  rewrite setPixel_spec. unfold updatePixel.
  crush;
    destruct Hij as [Hw [Hh Hi]];
    [ | congruence | congruence ].
  exists Hw. exists Hh. intros x' Hx' y' Hy'. simpl.
  destruct (decide (x' = x /\ y' = y)).
  - reflexivity.
  - exact (Hi x' Hx' y' Hy').
Qed.

Instance readPixel_propr x y : PropR (readPixel x y).
Proof. rewrite readPixel_spec. crush. Qed.

Lemma image_complete_lemma
      {i i': Image (option OutputColor)}
      (Hi: i ⊑ i') (Hc: image_complete i) : i = i'.
Proof.
  destruct i as [w h p].
  destruct i' as [w' h' p'].
  destruct Hi as [Hw [Hh Hp]].
  simpl in *. subst w'. subst h'.
  apply f_equal.
  extensionality x. extensionality Hx.
  extensionality y. extensionality Hy.
  specialize (Hp x Hx y Hy). simpl in Hp.
  specialize (Hc x Hx y Hy). simpl in Hc.
  rewrite <- (some_extract Hc) in *.
  destruct (p' x Hx y Hy) as [c'|].
  - unfold rel in Hp.
    destruct (extract Hc) as [[r g] b].
    destruct c' as [[r' g'] b'].
    cbn in Hp.
    destruct Hp as [[Hr Hg] Hb].
    crush.
  - crush.
Qed.

Instance newFrame_propr w h r: PropR (newFrame w h r).
Proof.
  rewrite newFrame_spec, extractImage_spec.
  crush; destruct (image_complete_lemma Hij HL).
  - destruct (proof_irrelevance _ HL HL0). reflexivity.
  - contradict HR. exact HL.
Qed.

Close Scope N.


(** ** Monotone steps *)

Global Instance oneStep_propr : PropR oneStep.
Proof.
  unfold oneStep. crush.
  destruct (y: Z) eqn:Hy;
    [ crush; reflexivity | | simp oneStep'; crush].

  (* Is there a more elegant way to do this. *)
  unfold oneStep'.
  repeat (match goal with
            [|- context [match _ with xI _ => _ | xO _ => _ | xH => _ end]] =>
            destruct p end).
  all:
    try rewrite putByte_spec;
    try rewrite putChar_spec;
    try rewrite addSample_spec;
    try rewrite readFrame_spec;
    crush.
Qed.

Global Instance nSteps_propr n : PropR (nSteps n).
Proof.
  induction n; simp nSteps; unfold chain; crush.
  destruct y; crush.
Qed.
