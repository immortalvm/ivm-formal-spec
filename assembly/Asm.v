Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Operations.
Require Import Assembly.Machine.
Require Assembly.OpCodes.


(** ** Specialization *)

Arguments proj : clear implicits.
Arguments proj {_} {_}.
Arguments update : clear implicits.
Arguments update {_} {_}.

Notation MEM := (Machine.MEM).
Notation OUT_IMAGE := (Machine.OUT_IMAGE).

(** *** Memory specialization *)

Definition memRel (m m': Memory) := forall a Ha, m a Ha -> m' a Ha = m a Ha.

Instance memRel_reflexive : Reflexive memRel.
Proof.
  intros m a Ha H. reflexivity.
Qed.

Instance memRel_transitive : Transitive memRel.
Proof.
  intros m1 m2 m3 H12 H23 a Ha H.
  derive H (some_some H).
  destruct H as [x H].
  specialize (H12 a Ha). rewrite H in H12. specialize (H12 I).
  specialize (H23 a Ha). rewrite H12 in H23. specialize (H23 I).
  rewrite H, H23.
  reflexivity.
Qed.


(** *** Output image specialization *)

Import EqNotations.

Definition oiRel (i i': Image (option OutputColor)) :=
  exists (Hw: width i = width i')
    (Hh: height i = height i'),
    forall x Hx y Hy, @pixel _ i x Hx y Hy ->
                 @pixel _ i x Hx y Hy =
                 @pixel _ i' x (rew Hw in Hx) y (rew Hh in Hy).

Instance oiRel_reflexive : Reflexive oiRel.
Proof.
  intros i.
  exists eq_refl, eq_refl.
  intros x Hx y Hy.
  reflexivity.
Qed.

Instance oiRel_transitive : Transitive oiRel.
Proof.
  intros i1 i2 i3 [Hw12 [Hh12 H12]] [Hw23 [Hh23 H23]].
  exists (eq_Transitive _ _ _ Hw12 Hw23).
  exists (eq_Transitive _ _ _ Hh12 Hh23).
  intros x Hx y Hy H.
  derive H (some_some H).
  destruct H as [c H].
  specialize (H12 x Hx y Hy). rewrite H in *. specialize (H12 I).
  specialize (H23 x (rew Hw12 in Hx) y (rew Hh12 in Hy)). rewrite <- H12 in H23. specialize (H23 I).
  rewrite H23.
  unfold eq_Transitive.
  do 2 rewrite rew_compose.
  reflexivity.
Qed.


(** ** Monotonicity *)

Section monotonicity_section.

  Local Ltac rewr := repeat (independent_rewrite1 || proj_rewrite1 || simpl).

  Let RS : relation State := proj_relation (proj_prod MEM OUT_IMAGE) (prod_relation memRel oiRel).

  Let RM {A} (R: relation A) : relation (M A) := est_relation (RS:=RS) R.


  (** *** Rel *)

  Class Rel (A: Type) := rel : relation A.

  Arguments rel : clear implicits.
  Arguments rel {_} _.
  Class Rela {A} {HA: Rel A} (a a': A) := rela : rel HA a a'.
  Infix "⊑" := Rela (at level 70).

  Notation PropR a := (a ⊑ a).
  (* Instance proper_propR {A} {HA: Rel A} (a: A) {Pa: Proper (rel HA) a} : PropR a | 10 := Pa. *)

  Instance eq_Rel A : Rel A | 20 := { rel := eq }.
  Instance eq_Rela A (a: A) : @Rela A (eq_Rel A) a a := eq_refl.

  Instance fun_Rel {A B} (HA: Rel A) (HB: Rel B) : Rel (A -> B) | 10 :=
    fun f f' => forall (a a': A), a ⊑ a' -> f a ⊑ f' a'.

  (* TODO: Coordinate with option_relation and prod_relation!! *)
  Instance opt_Rel {A} (HA: Rel A) : Rel (option A) | 5 :=
    fun x x' =>
      match x, x' with
      | None, _ => True
      | Some _, None => False
      | Some x, Some x' => x ⊑ x'
      end.

  Instance prod_Rel {A B} (HA: Rel A) (HB: Rel B) : Rel (A * B) | 5 :=
    fun p p' =>
      match p, p' with
      | (a, b), (a', b') => a ⊑ a' /\ b ⊑ b'
      end.

  Instance mem_Rel : Rel Memory := memRel.
  Instance oi_Rel : Rel (Image _) := oiRel.
  Instance rs_Rel : Rel State := RS.
  Instance rm_Rel {A} (HA: Rel A) : Rel (M A) := RM (rel HA).


  (** *** Get *)

  Instance getMem_propR : PropR (get' MEM).
  Proof.
    intros s s' Hs. split; [|destruct Hs as [_ [Hs _]]]; exact Hs.
  Qed.

  Instance getOi_propR : PropR (get' OUT_IMAGE).
  Proof.
    intros s s' Hs. split; [|destruct Hs as [_ [_ Hs]]]; exact Hs.
  Qed.

  (** We have ordered the assumptions that the projections are pairwise
      independent so that we won't have to combine the following with
      [independent_symm]. Similarly for [putOther_propR] below. *)

  Instance getOther_propR X
           (PX: Proj State X)
           (Imem: Independent MEM PX)
           (Ioi: Independent OUT_IMAGE PX) : PropR (get' PX).
  Proof.
    intros s s' Hs.
    split; [exact Hs|].
    destruct Hs as [Hs _].
    unfold aligned in Hs.
    simpl in Hs.
    rewrite <- Hs.
    now rewr.
  Qed.


  (** *** Put *)

  Local Ltac putTactic PX x x' Hx:=
    try (cbv in Hx; subst x);
    intros s s' Hs;
    (split; [|reflexivity]);
    (split; [|split]);
    [ destruct Hs as [Hs _];
      derive Hs (f_equal (fun t => update PX t x') Hs);
      simpl in Hs;
      rewrite <- Hs;
      unfold aligned;
      now rewr
    | |].

  Instance putMem_Rela (m m': Memory) (Hm: m ⊑ m') : put' MEM m ⊑ put' MEM m'.
  Proof.
    putTactic MEM m m' Hm.
    - rewr. exact Hm.
    - destruct Hs as [_ [_ Hs]]. rewr. exact Hs.
  Qed.

  Instance putOi_Rela (i i': Image _) (Hi: i ⊑ i') : put' OUT_IMAGE i ⊑ put' OUT_IMAGE i'.
  Proof.
    putTactic OUT_IMAGE i i' Hi.
    - destruct Hs as [_ [Hs _]]. rewr. exact Hs.
    - rewr. exact Hi.
  Qed.

  Instance putOther_Rela X
           (PX: Proj State X)
           (Imem: Independent MEM PX)
           (Ioi: Independent OUT_IMAGE PX)
           (x x': X)
           (Hx: x ⊑ x') : put' PX x ⊑ put' PX x'.
  Proof.
    putTactic PX x x' Hx.
    - destruct Hs as [_ [Hs _]]. rewr. exact Hs.
    - destruct Hs as [_ [_ Hs]]. rewr. exact Hs.
  Qed.


  (** Load *)

  Instance fun_propR {A B} {HA: Rel A} {HB: Rel B} (f: A -> B)
           (HR: forall a a' (HR: Rela a a'), Rela (f a) (f a')) : PropR f.
  Proof.
    intros a a' Ha. apply HR. exact Ha.
  Qed.

  Global Instance bind_propR {A B} (HA: Rel A) (HB: Rel B) : PropR (@bind _ M _ A B).
  Proof.
    intros ma ma' Hma f f' Hf.
    intros s s' Hs. simpl.
    specialize (Hma s s' Hs).
    destruct (ma s) as [(t,a)|]; destruct (ma' s') as [(t',a')|].
    - destruct Hma as [Ht Ha].
      exact (Hf _ _ Ha _ _ Ht).
    - contradict Hma.
    - exact I.
    - exact I.
  Qed.

  Global Instance err_propR {A} (HA: Rel A): PropR (err: M A).
  Proof.
    intros s s' Hs. exact I.
  Qed.

  Global Instance ret_propR {A} (HA: Rel A) (a a': A) (Ha: @Rela _ HA a a') : @Rela _ (rm_Rel HA) (ret a) (ret a').
  Proof.
    intros s s' Hs.
    simpl.
    split; assumption.
  Qed.

  Ltac crush :=
  match goal with
  | [|- PropR ?a] =>
    match type of a with
    | (_ -> _) -> _ =>
      apply fun_propR;
        let f := fresh "f" in
        let g := fresh "g" in
        let Hfg := fresh "Hfg" in
        intros f g Hfg
    | _ -> _ =>
      apply fun_propR;
        let x := fresh "x" in
        let y := fresh "y" in
        let Hxy := fresh "Hxy" in
        intros x y Hxy
    end
  | [H : @Rela _ (eq_Rel _) ?x ?x' |- _] => cbv in H; first [subst x|subst x']

  | [|- Rela (match ?H with left _ => _ | right _ => _ end) _] => destruct H as [HL|HR]

  | [|- Rela (bind _ _) (bind _ _)] => unshelve eapply bind_propR

  | [|- Rela (ret _) (ret _)] => unshelve eapply ret_propR

  | [|- Rela err _] => unshelve eapply err_propR

  | [|- PropR _] => typeclasses eauto

  | [|- Rela (match ?H with Some _ => _ | None => _ end) _] =>
    let u := fresh "u" in
    let Hu := fresh "Hu" in
    destruct H as [u|] eqn:Hu

  | [|- Rela _ (match ?H with Some _ => _ | None => _ end)] =>
    let v := fresh "v" in
    let Hv := fresh "Hv" in
    destruct H as [v|] eqn:Hv

  | [|- Rela (put' MEM _) (put' MEM _)] => unshelve eapply putMem_Rela
  | [|- Rela (put' OUT_IMAGE _) (put' OUT_IMAGE _)] => unshelve eapply putOi_Rela
  | [|- Rela (put' _ _) (put' _ _)] => unshelve eapply putOther_Rela

  | _ => unfold popMany, pushMany

  end.

  Instance load_propR a : PropR (load a).
  Proof.
    repeat (crush || unfold load);
      specialize (Hfg a HL); rewrite Hu, Hv in *.
    - injection (Hfg I). congruence.
    - discriminate (Hfg I).
  Qed.

  Instance nextN_propR n : PropR (nextN n).
  Proof.
    repeat (unfold nextN, next; crush).
    revert y.
    induction n as [|n IH];
      intro a;
      simp loadMany;
      repeat crush.
  Qed.

  Instance popN_propR: PropR popN.
  Proof.
    repeat (unfold popN, loadMany; crush).
  Qed.

  Instance pop64_propR: PropR pop64.
  Proof.
    unfold pop64. repeat crush.
  Qed.

  Instance storeMany_propR a lst : PropR (storeMany a lst).
  Proof.
    revert a.
    induction lst as [|x r IH]; intro a; repeat (crush || simp storeMany).
    unfold store.
    repeat crush.
    intros a' HL'.
    destruct (eq_dec a a') as [Ha|Ha]; [easy|].
    specialize (Hfg a' HL').
    destruct (f a' HL') as [fa'|] eqn:Hfa.
    - exact Hfg.
    - intros [].
  Qed.

  Instance push64_propR z: PropR (push64 z).
  Proof.
    unfold push64. repeat crush.
  Qed.

  Instance loadN_propR n a : PropR (loadN n a).
  Proof.
    unfold loadN. repeat crush.
    revert a.
    induction n as [|n IH]; intro a; simp loadMany; repeat crush.
  Qed.

  Instance storeZ_propR n a z : PropR (storeZ n a z).
  Proof.
    unfold storeZ. repeat crush.
  Qed.

  Global Instance oneStep_propR : PropR oneStep.
  Proof.
    unfold oneStep.
    repeat crush.
    destruct y as [|n]; repeat crush.
    (* TODO: Increase to 256. Beware: It will take a long time! *)
    Ltac print := match goal with [|- _ (_ ?i)] => idtac i end.
    do 23 (try (destruct n as [|n]; print; simp oneStep'; repeat crush)).


    (********** Continue from here *********)

  Admitted.


(** ** Certified programs *)

Inductive Reach (stop: State) : forall (cont: bool) (start: State), Prop :=
| Stop s : stop ⊑ s -> Reach stop true s
| Exit s' s : oneStep s = Some (s', false) -> stop ⊑ s' -> Reach stop false s
| More c s' s : oneStep s = Some (s', true) -> Reach stop c s' -> Reach stop c s.

Arguments Stop {_} {_}.
Arguments Exit {_} {_} {_}.
Arguments More {_} {_} {_} {_}.

Lemma generalize_stop {s1 s2 s3 c} (Hs: s3 ⊑ s2) (Hr: Reach s2 c s1) : Reach s3 c s1.
Proof.
  induction Hr as [s1 H | s1' s1 Ho H | c s1' s1 Ho Hr IH];
    [apply Stop | apply (Exit Ho) | exact (More Ho IH)];
    unfold Rela in *; transitivity s2; assumption.
Qed.

Lemma generalize_start {s1 s2 s3 c} (Hr: Reach s3 c s2) (Hs: Rela s2 s1) : Reach s3 c s1.
Proof. (* TODO: clean up *)
  revert s1 Hs.
  induction Hr as [s2 H | s2' s2 Ho H | c s2' s2 Ho Hr IH]; intros s1 Hs.
  - apply Stop; unfold Rela in *; transitivity s2; assumption.
  - assert (Rela (oneStep s2) (oneStep s1)) as H_one.
    + unfold Rela, rel, opt_Rel.
      exact (oneStep_propR s2 s1 Hs).
    + clear Hs.
      rewrite Ho in H_one. clear Ho.
      destruct (oneStep s1) as [[s1' b]|] eqn:H1.
      * cbn in H_one.
        destruct H_one as [Ho1 Ho2].
        unfold Rela, rel, eq_Rel in Ho2.
        subst b.
        apply (Exit H1).
        unfold Rela in*.
        transitivity s2'; assumption.
      * contradict H_one.

  - assert (Rela (oneStep s2) (oneStep s1)) as H_one.
    + unfold Rela, rel, opt_Rel.
      exact (oneStep_propR s2 s1 Hs).
    + clear Hs.
      rewrite Ho in H_one. clear Ho.
      destruct (oneStep s1) as [[s1' b]|] eqn:H1.
      * cbn in H_one.
        destruct H_one as [Ho1 Ho2].
        unfold Rela, rel, eq_Rel in Ho2.
        subst b.
        specialize (IH s1' Ho1).
        apply (More H1 IH).
      * contradict H_one.
Qed.

Class Cert (spec: M bool) :=
  evidence s:
    match spec s with
    | Some (s', b) => Reach s' b s
    | None => True
    end.

Example true_cert : Cert (ret true).
Proof.
  intros s.
  simpl.
  apply Stop.
  unfold PropR.
  reflexivity.
Qed.

Notation PC := (Machine.PC).

Equations opsAtPc (ops: list B8) (s: State) : Prop :=
  opsAtPc [] _ := True;
  opsAtPc (x :: r) s :=
    let pc := proj PC s in
    match decision (available pc) with
    | right _ => False
    | left H =>
      match proj MEM s pc H with
      | None => False
      | Some x' => x' = x /\ opsAtPc r (update PC s (offset 1 pc))
      end
    end.

Instance opsAtPc_decidable ops s : Decidable (opsAtPc ops s).
Proof.
  revert s.
  induction ops; intros s.
  - simp opsAtPc. typeclasses eauto.
  - simp opsAtPc.
    simpl.
    destruct (decision (available (proj PC s))) as [H|H].
    + destruct (proj MEM s (proj PC s) H) as [x|];
      typeclasses eauto.
    + typeclasses eauto.
Qed.

Require Import Assembly.OpCodes.

Instance nop_cert:
  Cert (let* s := get in
        assert* opsAtPc [toB8 NOP] s in
        let* pc := get' PC in
        put' PC (offset 1 pc);;
        ret true).
Proof. (* TODO: clean up / automate *)
  intros s. simpl.
  destruct (decision (opsAtPc [toB8 1] s)) as [Hs|Hs]; [|exact I].

  set (s' := update PC s (offset 1 (proj PC s))).
  assert (nextN 1 s = Some (s', 1)) as H1.

  - unfold nextN, next. simpl. unfold load. simpl.
    simp opsAtPc in Hs. simpl in Hs.
    set (pc := proj PC s) in *.
    destruct (decision (available pc)) as [HA|HA].
    + destruct (proj MEM s pc HA) as [x|].
      * destruct Hs as [? _]. subst x. reflexivity.
      * destruct Hs.
    + destruct Hs.

  - refine (@More s' true _ s _ _).
    + unfold oneStep. simpl.
      rewrite H1. simp oneStep'.
      reflexivity.
    + apply Stop. unfold PropR. reflexivity.
Qed.
