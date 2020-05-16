Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Operations.
Require Import Assembly.Machine.
Require Import Assembly.Mono.


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
