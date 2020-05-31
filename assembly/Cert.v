Require Import Equations.Equations.

From Assembly Require Import Convenience Dec Lens Mon Operations Bits Machine Rel Mono.
Set Implicit Arguments.


(** ** Certified programs *)

Inductive Reach (stop: State) : forall (cont: bool) (start: State), Prop :=
| Stop s : stop ⊑ s -> Reach stop true s
| Exit s' s : oneStep s = Some (s', false) -> stop ⊑ s' -> Reach stop false s
| More c s' s : oneStep s = Some (s', true) -> Reach stop c s' -> Reach stop c s.

Arguments Stop {_} {_}.
Arguments Exit {_} {_} {_}.
Arguments More {_} {_} {_} {_}.

Lemma generalize_stop {s1 s2 s3 c} (Hs: s3 ⊑ s2) (Hr: Reach s2 c s1) : Reach s3 c s1.
Proof using.
  induction Hr as [s1 H | s1' s1 Ho H | c s1' s1 Ho Hr IH];
    [apply Stop | apply (Exit Ho) | exact (More Ho IH)];
    transitivity s2; assumption.
Qed.

(* TODO: Why is this needed? *)
Instance osb_relation : Rel (option (State * bool)) :=
  option_relation (prod_relation _ eq_relation).

Notation oneStep := (@oneStep Mono.MP1 estParams2).

Lemma generalize_start {s1 s2 s3 c} (Hr: Reach s3 c s2) (Hs: s2 ⊑s1) : Reach s3 c s1.
Proof using. (* TODO: clean up *)
  revert s1 Hs.
  induction Hr as [s2 H | s2' s2 Ho H | c s2' s2 Ho Hr IH]; intros s1 Hs.
  - apply Stop; transitivity s2; assumption.
  - assert (oneStep s2 ⊑ oneStep s1) as H_one.
    + unfold rel, option_relation.
      exact (oneStep_propR Hs).
    + clear Hs.
      rewrite Ho in H_one. clear Ho.
      destruct (oneStep s1) as [[s1' b]|] eqn:H1.
      * cbn in H_one.
        destruct H_one as [Ho1 Ho2].
        unfold rel, eq_relation in Ho2.
        subst b.
        apply (Exit H1).
        transitivity s2'; assumption.
      * contradict H_one.

  - assert (oneStep s2 ⊑ oneStep s1) as H_one.
    + unfold rel, option_relation.
      exact (oneStep_propR Hs).
    + clear Hs.
      rewrite Ho in H_one. clear Ho.
      destruct (oneStep s1) as [[s1' b]|] eqn:H1.
      * cbn in H_one.
        destruct H_one as [Ho1 Ho2].
        unfold rel, eq_relation in Ho2.
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

Local Definition not_terminated := ret true.
Local Definition terminated := ret false.

(** The empty program has no effect. *)
Example null_cert : Cert (not_terminated).
Proof using.
  intros s.
  simpl.
  apply Stop.
  unfold PropR.
  reflexivity.
Qed.

Notation PC := (@PC concreteParams0 Mono.MP1).

Require Import Assembly.OpCodes.


(** ** First real example, the NOP program *)

(* TODO: Triggers coq-equations bug without [noind].
   "Error: Incorrect universe constraints declared for inductive type." *)
Equations(noind) opsAtPc (ops: list B8) (s: State) : Prop :=
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
    (* TODO: Fix *)
    + destruct (proj MEM s (proj PC s) H) as [x|];
      typeclasses eauto.
    + typeclasses eauto.
Qed.

Instance nop_cert:
  Cert (let* s := get in
        assert* opsAtPc [toB8 NOP] s in
        let* pc := get' PC in
        put' PC (offset 1 pc);;
        ret true).
Proof.
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


(** ** Second attempt, the NOP program revisited *)

Definition assumingOps (expected: list nat) : M unit :=
  let* pc := get' PC in
  let* actual := loadMany (length expected) pc in
  assert* (actual = (map toB8 (map Z.of_nat expected)) :> list B8) in
  ret tt.

Definition incPC z : M unit :=
  let* pc := get' PC in
  put' PC (offset z pc).

Instance nop_cert:
  Cert (assumingOps [NOP];;
        incPC 1;;
        not_terminated).
Proof.

(***** To be continued *****)
