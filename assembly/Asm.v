Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Operations.
Require Assembly.OpCodes.


(** ** Specialization *)

Arguments proj : clear implicits.
Arguments proj {_} {_}.
Arguments update : clear implicits.
Arguments update {_} {_}.


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

  Let RS : relation State := proj_relation (proj_prod MEM OUT_IMAGE) (prod_relation memRel oiRel).

  Let RM {A} (R: relation A) : relation (M A) := est_relation RS R.

  Instance load_propR : Proper (eq ==> RM eq) load.
  Proof.
    intros a a' Ha. subst a'.
    intros s s' Hs.
    unfold load.
    destruct (decision (available a)) as [Ha|Ha].
    - unfold get'.
      unshelve eapply bind_propR.
      + exact memRel.
      + unshelve eapply proper_prf.
        unshelve eapply bind_propR.
        * exact RS.
        * apply get_propR.
        * intros t t' Ht.
          unshelve eapply (@ret_propR State RS Memory memRel).
          destruct Ht as [_ [Ht _]].
          exact Ht.
      + intros m m' Hm.
        specialize (Hm a Ha).
        destruct (m a Ha) as [x|] eqn:Hx;
        destruct (m' a Ha) as [x'|] eqn:Hx'.
        * specialize (Hm I).
          inversion Hm.
          subst x'.
          intros t t' Ht.
          split; [assumption|reflexivity].
        * specialize (Hm I).
          discriminate Hm.
        * intros t t' Ht. exact I.
        * intros t t' Ht. exact I.
      + exact Hs.
    - exact I.
  Qed.

  (************* Continue from here ***********)

  (* TODO: Create specialized tactic! *)

  Global Instance oneStep_propR : Proper (RM eq) oneStep.
  Proof.
    unfold oneStep.
    unshelve eapply bind_propR.
    - exact eq.
    - intros s s' Hs.
      unfold nextN, next.
      simpl.

      destruct (next 1 s) as [x|]; destruct (next 1 s') as

unfold RS, est_relation.
      simpl.


reflexivity.


      Unshelve.
    3: exact eq.
    reflexivity.
repeat shelve. Unshelve.


    intros s s' Hs.





(*************** Rewrite/remove below *****************)

Inductive Reach (stop: State) : forall (start: State), Prop :=
| Stop s : Specializes stop s -> Reach stop s
| More s' s : oneStep s = Some (s', true)
              -> Reach stop s'
              -> Reach stop s.

Arguments Stop {_} {_}.
Arguments More {_} {_} {_}.

Lemma generalize_stop {s1 s2 s3} (Hs: Specializes s3 s2) (Hr: Reach s2 s1) : Reach s3 s1.
Proof.
  induction Hr as [s1 H | s1' s1 H Hr IH].
  - apply Stop. transitivity s2; assumption.
  - exact (More H IH).
Qed.

Lemma specialize_start {s1 s2 s3} (Hr: Reach s3 s2) (Hs: Specializes s2 s1) : Reach s3 s1.
Proof.
  induction Hr as [s2 H | s2' s2 H Hr IH].
  - apply Stop. transitivity s2; assumption.
  -


Equations join {s1 s2 s3: State} (Hr2: Reach s3 s2) (Hr1: Reach s2 s1) : Reach s3 s1 :=
  join Hr2 (Stop Hs) := specializes_reach Hs Hr2;
  join Hr2 (More H Hr) := More H (join Hr2 Hr).

Instance reach_transitive : Transitive Reach.
Proof.
  intros x y z. exact join.
Qed.

Definition Cert : Type :=
  forall (s: State), option { s' : State | Reach s' s }.  (* ! *)

Example true_verif : Cert :=
  fun s => Some (exist s (Stop s)).

(** Weakening the claim by strengthening the precondition. *)
Definition weaken (v: Cert) (f: State -> bool) : Cert :=
  fun s => if f s then v s else None.

Definition join_verifs (v1 v2 : Cert) : Cert.
  refine (
      fun s0 => match v1 s0 with
             | None => None
             | Some (exist s1 H1) =>
               match v2 s1 with
               | None => None
               | Some (exist s2 H2) => Some (exist s2 _)
               end
             end).
  transitivity s1; [ exact H2 | exact H1 ].
Defined.

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

(* TODO: Is this useful?

Inductive opsAtPc' : list B8 -> State -> Prop :=
| NilOpsAtPc s : opsAtPc' [] s
| ConsOpsAtPc x rest s :
    let pc := proj PC s in
    (exists (H: available pc), proj MEM s pc H = Some x)
    -> opsAtPc' rest (update PC s (offset 1 pc))
    -> opsAtPc' (x :: rest) s.

Lemma inv_opsAtPc {ops s} (Ho: opsAtPc ops s) : opsAtPc' ops s.
Proof.
  revert s Ho.
  induction ops as [|x rest IH]; intros s Ho.
  - exact (NilOpsAtPc s).
  - simp opsAtPc in Ho. simpl in Ho.
    destruct (decision (available (proj PC s))) as [H|H].
    + assert (exists y, proj MEM s (proj PC s) H = Some y) as Hy.
      * destruct (proj MEM s (proj PC s) H) as [y|].
        -- exists y. congruence.
        -- destruct Ho.
      * destruct Hy as [y Hy].
        constructor.
        -- exists H.
           rewrite Hy in *. clear Hy.
           destruct Ho as [Ho _]. congruence.
        -- rewrite Hy in *. clear Hy.
           destruct Ho as [_ Ho].
           exact (IH _ Ho).
    + destruct Ho.
Qed.

 *)

Definition nop_cert : Cert.
  intros s.
  refine (
      let s' := update PC s (offset 1 (proj PC s)) in
      let ops := map (fun (x:nat) => toB8 x) [NOP] in
      match decision (opsAtPc ops s) with
      | right _ => None
      | left Hs => Some (exist s' (More s' s' s _ (Stop s')))
      end).

  (* TODO: Automate! *)

  subst ops. simpl in *.
  unfold oneStep. simpl.
  assert (nextN 1 s = Some (s', 1)) as H1.

  - unfold nextN, next. simpl. unfold load. simpl.
    simp opsAtPc in Hs. simpl in Hs.
    set (pc := proj PC s) in *.
    destruct (decision (available pc)) as [HA|HA].
    + destruct (proj MEM s pc HA) as [x|].
      * destruct Hs as [? _]. subst x. reflexivity.
      * destruct Hs.
    + destruct Hs.

  - rewrite H1. simp oneStep'. reflexivity.
Defined.
