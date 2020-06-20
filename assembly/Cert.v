From Assembly Require Import Mono.

Unset Suggest Proof Using.

(* Does it create more problems than it solves? *)
(* Set Implicit Arguments. *)

(* TODO: Move to Mono.v *)
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
Proof using.
  intros s. repeat split; reflexivity.
Qed.

Instance srel_transitive : Transitive state_relation.
Proof using.
  intros s1 s2 s3 H12 H23.
  srel_destruct H12.
  srel_destruct H23.
  repeat split; transitivity s2; assumption.
Qed.


(** ** Certified programs *)

Inductive Reach (stop: State) : forall (cont: bool) (start: State), Prop :=
| Stop s : stop ⊑ s -> Reach stop true s
| Exit s' s : oneStep s = Some (s', false) -> stop ⊑ s' -> Reach stop false s
| More c s' s : oneStep s = Some (s', true) -> Reach stop c s' -> Reach stop c s.

Derive Signature for Reach.

Arguments Stop {_} {_}.
Arguments Exit {_} {_} {_}.
Arguments More {_} {_} {_} {_}.

Lemma generalize_stop {s1 s2 s3 c} (Hs: s3 ⊑ s2) (Hr: Reach s2 c s1) : Reach s3 c s1.
Proof.
  induction Hr as [s1 H | s1' s1 Ho H | c s1' s1 Ho Hr IH];
    [apply Stop | apply (Exit Ho) | exact (More Ho IH)];
    transitivity s2; assumption.
Qed.

(* TODO: Why is this needed? *)
Instance osb_relation : Rel (option (State * bool)) :=
  option_relation (prod_relation _ eq_relation).

Notation oneStep := (@oneStep Mono.MP1 estParams2).

Lemma generalize_start {s1 s2 s3 c} (Hr: Reach s3 c s2) (Hs: s2 ⊑s1) : Reach s3 c s1.
Proof. (* TODO: clean up *)
  revert s1 Hs.
  induction Hr as [s2 H | s2' s2 Ho H | c s2' s2 Ho Hr IH]; intros s1 Hs.
  - apply Stop; transitivity s2; assumption.
  - assert (oneStep s2 ⊑ oneStep s1) as H_one.
    + unfold rel, option_relation.
      exact (oneStep_propr Hs).
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
      exact (oneStep_propr Hs).
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

Lemma reach_comp {s1 s2 s3 t} (H23: Reach s3 t s2) (H12: Reach s2 true s1) : Reach s3 t s1.
Proof.
  depind H12.
  - exact (generalize_start H23 H).
  - exact (More H (IHReach _ _ H23)).
Qed.


(** ** Cert *)

Notation M := (@M _ estParams2).

Class Cert (spec: M bool) :=
  evidence s:
    match spec s with
    | Some (s', b) => Reach s' b s
    | None => True
    end.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(** The empty program has no effect. *)
Instance cert_id : Cert (not_terminated).
Proof.
  intros s.
  simpl.
  apply Stop.
  unfold PropR.
  reflexivity.
Qed.

Instance cert_comp (u: M bool) {Cu: Cert u} (v: M bool) {Cv: Cert v} :
  Cert (let* t := u in
        if t then v else ret false).
Proof.
  intros s. specialize (Cu s). simpl.
  destruct (u s) as [[s' t]|] eqn:Hu; [|exact I].
  destruct t eqn:Ht.
  - specialize (Cv s').
    destruct (v s') as [[s'' t']|] eqn:Hvs; [|exact I].
    exact (reach_comp Cv Cu).
  - exact Cu.
Qed.





(* TODO: Move *)

Instance dec_decidable {P: Prop} {HP: Decidable P}
         (f: P -> Prop) {Hf: forall H, Decidable (f H)}
         (g: not P -> Prop) {Hg: forall H, Decidable (g H)}:
  Decidable match decide P with
            | left H => f H
            | right H => g H
            end.
Proof.
  destruct (decide P) as [H|H].
  - apply Hf.
  - apply Hg.
Defined.

Instance opt_decidable {X}
         (f: X -> Prop) {Hf: forall x, Decidable (f x)}
         (Q: Prop) {HQ: Decidable Q}
         {ox: option X} :
  Decidable match ox with
            | Some x => f x
            | None => Q
            end.
Proof.
  destruct ox as [x|].
  - apply Hf.
  - exact HQ.
Defined.


(** ** Basic certs *)

Instance cert1 {u: M unit} (b: bool)
         (H: forall s, match u s with
                  | Some (s', _) => Reach s' b s
                  | None => True
                  end) : Cert (u;; ret b).
Proof.
  intros s.
  specialize (H s).
  simpl.
  destruct (u s) as [[s' _]|]; exact H.
Qed.

(* TODO: Move to Init.v *)
Instance Z_EqDec: EqDec Z := Z.eq_dec.

Equations swallow (ops: list Z) : M unit :=
  swallow [] := ret tt;
  swallow (op :: rest) :=
    let* pc := get' PC in
    let* x := load pc in
    assert* x = op :> Z in
    put' PC (offset 1 pc);;
    swallow rest.

(* TODO: Replace faulty proof in Convenience.v. *)
Lemma to_list_equation_1: forall A, to_list []%vector = nil :> list A.
Proof. reflexivity. Qed.
Hint Rewrite to_list_equation_1 : to_list.

(* TODO: simplify? *)
Ltac comp :=
  repeat (
      simpl
    || simp to_list fromLittleEndian toBits bitListToNat).

Ltac cert_start :=
  apply cert1; intros s;
  simp swallow; simpl;
  (destruct load as [[s' x]|] eqn:H1; [|exact I]);
  (destruct decide; [subst x|exact I]).

Section offset_opaque_section.

  Opaque offset.

  Global Instance cert_exit : Cert (swallow [EXIT];;
                                    terminated).
  Proof.
    cert_start.
    set (stop := update _ _ _).
    refine (Exit _ ltac:(reflexivity)).
    unfold oneStep. simpl.
    rewrite H1. comp.
    reflexivity.
  Qed.

  Instance cert_nop: Cert (swallow [NOP];;
                           not_terminated).
  Proof.
    cert_start.
    set (stop := update _ _ _).
    refine (More _ (Stop ltac:(reflexivity))).
    unfold oneStep. simpl.
    rewrite H1. comp.
    reflexivity.
  Qed.


(** Assembler jump_zero *)

Equations availableBefore (a: Addr) (n: nat) : M unit :=
  availableBefore _ 0 := ret tt;
  availableBefore a (S n) :=
    assert* (available (offset (S n) a)) in
    availableBefore a n.

Definition requireStack (n: nat) : M unit :=
  let* sp := get' SP in
  availableBefore sp (8 * n).

Definition isZero := [PUSH1; toB8 1; LT].

Definition boolRep (P: Prop) {DP: Decidable P} : Z :=
  if decide P then (-1)%Z else 0%Z.

Instance cert_isZero : Cert (swallow isZero;;
                             requireStack 1;;
                             let* n := popN in
                             push64 (boolRep (n = 0));;
                             not_terminated).
Proof.
  setoid_rewrite <- bind_assoc at 3.
  setoid_rewrite <- bind_assoc at 2.
  setoid_rewrite <- bind_assoc at 1.

  apply cert1. intros s. unfold isZero, requireStack.
  simpl mult. rewrite swallow_equation_2.
  (* simp swallow. *)
  (* Does not work here: simp availableBefore.
     Neither does: setoid_rewrite availableBefore_equation_2. *)

  simpl.
  (destruct load as [[s' x]|] eqn:H1; [|exact I]).




  setoid_rewrite bind_assoc.

simpl.
  (destruct decide; [subst x|exact I]).

  cert_start.



Definition pushNum (z: Z) :=
  (* Non-optimized *)
  PUSH8 :: toLittleEndian 8 z.

Definition pop n :=
  let pop1 := [JUMP_ZERO; toB8 0] in
  match n with
  | 0 => []
  | 1 => pop1
  | 2 => pop1 ++ pop1
  | n => [GET_SP] ++ pushNum (n * 8) ++ [ADD; SET_SP]
  end.

Definition genericConditional interjection :=
  [
    GET_SP; PUSH1; toB8 8; ADD; LOAD8 (* a::x::r -> x::a::x::r *)
  ] ++ interjection ++ [
    JUMP_ZERO; toB8 6;
    (* If not zero: *)
    GET_SP; PUSH1; toB8 8; ADD; STORE8 (* a::x::r -> a::r *)
  ] ++ pop 2. (* If zero *)


Definition jump_zero_ops :=
  [

  ]
End offset_opaque_section.
