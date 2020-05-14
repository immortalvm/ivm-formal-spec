Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Operations.
Require Assembly.OpCodes.

(* Global parameters! *)
Context
  (memStart: nat) (* TODO: Use B64 instead? *)
  (memSize: nat)
  (inputImages : list (Image B8))
  (State: Type).

Module Export MT <: machine_type.
  Definition State := State.
  Definition M := EST State.
  Definition H_mon := est_smonad State.
  Definition Addr := B64.
  Definition H_eqdec := (ltac:(typeclasses eauto) : EqDec B64).
  Definition available := fun (a: B64) => as_bool (decision (memStart <= a /\ a < memStart + memSize)).
  Definition offset := fun (z: Z) (a: B64) => toB64 (z + a).
  Definition Cell := B8.

  Definition InputColor := B8.
  Definition allInputImages := inputImages.

  Definition OutputColor : Type := B64 * B64 * B64.
  Definition Char := B32.
  Definition Byte := B8.
  Definition Sample := B16.
End MT.

Include core_module MT.

Identity Coercion id_Addr : Addr >-> B64.
Identity Coercion id_Cell : Cell >-> B8.
Identity Coercion id_InputColor : InputColor >-> B8.
Identity Coercion id_Char : Char >-> B32.
Identity Coercion id_Byte : Byte >-> B8.
Identity Coercion id_Sample : Sample >-> B16.

Definition nextN (n: nat) : M nat :=
  let* bytes := next n in
  ret (fromLittleEndian bytes).

Definition push64 (z: Z) : M unit :=
  pushMany (toLittleEndian 8 z).

Definition popN : M nat :=
  let* bytes := popMany 8 in
  ret (fromLittleEndian bytes).

Definition pop64 : M B64 :=
  let* x := popN in
  ret (toB64 x).

Definition loadN (n: nat) (a: Z) : M nat :=
  let* bytes := loadMany n (toB64 a) in
  ret (fromLittleEndian bytes).

Definition storeZ (n: nat) (a: Z) (x: Z) : M unit :=
  storeMany (toB64 a) (map Some (toLittleEndian n x)).

Import OpCodes.

(* Without [noind] solving obligations seems to go on forever.
   Alas, this still generated 257 equations... *)
Equations(noind) oneStep' (op: nat) : M unit :=
  oneStep' NOP := ret tt;

  oneStep' JUMP :=
    let* a := popN in
    put' PC (toB64 a);

  oneStep' JUMP_ZERO :=
      let* o := nextN 1 in
      let* x := popN in
      (if (decision (x = 0))
       then
         let* pc := get' PC in
         put' PC (offset (signed (toB8 o)) pc)
       else
         ret tt);

  oneStep' SET_SP :=
      let* a := pop64 in
      put' SP a;

  oneStep' GET_PC =>
      let* a := get' PC in
      push64 a;

  oneStep' GET_SP :=
      let* a := get' SP in
      push64 a;

  oneStep' PUSH0 :=
      push64 0;

  oneStep' PUSH1 :=
      let* x := nextN 1 in
      push64 x;

  oneStep' PUSH2 :=
      let* x := nextN 2 in
      push64 x;

  oneStep' PUSH4 :=
      let* x := nextN 4 in
      push64 x;

  oneStep' PUSH8 :=
      let* x := nextN 8 in
      push64 x;

  oneStep' SIGX1 :=
      let* x := popN in
      push64 (signed (toB8 x));

  oneStep' SIGX2 :=
      let* x := popN in
      push64 (signed (toB16 x));

  oneStep' SIGX4 :=
      let* x := popN in
      push64 (signed (toB32 x));

  oneStep' LOAD1 :=
      let* a := popN in
      let* x := loadN 1 a in
      push64 x;

  oneStep' LOAD2 :=
      let* a := popN in
      let* x := loadN 2 a in
      push64 x;

  oneStep' LOAD4 :=
      let* a := popN in
      let* x := loadN 4 a in
      push64 x;

  oneStep' LOAD8 :=
      let* a := popN in
      let* x := loadN 8 a in
      push64 x;

  oneStep' STORE1 :=
      let* a := popN in
      let* x := popN in
      storeZ 1 a x;

  oneStep' STORE2 :=
      let* a := popN in
      let* x := popN in
      storeZ 2 a x;

  oneStep' STORE4 :=
      let* a := popN in
      let* x := popN in
      storeZ 4 a x;

  oneStep' STORE8 :=
      let* a := popN in
      let* x := popN in
      storeZ 8 a x;

  oneStep' ADD :=
      let* x := popN in
      let* y := popN in
      push64 (x + (y:nat));

  oneStep' MULT :=
      let* x := popN in
      let* y := popN in
      push64 (x * (y:nat));

  oneStep' DIV :=
      let* x := popN in
      let* y := popN in
      push64 (if decision (x=0) then 0 else (y:nat) / x);

  oneStep' REM :=
      let* x := popN in
      let* y := popN in
      push64 (if decision (x=0) then 0 else (y:nat) mod x);

  oneStep' LT :=
      let* x := popN in
      let* y := popN in
      push64 (if decision (y < x) then -1 else 0);

  oneStep' AND :=
      let* x := pop64 in
      let* y := pop64 in
      push64 (Vector.map2 andb x y : B64);

  oneStep' OR :=
      let* x := pop64 in
      let* y := pop64 in
      push64 (Vector.map2 orb x y : B64);

  oneStep' NOT :=
      let* x := pop64 in
      push64 (Vector.map negb x : B64);

  oneStep' XOR :=
      let* x := pop64 in
      let* y := pop64 in
      push64 (Vector.map2 xorb x y : B64);

  oneStep' READ_FRAME :=
      let* i := popN in
      let* pair := readFrame (i: nat) in
      push64 (fst pair);;
      push64 (snd pair);

  oneStep' READ_PIXEL :=
      let* y := popN in
      let* x := popN in
      let* c := readPixel x y in
      push64 c;

  oneStep' NEW_FRAME :=
      let* r := popN in
      let* h := popN in
      let* w := popN in
      newFrame w h r;

  oneStep' SET_PIXEL :=
      let* b := pop64 in
      let* g := pop64 in
      let* r := pop64 in
      let* y := popN in
      let* x := popN in
      setPixel x y (r, g, b);

  oneStep' ADD_SAMPLE :=
      let* r := popN in
      let* l := popN in
      addSample (toB16 l) (toB16 r);

  oneStep' PUT_CHAR :=
      let* c := popN in
      putChar (toB32 c);

  oneStep' PUT_BYTE :=
      let* b := popN in
      putByte (toB8 b);

  oneStep' _ := err.

Definition oneStep : M bool :=
  let* op := nextN 1 in
  match op with
  | EXIT => ret false
  | _ => oneStep' op;; ret true
  end.


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
