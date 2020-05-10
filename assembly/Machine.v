Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Convenience.
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


(** Verification *)

Inductive Reach (stop: State) : forall (start: State), Prop :=
| Stop : Reach stop stop
| More s' s : oneStep s = Some (s', true)
              -> Reach stop s'
              -> Reach stop s.

Equations join {s1 s2 s3: State} (r2: Reach s3 s2) (r1: Reach s2 s1) : Reach s3 s1 :=
  join r2 Stop := r2;
  join r2 (More _ s' s H r) := More _ s' s H (join r2 r).

Instance reach_transitive : Transitive Reach.
Proof.
  intros x y z. exact join.
Qed.

Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Record Verif :=
{
  condition (s: State) : bool;
  effect (s: State) (Hs: condition s) : State;
  evidence (s: State) (Hs: condition s) : Reach (effect s Hs) s;
}.

Example true_verif : Verif :=
{|
  condition _ := true;
  effect s _ := s;
  evidence s _ := Stop s;
|}.

(** Weakening the claim by strengthening the precondition. *)
Definition weakened (v: Verif) (c: State -> bool) (Hc: forall s, c s -> condition v s) : Verif :=
{|
  condition := c;
  effect s Hs := effect v s (Hc s Hs);
  evidence s Hs := evidence v s (Hc s Hs);
|}.

Instance bool_ex_decidable (b: bool) (f: b -> bool) : Decidable (exists (x:b), f x).
Proof.
  destruct b.
  - remember (f eq_refl) as c eqn:Hc.
    destruct c.
    + left. exists eq_refl. rewrite <- Hc. reflexivity.
    + right. intros [x Hf].
      assert (x = eq_refl) as Hx.
      * assert (UIP bool) as Hu; [typeclasses eauto | apply Hu].
      * subst x. rewrite <- Hc in Hf. discriminate Hf.
  - right. intros [x _]. discriminate x.
Defined.

Lemma as_bool_decision {P: Prop} {Hd: Decidable P} (Hb: as_bool (decision P)) : P.
Proof.
  destruct (decision P).
  - assumption.
  - discriminate Hb.
Defined.

Ltac derive name term :=
  let H := fresh in
  let A := type of term in
  assert A as H;
  [ exact term | ];
  clear name;
  rename H into name.

Definition join_verifs (v1 v2: Verif) : Verif.
  refine {|
      condition s := as_bool (decision (exists (H1: condition v1 s), condition v2 (effect v1 s H1)));
      effect s Hs := effect v2 (effect v1 s _) _;
      evidence s Hs := _;
    |}.
  shelve. Unshelve.
  - simpl in Hs. destruct (as_bool_decision Hs) as [H1 _]. exact H1.

  - simpl in Hs.
    set (P := exists H1 : condition v1 s, condition v2 (effect v1 s H1)) in *.
    unfold as_bool_decision.
    destruct (decision P) as [HP|_].
    + subst P. destruct HP as [H1 H2]. exact H2.
    + discriminate Hs.

  - set (H1 := match as_bool_decision Hs with ex_intro _ H _ => H end).
    transitivity (effect v1 s H1); apply evidence.
Defined.


(** ** Basics *)

Arguments proj : clear implicits.
Arguments proj {_} {_}.
Arguments update : clear implicits.
Arguments update {_} {_}.

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

Definition nop_verif : Verif.
  refine (
      let f s := update PC s (offset 1 (proj PC s)) in
      let ops := map (fun (x:nat) => toB8 x) [NOP] in
      {|
        condition s := as_bool (decision (opsAtPc ops s));
        effect s _ := f s;
        evidence s Hs := More (f s) (f s) s _ (Stop (f s))
      |}).

  (* TODO: Automate! *)

  subst ops. simpl in *.
  derive Hs (as_bool_decision Hs).
  unfold oneStep. simpl.
  assert (nextN 1 s = Some (f s, 1)) as H1.

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
