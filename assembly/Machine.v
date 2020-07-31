From Assembly Require Export Basics Operations.
Require Assembly.OpCodes.

Unset Suggest Proof Using.

Set Implicit Arguments.

Notation toB8 := (toBits 8).
Notation toB16 := (toBits 16).
Notation toB32 := (toBits 32).
Notation toB64 := (toBits 64).

Open Scope Z.
Open Scope vector.

Coercion bytesToBits : Bytes >-> Bits.
Coercion bitsToN : Bits >-> N.

(** Now we have coercions [Bytes >-> Bits >-> N >-> Z]
    and also [nat >-> Z] and [option >-> bool >-> Prop]. *)

(* Global parameters! *)
Context
  (available': B64 -> bool)
  (allInputImages' : list (Image B8)).

Module concreteParameters <: MachineParameters.
  Definition Addr := B64.
  Definition H_eqdec := (ltac:(typeclasses eauto) : EqDec B64).
  Definition available := available'.
  Definition offset := fun (z: Z) (a: B64) => toB64 (z + a).
  Instance offset_action : Z_action offset.
  Proof.
    unfold offset.
    split; intros.
    - cbn. apply toBits_ofN_bitsToN.
    - apply toBits_cong.
      repeat rewrite ofN_bitsToN.
      rewrite fromBits_toBits_cong.
      apply eq_cong.
      lia.
  Qed.
  Definition Cell := B8.

  Definition InputColor := B8.
  Definition allInputImages := allInputImages'.

  Definition OutputColor := (B64 * B64 * B64)%type.
  Definition Char := B32.
  Definition Byte := B8.
  Definition Sample := B16.
End concreteParameters.

Module ConcreteCore := Core concreteParameters.
Export ConcreteCore.

(* TODO: Is there a more elegant way to achieve this? *)
Definition cells_to_bytes {n} : Cells n -> Bytes n := id.
Coercion cells_to_bytes : Cells >-> Bytes.

Section machine_section.

  (** We leave these assumptions abstract in order improve proof search.
      In Concete.v we have shown that they hold in our standard model. *)

  Context {MP1: MachineParams1}.
  Context {MP2: MachineParams2}.

  Definition toBytes (n: nat) z := bitsToBytes (toBits (n * 8) z).

  Coercion to_list : vector >-> list.

  Definition pushZ (z: Z) : M unit :=
    pushMany (toBytes 8 z).

  Definition pop64 : M B64 :=
    let* bytes := popMany 8 in
    ret (bytes : B64).

  Definition storeZ (n: nat) (a: Z) (x: Z) : M unit :=
    storeMany (toB64 a) (toBytes n x).

  Import OpCodes.

  (* Without [noind] solving obligations seems to go on forever. *)
  Equations(noind) oneStep' (op: Z) : M unit :=
    oneStep' NOP := ret tt;

    oneStep' JUMP :=
      let* a := pop64 in
      put' PC (toB64 a);

    oneStep' JUMP_ZERO :=
        let* o := next 1 in
        let* x := pop64 in
        (if (decide (x = 0 :> Z))
         then
           let* pc := get' PC in
           put' PC (offset o pc)
         else
           ret tt);

    oneStep' SET_SP :=
        let* a := pop64 in
        put' SP a;

    oneStep' GET_PC =>
        let* a := get' PC in
        pushZ a;

    oneStep' GET_SP :=
        let* a := get' SP in
        pushZ a;

    oneStep' PUSH0 :=
        pushZ 0;

    oneStep' PUSH1 :=
        let* x := next 1 in
        pushZ x;

    oneStep' PUSH2 :=
        let* x := next 2 in
        pushZ x;

    oneStep' PUSH4 :=
        let* x := next 4 in
        pushZ x;

    oneStep' PUSH8 :=
        let* x := next 8 in
        pushZ x;

    oneStep' SIGX1 :=
        let* x := pop64 in
        pushZ (bitsToZ (toB8 x));

    oneStep' SIGX2 :=
        let* x := pop64 in
        pushZ (bitsToZ (toB16 x));

    oneStep' SIGX4 :=
        let* x := pop64 in
        pushZ (bitsToZ (toB32 x));

    oneStep' LOAD1 :=
        let* a := pop64 in
        let* x := loadMany 1 a in
        pushZ x;

    oneStep' LOAD2 :=
        let* a := pop64 in
        let* x := loadMany 2 a in
        pushZ x;

    oneStep' LOAD4 :=
        let* a := pop64 in
        let* x := loadMany 4 a in
        pushZ x;

    oneStep' LOAD8 :=
        let* a := pop64 in
        let* x := loadMany 8 a in
        pushZ x;

    oneStep' STORE1 :=
        let* a := pop64 in
        let* x := pop64 in
        storeZ 1 a x;

    oneStep' STORE2 :=
        let* a := pop64 in
        let* x := pop64 in
        storeZ 2 a x;

    oneStep' STORE4 :=
        let* a := pop64 in
        let* x := pop64 in
        storeZ 4 a x;

    oneStep' STORE8 :=
        let* a := pop64 in
        let* x := pop64 in
        storeZ 8 a x;

    oneStep' ADD :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (x + y);

    oneStep' MULT :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (x * y);

    oneStep' DIV :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (if decide (x = 0 :> Z) then 0 else y / x);

    oneStep' REM :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (if decide (x = 0 :> Z) then 0 else y mod x);

    oneStep' LT :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (if decide (y < x) then -1 else 0);

    oneStep' AND :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (Vector.map2 andb x y : B64);

    oneStep' OR :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (Vector.map2 orb x y : B64);

    oneStep' NOT :=
        let* x := pop64 in
        pushZ (Vector.map negb x : B64);

    oneStep' XOR :=
        let* x := pop64 in
        let* y := pop64 in
        pushZ (Vector.map2 xorb x y : B64);

    oneStep' READ_FRAME :=
        let* i := pop64 in
        let* pair := readFrame i in
        pushZ (fst pair);;
        pushZ (snd pair);

    oneStep' READ_PIXEL :=
        let* y := pop64 in
        let* x := pop64 in
        let* c := readPixel x y in
        pushZ c;

    oneStep' NEW_FRAME :=
        let* r := pop64 in
        let* h := pop64 in
        let* w := pop64 in
        newFrame w h r;

    oneStep' SET_PIXEL :=
        let* b := pop64 in
        let* g := pop64 in
        let* r := pop64 in
        let* y := pop64 in
        let* x := pop64 in
        setPixel x y (r, g, b);

    oneStep' ADD_SAMPLE :=
        let* r := pop64 in
        let* l := pop64 in
        addSample (toB16 l) (toB16 r);

    oneStep' PUT_CHAR :=
        let* c := pop64 in
        putChar (toB32 c);

    oneStep' PUT_BYTE :=
        let* b := pop64 in
        putByte (toB8 b);

    oneStep' _ := err.

  Definition oneStep : M bool :=
    let* op := next 1 in
    match (op: Z) with
    | EXIT => ret false
    | _ => oneStep' op;; ret true
    end.


  (** ** Chaining steps *)

  Definition chain (u v : M bool) :=
    let* cont := u in
    if cont then v else ret false.

  Unset Suggest Proof Using.

  Lemma true_chain (u: M bool) : chain (ret true) u = u.
  Proof.
    unfold chain. rewrite ret_bind. reflexivity.
  Qed.

  Lemma chain_true (u: M bool) : chain u (ret true) = u.
  Proof.
    unfold chain.
    rewrite <- bind_ret.
    f_equal.
    extensionality cont.
    destruct cont; reflexivity.
  Qed.

  Lemma chain_assoc (u v w : M bool) : chain (chain u v) w = chain u (chain v w).
  Proof.
    unfold chain.
    smon_rewrite.
    f_equal.
    extensionality x.
    destruct x; [reflexivity|].
    rewrite ret_bind.
    reflexivity.
  Qed.

  (** In other words, this defines a monoid (up to functional extensionality). *)

  Lemma false_chain (u: M bool) : chain (ret false) u = ret false.
  Proof.
    unfold chain. rewrite ret_bind. reflexivity.
  Qed.

  Equations nSteps (n: nat) : M bool :=
    nSteps 0 := ret true;
    nSteps (S n) := chain oneStep (nSteps n).

  Lemma nSteps_action (m n: nat) : nSteps (m + n) = chain (nSteps m) (nSteps n).
  Proof.
    revert n. induction m; intros n; simpl Nat.add; simp nSteps.
    - rewrite true_chain. reflexivity.
    - rewrite chain_assoc, IHm. reflexivity.
  Qed.

End machine_section.
