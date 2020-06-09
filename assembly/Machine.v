From Assembly Require Export Basics Operations.
Require Assembly.OpCodes.

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
  Definition Cell := B8.

  Definition InputColor := B8.
  Definition allInputImages := allInputImages'.

  Definition OutputColor := (B64 * B64 * B64)%type.
  Definition Char := B32.
  Definition Byte := B8.
  Definition Sample := B16.

  Identity Coercion Addr_identity_coercion : Addr >-> B64.
  Identity Coercion Cell_identity_coercion : Cell >-> B8.
  Identity Coercion InputColor_identity_coercion : InputColor >-> B8.
  Identity Coercion Char_identity_coercion : Char >-> B32.
  Identity Coercion Byte_identity_coercion : Byte >-> B8.
  Identity Coercion Sample_identity_coercion : Sample >-> B16.
End concreteParameters.

Module ConcreteCore := Core concreteParameters.
Export ConcreteCore.

Section machine_section.

  (** We leave these assumptions abstract in order improve proof search.
      In Concete.v we have shown that they hold in our standard model. *)

  Context {MP1: MachineParams1}.
  Context {MP2: MachineParams2}.

  Existing Instance H_mon.

  Definition nextB n : M (Bytes n) := next n.

  (* Definition nextN (n: nat) : M N := *)
  (*   let* bytes := nextB n in *)
  (*   ret (bytes: N). *)

  Definition toBytes (n: nat) z := bitsToBytes (toBits (n * 8) z).

  Coercion to_list : vector >-> list.

  Definition pushZ (z: Z) : M unit :=
    pushMany (toBytes 8 z).

  Definition popN : M N :=
    let* bytes := popMany 8 in
    ret ((bytes: Bytes 8) : N).

  Definition pop64 : M B64 :=
    let* x := popN in
    ret (toB64 x).

  Definition loadN (n: nat) (a: Z) : M N :=
    let* bytes := loadMany n (toB64 a) in
    ret ((bytes : Bytes n) : N).

  Definition storeZ (n: nat) (a: Z) (x: Z) : M unit :=
    storeMany (toB64 a) (map Some (toBytes n x)).

  Import OpCodes.

  (* Without [noind] solving obligations seems to go on forever. *)
  Equations(noind) oneStep' (op: N) : M unit :=
    oneStep' NOP := ret tt;

    oneStep' JUMP :=
      let* a := popN in
      put' PC (toB64 a);

    oneStep' JUMP_ZERO :=
        let* o := nextB 1 in
        let* x := popN in
        (if (decide (x=0)%N)
         then
           let* pc := get' PC in
           put' PC (offset (bitsToZ (toB8 o)) pc)
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
        let* x := nextB 1 in
        pushZ x;

    oneStep' PUSH2 :=
        let* x := nextB 2 in
        pushZ x;

    oneStep' PUSH4 :=
        let* x := nextB 4 in
        pushZ x;

    oneStep' PUSH8 :=
        let* x := nextB 8 in
        pushZ x;

    oneStep' SIGX1 :=
        let* x := popN in
        pushZ (bitsToZ (toB8 x));

    oneStep' SIGX2 :=
        let* x := popN in
        pushZ (bitsToZ (toB16 x));

    oneStep' SIGX4 :=
        let* x := popN in
        pushZ (bitsToZ (toB32 x));

    oneStep' LOAD1 :=
        let* a := popN in
        let* x := loadN 1 a in
        pushZ x;

    oneStep' LOAD2 :=
        let* a := popN in
        let* x := loadN 2 a in
        pushZ x;

    oneStep' LOAD4 :=
        let* a := popN in
        let* x := loadN 4 a in
        pushZ x;

    oneStep' LOAD8 :=
        let* a := popN in
        let* x := loadN 8 a in
        pushZ x;

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
        pushZ (x + y);

    oneStep' MULT :=
        let* x := popN in
        let* y := popN in
        pushZ (x * y);

    oneStep' DIV :=
        let* x := popN in
        let* y := popN in
        pushZ (if decide (x=0)%N then 0 else y / x);

    oneStep' REM :=
        let* x := popN in
        let* y := popN in
        pushZ (if decide (x=0)%N then 0 else y mod x);

    oneStep' LT :=
        let* x := popN in
        let* y := popN in
        pushZ (if decide (y < x)%N then -1 else 0);

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
        let* i := popN in
        let* pair := readFrame i in
        pushZ (fst pair);;
        pushZ (snd pair);

    oneStep' READ_PIXEL :=
        let* y := popN in
        let* x := popN in
        let* c := readPixel x y in
        pushZ c;

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
    let* op := nextB 1 in
    match (op: N) with
    | EXIT => ret false
    | _ => oneStep' op;; ret true
    end.

End machine_section.
