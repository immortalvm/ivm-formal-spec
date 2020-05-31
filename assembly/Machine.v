Require Import Equations.Equations.

From Assembly Require Import Convenience Dec Lens Mon Bits Operations.
Require Assembly.OpCodes.
Set Implicit Arguments.


(* Global parameters! *)
Context
  (available': B64 -> bool)
  (allInputImages' : list (Image B8)).

Instance concreteParams0 : MachineParams0 :=
{
  Addr := B64;
  H_eqdec := (ltac:(typeclasses eauto) : EqDec B64);
  available := available';
  offset := fun (z: Z) (a: B64) => toB64 (z + a);
  Cell := B8;

  InputColor := B8;
  allInputImages := allInputImages';

  OutputColor := B64 * B64 * B64;
  Char := B32;
  Byte := B8;
  Sample := B16;
}.

Section machine_section.

  (** We leave these assumptions abstract in order improve proof search.
      In Concete.v we have shown that they hold in our standard model. *)

  Context {MP1: @MachineParams1 concreteParams0}.
  Context {MP2: @MachineParams2 concreteParams0 MP1}.

  Existing Instance H_mon.

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
        push64 (a: B64);

    oneStep' GET_SP :=
        let* a := get' SP in
        push64 (a: B64);

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
        push64 (c: B8);

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

End machine_section.
