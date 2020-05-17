Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Operations.
Require Assembly.OpCodes.

From RecordUpdate Require Import RecordSet.

(* Global parameters! *)
Context
  (memStart: nat) (* TODO: Use B64 instead? *)
  (memSize: nat)
  (inputImages : list (Image B8)).

Module CT <: core_type'.

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

  Include machine_type_defs.

  Record actual_State :=
  mkState {
    state_memory: Memory;
    state_pc: Addr;
    state_sp: Addr;
    state_inp: Image InputColor;
    state_image: Image (option OutputColor);
    state_bytes: list Byte;
    state_chars: list Char;
    state_sound: Sound;
    state_log: list OutputFrame;
  }.
  Instance etaState : Settable _ :=
    settable! mkState <state_memory;
                       state_pc;
                       state_sp;
                       state_inp;
                       state_image;
                       state_bytes;
                       state_chars;
                       state_sound;
                       state_log>.
  Definition State := actual_State.
  Definition M := EST State.
  Definition H_mon := est_smonad State.

  Local Ltac crush :=
    let s := fresh in try split; intro s; intros; destruct s; reflexivity.

  Local Ltac derive_proj f :=
    refine {|
        proj := f;
        update s m := set f (fun _ => m) s;
    |}; crush.

  Definition MEM : Proj State Memory. derive_proj state_memory. Defined.
  Definition PC : Proj State Addr. derive_proj state_pc. Defined.
  Definition SP : Proj State Addr. derive_proj state_sp. Defined.
  Definition INP : Proj State (Image InputColor). derive_proj state_inp. Defined.
  Definition OUT_CHARS : Proj State (list Char). derive_proj state_chars. Defined.
  Definition OUT_BYTES : Proj State (list Byte). derive_proj state_bytes. Defined.
  Definition OUT_SOUND : Proj State Sound. derive_proj state_sound. Defined.
  Definition OUT_IMAGE : Proj State (Image (option OutputColor)). derive_proj state_image. Defined.
  Definition LOG : Proj State (list OutputFrame). derive_proj state_log. Defined.

  Instance independent_MEM_IMAGE: Independent MEM OUT_IMAGE. crush. Defined.
  Instance independent_MEM_BYTES: Independent MEM OUT_BYTES. crush. Defined.
  Instance independent_MEM_CHARS: Independent MEM OUT_CHARS. crush. Defined.
  Instance independent_MEM_SOUND: Independent MEM OUT_SOUND. crush. Defined.
  Instance independent_MEM_LOG:   Independent MEM LOG. crush. Defined.
  Instance independent_MEM_INP:   Independent MEM INP. crush. Defined.
  Instance independent_MEM_PC:    Independent MEM PC. crush. Defined.
  Instance independent_MEM_SP:    Independent MEM SP. crush. Defined.

  Instance independent_IMAGE_BYTES: Independent OUT_IMAGE OUT_BYTES. crush. Defined.
  Instance independent_IMAGE_CHARS: Independent OUT_IMAGE OUT_CHARS. crush. Defined.
  Instance independent_IMAGE_SOUND: Independent OUT_IMAGE OUT_SOUND. crush. Defined.
  Instance independent_IMAGE_LOG:   Independent OUT_IMAGE LOG. crush. Defined.
  Instance independent_IMAGE_INP:   Independent OUT_IMAGE INP. crush. Defined.
  Instance independent_IMAGE_PC:    Independent OUT_IMAGE PC. crush. Defined.
  Instance independent_IMAGE_SP:    Independent OUT_IMAGE SP. crush. Defined.

  Instance independent_BYTES_CHARS: Independent OUT_BYTES OUT_CHARS. crush. Defined.
  Instance independent_BYTES_SOUND: Independent OUT_BYTES OUT_SOUND. crush. Defined.
  Instance independent_BYTES_LOG:   Independent OUT_BYTES LOG. crush. Defined.
  Instance independent_BYTES_INP:   Independent OUT_BYTES INP. crush. Defined.
  Instance independent_BYTES_PC:    Independent OUT_BYTES PC. crush. Defined.
  Instance independent_BYTES_SP:    Independent OUT_BYTES SP. crush. Defined.

  Instance independent_CHARS_SOUND: Independent OUT_CHARS OUT_SOUND. crush. Defined.
  Instance independent_CHARS_LOG:   Independent OUT_CHARS LOG. crush. Defined.
  Instance independent_CHARS_INP:   Independent OUT_CHARS INP. crush. Defined.
  Instance independent_CHARS_PC:    Independent OUT_CHARS PC. crush. Defined.
  Instance independent_CHARS_SP:    Independent OUT_CHARS SP. crush. Defined.

  Instance independent_SOUND_LOG: Independent OUT_SOUND LOG. crush. Defined.
  Instance independent_SOUND_INP: Independent OUT_SOUND INP. crush. Defined.
  Instance independent_SOUND_PC:  Independent OUT_SOUND PC. crush. Defined.
  Instance independent_SOUND_SP:  Independent OUT_SOUND SP. crush. Defined.

  Instance independent_LOG_INP: Independent LOG INP. crush. Defined.
  Instance independent_LOG_PC:  Independent LOG PC. crush. Defined.
  Instance independent_LOG_SP:  Independent LOG SP. crush. Defined.

  Instance independent_INP_PC: Independent INP PC. crush. Defined.
  Instance independent_INP_SP: Independent INP SP. crush. Defined.

  Instance independent_PC_SP: Independent PC SP. crush. Defined.
End CT.

Export CT.

Module CM := core_module CT.
Export CM.

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
