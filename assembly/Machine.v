Require Import Utf8.

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
  (inputImages : list (Image B8)).

Notation as_bool x := (if x then true else false).

Module Export MT <: machine_type.
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

Definition nextN (n: nat) : M nat :=
  let* bytes := next n in
  ret (fromLittleEndian (bytes : Vector.t _ _)).

Definition push64 (z: Z) : M unit :=
  pushMany (toLittleEndian 8 z).

Definition popN : M nat :=
  let* bytes := popMany 8 in
  ret (fromLittleEndian (bytes : Vector.t _ _)).

Definition pop64 : M B64 :=
  let* x := popN in
  ret (toB64 (x: nat)).

Definition loadN (n: nat) (a: Z) : M nat :=
  let* bytes := loadMany n (toB64 a) in
  ret (fromLittleEndian (bytes : Vector.t _ _)).

Definition storeZ (n: nat) (a: Z) (x: Z) : M unit :=
  storeMany (toB64 a) (map Some (toLittleEndian n x)).

Import OpCodes.

Definition oneStep : M bool :=
  let exit := ret false : M bool in
  let continue := ret true : M bool in
  let error := err : M bool in

  let* opcode := nextN 1 in
  match opcode with
  | EXIT => exit
  | NOP => continue

  | JUMP =>
      let* a := popN in
      put' PC (toB64 (a: nat));;
      continue

  | JUMP_ZERO =>
      let* o := nextN 1 in
      let* x := popN in
      (if (decision (x = 0))
       then
         let* pc := get' PC in
         put' PC (offset (signed (toB8 (o: nat))) pc)
       else
         ret tt);;
      continue

  | SET_SP =>
      let* a := pop64 in
      put' SP a;;
      continue

  | GET_PC =>
      let* a := get' PC in
      push64 (a: B64);;
      continue

  | GET_SP =>
      let* a := get' SP in
      push64 (a: B64);;
      continue

  | PUSH0 =>
      push64 0;;
      continue

  | PUSH1 =>
      let* x := nextN 1 in
      push64 (x: nat);;
      continue

  | PUSH2 =>
      let* x := nextN 2 in
      push64 (x: nat);;
      continue

  | PUSH4 =>
      let* x := nextN 4 in
      push64 (x: nat);;
      continue

  | PUSH8 =>
      let* x := nextN 8 in
      push64 (x: nat);;
      continue

  | SIGX1 =>
      let* x := popN in
      push64 (signed (toB8 (x: nat)));;
      continue

  | SIGX2 =>
      let* x := popN in
      push64 (signed (toB16 (x: nat)));;
      continue

  | SIGX4 =>
      let* x := popN in
      push64 (signed (toB32 (x : nat)));;
      continue

  | LOAD1 =>
      let* a := popN in
      let* x := loadN 1 (a: nat) in
      push64 (x: nat);;
      continue

  | LOAD2 =>
      let* a := popN in
      let* x := loadN 2 (a: nat) in
      push64 (x: nat);;
      continue

  | LOAD4 =>
      let* a := popN in
      let* x := loadN 4 (a: nat) in
      push64 (x: nat);;
      continue

  | LOAD8 =>
      let* a := popN in
      let* x := loadN 8 (a: nat) in
      push64 (x: nat);;
      continue

  | STORE1 =>
      let* a := popN in
      let* x := popN in
      storeZ 1 (a: nat) (x: nat);;
      continue

  | STORE2 =>
      let* a := popN in
      let* x := popN in
      storeZ 2 (a: nat) (x: nat);;
      continue

  | STORE4 =>
      let* a := popN in
      let* x := popN in
      storeZ 4 (a: nat) (x: nat);;
      continue

  | STORE8 =>
      let* a := popN in
      let* x := popN in
      storeZ 8 (a: nat) (x: nat);;
      continue

  | ADD =>
      let* x := popN in
      let* y := popN in
      push64 ((x:nat) + (y:nat));;
      continue

  | MULT =>
      let* x := popN in
      let* y := popN in
      push64 ((x:nat) * (y:nat));;
      continue

  | DIV =>
      let* x := popN in
      let* y := popN in
      push64 (if decision (x=0) then 0 else (y:nat) / x);;
      continue

  | REM =>
      let* x := popN in
      let* y := popN in
      push64 (if decision (x=0) then 0 else (y:nat) mod x);;
      continue

  | LT =>
      let* x := popN in
      let* y := popN in
      push64 (if decision (y < x) then -1 else 0);;
      continue

  | AND =>
      let* x := pop64 in
      let* y := pop64 in
      push64 (Vector.map2 andb x y : B64);;
      continue

  | OR =>
      let* x := pop64 in
      let* y := pop64 in
      push64 (Vector.map2 orb x y : B64);;
      continue

  | NOT =>
      let* x := pop64 in
      push64 (Vector.map negb x : B64);;
      continue

  | XOR =>
      let* x := pop64 in
      let* y := pop64 in
      push64 (Vector.map2 xorb x y : B64);;
      continue

  (* *** *)

  | READ_FRAME =>
      let* i := popN in
      let* pair := readFrame (i: nat) in
      push64 (fst pair : nat);;
      push64 (snd pair : nat);;
      continue

  | READ_PIXEL =>
      let* y := popN in
      let* x := popN in
      let* c := readPixel (x:nat) (y:nat) in
      push64 (c:B8);;
      continue

  | NEW_FRAME =>
      let* r := popN in
      let* h := popN in
      let* w := popN in
      newFrame (w:nat) (h:nat) (r:nat);;
      continue

  | SET_PIXEL =>
      let* b := pop64 in
      let* g := pop64 in
      let* r := pop64 in
      let* y := popN in
      let* x := popN in
      setPixel (x:nat) (y:nat) (r:B64, g:B64, b:B64);;
      continue

  | ADD_SAMPLE =>
      let* r := popN in
      let* l := popN in
      addSample (toB16 (l:nat)) (toB16 (r:nat));;
      continue

  | PUT_CHAR =>
      let* c := popN in
      putChar (toB32 (c:nat));;
      continue

  | PUT_BYTE =>
      let* b := popN in
      putByte (toB8 (b:nat));;
      continue

  | _ => error
  end.
