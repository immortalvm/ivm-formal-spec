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

(** The machine will reach [doneState]
    if we start the machine in the given state
    and run as long as [while] does not fail. *)

Inductive OkFrom (while: M unit) (post: State -> Prop) : State -> Prop :=
| Done s : not (while s) -> post s -> OkFrom while post s
| More s (_: while s) s': oneStep s = Some (s', true)
                          -> OkFrom while post s'
                          -> OkFrom while post s.

(** Using elements of [M unit] is a quick and dirty way to express the
    decidable predicates on [State], where side-effects other than [err]
    are essentially ignored. *)

Definition unconditionally : M unit := ret tt.

Definition opsAtPc (ops: list B8) : M unit :=
  let* pc := get' PC in
  let* bytes := loadMany (length ops) pc in
  assert* ops = bytes in
  unconditionally.

Definition pcInRegion (n: nat) (s: State) : M unit :=
  match get' PC s with
  | None => err (* This will never happen. *)
  | Some (_, start) =>
      let* pc := get' PC in
      let i := Z.to_nat ((pc - start) mod 2^64)%Z in
      assert* i < n in
      unconditionally
  end.

Class Spec (ops: list nat) :=
{
  precondition: M unit;
  postcondition: State -> State -> Prop;
  witness s : opsAtPc (map (fun (op:nat) => toB8 op) ops) s
              -> precondition s
              -> OkFrom (pcInRegion (length ops) s) (postcondition s) s;
}.

#[refine]
Instance trivial_spec : Spec [] :=
{
  precondition := unconditionally;
  postcondition := eq;
  witness s _ _ := Done _ _ s _ _;
}.
Proof.
  all: tauto.
Qed.

#[refine]
Instance nop_spec : Spec [NOP] :=
{
  precondition := unconditionally;
  postcondition s := eq (update (Proj:=PC) s (offset 1 (proj (Proj:=PC) s)));
  witness s _ _ := _;
}.
Proof.
  match goal with
    [|- OkFrom ?x (eq ?y) s] => set (w:=x); set (s':=y) end.
  apply (More w unconditionally s _ s').


  set (s' := @update State Addr PC s (offset (Zpos xH) (@proj State Addr PC s))).

  set (s' := update s (Proj:=PC) (offset 1 (proj s))).
  Set Printing All.


  set (s' := update (Proj:=PC) s (offset 1 (proj (Proj:=PC) s))).
