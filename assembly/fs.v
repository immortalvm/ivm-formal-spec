Require Import Utf8.

From FreeSpec Require Import Core.
From Prelude Require Import All.

From Coq Require Import ZArith.
From Coq Require Import Lia.

From Equations Require Import Equations.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Import EqNotations.

(* Undo FreeSpec setting. *)
Generalizable No Variables.

Set Implicit Arguments.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Open Scope bool_scope.
Coercion is_true : bool >-> Sortclass.

Coercion Z.of_nat : nat >-> Z.


(** Prelude.Control only provides an uptyped version. *)
Notation "'let*' ( a : t ) ':=' p 'in' q" := (bind p%monad (fun (a:t) => q%monad))
  (in custom monad at level 0, a ident, p constr, q at level 10, right associativity, only parsing).


(** ** Lists and vectors *)

Definition map := List.map. (* Prelude binds this. *)

Derive Signature NoConfusion NoConfusionHom for Vector.t.
Arguments Vector.nil {A}.
Arguments Vector.cons : default implicits.
Coercion Vector.to_list : Vector.t >-> list.

Import Coq.Vectors.Vector.VectorNotations.
Close Scope vector.

Lemma to_list_equation_1: forall A, nil%vector = nil :> list A.
Proof. reflexivity. Qed.

Lemma to_list_equation_2: forall A n (x: A) (u: Vector.t A n), (x :: u)%vector = x :: u :> list A.
Proof. reflexivity. Qed.

Hint Rewrite to_list_equation_1 : to_list.
Hint Rewrite to_list_equation_2 : to_list.

Lemma to_list_injective {A n} (u v: Vector.t A n) : u = v :> list A -> u = v.
Proof.
  induction n as [|n IH]; depelim u; depelim v.
  - easy.
  - simp to_list. intro Heq.
    f_equal; [|apply (IH u v)]; congruence.
Qed.

Instance vector_eqdec {A n} `(EqDec A) : EqDec (Vector.t A n).
Proof.
  intros u v.
  destruct (@eq_dec (list A) _ u v).
  - left. now apply to_list_injective.
  - right. congruence.
Defined.


(** ** Bits *)

Definition BitList := list bool.
Identity Coercion Id_BitList_List : BitList >-> list.

Definition boolToNat (x: bool) : nat := if x then 1 else 0.
Coercion boolToNat : bool >-> nat.

(** Little-endian (reverse of binary notation) *)
Equations bitListToNat (_: BitList) : nat :=
  bitListToNat [] := 0;
  bitListToNat (x :: u) := 2 * bitListToNat u + x.

Coercion bitListToNat : BitList >-> nat.

(** Specialize [to_list] to get coercion [Bits >-> nat]. *)
Definition Bits: nat -> Type := Vector.t bool.
Definition to_BitList {n} (u: Bits n) : BitList := u.
Coercion to_BitList : Bits >-> BitList.

Open Scope vector.
Open Scope Z_scope.

Equations toBits (n: nat) (_: Z) : Bits n :=
  toBits O _ := [];
  toBits (S n) z := (z mod 2 =? 1) :: toBits n (z / 2).

Close Scope Z_scope.
Close Scope vector.

Equations signed (_: list bool) : Z :=
  signed [] := 0;
  signed (x :: u) := match u with
                    | [] => -x
                    | _ => 2 * signed u + x
                    end.

(*
Definition fromLittleEndian (u: list Cell) : nat :=
  bitListToNat (concat (map to_BitList u)).
 *)

Notation B8 := (Bits 8).
Notation B16 := (Bits 16).
Notation B32 := (Bits 32).
Notation B64 := (Bits 64).

Notation toB8 := (toBits 8).
Notation toB16 := (toBits 16).
Notation toB32 := (toBits 32).
Notation toB64 := (toBits 64).

Equations fromLittleEndian (_: list B8): nat :=
  fromLittleEndian [] := 0;
  fromLittleEndian (x :: r) := 256 * (fromLittleEndian r) + x.

Open Scope vector_scope.

Equations toLittleEndian n (_: Z) : Vector.t B8 n :=
  toLittleEndian 0 _ := [];
  toLittleEndian (S n) z := (toB8 z) :: (toLittleEndian n (z / 256)).

Close Scope vector_scope.


(** ** Bitmap images *)

Record Image (C: Type) :=
  mkImage {
      width: nat;
      height: nat;
      pixel (x: nat) (Hx: x < width) (y: nat) (Hy: y < height): C;
    }.

Definition noImage {C}: Image C.
  refine {|
      width := 0;
      height := 0;
      pixel x Hx y Hy := _;
    |}.
  lia.
Defined.

(* It seems RecordUpdate does not handle dependent types. *)
Definition updatePixel {C} (x y: nat) (c: C) (im: Image C) : Image C :=
{|
  width := width im;
  height := height im;
  pixel x' Hx y' Hy :=
    if (x' =? x) && (y' =? y) then c
    else pixel im Hx Hy
|}.


(** ** Building blocks *)

(** Erroneous operation(s) *)
Inductive ERROR : interface :=
| Error {A: Type} : ERROR A.

Definition error_contract: contract ERROR unit :=
  {|
  witness_update _ _ _ _ := tt;
  caller_obligation _ _ _ := False;
  callee_obligation := no_callee_obligation;
  |}.

Section log_section.

  Context (Value: Type).

  (** Append-only log *)
  Inductive LOG : interface :=
  | Log (x: Value) : LOG unit.

  Definition log_contract: contract LOG (list Value) :=
  {|
    witness_update lst _ op _ := match op with Log x => x :: lst end;
    caller_obligation := no_caller_obligation;
    callee_obligation := no_callee_obligation;
  |}.

End log_section.

(** We will also use [STORE], which is built in. *)


(** ** Core *)

Module Type machine_type.

  (** This abstraction simplifies some of the definitions below (that
      otherwise tend to hang), possibly because we avoid coercions. *)

  Context
    (Addr: Type)
    `{H_eqdec: EqDec Addr}
    (available: Addr -> Prop)
    (offset: Z -> Addr -> Addr) (* This should be a group action. *)
    (Cell: Type)

    (InputColor: Type)
    (allInputImages: list (Image InputColor))

    (OutputColor: Type)
    (Char: Type)
    (Byte: Type)
    (Sample: Type).

End machine_type.

Module core_module (M: machine_type).

  Import M.
  Existing Instance H_eqdec.

  Inductive MEMORY : interface :=
  | Load (a: Addr) : MEMORY Cell
  | Store (a: Addr) (x: option Cell) : MEMORY unit.

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Equations o_caller_memory (mem: Memory) {A: Type} (op: MEMORY A) : Prop :=
    o_caller_memory mem (Load a) := exists (H: available a), mem a H <> None;
    o_caller_memory _ (Store a _) := available a.

  (* For "undefined" memory addresses Load can return any value. *)
  Equations o_callee_memory (mem: Memory) {A: Type} (op: MEMORY A) (y: A) : Prop :=
    o_callee_memory mem (Load a) y := forall (Ha: available a), mem a Ha = Some y;
    o_callee_memory _ _ _ := True.

  Definition memory_contract: contract MEMORY Memory :=
  {|
    witness_update mem _ op _ :=
      match op with
      | Store a x => fun a' Ha => if eq_dec a a' then x else mem a' Ha
      | _ => mem
      end;
    caller_obligation := o_caller_memory;
    callee_obligation := o_callee_memory;
  |}.

  Class Core (ix: interface) :=
    {
    Mmem :> MayProvide ix MEMORY;
    Hmem :> @Provide ix MEMORY Mmem;

    Mpc: MayProvide ix (STORE Addr);
    Hpc : @Provide ix (STORE Addr) Mpc;

    Msp : MayProvide ix (STORE Addr);
    Hsp : @Provide ix (STORE Addr) Msp;
    }.

End core_module.


(** ** I/O *)

Module input_module (M: machine_type).

  Import M.

  Inductive INPUT: interface :=
  | ReadFrame (i: nat) : INPUT (nat * nat)%type
  | ReadPixel (x y: nat) : INPUT InputColor.

  Local Definition Input := Image InputColor.

  Equations o_caller_input (inp: Input) {A: Type} (op: INPUT A) : Prop :=
    o_caller_input inp (ReadPixel x y) := x < width inp /\ y < height inp;
    o_caller_input inp _ := True.

  Equations o_callee_input (inp: Input) {A: Type} (op: INPUT A) (_: A) : Prop :=
    o_callee_input inp (ReadPixel x y) c :=
      forall (Hx: x < width inp) (Hy: y < height inp), pixel inp Hx Hy = c;
    o_callee_input _ _ _ := True.

  Definition input_contract: contract INPUT Input :=
  {|
    witness_update inp _ op _ :=
      match op with
      | ReadFrame i => nth i allInputImages noImage
      | _ => inp
      end;
    caller_obligation := o_caller_input;
    callee_obligation := o_callee_input;
  |}.

End input_module.


Module output_module (M: machine_type).

  Import M.

  Record Sound := mkSound
  {
    rate: nat;
    samples (Hr: rate <> 0) : list (Sample * Sample); (* reversed *)
  }.

  Definition addSample (l r: Sample) (sn: Sound) :=
  {|
    rate := rate sn;
    samples Hr := (l, r) :: (samples sn Hr);
  |}.

  Record Frame (C: Type) := mkFrame
  {
    image: Image C;
    sound: Sound;
    chars: list Char;  (* reversed *)
    bytes: list Byte;  (* reversed *)
  }.

  Definition similarFrames {C D} (f: Frame C) (g: Frame D) (e: C -> D -> Prop) :=
    (let i := image f in
     let j := image g in
     exists (Hw: width i = width j)
       (Hh: height i = height j),
       forall x (Hx: x < width i) y (Hy: y < height i),
         e (pixel i Hx Hy) (pixel j (rew Hw in Hx) (rew Hh in Hy)))
    /\ (let s := sound f in
       let t := sound g in
       exists (Hr: rate s = rate t),
         forall (H: rate s <> 0),
           samples s H = samples t (rew [fun n => n <> 0] Hr in H)
      )
    /\ chars f = chars g
    /\ bytes f = bytes g.

  Local Definition OC := option OutputColor.

  Instance etaFrame : Settable _ := settable! (@mkFrame OC) <(@image OC); (@sound OC); (@chars OC); (@bytes OC)>.

  Inductive OUTPUT: interface :=
  | NextFrame (width heigth rate : nat) : OUTPUT (Frame OutputColor) (* Returns the previous frame *)
  | SetPixel (x y: nat) (c: OutputColor) : OUTPUT unit
  | AddSample (l: Sample) (r: Sample) : OUTPUT unit
  | PutChar (c: Char) : OUTPUT unit
  | PutByte (b: Byte) : OUTPUT unit.

  Definition freshFrame (w h r: nat) : Frame OC :=
    {|
    image :=
      {|
        width := w;
        height := h;
        pixel _ _ _ _ := None;
      |};
    sound :=
      {|
        rate := r;
        samples _ := [];
      |};
    chars := [];
    bytes := [];
    |}.

  Equations o_callee_output (fr: Frame OC) {A: Type} (op: OUTPUT A) (_: A) : Prop :=
    o_callee_output fr (NextFrame _ _ _) res := similarFrames fr res (fun oc c => oc = Some c);
    o_callee_output _ _ _ := True.

  Definition output_contract: contract OUTPUT (Frame OC) :=
    {|
    witness_update fr _ op _ :=
      match op with
      | NextFrame w h r => freshFrame w h r
      | SetPixel x y c => set (@image OC) (updatePixel x y (Some c)) fr
      | AddSample l r => set (@sound OC) (addSample l r) fr
      | PutChar c => set (@chars OC) (cons c) fr
      | PutByte b => set (@bytes OC) (cons b) fr
      end;

    caller_obligation fr _ op :=
      match op with
      | NextFrame _ _ _ =>
        (* Every pixel must be set! *)
        let im := image fr in
        forall x (Hx: x < width im) y (Hy: y < height im), pixel im Hx Hy <> None
      | SetPixel x y _ => x < width (image fr) /\ y < height (image fr)
      | _ => True
      end;

    callee_obligation := o_callee_output;
    |}.

End output_module.


(** ** Integration *)

Module Instructions.

  Open Scope nat_scope.
  Notation EXIT := 0.
  Notation NOP := 1.
  Notation JUMP := 2.
  Notation JUMP_ZERO := 3.
  Notation SET_SP := 4.
  Notation GET_PC := 5.
  Notation GET_SP := 6.
  Notation PUSH0 := 7.
  Notation PUSH1 := 8.
  Notation PUSH2 := 9.
  Notation PUSH4 := 10.
  Notation PUSH8 := 11.
  Notation SIGX1 := 12.
  Notation SIGX2 := 13.
  Notation SIGX4 := 14.
  Notation LOAD1 := 16.
  Notation LOAD2 := 17.
  Notation LOAD4 := 18.
  Notation LOAD8 := 19.
  Notation STORE1 := 20.
  Notation STORE2 := 21.
  Notation STORE4 := 22.
  Notation STORE8 := 23.
  Notation ADD := 32.
  Notation MULT := 33.
  Notation DIV := 34.
  Notation REM := 35.
  Notation LT := 36.
  Notation AND := 40.
  Notation OR := 41.
  Notation NOT := 42.
  Notation XOR := 43.
  Notation POW2 := 44.

  Notation READ_FRAME := 255.
  Notation READ_PIXEL := 254.
  Notation NEW_FRAME := 253.
  Notation SET_PIXEL := 252.
  Notation ADD_SAMPLE := 251.
  Notation PUT_CHAR := 250.
  Notation PUT_BYTE := 249.

End Instructions.

(* Global parameters! *)
Context
  (memStart: nat) (* TODO: Use B64 instead? *)
  (memSize: nat)
  (inputImages : list (Image B8)).

Module Export M <: machine_type.
  Definition Addr := B64.
  Definition H_eqdec := (ltac:(typeclasses eauto) : EqDec B64).
  Definition available := fun (a: B64) => memStart <= a /\ a < memStart + memSize.
  Definition offset := fun (z: Z) (a: B64) => toB64 (z + a).
  Definition Cell := B8.

  Definition InputColor := B8.
  Definition allInputImages := inputImages.

  Definition OutputColor : Type := B64 * B64 * B64.
  Definition Char := B32.
  Definition Byte := B8.
  Definition Sample := B16.
End M.

Module CM := core_module M.
Export CM.

Module IM := input_module M.
Export IM.

Module OM := output_module M.
Export OM.

Class Machine (ix: interface) :=
{
  Hc :> Core ix;

  Minp :> MayProvide ix INPUT;
  Hinp :> @Provide ix INPUT Minp;

  Mout :> MayProvide ix OUTPUT;
  Hout :> @Provide ix OUTPUT Mout;

  Mcon :> MayProvide ix (LOG (Frame OutputColor));
  Hcon :> @Provide ix (LOG (Frame OutputColor)) Mcon;

  Mf :> MayProvide ix ERROR;
  Hf :> @Provide ix ERROR Mf;
}.

(* More global parameters! *)
Context
  (ix: interface)
  (Hm: Machine ix).


(** ** PC and SP (generic) *)

Definition getPC : impure ix Addr := @request _ _ Mpc Hpc _ Get.
Definition setPC a : impure ix unit := @request _ _ Mpc Hpc _ (Put a).

Definition getSP : impure ix Addr := @request _ _ Msp Hsp _ Get.
Definition setSP a : impure ix unit := @request _ _ Msp Hsp _ (Put a).

Equations loadMem (n: nat) (_: Addr) : impure ix (Vector.t Cell n) :=
  loadMem 0 _ := pure Vector.nil;
  loadMem (S n) a :=
    do let* x := request (Load a) in
       let* r := loadMem n (offset 1 a) in
       pure (Vector.cons x r)
    end.

Equations storeMem (_: Addr) (_: list (option Cell)) : impure ix unit :=
  storeMem _ nil := pure tt;
  storeMem a (x :: u) :=
    do request (Store a x);
       storeMem (offset 1 a) u
    end.

Definition next (n: nat) : impure ix (Vector.t Cell n) :=
  do let* pc := getPC in
     let* res := loadMem n pc in
     setPC (offset n pc);
     pure res
  end.

Definition push (u: list Cell) : impure ix unit :=
  do let* sp := getSP in
     (* The stack grows downwards. *)
     let a := offset (- List.length u) sp in
     setSP a;
     storeMem a (map Some u)
  end.

Definition pop (n: nat) : impure ix (Vector.t Cell n) :=
  do let* sp := getSP in
     let* res := loadMem n sp in
     (* Mark memory as undefined *)
     storeMem sp (repeat None n);
     setSP (offset n sp);
     pure res
  end.


(** ** Non-generic *)

Definition newFrame (w h r : nat) : impure ix unit :=
  do
    let* previous := request (NextFrame w h r) in
    request (Log previous)
  end.

Definition nextN n : impure ix nat :=
  do
    (* Coq/FreeSpec hangs if the typing is dropped. *)
    let* (bytes : Vector.t Cell n) := next n in
    pure (fromLittleEndian bytes)
  end.

Definition popN : impure ix nat :=
  do
    let* (bytes: Vector.t Cell 8) := pop 8 in
    pure (fromLittleEndian bytes)
  end.

Definition pop64 : impure ix B64 :=
  do
    let* (x: nat) := popN in
    pure (toB64 x)
  end.

Definition push64 (z: Z) : impure ix unit :=
  push (toLittleEndian 8 z).

Definition load (n: nat) (a: Z) : impure ix nat :=
  do
    let* (bytes: Vector.t B8 n) := loadMem n (toB64 a) in
    pure (fromLittleEndian bytes)
  end.

Definition store (n: nat) (a: Z) (x: Z) : impure ix unit :=
  storeMem (toB64 a) (map Some (toLittleEndian n x)).


(** ** Semantics *)

Section limit_scope.

  Import Instructions.

  Definition oneStep : impure ix bool :=
    let exit := pure false : impure ix bool in
    let continue := pure true : impure ix bool in
    let error := request Error : impure ix bool in
    do

      let* opcode := nextN 1 in
      match opcode with
      | EXIT => exit
      | NOP => continue

      | JUMP =>
        do
          let* (a: nat) := popN in
          setPC (toB64 a);
          continue
        end

      | JUMP_ZERO =>
        do
          let* (o: nat) := nextN 1 in
          let* (x: nat) := popN in
          when (x =? 0)
          do
            let* (pc: B64) := getPC in
            setPC (offset (signed (toB8 o)) pc : Addr)
          end;
          continue
        end

      | SET_SP =>
        do
          let* (a: nat) := popN in
          setSP (toB64 a);
          continue
        end

      | GET_PC =>
        do
          let* (a: B64) := getPC in
          push64 a;
          continue
        end

      | GET_SP =>
        do
          let* (a: B64) := getSP in
          push64 a;
          continue
        end

      | PUSH0 =>
        do
          push64 0;
          continue
        end

      | PUSH1 =>
        do
          let* (x: nat) := nextN 1 in
          push64 x;
          continue
        end

      | PUSH2 =>
        do
          let* (x: nat) := nextN 2 in
          push64 x;
          continue
        end

      | PUSH4 =>
        do
          let* (x: nat) := nextN 4 in
          push64 x;
          continue
        end

      | PUSH8 =>
        do
          let* (x: nat) := nextN 8 in
          push64 x;
          continue
        end

      | SIGX1 =>
        do
          let* (x: nat) := popN in
          push64 (signed (toB8 x));
          continue
        end

      | SIGX2 =>
        do
          let* (x: nat) := popN in
          push64 (signed (toB16 x));
          continue
        end

      | SIGX4 =>
        do
          let* (x: nat) := popN in
          push64 (signed (toB32 x));
          continue
        end

      | LOAD1 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := load 1 a in
          push64 x;
          continue
        end

      | LOAD2 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := load 2 a in
          push64 x;
          continue
        end

      | LOAD4 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := load 4 a in
          push64 x;
          continue
        end

      | LOAD8 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := load 8 a in
          push64 x;
          continue
        end

      | STORE1 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := popN in
          store 1 a x;
          continue
        end

      | STORE2 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := popN in
          store 2 a x;
          continue
        end

      | STORE4 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := popN in
          store 4 a x;
          continue
        end

      | STORE8 =>
        do
          let* (a: nat) := popN in
          let* (x: nat) := popN in
          store 8 a x;
          continue
        end

      | ADD =>
        do
          let* (x: nat) := popN in
          let* (y: nat) := popN in
          push64 (x + y);
          continue
        end

      | MULT =>
        do
          let* (x: nat) := popN in
          let* (y: nat) := popN in
          push64 (x * y);
          continue
        end

      | DIV =>
        do
          let* (x: nat) := popN in
          let* (y: nat) := popN in
          push64 (if x =? 0 then 0 else y / x);
          continue
        end

      | REM =>
        do
          let* (x: nat) := popN in
          let* (y: nat) := popN in
          push64 (if x =? 0 then 0 else y mod x);
          continue
        end

      | LT =>
        do
          let* (x: nat) := popN in
          let* (y: nat) := popN in
          push64 (if y <? x then -1 else 0);
          continue
        end

      | AND =>
        do
          let* (x: B64) := pop64 in
          let* (y: B64) := pop64 in
          push64 (Vector.map2 andb x y : B64);
          continue
        end

      | OR =>
        do
          let* (x: B64) := pop64 in
          let* (y: B64) := pop64 in
          push64 (Vector.map2 orb x y : B64);
          continue
        end

      | NOT =>
        do
          let* (x: B64) := pop64 in
          push64 (Vector.map negb x : B64);
          continue
        end

      | XOR =>
        do
          let* (x: B64) := pop64 in
          let* (y: B64) := pop64 in
          push64 (Vector.map2 xorb x y : B64);
          continue
        end

      (* *** *)

      | READ_FRAME =>
        do
          let* (i: nat) := popN in
          let* (pair: (nat * nat)%type) := request (ReadFrame i) in
          push64 (fst pair);
          push64 (snd pair);
          continue
        end

      | READ_PIXEL =>
        do
          let* (y: nat) := popN in
          let* (x: nat) := popN in
          let* (c: B8) := request (ReadPixel x y) in
          push64 c;
          continue
        end

      | NEW_FRAME =>
        do
          let* (r: nat) := popN in
          let* (h: nat) := popN in
          let* (w: nat) := popN in
          newFrame w h r;
          continue
        end

      | SET_PIXEL =>
        do
          let* (b: B64) := pop64 in
          let* (g: B64) := pop64 in
          let* (r: B64) := pop64 in
          let* (y: nat) := popN in
          let* (x: nat) := popN in
          request (SetPixel x y (r, g, b));
          continue
        end

      | ADD_SAMPLE =>
        do
          let* (r: nat) := popN in
          let* (l: nat) := popN in
          request (AddSample (toB16 l) (toB16 r));
          continue
        end

      | PUT_CHAR =>
        do
          let* (c: nat) := popN in
          request (PutChar (toB32 c));
          continue
        end

      | PUT_BYTE =>
        do
          let* (b: nat) := popN in
          request (PutByte (toB8 b));
          continue
        end

      | _ => error
      end
    end.

End limit_scope.


(** ** Next steps

The return value of [oneStep] indicates of the machine has stopped
(normally). In addition, the machine state consists of:

* The memory state/witness of type: [Memory].
* The input state: [Image InputColor]
* The current output state: [Frame (option OutputColor)]
* The output log state: [list (Frame OutputColor)]

Let [ActiveState] denote their product (as a record) except for the log.
*)

Record ActiveState : Type :=
  mkActiveState
    {
      A_mem: Memory;
      A_inp: Image InputColor;
      A_out: Frame (option OutputColor)
    }.

(** Below, we shall prove what happens when the machine is started in
various states [s:ActiveState]. In each case there will be:

* A predicate [pre: ActiveState -> Prop] saying which initial states [s0] we
  consider. [pre] can also refer to the parameters of the machine such as
  [memSize]. Most importantly, [pre] will usually describe the
  instructions immediately following the PC.

* A decidable predicate [end: ActiveState -> ActiveState -> bool] relating the
  initial state to the states [s] at which we should continue running.
  Thus, [end s0 s = true] for the final state [s]. Initially, we will just
  check that whether the PC is still within program fragment we are
  interested in.

* A predicate [outcome: ActiveState -> Outcome -> Prop] relating the initial
  state to a sequence describing the effect of running [cont] holds or the
  machine stops.

Given such a triple of predicates, we want to show that starting the
machine in an accepted initial state [s0] will always lead to an accepted
terminal state. *)

Definition Outcome : Type := ActiveState * list (Frame OutputColor).

(** We will not be interested in computations do not terminate. *)
