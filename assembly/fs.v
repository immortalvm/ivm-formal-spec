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

Equations to_Bits (n: nat) (_: Z) : Bits n :=
  to_Bits O _ := [];
  to_Bits (S n) z := (z mod 2 =? 1) :: to_Bits n (z / 2).

Close Scope Z_scope.
Close Scope vector.


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

Class Core0 :=
{
  Addr: Type;
  H_eqdec :> EqDec Addr;
  available: Addr -> Prop;
  offset: Z -> Addr -> Addr; (* This should be a group action. *)
  Cell: Type;
}.

Section memory_section.

  Context `{Hc0: Core0}.

  Inductive MEMORY : interface :=
  | Load (a: Addr) : MEMORY Cell
  | Store (a: Addr) (x: option Cell) : MEMORY unit.

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Equations o_caller_memory (mem: Memory) {A: Type} (op: MEMORY A) : Prop :=
    o_caller_memory mem (Load a) := available a;
    o_caller_memory _ (Store a _) := available a.

  (* For "undefined" memory addresses Load can return any value. *)
  Equations o_callee_memory (mem: Memory) {A: Type} (op: MEMORY A) (y: A) : Prop :=
    o_callee_memory mem (Load a) y := exists (Ha: available a), match mem a Ha with Some x => y = x | _ => True end;
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

End memory_section.

Class Core (ix: interface) `{Hc0 : Core0} :=
{
  Mmem :> MayProvide ix MEMORY;
  Hmem :> @Provide ix MEMORY Mmem;

  Mpc: MayProvide ix (STORE Addr);
  Hpc : @Provide ix (STORE Addr) Mpc;

  Msp : MayProvide ix (STORE Addr);
  Hsp : @Provide ix (STORE Addr) Msp;
}.

Section pc_sp_section.

  Context ix `{Hc: Core ix}.

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
       (* Clear memory! *)
       storeMem sp (repeat None n);
       setSP (offset n sp);
       pure res
    end.

End pc_sp_section.


(** ** I/O *)

Class Inp0 :=
{
  InputColor: Type;
  allInputImages: list (Image InputColor);
}.

Section input_section.

  Context `{Hi0: Inp0}.

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

End input_section.

Class Out0 :=
{
  OutputColor: Type;
  Char: Type;
  Byte: Type;
  Sample: Type;
}.

Section output_section.

  Context `{Ho0: Out0}.

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

End output_section.


(** ** Integration *)

Class Machine (ix: interface) `{Hc0 : Core0} `{Hi0 : Inp0} `{Ho0 : Out0} :=
{
  Hc :> @Core ix Hc0;

  Minp :> MayProvide ix INPUT;
  Hinp :> @Provide ix INPUT Minp;

  Mout :> MayProvide ix OUTPUT;
  Hout :> @Provide ix OUTPUT Mout;

  Mcon :> MayProvide ix (LOG (Frame OutputColor));
  Hcon :> @Provide ix (LOG (Frame OutputColor)) Mcon;

  Mf :> MayProvide ix ERROR;
  Hf :> @Provide ix ERROR Mf;
}.

Definition newFrame {ix} `{Machine ix} (w h r : nat) : impure ix unit :=
  do
    let* previous := request (NextFrame w h r) in
    request (Log previous)
  end.

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

Section integration_section.

  (** Use notation instead of definition to keep coercions. *)
  (* #[local] Notation Addr := (Bits 64) (only parsing). *)
  (* #[local] Notation Cell := (Bits 8) (only parsing). *)

  Context
    (memStart: nat) (* Alternative type: Bits 64. *)
    (memSize: nat)
    (inputImages : list (Image (Bits 8))).

  Instance Hc0 : Core0 :=
  {
    Addr := Bits 64;
    available a := memStart <= a /\ a < memStart + memSize;
    offset z a := to_Bits 64 (z + a);
    Cell := Bits 64;
  }.

  Instance Hi0 : Inp0 :=
  {
    InputColor := Bits 8;
    allInputImages := inputImages;
  }.

  Instance Ho0 : Out0 :=
  {
    OutputColor := (Bits 64) * (Bits 64) * (Bits 64);
    Char := Bits 32;
    Byte := Bits 8;
    Sample := Bits 16;
  }.

  Context ix `{@Machine ix Hc0 Hi0 Ho0}.

  Definition littleEndian (u: list Cell) : nat :=
    bitListToNat (concat (map to_BitList u)).

  Definition next' n : impure ix nat :=
    do
      (* Coq/FreeSpec hangs if the typing is dropped. *)
      let* (bytes : Vector.t Cell n) := next n in
      pure (littleEndian bytes)
    end.

  Definition pop' : impure ix (Bits 64) :=
    do
      let* (bytes: Vector.t Cell 8) := pop 8 in
      pure (to_Bits 64 (littleEndian bytes))
    end.

  Import Instructions.

  Set Printing Coercions.

  Definition oneStep : impure ix bool :=
    do
      let continue := pure true : impure ix bool in
      let stop := pure false : impure ix bool in
      let error := request Error : impure ix bool in

      let* opcode := next' 1 in
      match opcode with
      | EXIT => stop
      | NOP => continue
      | JUMP =>
        do
          let* (a: Bits 64) := pop' in
          setPC a;
          continue
        end
      | JUMP_ZERO =>
        do
          let* (o: nat) := next' 1 in
          let* x := pop' in
          if x =? 0
          then
            do
              let* (pc: Bits 64) := getPC in
              setPC (offset o pc)
            end : impure ix unit
          else
            pure tt;
          continue
        end

      | SET_SP => continue
      | GET_PC => continue
      | GET_SP => continue
      | PUSH0 => continue
      | PUSH1 => continue
      | PUSH2 => continue
      | PUSH4 => continue
      | PUSH8 => continue
      | SIGX1 => continue
      | SIGX2 => continue
      | SIGX4 => continue
      | LOAD1 => continue
      | LOAD2 => continue
      | LOAD4 => continue
      | LOAD8 => continue
      | STORE1 => continue
      | STORE2 => continue
      | STORE4 => continue
      | STORE8 => continue
      | ADD => continue
      | MULT => continue
      | DIV => continue
      | REM => continue
      | LT => continue
      | AND => continue
      | OR => continue
      | NOT => continue
      | XOR => continue

      | READ_FRAME => continue
      | READ_PIXEL => continue
      | NEW_FRAME => continue
      | SET_PIXEL => continue
      | ADD_SAMPLE => continue
      | PUT_CHAR => continue
      | PUT_BYTE => continue

      | _ => error
      end
    end.



End integration_section.
