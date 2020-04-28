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
Definition Id_BitList_List (u: BitList) : list bool := u.
Coercion Id_BitList_List : BitList >-> list.

Definition boolToNat (x: bool) : nat := if x then 1 else 0.
Coercion boolToNat : bool >-> nat.

(** Little-endian (reverse of binary notation) *)
Equations bitListToNat (_: BitList) : nat :=
  bitListToNat [] := 0;
  bitListToNat (x :: u) := 2 * bitListToNat u + x.

Coercion bitListToNat : BitList >-> nat.


(** ** Core *)

Section core_section.

  Context
    (Addr: Type) `{EqDec Addr} (available: Addr -> Prop)
    (offset: Z -> Addr -> Addr) (* This should be a group action. *)
    (Cell: Type).

  (* Definition TERMINATED := STORE bool. *)
  Definition PC := STORE Addr.
  Definition SP := STORE Addr.

  Inductive MEMORY : interface :=
  | Load (a: Addr) : MEMORY Cell
  | Store (a: Addr) (x: option Cell) : MEMORY unit.

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Equations o_caller_memory (mem: Memory) {A: Type} (op: MEMORY A) : Prop :=
    o_caller_memory mem (Load a) := exists (Ha: available a), mem a Ha <> None;
    o_caller_memory _ (Store a _) := available a.

  Equations o_callee_memory (mem: Memory) {A: Type} (op: MEMORY A) (x: A) : Prop :=
    o_callee_memory mem (Load a) x := exists (Ha: available a), mem a Ha = Some x;
    o_callee_memory _ _ _ := True.

  Definition memory_contract (A: Type) : contract MEMORY Memory :=
    {|
    witness_update mem _ op _ :=
      match op with
      | Store a x => fun a' Ha => if eq_dec a a' then x else mem a' Ha
      | _ => mem
      end;
    caller_obligation := o_caller_memory;
    callee_obligation := o_callee_memory;
    |}.

  Context
    `{ix: interface}
    `{Hpc: Provide ix PC}
    `{Hsp: Provide ix SP}
    `{Hmem: Provide ix MEMORY}.

  Definition getPC : impure ix Addr := request (Get : PC Addr).
  Definition setPC a : impure ix unit := request (Put a : PC unit).

  Definition getSP : impure ix Addr := request (Get : SP Addr).
  Definition setSP a : impure ix unit := request (Put a : SP unit).

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
       let a := offset (- List.length u) sp in (* The stack grows downwards. *)
       setSP a;
       storeMem a (map Some u)
    end.

  Definition pop (n: nat) : impure ix unit :=
    do let* sp := getSP in
       storeMem sp (repeat None n); (* Clear memory! *)
       setSP (offset n sp)
    end.

End core_section.


(** ** I/O *)

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

Section input_section.

  Context
    (Color: Type)
    (allImages: list (Image Color)).

  Inductive INPUT: interface :=
  | ReadFrame (i: nat) : INPUT (nat * nat)%type
  | ReadPixel (x y: nat) : INPUT Color.

  Local Definition Input := Image Color.

  Equations o_caller_input (inp: Input) {A: Type} (op: INPUT A) : Prop :=
    o_caller_input inp (ReadPixel x y) := x < width inp /\ y < height inp;
    o_caller_input inp _ := True.

  Equations o_callee_input (inp: Input) {A: Type} (op: INPUT A) (_: A) : Prop :=
    o_callee_input inp (ReadPixel x y) c :=
      forall (Hx: x < width inp) (Hy: y < height inp), pixel inp Hx Hy = c;
    o_callee_input _ _ _ := True.

  Definition input_contract : contract INPUT Input :=
    {|
    witness_update inp _ op _ :=
      match op with
      | ReadFrame i => nth i allImages noImage
      | _ => inp
      end;
    caller_obligation := o_caller_input;
    callee_obligation := o_callee_input;
    |}.

End input_section.

Section consumer_section.

  Context (Value: Type).

  Inductive CONSUMER : interface :=
  | Consume (x: Value) : CONSUMER unit.

  Definition consumer_contract : contract CONSUMER (list Value) :=
    {|
    witness_update lst _ op _ := match op with Consume x => x :: lst end;
    caller_obligation := no_caller_obligation;
    callee_obligation := no_callee_obligation;
    |}.

End consumer_section.

Section output_section.

  Context
    (Color: Type)
    (Char: Type)
    (Byte: Type)
    (Sample: Type).

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

  Local Definition OC := option Color.

  Instance etaFrame : Settable _ := settable! (@mkFrame OC) <(@image OC); (@sound OC); (@chars OC); (@bytes OC)>.

  Inductive OUTPUT: interface :=
  | NextFrame (width heigth rate : nat) : OUTPUT (Frame Color) (* Returns the previous frame *)
  | SetPixel (x y: nat) (c: Color) : OUTPUT unit
  | AddSample (l: Sample) (r: Sample) : OUTPUT unit
  | PutChar (c: Char) : OUTPUT unit
  | PutByte (b: Byte) : OUTPUT unit.

  Definition newFrame (w h r: nat) : Frame OC :=
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

  Definition output_contract : contract OUTPUT (Frame OC) :=
    {|
    witness_update fr _ op _ :=
      match op with
      | NextFrame w h r => newFrame w h r
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

Section integration_section.

  (** Specialize [to_list] to get coercion [Bits >-> nat]. *)
  Definition Bits: nat -> Type := Vector.t bool.
  Definition to_BitList {n} (u: Bits n) : BitList := u.
  Coercion to_BitList : Bits >-> BitList.

  (** Use notation instead of definition to keep coercions. *)
  #[local] Notation Addr := (Bits 64) (only parsing).
  #[local] Notation Cell := (Bits 8) (only parsing).
  #[local] Notation InputColor := (Bits 8) (only parsing).
  Definition OutputColor: Type := (Bits 64) * (Bits 64) * (Bits 64).

  #[local] Notation Char := (Bits 32) (only parsing).
  #[local] Notation Byte := (Bits 8) (only parsing).
  #[local] Notation Sample := (Bits 16) (only parsing).

  Context
    (memStart: Addr)
    (memSize: nat)

    (* The available memory should not "wrap". *)
    (Hsize: memStart + memSize <= 2 ^ 64)

    (ix: interface)
    `{Hpc: Provide ix (PC Addr)}
    `{Hsp: Provide ix (SP Addr)}
    `{Hmem: Provide ix (MEMORY Addr Cell)}

    (allInputImages: list (Image InputColor))
    `{Hinp: Provide ix (INPUT InputColor)}.

  Instance Addr_eqdec : EqDec Addr.
  Proof.
    eqdec_proof.
  Defined.

  Definition available (a: Addr) : Prop := memStart <= a /\ a < memStart + memSize.

  Definition littleEndian (u: list Cell) : nat := bitListToNat (concat (map to_BitList u)).



End integration_section.
