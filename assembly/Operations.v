Require Import Utf8.

Require Import Equations.Equations.

Require Import RecordUpdate.RecordSet.
Import RecordSetNotations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.
Require Import Assembly.Convenience.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Set Implicit Arguments.

Open Scope monad_scope.


Notation "'assert*' P 'in' result" :=
  (if (decision P%type) then result else err) (at level 70).

Notation "'assert*' P 'as' H 'in' result" :=
  (match (decision P%type) with
   | left H => result
   | right _ => err
   end) (at level 70).

(* It seems RecordUpdate does not handle dependent types. *)
Definition updatePixel {C} (x y: nat) (c: C) (im: Image C) : Image C :=
{|
  width := width im;
  height := height im;
  pixel x' Hx y' Hy :=
    if (decision ((x' = x) /\ (y' = y)))
    then c
    else pixel im Hx Hy
|}.


(** ** Machine parameters

    This abstraction makes life easier, presumably since we avoid
    (unwanted) coercions from bits to number. *)

Module Type machine_type.

  Context
    (State: Type)
    (M: Type -> Type)
    {H_mon: SMonad State M}

    (Addr: Type)
    {H_eqdec: EqDec Addr}
    (available: Addr -> bool)
    (offset: Z -> Addr -> Addr) (* This should be a group action. *)
    (Cell: Type)

    (InputColor: Type)
    (allInputImages: list (Image InputColor))

    (OutputColor: Type)
    (Char: Type)
    (Byte: Type)
    (Sample: Type).

End machine_type.


Module core_module (MT: machine_type).

  Import MT.
  Existing Instance H_mon.
  Existing Instance H_eqdec.

  Definition get' {X} (proj: Proj State X) := get (SMonad := proj_smonad M proj).
  Definition put' {X} (proj: Proj State X) := put (SMonad := proj_smonad M proj).


  (** ** Memory *)

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Context (MEM: Proj State Memory).

  Definition load (a: Addr): M Cell :=
    assert* available a as H in
    let* s := get' MEM in
    match s a H with
    | Some x => ret x
    | _ => err
    end.

  Definition store (a: Addr) (o: option Cell) : M unit :=
    assert* available a in
    let* s := get' MEM in
    let s' a' H := if eq_dec a a' then o else s a' H in
    put' MEM s'.

  (* TODO: noind is used to circumvent what appears to be an Equation bug. *)
  Equations(noind) loadMany (n: nat) (_: Addr): M (Vector.t Cell n) :=
    loadMany 0 _ := ret Vector.nil;
    loadMany (S n) a :=
      let* x := load a in
      let* r := loadMany n (offset 1 a) in
      ret (Vector.cons x r).

  Equations storeMany (_: Addr) (_: list (option Cell)) : M unit :=
    storeMany _ nil := ret tt;
    storeMany a (x :: u) :=
      store a x;;
      storeMany (offset 1 a) u.


  (** ** Registers *)

  Context (PC: Proj State Addr)
          (SP: Proj State Addr).

  Definition next (n: nat) : M (Vector.t Cell n) :=
    let* pc := get' PC in
    let* res := loadMany n pc in
    put' PC (offset n pc);;
    ret res.

  Definition pushMany (u: list Cell): M unit :=
    let* sp := get' SP in
    (* The stack grows downwards. *)
    let a := offset (- List.length u) sp in
    put' SP a;;
    storeMany a (map Some u).

  Definition popMany (n: nat): M (Vector.t Cell n) :=
    let* sp := get' SP in
    let* res := loadMany n sp in
    (* Mark memory as undefined *)
    storeMany sp (repeat None n);;
    put' SP (offset n sp);;
    ret res.


  (** ** Input *)

  Local Definition Input := Image InputColor.

  Context (INP: Proj State Input).

  Definition readFrame (i: nat) : M (nat * nat) :=
    let inp := nth i allInputImages noImage in
    put' INP inp;;
    ret (width inp, height inp).

  Definition readPixel (x y : nat) : M InputColor :=
    let* inp := get' INP in
    assert* x < width inp as Hx in
    assert* y < height inp as Hy in
    ret (pixel inp Hx Hy).


  (** ** Current output *)

  Record Sound := mkSound
  {
    rate: nat;
    samples (Hr: rate <> 0) : list (Sample * Sample); (* reversed *)
  }.

  Definition extendSamples (l r: Sample) (sn: Sound) :=
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

  Local Definition OC := option OutputColor.

  Instance etaFrame : Settable _ := settable! (@mkFrame OC) <(@image OC); (@sound OC); (@chars OC); (@bytes OC)>.

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

  Context (OUT: Proj State (Frame OC)).

  Definition image_complete (img: Image OC) : Prop :=
    forall x (Hx: x < width img) y (Hy: y < height img), pixel img Hx Hy.

  Definition get_some {A} {x: option A} : x -> A :=
    match x return x -> A with
    | Some y => fun _ => y
    | None => none_not_some
    end.

  Definition extractImage (img: Image OC) : M (Image OutputColor) :=
    assert* image_complete img as H_complete in
    ret {|
        width := width img;
        height := height img;
        pixel x Hx y Hy := get_some (H_complete x Hx y Hy);
      |}.

  Definition nextOutputFrame (w r h: nat) : M (Frame OutputColor) :=
    let* current := get' OUT in
    let* img := extractImage (image current) in
    put' OUT (freshFrame w r h);;
    ret {|
        bytes := bytes current;
        chars := chars current;
        sound := sound current;
        image := img;
      |}.

  Definition setPixel (x y: nat) (c: OutputColor) : M unit :=
    let* current := get' OUT in
    assert* x < width (image current) in
    assert* y < height (image current) in
    put' OUT (set (@image OC) (updatePixel x y (Some c)) current).

  Definition addSample (l r: Sample) : M unit :=
    let* current := get' OUT in
    put' OUT (set (@sound OC) (extendSamples l r) current).

  Definition putChar (c: Char) : M unit :=
    let* current := get' OUT in
    put' OUT (set (@chars OC) (cons c) current).

  Definition putByte (b: Byte) : M unit :=
    let* current := get' OUT in
    put' OUT (set (@bytes OC) (cons b) current).


  (** ** Output log *)

  Context (LOG: Proj State (list (Frame OutputColor))).

  Definition newFrame (w r h: nat) : M unit :=
    let* current := get' LOG in
    let* flushed := nextOutputFrame w r h in
    put' LOG (flushed :: current).


  (** ** Pairwise disjoint projections *)

  Context (disjoint_PC_SP:  Disjoint PC SP)
          (disjoint_PC_MEM: Disjoint PC MEM)
          (disjoint_PC_INP: Disjoint PC INP)
          (disjoint_PC_OUT: Disjoint PC OUT)
          (disjoint_PC_LOG: Disjoint PC LOG)

          (disjoint_SP_MEM: Disjoint SP MEM)
          (disjoint_SP_INP: Disjoint SP INP)
          (disjoint_SP_OUT: Disjoint SP OUT)
          (disjoint_SP_LOG: Disjoint SP LOG)

          (disjoint_MEM_INP: Disjoint MEM INP)
          (disjoint_MEM_OUT: Disjoint MEM OUT)
          (disjoint_MEM_LOG: Disjoint MEM LOG)

          (disjoint_INP_OUT: Disjoint INP OUT)
          (disjoint_INP_LOG: Disjoint INP LOG)

          (disjoint_OUT_LOG: Disjoint OUT LOG).

End core_module.
