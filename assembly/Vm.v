(* coqc -Q . Assembly mon.v && coqc -Q . Assembly bits.v *)

Require Import Utf8.

Require Import Equations.Equations.
Set Equations With UIP. (* TODO: Is this useful here? *)

Require Import RecordUpdate.RecordSet.
Import RecordSetNotations.

Require Import Assembly.mon.
Require Import Assembly.bits.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Set Implicit Arguments.

Open Scope monad_scope.

Notation "'assert*' P 'in' result" := (if (decide0 P%type) then result else err) (at level 70).

Notation "'assert*' H ':=' P 'in' result" :=
  (match (decide1 P%type) with
   | left H => result
   | right _ => err
   end) (at level 70).


(** ** Machine parameters

    This abstraction makes life easier, presumably since we avoid
    (unwanted) coercions from bits to number. *)

Module Type machine_type.

  Context
    (Addr: Type)
    `{H_eqdec: EqDec Addr}
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
  Existing Instance H_eqdec.


  (** ** Memory *)

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Context {State: Type}
          {M: Type -> Type}
          `(H_mon: SMonad State M)
          `(H_mem: Proj State Memory).

  Existing Instance H_mon.
  Existing Instance H_mem.

  Definition getMem := get (SMonad := proj_smonad M H_mem).
  Definition putMem := put (SMonad := proj_smonad M H_mem).

  Definition load (a: Addr): M Cell :=
    assert* H := available a in
    let* s := getMem in
    match s a H with
    | Some x => ret x
    | _ => err
    end.

  Definition store (a: Addr) (o: option Cell) : M unit :=
    assert* available a in
    let* s := getMem in
    let s' a' H := if eq_dec a a' then o else s a' H in
    putMem s'.

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

  Context `(H_pc: Proj State Addr)
          `(H_sp: Proj State Addr).

  Definition getPC := get (SMonad := proj_smonad M H_pc).
  Definition setPC := put (SMonad := proj_smonad M H_pc).
  Definition getSP := get (SMonad := proj_smonad M H_sp).
  Definition setSP := put (SMonad := proj_smonad M H_sp).

  Definition next (n: nat) : M (Vector.t Cell n) :=
    let* pc := getPC in
    let* res := loadMany n pc in
    setPC (offset n pc);;
    ret res.

  Definition pushMany (u: list Cell): M unit :=
    let* sp := getSP in
    (* The stack grows downwards. *)
    let a := offset (- List.length u) sp in
    setSP a;;
    storeMany a (map Some u).

  Definition popMany (n: nat): M (Vector.t Cell n) :=
    let* sp := getSP in
    let* res := loadMany n sp in
    (* Mark memory as undefined *)
    storeMany sp (repeat None n);;
    setSP (offset n sp);;
    ret res.


  (** ** Input *)

  Local Definition Input := Image InputColor.

  Context `(H_inp: Proj State Input).

  Definition readFrame (i: nat) : M unit :=
    put (SMonad := proj_smonad M H_inp)
        (nth i allInputImages noImage).

  Definition readPixel (x y : nat) : M InputColor :=
    let* inp := get (SMonad := proj_smonad M H_inp) in
    assert* Hx := x < width inp in
    assert* Hy := y < height inp in
    ret (pixel inp Hx Hy).


  (** ** Current output *)

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

  Context `{H_out: Proj State (Frame OC)}.

  Definition getOut := get (SMonad := proj_smonad M H_out).
  Definition setOut := put (SMonad := proj_smonad M H_out).

  #[refine]
  Instance option_decidable {A: Type} (x: option A) : Decidable (x <> None) :=
    {
    decision := if x then true else false;
    }.
  Proof.
    destruct x as [x|]; constructor; easy.
  Defined.

  Instance image_complete_decidable (img: Image OC) :
    Decidable (forall x (Hx: x < width img) y (Hy: y < height img), pixel img Hx Hy <> None).
  Proof.
    assert (forall x (Hx:x<width img), Decidable (forall y (Hy:y<height img), pixel img Hx Hy <> None)) as H_inner.
    - intros x Hx.
      apply (@bounded_quantifiers_decidable _ (fun y => option_decidable _)) .

    exists true.
    split.




  Definition finalImage (img: Image OC) : M (Image OutputColor) :=


    err.

  Definition nextOutputFrame (w r h: nat) : M (Frame OutputColor) :=
    let* current := getOut in
    setOut (freshFrame w r h);;
    ret {|
        bytes := bytes current;
        chars := chars current;
        sound := sound current;
        image := {|
                  width := width current;
                  height := height current;
                  pixel x Hx y Hy :=
                |}
        |}.



End core_module.


(* TODO: State that all the projections must be disjoint. *)
