Require Import Utf8.

Require Import Equations.Equations.

Require Import Assembly.Mon.
Require Import Assembly.Bits.
Require Import Assembly.Dec.

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
    storeMany _ [] := ret tt;
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
    (* Instead of marking the memory as undefined here,
       we will express this in the corresponding [Cert]s.
       [storeMany sp (repeat None n);;]
    *)
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

  Context (OUT_CHARS : Proj State (list Char)).
  Context (OUT_BYTES : Proj State (list Byte)).
  Context (OUT_SOUND : Proj State Sound).
  Context (OUT_IMAGE : Proj State (Image (option OutputColor))).

  Definition putChar (c: Char) : M unit :=
    let* chars := get' OUT_CHARS in
    put' OUT_CHARS (cons c chars).

  Definition putByte (b: Byte) : M unit :=
    let* bytes := get' OUT_BYTES in
    put' OUT_BYTES (cons b bytes).

  Definition addSample (l r: Sample) : M unit :=
    let* samples := get' OUT_SOUND in
    put' OUT_SOUND (extendSamples l r samples).

  Definition setPixel (x y: nat) (c: OutputColor) : M unit :=
    let* img := get' OUT_IMAGE in
    assert* x < width img in
    assert* y < height img in
    put' OUT_IMAGE (updatePixel x y (Some c) img).


  (** ** Output log *)

  Record OutputFrame := mkFrame
  {
    image: Image OutputColor;
    sound: Sound;
    chars: list Char;  (* reversed *)
    bytes: list Byte;  (* reversed *)
  }.

  Context (LOG: Proj State (list OutputFrame)). (* reversed *)

  Definition image_complete (img: Image (option OutputColor)) : Prop :=
    forall x (Hx: x < width img) y (Hy: y < height img), pixel img Hx Hy.

  Definition extractImage (img: Image (option OutputColor)) : M (Image OutputColor) :=
    assert* image_complete img as H_complete in
    ret {|
        width := width img;
        height := height img;
        pixel x Hx y Hy := proj1_sig (some_some (H_complete x Hx y Hy));
      |}.

  Definition newFrame (w r h: nat) : M unit :=
    let* bytes := get' OUT_BYTES in
    let* chars := get' OUT_CHARS in
    let* sound := get' OUT_SOUND in
    let* img := get' OUT_IMAGE in
    let* image := extractImage img in
    let frame :=
        {|
          bytes := bytes;
          chars := chars;
          sound := sound;
          image := image;
        |} in
    let* current := get' LOG in
    put' LOG (frame :: current);;
    put' OUT_BYTES [];;
    put' OUT_CHARS [];;
    put' OUT_SOUND {|
           rate := r;
           samples _ := [];
         |};;
    put' OUT_IMAGE {|
           width := w;
           height := h;
           pixel _ _ _ _ := None;
         |}.


  (** ** Pairwise independent projections *)

  Context (independent_PC_SP:    Independent PC SP)
          (independent_PC_MEM:   Independent PC MEM)
          (independent_PC_INP:   Independent PC INP)
          (independent_PC_BYTES: Independent PC OUT_BYTES)
          (independent_PC_CHARS: Independent PC OUT_CHARS)
          (independent_PC_SOUND: Independent PC OUT_SOUND)
          (independent_PC_IMAGE: Independent PC OUT_IMAGE)
          (independent_PC_LOG:   Independent PC LOG)

          (independent_SP_MEM:   Independent SP MEM)
          (independent_SP_INP:   Independent SP INP)
          (independent_SP_BYTES: Independent SP OUT_BYTES)
          (independent_SP_CHARS: Independent SP OUT_CHARS)
          (independent_SP_SOUND: Independent SP OUT_SOUND)
          (independent_SP_IMAGE: Independent SP OUT_IMAGE)
          (independent_SP_LOG:   Independent SP LOG)

          (independent_MEM_INP:   Independent MEM INP)
          (independent_MEM_BYTES: Independent MEM OUT_BYTES)
          (independent_MEM_SOUND: Independent MEM OUT_CHARS)
          (independent_MEM_CHARS: Independent MEM OUT_SOUND)
          (independent_MEM_IMAGE: Independent MEM OUT_IMAGE)
          (independent_MEM_LOG:   Independent MEM LOG)

          (independent_INP_BYTES: Independent INP OUT_BYTES)
          (independent_INP_CHARS: Independent INP OUT_CHARS)
          (independent_INP_SOUND: Independent INP OUT_SOUND)
          (independent_INP_IMAGE: Independent INP OUT_IMAGE)
          (independent_INP_LOG:   Independent INP LOG)

          (independent_BYTES_CHARS: Independent OUT_BYTES OUT_CHARS)
          (independent_BYTES_SOUND: Independent OUT_BYTES OUT_SOUND)
          (independent_BYTES_IMAGE: Independent OUT_BYTES OUT_IMAGE)
          (independent_BYTES_LOG:   Independent OUT_BYTES LOG)

          (independent_CHARS_SOUND: Independent OUT_CHARS OUT_SOUND)
          (independent_CHARS_IMAGE: Independent OUT_CHARS OUT_IMAGE)
          (independent_CHARS_LOG:   Independent OUT_CHARS LOG)

          (independent_SOUND_IMAGE: Independent OUT_SOUND OUT_IMAGE)
          (independent_SOUND_LOG:   Independent OUT_SOUND LOG)

          (independent_IMAGE_LOG: Independent OUT_IMAGE LOG).

End core_module.
