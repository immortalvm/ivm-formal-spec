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


(** ** Machine parameters

This sort of abstraction makes life easier, presumably since we avoid
(unwanted) coercions from bits to number etc. See also this thread:
https://sympa.inria.fr/sympa/arc/coq-club/2018-08/msg00036.html *)

Module Type machine_type.

  Context
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

Module Type machine_type_defs (MT: machine_type).

  Import MT.

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Record Sound := mkSound
  {
    rate: nat;
    samples (Hr: rate <> 0) : list (Sample * Sample); (* reversed *)
  }.

  Record OutputFrame := mkFrame
  {
    image: Image OutputColor;
    sound: Sound;
    chars: list Char;  (* reversed *)
    bytes: list Byte;  (* reversed *)
  }.

End machine_type_defs.

Module Type machine_type' := machine_type <+ machine_type_defs.

Module Type core_type (MT: machine_type').

  Import MT.

  Context
    (State: Type)
    (M: Type -> Type)
    {H_mon: SMonad State M}

    (MEM: Proj State Memory)

    (PC: Proj State Addr)
    (SP: Proj State Addr)

    (INP: Proj State (Image InputColor))

    (** The following lists all have the latest element first. *)
    (OUT_CHARS : Proj State (list Char))
    (OUT_BYTES : Proj State (list Byte))
    (OUT_SOUND : Proj State Sound)
    (OUT_IMAGE : Proj State (Image (option OutputColor)))

    (LOG: Proj State (list OutputFrame)).

  (** Pairwise independent projections

  We choose the pairs with MEM and OUT_IMAGE on the left to avoid relying
  on the symmetry of [Independent] later (which easily leads to inifinite
  loops). *)

  Context (independent_MEM_IMAGE: Independent MEM OUT_IMAGE)
          (independent_MEM_BYTES: Independent MEM OUT_BYTES)
          (independent_MEM_CHARS: Independent MEM OUT_CHARS)
          (independent_MEM_SOUND: Independent MEM OUT_SOUND)
          (independent_MEM_LOG:   Independent MEM LOG)
          (independent_MEM_INP:   Independent MEM INP)
          (independent_MEM_PC:    Independent MEM PC)
          (independent_MEM_SP:    Independent MEM SP)

          (independent_IMAGE_BYTES: Independent OUT_IMAGE OUT_BYTES)
          (independent_IMAGE_CHARS: Independent OUT_IMAGE OUT_CHARS)
          (independent_IMAGE_SOUND: Independent OUT_IMAGE OUT_SOUND)
          (independent_IMAGE_LOG:   Independent OUT_IMAGE LOG)
          (independent_IMAGE_INP:   Independent OUT_IMAGE INP)
          (independent_IMAGE_PC:    Independent OUT_IMAGE PC)
          (independent_IMAGE_SP:    Independent OUT_IMAGE SP)

          (independent_BYTES_CHARS: Independent OUT_BYTES OUT_CHARS)
          (independent_BYTES_SOUND: Independent OUT_BYTES OUT_SOUND)
          (independent_BYTES_LOG:   Independent OUT_BYTES LOG)
          (independent_BYTES_INP:   Independent OUT_BYTES INP)
          (independent_BYTES_PC:    Independent OUT_BYTES PC)
          (independent_BYTES_SP:    Independent OUT_BYTES SP)

          (independent_CHARS_SOUND: Independent OUT_CHARS OUT_SOUND)
          (independent_CHARS_LOG:   Independent OUT_CHARS LOG)
          (independent_CHARS_INP:   Independent OUT_CHARS INP)
          (independent_CHARS_PC:    Independent OUT_CHARS PC)
          (independent_CHARS_SP:    Independent OUT_CHARS SP)

          (independent_SOUND_LOG: Independent OUT_SOUND LOG)
          (independent_SOUND_INP: Independent OUT_SOUND INP)
          (independent_SOUND_PC:  Independent OUT_SOUND PC)
          (independent_SOUND_SP:  Independent OUT_SOUND SP)

          (independent_LOG_INP: Independent LOG INP)
          (independent_LOG_PC:  Independent LOG PC)
          (independent_LOG_SP:  Independent LOG SP)

          (independent_INP_PC: Independent INP PC)
          (independent_INP_SP: Independent INP SP)

          (independent_PC_SP: Independent PC SP).

End core_type.

Module Type core_type' := machine_type' <+ core_type.


Module core_module (CT: core_type').

  Import CT.
  Existing Instance H_eqdec.
  Existing Instance H_mon.

  Definition get' {X} (proj: Proj State X) := get (SMonad := proj_smonad M proj).
  Definition put' {X} (proj: Proj State X) := put (SMonad := proj_smonad M proj).


  (** ** Memory *)

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

  Definition extendSamples (l r: Sample) (sn: Sound) :=
  {|
    rate := rate sn;
    samples Hr := (l, r) :: (samples sn Hr);
  |}.

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

End core_module.
