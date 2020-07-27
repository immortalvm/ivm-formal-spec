From Assembly Require Import Basics.

Unset Suggest Proof Using.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Set Implicit Arguments.


(** ** [Z]-actions *)

Class Z_action {X} (f: Z -> X -> X) : Prop :=
{
  Z_action_zero x : f 0 x = x;
  Z_action_add z z' x : f (z + z')%Z x = f z (f z' x);
}.


(** ** Images *)

Local Open Scope N.

Record Image (C: Type) :=
  mkImage {
      width: N;
      height: N;
      pixel (x: N) (Hx: x < width) (y: N) (Hy: y < height): C;
    }.

Definition noImage {C}: Image C.
  refine {|
      width := 0;
      height := 0;
      pixel x Hx y Hy := _;
    |}.
  lia.
Defined.

Local Definition image_telescope {C} (img: Image C) :
  sigma(fun w => sigma(fun h => forall x (Hx: x<w) y (Hy: y<h), C)) :=
  match img with @mkImage _ w h p => sigmaI _ w (sigmaI _ h p) end.

Lemma inj_right_image {C} {w h p p'} :
  {|width:=w; height:=h; pixel:=p|} = {|width:=w; height:=h; pixel:=p'|} :> Image C
  -> p = p'.
Proof.
  intros Hi.
  match type of Hi with
  | ?i = ?i' => assert (image_telescope i = image_telescope i') as Ht;
                 [f_equal; exact Hi | ]
  end.
  unfold image_telescope in Ht.
  do 2 derive Ht (EqDec.inj_right_sigma _ _ _ Ht).
  exact Ht.
Qed.

Definition updatePixel {C} (x y: N) (c: C) (im: Image C) : Image C :=
{|
  width := width im;
  height := height im;
  pixel x' Hx y' Hy :=
    if decide ((x' = x) /\ (y' = y))
    then c
    else pixel im Hx Hy
|}.


(** ** Machine parameters

Abstractions makes working with Coq much easier. *)

Module Type MachineParameters.
  Parameter Inline Addr: Type.
  Parameter Inline H_eqdec: EqDec Addr.
  Parameter Inline available: Addr -> bool.
  Parameter Inline offset: Z -> Addr -> Addr.
  Parameter offset_action: Z_action offset.
  Parameter Inline Cell: Type.

  Parameter Inline InputColor: Type.
  Parameter Inline allInputImages: list (Image InputColor).

  Parameter Inline OutputColor: Type.
  Parameter Inline Char: Type.
  Parameter Inline Byte: Type.
  Parameter Inline Sample: Type.
End MachineParameters.

Module Core (MP: MachineParameters).

  Export MP.

  Definition Cells := vector Cell.

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Record Sound := mkSound
  {
    rate: N;
    samples (Hr: rate <> 0) : list (Sample * Sample); (* reversed *)
  }.

  Record OutputFrame := mkFrame
  {
    image: Image OutputColor;
    sound: Sound;
    chars: list Char;  (* reversed *)
    bytes: list Byte;  (* reversed *)
  }.

  Class MachineParams1 :=
  {
    State: Type;

    MEM: Lens State Memory;
    PC: Lens State Addr;
    SP: Lens State Addr;

    INP: Lens State N; (* Index of current input frame. *)

    (** The following lists all have the latest element first. *)
    OUT_CHARS : Lens State (list Char);
    OUT_BYTES : Lens State (list Byte);
    OUT_SOUND : Lens State Sound;
    OUT_IMAGE : Lens State (Image (option OutputColor));

    LOG: Lens State (list OutputFrame);

    (** Pairwise independent lenses

    We choose the pairs with MEM and OUT_IMAGE on the left to avoid relying
    on the symmetry of [Independent] later (which easily leads to inifinite
    loops). *)

    independent_MEM_IMAGE: Independent MEM OUT_IMAGE;
    independent_MEM_BYTES: Independent MEM OUT_BYTES;
    independent_MEM_CHARS: Independent MEM OUT_CHARS;
    independent_MEM_SOUND: Independent MEM OUT_SOUND;
    independent_MEM_LOG:   Independent MEM LOG;
    independent_MEM_INP:   Independent MEM INP;
    independent_MEM_PC:    Independent MEM PC;
    independent_MEM_SP:    Independent MEM SP;

    independent_IMAGE_BYTES: Independent OUT_IMAGE OUT_BYTES;
    independent_IMAGE_CHARS: Independent OUT_IMAGE OUT_CHARS;
    independent_IMAGE_SOUND: Independent OUT_IMAGE OUT_SOUND;
    independent_IMAGE_LOG:   Independent OUT_IMAGE LOG;
    independent_IMAGE_INP:   Independent OUT_IMAGE INP;
    independent_IMAGE_PC:    Independent OUT_IMAGE PC;
    independent_IMAGE_SP:    Independent OUT_IMAGE SP;

    independent_BYTES_CHARS: Independent OUT_BYTES OUT_CHARS;
    independent_BYTES_SOUND: Independent OUT_BYTES OUT_SOUND;
    independent_BYTES_LOG:   Independent OUT_BYTES LOG;
    independent_BYTES_INP:   Independent OUT_BYTES INP;
    independent_BYTES_PC:    Independent OUT_BYTES PC;
    independent_BYTES_SP:    Independent OUT_BYTES SP;

    independent_CHARS_SOUND: Independent OUT_CHARS OUT_SOUND;
    independent_CHARS_LOG:   Independent OUT_CHARS LOG;
    independent_CHARS_INP:   Independent OUT_CHARS INP;
    independent_CHARS_PC:    Independent OUT_CHARS PC;
    independent_CHARS_SP:    Independent OUT_CHARS SP;

    independent_SOUND_LOG: Independent OUT_SOUND LOG;
    independent_SOUND_INP: Independent OUT_SOUND INP;
    independent_SOUND_PC:  Independent OUT_SOUND PC;
    independent_SOUND_SP:  Independent OUT_SOUND SP;

    independent_LOG_INP: Independent LOG INP;
    independent_LOG_PC:  Independent LOG PC;
    independent_LOG_SP:  Independent LOG SP;

    independent_INP_PC: Independent INP PC;
    independent_INP_SP: Independent INP SP;

    independent_PC_SP: Independent PC SP;
  }.

 Section core_section.

  Existing Instance offset_action.

  Context {MP1: MachineParams1}.

  Existing Instance independent_MEM_IMAGE.
  Definition independent_IMAGE_MEM := independent_symm independent_MEM_IMAGE.
  Existing Instance independent_IMAGE_MEM.
  Existing Instance independent_MEM_BYTES.
  Definition independent_BYTES_MEM := independent_symm independent_MEM_BYTES.
  Existing Instance independent_BYTES_MEM.
  Existing Instance independent_MEM_CHARS.
  Definition independent_CHARS_MEM := independent_symm independent_MEM_CHARS.
  Existing Instance independent_CHARS_MEM.
  Existing Instance independent_MEM_SOUND.
  Definition independent_SOUND_MEM := independent_symm independent_MEM_SOUND.
  Existing Instance independent_SOUND_MEM.
  Existing Instance independent_MEM_LOG.
  Definition independent_LOG_MEM := independent_symm independent_MEM_LOG.
  Existing Instance independent_LOG_MEM.
  Existing Instance independent_MEM_INP.
  Definition independent_INP_MEM := independent_symm independent_MEM_INP.
  Existing Instance independent_INP_MEM.
  Existing Instance independent_MEM_PC.
  Definition independent_PC_MEM := independent_symm independent_MEM_PC.
  Existing Instance independent_PC_MEM.
  Existing Instance independent_MEM_SP.
  Definition independent_SP_MEM := independent_symm independent_MEM_SP.
  Existing Instance independent_SP_MEM.
  Existing Instance independent_IMAGE_BYTES.
  Definition independent_BYTES_IMAGE := independent_symm independent_IMAGE_BYTES.
  Existing Instance independent_BYTES_IMAGE.
  Existing Instance independent_IMAGE_CHARS.
  Definition independent_CHARS_IMAGE := independent_symm independent_IMAGE_CHARS.
  Existing Instance independent_CHARS_IMAGE.
  Existing Instance independent_IMAGE_SOUND.
  Definition independent_SOUND_IMAGE := independent_symm independent_IMAGE_SOUND.
  Existing Instance independent_SOUND_IMAGE.
  Existing Instance independent_IMAGE_LOG.
  Definition independent_LOG_IMAGE := independent_symm independent_IMAGE_LOG.
  Existing Instance independent_LOG_IMAGE.
  Existing Instance independent_IMAGE_INP.
  Definition independent_INP_IMAGE := independent_symm independent_IMAGE_INP.
  Existing Instance independent_INP_IMAGE.
  Existing Instance independent_IMAGE_PC.
  Definition independent_PC_IMAGE := independent_symm independent_IMAGE_PC.
  Existing Instance independent_PC_IMAGE.
  Existing Instance independent_IMAGE_SP.
  Definition independent_SP_IMAGE := independent_symm independent_IMAGE_SP.
  Existing Instance independent_SP_IMAGE.
  Existing Instance independent_BYTES_CHARS.
  Definition independent_CHARS_BYTES := independent_symm independent_BYTES_CHARS.
  Existing Instance independent_CHARS_BYTES.
  Existing Instance independent_BYTES_SOUND.
  Definition independent_SOUND_BYTES := independent_symm independent_BYTES_SOUND.
  Existing Instance independent_SOUND_BYTES.
  Existing Instance independent_BYTES_LOG.
  Definition independent_LOG_BYTES := independent_symm independent_BYTES_LOG.
  Existing Instance independent_LOG_BYTES.
  Existing Instance independent_BYTES_INP.
  Definition independent_INP_BYTES := independent_symm independent_BYTES_INP.
  Existing Instance independent_INP_BYTES.
  Existing Instance independent_BYTES_PC.
  Definition independent_PC_BYTES := independent_symm independent_BYTES_PC.
  Existing Instance independent_PC_BYTES.
  Existing Instance independent_BYTES_SP.
  Definition independent_SP_BYTES := independent_symm independent_BYTES_SP.
  Existing Instance independent_SP_BYTES.
  Existing Instance independent_CHARS_SOUND.
  Definition independent_SOUND_CHARS := independent_symm independent_CHARS_SOUND.
  Existing Instance independent_SOUND_CHARS.
  Existing Instance independent_CHARS_LOG.
  Definition independent_LOG_CHARS := independent_symm independent_CHARS_LOG.
  Existing Instance independent_LOG_CHARS.
  Existing Instance independent_CHARS_INP.
  Definition independent_INP_CHARS := independent_symm independent_CHARS_INP.
  Existing Instance independent_INP_CHARS.
  Existing Instance independent_CHARS_PC.
  Definition independent_PC_CHARS := independent_symm independent_CHARS_PC.
  Existing Instance independent_PC_CHARS.
  Existing Instance independent_CHARS_SP.
  Definition independent_SP_CHARS := independent_symm independent_CHARS_SP.
  Existing Instance independent_SP_CHARS.
  Existing Instance independent_SOUND_LOG.
  Definition independent_LOG_SOUND := independent_symm independent_SOUND_LOG.
  Existing Instance independent_LOG_SOUND.
  Existing Instance independent_SOUND_INP.
  Definition independent_INP_SOUND := independent_symm independent_SOUND_INP.
  Existing Instance independent_INP_SOUND.
  Existing Instance independent_SOUND_PC.
  Definition independent_PC_SOUND := independent_symm independent_SOUND_PC.
  Existing Instance independent_PC_SOUND.
  Existing Instance independent_SOUND_SP.
  Definition independent_SP_SOUND := independent_symm independent_SOUND_SP.
  Existing Instance independent_SP_SOUND.
  Existing Instance independent_LOG_INP.
  Definition independent_INP_LOG := independent_symm independent_LOG_INP.
  Existing Instance independent_INP_LOG.
  Existing Instance independent_LOG_PC.
  Definition independent_PC_LOG := independent_symm independent_LOG_PC.
  Existing Instance independent_PC_LOG.
  Existing Instance independent_LOG_SP.
  Definition independent_SP_LOG := independent_symm independent_LOG_SP.
  Existing Instance independent_SP_LOG.
  Existing Instance independent_INP_PC.
  Definition independent_PC_INP := independent_symm independent_INP_PC.
  Existing Instance independent_PC_INP.
  Existing Instance independent_INP_SP.
  Definition independent_SP_INP := independent_symm independent_INP_SP.
  Existing Instance independent_SP_INP.
  Existing Instance independent_PC_SP.
  Definition independent_SP_PC := independent_symm independent_PC_SP.
  Existing Instance independent_SP_PC.

  Class MachineParams2 :=
  {
    M: Type -> Type;
    H_mon: SMonad State M;
  }.

  Context {MP2: MachineParams2}.

  Existing Instance H_eqdec.
  Existing Instance H_mon.

  Definition extr {X} (ox: option X) : M X :=
    match ox with
    | Some x => ret x
    | None => err
    end.


  (** ** Memory and stack *)

  Definition load0 (a: Addr): M (option Cell) :=
    assert* available a as H in
    let* s := get' MEM in
    ret (s a H).

  Definition load (a: Addr): M Cell := load0 a >>= extr.
  Proposition load_spec a : load a = load0 a >>= extr.
  Proof. reflexivity. Qed.
  Opaque load.

  Global Instance load_confined a : Confined MEM (load a).
  Proof.
    rewrite load_spec.
    typeclasses eauto.
  Qed.

  Definition store0 (a: Addr) (o: option Cell) : M unit :=
    assert* available a in
    let* s := get' MEM in
    let s' a' H := if decide (a = a') then o else s a' H in
    put' MEM s'.

  Definition store (a: Addr) (x: Cell) : M unit := store0 a (Some x).
  Proposition store_spec a x : store a x = store0 a (Some x).
  Proof. reflexivity. Qed.
  Opaque store.

  Global Instance store_confined a x : Confined MEM (store a x).
  Proof.
    rewrite store_spec.
    typeclasses eauto.
  Qed.

  Open Scope vector.

  (* TODO: noind is used to circumvent what appears to be an Equation bug. *)
  Equations(noind) loadMany (n: nat) (_: Addr): M (Cells n) :=
    loadMany 0 _ := ret [];
    loadMany (S n) a :=
      let* x := load a in
      let* r := loadMany n (offset 1 a) in
      ret (x :: r).

  (* [simp] does not, and [setoid_rewrite] requires unneccessary Addr argument. *)
  Ltac simp_loadMany := rewrite_strat (outermost (hints loadMany)).

  Equations(noind) next (n: nat) : M (Cells n) :=
    next 0 := ret [];
    next (S n) :=
      let* pc := get' PC in
      let* x := load pc in
      put' PC (offset 1 pc);;
      let* r := next n in
      ret (x :: r).

  Lemma next_spec n : next n = let* pc := get' PC in
                               put' PC (offset n pc);;
                               loadMany n pc.
  Proof.
    (* TODO: automate more? *)
    induction n; simp next.
    - simpl (offset _ _).
      setoid_rewrite Z_action_zero.
      simp_loadMany.
      rewrite get_spec, put_spec, (bind_spec PC).
      smon_rewrite.
    - rewrite IHn. clear IHn.
      simp_loadMany.

      (* rewrite (get_spec PC), (put_spec PC), (bind_spec PC). *)
      rewrite get_spec, put_spec, (bind_spec PC).
      smon_rewrite'.
      setoid_rewrite (confined_after_put MEM PC _).

      assert (forall pc, offset n (offset 1 pc) = offset (S n) pc).
      + intros pc. setoid_rewrite <- Z_action_add. f_equal. lia.
      + setoid_rewrite H.
        reflexivity.
  Qed.

  (* Instead of marking the freed stack as undefined here,
     we will express this in the corresponding [Cert]s. *)
  Definition popMany (n: nat): M (Cells n) :=
    let* sp := get' SP in
    let* res := loadMany n sp in
    put' SP (offset n sp);;
    ret res.

  Lemma popMany_equation_0 : popMany 0 = ret [].
  Proof.
    unfold popMany.
    simp_loadMany.
    simpl (offset _ _).
    rewrite_strat (outermost Z_action_zero).
    smon_rewrite.
    rewrite get_spec, put_spec.
    repeat rewrite (bind_spec SP).
    smon_rewrite.
  Qed.

  Lemma popMany_equation_1 n :
    popMany (S n) = let* sp := get' SP in
                    let* x := load sp in
                    let* r := popMany n in
                    ret (x :: r).
  Proof.
    unfold popMany.
    simp_loadMany.
    Opaque load. (* TODO *)
    smon_rewrite.


let* u := popMany m in
                    let* v := popMany n in
                    ret (u ++ v).


  Lemma popMany_equation_2 m n :
    popMany (m + n) = let* u := popMany m in
                      let* v := popMany n in
                      ret (u ++ v).
  Proof.
    induction m.
    - rewrite popMany_equation_1. smon_rewrite.
    - cbn.





let* sp := get' SP in
                      let* x := load sp in
                      put' SP (offset n sp);;
                      ret res.



  Close Scope vector.

  Equations storeMany (_: Addr) (_: list Cell) : M unit :=
    storeMany _ [] := ret tt;
    storeMany a (x :: u) :=
      store a x;;
      storeMany (offset 1 a) u.

  Definition pushMany (u: list Cell): M unit :=
    let* sp := get' SP in
    (* The stack grows downwards. *)
    let a := offset (- List.length u) sp in
    put' SP a;;
    storeMany a u.


  (** ** Input *)

  Local Definition Input := Image InputColor.

  Definition readFrame (i: N) : M (N * N) :=
    put' INP i;;
    let img := nth (N.to_nat i) allInputImages noImage in
    ret (width img, height img).

  Definition readPixel (x y : N) : M InputColor :=
    let* i := get' INP in
    let img := nth (N.to_nat i) allInputImages noImage in
    assert* x < width img as Hx in
    assert* y < height img as Hy in
    ret (pixel img Hx Hy).


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

  Definition setPixel (x y: N) (c: OutputColor) : M unit :=
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
        pixel x Hx y Hy := extract (H_complete x Hx y Hy);
      |}.

  Definition newFrame (w r h: N) : M unit :=
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

 End core_section.
End Core.
