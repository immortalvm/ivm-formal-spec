From Assembly Require Import Basics.

Unset Suggest Proof Using.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Set Implicit Arguments.


(** ** [Z]-actions *)

Local Open Scope Z.

Class Z_action {X} (f: Z -> X -> X) : Prop :=
{
  Z_action_zero x : f 0 x = x;
  Z_action_add z z' x : f (z + z') x = f z' (f z x);
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

Close Scope N.
Local Notation "0" := 0%nat.


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
  Existing Instance independent_MEM_BYTES.
  Existing Instance independent_MEM_CHARS.
  Existing Instance independent_MEM_SOUND.
  Existing Instance independent_MEM_LOG.
  Existing Instance independent_MEM_INP.
  Existing Instance independent_MEM_PC.
  Existing Instance independent_MEM_SP.
  Existing Instance independent_IMAGE_BYTES.
  Existing Instance independent_IMAGE_CHARS.
  Existing Instance independent_IMAGE_SOUND.
  Existing Instance independent_IMAGE_LOG.
  Existing Instance independent_IMAGE_INP.
  Existing Instance independent_IMAGE_PC.
  Existing Instance independent_IMAGE_SP.
  Existing Instance independent_BYTES_CHARS.
  Existing Instance independent_BYTES_SOUND.
  Existing Instance independent_BYTES_LOG.
  Existing Instance independent_BYTES_INP.
  Existing Instance independent_BYTES_PC.
  Existing Instance independent_BYTES_SP.
  Existing Instance independent_CHARS_SOUND.
  Existing Instance independent_CHARS_LOG.
  Existing Instance independent_CHARS_INP.
  Existing Instance independent_CHARS_PC.
  Existing Instance independent_CHARS_SP.
  Existing Instance independent_SOUND_LOG.
  Existing Instance independent_SOUND_INP.
  Existing Instance independent_SOUND_PC.
  Existing Instance independent_SOUND_SP.
  Existing Instance independent_LOG_INP.
  Existing Instance independent_LOG_PC.
  Existing Instance independent_LOG_SP.
  Existing Instance independent_INP_PC.
  Existing Instance independent_INP_SP.
  Existing Instance independent_PC_SP.

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


  (** ** [load] and [store] *)

  Definition load0 (a: Addr): M (option Cell) :=
    assert* available a as H in
    let* s := get' MEM in
    ret (s a H).

  Definition load (a: Addr): M Cell := load0 a >>= extr.
  Definition load_spec := ltac:(spec_tac load).
  Global Opaque load.

  Global Instance confined_load {a} : Confined MEM (load a).
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
  Definition store_spec := ltac:(spec_tac store).
  Global Opaque store.

  Global Instance confined_store a x : Confined MEM (store a x).
  Proof.
    rewrite store_spec.
    typeclasses eauto.
  Qed.

  Lemma store_load a x {Y} (f: unit -> Cell -> M Y) : let* u := store a x in
                                                 let* x' := load a in
                                                 f u x' = store a x;;
                                                          f tt x.
  Proof.
    rewrite store_spec, load_spec.
    smon_rewrite.
    destruct (decide (available a)) as [Ha|Ha]; smon_rewrite.
    decided Ha. smon_rewrite.
    decided (@eq_refl _ a). smon_rewrite.
  Qed.

  Lemma store_store a a' x x' Y (H: a <> a') (f: unit -> unit -> M Y) :
    let* u := store a x in
    let* v := store a' x' in
    f u v = let* v := store a' x' in
            let* u := store a x in
            f u v.
  Proof.
    rewrite store_spec.
    unfold store0.
    smon_rewrite.
    destruct (decide (available a)) as [Ha|Ha];
      destruct (decide (available a')) as [Ha'|Ha'];
      smon_rewrite.
    apply bind_extensional. intros mem.
    f_equal.
    f_equal.
    extensionality a''.
    extensionality Ha''.
    destruct (decide (a=a'')) as [HH|HH];
      destruct (decide (a'=a'')) as [HH'|HH'];
      congruence.
  Qed.


  (** ** [loadMany] and [next] *)

  Open Scope vector.

  (* TODO: noind is used to circumvent what appears to be an Equation bug. *)
  Equations(noind) loadMany (n: nat) (_: Addr): M (Cells n) :=
    loadMany 0 _ := ret [];
    loadMany (S n) a :=
      let* x := load a in
      let* r := loadMany n (offset 1 a) in
      ret (x :: r).

  Global Instance confined_loadMany n a : Confined MEM (loadMany n a).
  Proof.
    revert a.
    induction n;
      intros a;
      simp loadMany;
      typeclasses eauto.
  Qed.

  (** [simp] does not work,
      and [setoid_rewrite] requires unneccessary Addr argument. *)
  Ltac simp_loadMany := rewrite_strat (outermost (hints loadMany)).

  Equations(noind) next (n: nat) : M (Cells n) :=
    next 0 := ret [];
    next (S n) :=
      let* pc := get' PC in
      let* x := load pc in
      put' PC (offset 1 pc);;
      let* r := next n in
      ret (x :: r).

  Proposition offset_inc (n: nat) a : offset n (offset 1 a) = offset (S n) a.
  Proof.
    setoid_rewrite <- Z_action_add.
    f_equal.
    lia.
  Qed.

  Lemma next_alt n : next n = let* pc := get' PC in
                              put' PC (offset n pc);;
                              loadMany n pc.
  Proof.
    induction n; simp next.
    - simpl (offset _ _).
      setoid_rewrite Z_action_zero.
      simp_loadMany.
      smon_rewrite.
    - rewrite IHn. clear IHn.
      simp_loadMany.
      smon_rewrite.
      assert (forall x, Neutral MEM (put' PC (offset 1 x))) as H.
      + typeclasses eauto.
      + setoid_rewrite offset_inc.
        setoid_rewrite (confined_load (neutral_put _ _ _)).
        reflexivity.
  Qed.

  Global Instance confined_next n : Confined (MEM * PC) (next n).
  Proof.
    rewrite next_alt.
    typeclasses eauto.
  Qed.


  (** *** POP *)

  (** Pop a single cell. Later we will always pop multiple cells at once. *)
  Definition pop : M Cell :=
    let* sp := get' SP in
    put' SP (offset 1 sp);;
    load sp.

  Proposition pop_alt : pop = let* sp := get' SP in
                              put' SP (offset 1 sp);;
                              load sp.
  Proof. reflexivity. Qed.

  Opaque pop.

  (** Instead of marking the freed stack as undefined here,
      we will express this later in the corresponding [Cert]s. *)
  Equations(noind) popMany (n: nat): M (Cells n) :=
    popMany 0 := ret [];
    popMany (S n) := let* x := pop in
                     let* r := popMany n in
                     ret (x :: r).

  (* TODO: Useful? *)
  Proposition popMany_action m n :
    popMany (m + n) = let* u := popMany m in
                      let* v := popMany n in
                      ret (u ++ v).
  Proof.
    induction m.
    - simp popMany. smon_rewrite.
    - cbn. simp popMany.
      rewrite IHm. clear IHm.
      smon_rewrite.
  Qed.

  Lemma popMany_alt n : popMany n = let* sp := get' SP in
                                     let* res := loadMany n sp in
                                     put' SP (offset n sp);;
                                     ret res.
  Proof.
    induction n; simp popMany; simp_loadMany.
    - smon_rewrite.
      setoid_rewrite Z_action_zero.
      smon_rewrite.
    - rewrite IHn. clear IHn.
      rewrite pop_alt.
      smon_rewrite.
      setoid_rewrite (confined_load (neutral_put _ _ _)).
      smon_rewrite.
      setoid_rewrite offset_inc.
      setoid_rewrite <- (confined_loadMany _ (neutral_put _ _ _)).
      smon_rewrite.
  Qed.

  Global Instance confined_popMany n : Confined (MEM * SP) (popMany n).
  Proof.
    rewrite popMany_alt.
    typeclasses eauto.
  Qed.

  Close Scope vector.


  (** ** [storeMany] *)

  Equations storeMany (_: Addr) (_: list Cell) : M unit :=
    storeMany _ [] := ret tt;
    storeMany a (x :: u) :=
      store a x;;
      storeMany (offset 1 a) u.

  (** Cf. [simp_loadMany] *)
  Ltac simp_storeMany := rewrite_strat (outermost (hints storeMany)).

  Proposition storeMany_one a x : storeMany a [x] = store a x.
  Proof.
    simp storeMany. smon_rewrite.
  Qed.

  Lemma storeMany_action a u v : storeMany a (u ++ v) =
                                 storeMany a u;; storeMany (offset (length u) a) v.
  Proof.
    revert a.
    induction u as [|x u IH]; intros a.
    - cbn. simp storeMany. rewrite Z_action_zero. smon_rewrite.
    - simpl length.
      simpl app.
      simp storeMany.
      rewrite IH. clear IH.
      smon_rewrite.
      setoid_rewrite <- Z_action_add.
      lia_rewrite (1 + length u = S (length u))%Z.
      reflexivity.
  Qed.

  Global Instance confined_storeMany a u : Confined MEM (storeMany a u).
  Proof.
    revert a.
    induction u as [|x u IH];
      intros a;
      simp storeMany;
      typeclasses eauto.
  Qed.

  Definition addressable (n: nat) :=
    forall a i, 0 < i < n -> offset i a <> a.

  Proposition addressable_mono {n} (Hn: addressable n) {m: nat} (Hmn: m <= n):
    addressable m.
  Proof.
    unfold addressable in *.
    intros. apply Hn. lia.
  Qed.

  Lemma storeMany_rev a x u :
    storeMany a (rev (x :: u)) = storeMany a (rev u);;
                                store (offset (length u) a) x.
  Proof.
    induction u as [|y u IH];
      simpl rev;
      simpl length;
      simp storeMany;
      smon_rewrite.
    - rewrite Z_action_zero. reflexivity.
    - repeat setoid_rewrite storeMany_action.
      smon_rewrite.
      setoid_rewrite storeMany_one.
      setoid_rewrite app_length.
      simpl length.
      setoid_rewrite rev_length.
      lia_rewrite (length u + 1 = S (length u))%nat.
      reflexivity.
  Qed.

  Lemma storeMany_equation_2' a x u (H: addressable (S (length u))) :
    storeMany a (x :: u) = storeMany (offset 1 a) u;;
                          store a x.
  Proof.
    rewrite <- (rev_involutive u).
    rewrite <- (rev_length u) in H.
    revert H.
    generalize (rev u). clear u. intros u H.
    simp storeMany.

    revert a x.
    induction u as [|y u IH]; intros a x; simp storeMany; smon_rewrite.
    simpl length in H.
    assert (addressable (S (length u))) as HH.
    - eapply (addressable_mono H). lia.
    - specialize (IH HH). clear HH.
      rewrite storeMany_rev.
      setoid_rewrite <- bind_assoc.
      setoid_rewrite IH.
      smon_rewrite.
      apply bind_extensional. intros [].
      setoid_rewrite <- bind_ret_tt.
      setoid_rewrite bind_assoc.
      rewrite store_store.
      + reflexivity.
      + apply not_eq_sym.
        rewrite <- Z_action_add.
        unfold addressable in H.
        apply (H a (1 + length u)).
        lia.
  Qed.

  Lemma storeMany_action' a u v (H: addressable (length u + length v)) :
    storeMany a (u ++ v) =
    storeMany (offset (length u) a) v;; storeMany a u.
  Proof.
    revert a.
    induction u as [|x u IH]; intros a.
    - cbn. rewrite Z_action_zero. simp storeMany. smon_rewrite.
    - simpl (_ ++ _).
      setoid_rewrite storeMany_equation_2'.
      rewrite IH.
      rewrite offset_inc.
      simpl length.
      smon_rewrite.
      all: eapply (addressable_mono H); try rewrite app_length; try simpl length; lia.
  Qed.

  Lemma storeMany_loadMany a n (u: Cells n) :
    addressable n -> storeMany a (to_list u);;
                    loadMany n a = storeMany a (to_list u);;
                                   ret u.
  Proof.
    revert a; induction n; intros a.
    - intros _. dependent elimination u. cbn.
      simp storeMany loadMany. smon_rewrite.
    - intros H. dependent elimination u as [Vector.cons (n:=n) x u]. simp to_list.
      rewrite storeMany_equation_2' at 1.
      + simp loadMany.
        smon_rewrite.
        rewrite store_load.
        rewrite <- bind_assoc.
        setoid_rewrite <- storeMany_equation_2'.
        * simp storeMany.
          smon_rewrite.
          apply bind_extensional. intros [].
          rewrite <- bind_assoc.
          rewrite IHn.
          -- smon_rewrite.
          -- apply (addressable_mono H). lia.
        * apply (addressable_mono H). rewrite length_to_list. lia.
      + apply (addressable_mono H). rewrite length_to_list. lia.
  Qed.

  Corollary storeMany_loadMany' a n (u: Cells n) {Y} (f: unit -> Cells n -> M Y) :
    addressable n -> let* x := storeMany a (to_list u) in
                    let* v := loadMany n a in
                    f x v = storeMany a (to_list u);;
                            f tt u.
  Proof.
    intros H.
    smon_rewrite.
    rewrite <- bind_assoc.
    rewrite storeMany_loadMany.
    - smon_rewrite.
    - exact H.
  Qed.


  (** ** [push] and [pushMany] *)

  (** Push a single cell *)
  Definition push (x: Cell) : M unit :=
    let* sp := get' SP in
    let a := offset (- 1) sp in
    put' SP a;;
    store a x.
  Definition push_spec := ltac:(spec_tac push).
  Global Opaque push.

  (** NB: Stores the elements in reversed order. *)
  Equations(noind) pushManyR (u: list Cell): M unit :=
    pushManyR [] := ret tt;
    pushManyR (x :: u) := push x;;
                         pushManyR u.

 Lemma pushManyR_action u v : pushManyR (u ++ v) = pushManyR u;; pushManyR v.
  Proof.
    revert v.
    induction u as [|x u IH];
      intros v;
      cbn;
      simp pushManyR;
      smon_rewrite.
    rewrite IH.
    reflexivity.
  Qed.

  (** Stores the elements correct order. *)
  Definition pushMany u := pushManyR (rev u).

  Corollary pushMany_action u v : pushMany (u ++ v) = pushMany v;; pushMany u.
  Proof.
    unfold pushMany.
    rewrite rev_app_distr.
    apply pushManyR_action.
  Qed.

  Lemma pushMany_alt u (H: addressable (length u)) :
    pushMany u = let* sp := get' SP in
                 let a := offset (- List.length u) sp in
                 put' SP a;;
                 storeMany a u.
  Proof.
    (* TODO: AUTOMATE! *)
    induction u as [|x u IH].
    - unfold pushMany. cbn.
      setoid_rewrite Z_action_zero.
      simp pushManyR.
      simp_storeMany.
      smon_rewrite.

    - change (x :: u) with ([x] ++ u).
      rewrite pushMany_action.
      smon_rewrite.
      set (f := offset (- length ([x] ++ u))).
      rewrite IH.
      + unfold pushMany.
        simpl rev.
        simp pushManyR.
        rewrite push_spec.
        smon_rewrite.
        apply bind_extensional. intros sp.

        setoid_rewrite <- (confined_storeMany _ _ (neutral_get _ _)).
        setoid_rewrite <- (confined_storeMany _ _ (neutral_put _ _ _)).
        smon_rewrite.
        setoid_rewrite <- Z_action_add.

        subst f.
        apply bind_extensional'.
        * f_equal. f_equal. cbn. lia.
        * intros [].
          setoid_rewrite (storeMany_action' _ [x] u).
          -- simp storeMany.
             smon_rewrite.
             apply bind_extensional'.
             ++ f_equal. rewrite <- Z_action_add.
                f_equal. rewrite app_length.
                simpl length. lia.
             ++ intros [].
                f_equal.
                f_equal.
                rewrite app_length.
                simpl length.
                lia.
          -- apply (addressable_mono H). simpl length. lia.
      + apply (addressable_mono H). simpl length. lia.
  Qed.


  (** ** Input *)

  Local Open Scope N.

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
