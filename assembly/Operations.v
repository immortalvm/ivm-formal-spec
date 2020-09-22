From Assembly Require Export Restr Mon.
From Assembly Require Import DSet.
Import DSetNotations.

Unset Suggest Proof Using.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.


(** ** Images *)

Local Open Scope N.

Record Image (C: Type) :=
  mkImage {
      width: N;
      height: N;
      pixel (x: N) (Hx: x < width) (y: N) (Hy: y < height): C;
    }.

Arguments width {_} _.
Arguments height {_} _.
Arguments pixel {_} _ {_} Hx {_} Hy.

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


(** ** [Z]-actions *)

Local Open Scope Z.

Class Z_action {X} (f: Z -> X -> X) : Prop :=
{
  Z_action_zero x : f 0 x = x;
  Z_action_add z z' x : f (z + z') x = f z' (f z x);
}.

Local Notation "0" := 0%nat.


(** ** Machine parameters

Abstractions makes working with Coq much easier. *)

Module Type MachineParameters.
  Parameter Inline Addr: Type.
  Parameter Inline H_eqdec: EqDec Addr.
  Parameter Inline available: Addr -> bool.
  Parameter Inline offset: Z -> Addr -> Addr.
  Declare Instance offset_action: Z_action offset.
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

  Context {MP1: MachineParams1}.

  Global Existing Instance independent_MEM_IMAGE.
  Global Existing Instance independent_MEM_BYTES.
  Global Existing Instance independent_MEM_CHARS.
  Global Existing Instance independent_MEM_SOUND.
  Global Existing Instance independent_MEM_LOG.
  Global Existing Instance independent_MEM_INP.
  Global Existing Instance independent_MEM_PC.
  Global Existing Instance independent_MEM_SP.
  Global Existing Instance independent_IMAGE_BYTES.
  Global Existing Instance independent_IMAGE_CHARS.
  Global Existing Instance independent_IMAGE_SOUND.
  Global Existing Instance independent_IMAGE_LOG.
  Global Existing Instance independent_IMAGE_INP.
  Global Existing Instance independent_IMAGE_PC.
  Global Existing Instance independent_IMAGE_SP.
  Global Existing Instance independent_BYTES_CHARS.
  Global Existing Instance independent_BYTES_SOUND.
  Global Existing Instance independent_BYTES_LOG.
  Global Existing Instance independent_BYTES_INP.
  Global Existing Instance independent_BYTES_PC.
  Global Existing Instance independent_BYTES_SP.
  Global Existing Instance independent_CHARS_SOUND.
  Global Existing Instance independent_CHARS_LOG.
  Global Existing Instance independent_CHARS_INP.
  Global Existing Instance independent_CHARS_PC.
  Global Existing Instance independent_CHARS_SP.
  Global Existing Instance independent_SOUND_LOG.
  Global Existing Instance independent_SOUND_INP.
  Global Existing Instance independent_SOUND_PC.
  Global Existing Instance independent_SOUND_SP.
  Global Existing Instance independent_LOG_INP.
  Global Existing Instance independent_LOG_PC.
  Global Existing Instance independent_LOG_SP.
  Global Existing Instance independent_INP_PC.
  Global Existing Instance independent_INP_SP.
  Global Existing Instance independent_PC_SP.

  Class MachineParams2 :=
  {
    M: Type -> Type;
    H_mon: SMonad State M;
  }.

  Context {MP2: MachineParams2}.

  Existing Instance H_eqdec.
  Global Existing Instance H_mon.

  Notation "⫫" := (@fstMixer State).


  (** *** Addressable  *)

  (** The address space may consist of multiple disjoint pieces. The
      following predicate states that each piece consists of at least [n]
      distinct addresses. *)
  Definition addressable (n: nat) : Prop :=
    forall a i, 0 < i < n -> offset i a <> a.

  Proposition addressable_neg {n} (Hn: addressable n) :
    forall a i, 0 < i < n -> offset (-i) a <> a.
  Proof.
    intros a i Hi H.
    apply (Hn a i Hi).
    rewrite <- H at 1.
    rewrite <- Z_action_add.
    lia_rewrite (-i + i = 0%Z).
    apply Z_action_zero.
  Qed.

  Proposition addressable_le {n} (Hn: addressable n) {m: nat} (Hm: m <= n):
    addressable m.
  Proof.
    unfold addressable in *.
    intros. apply Hn. lia.
  Qed.

  Ltac addressable_tac :=
    try match goal with
        | H : addressable ?n |- addressable ?m =>
          apply (addressable_le H (m:=m));
          repeat (simpl length
                  || rewrite app_length
                  || rewrite rev_length);
          repeat rewrite length_to_list;
          try lia
        end.


  (** *** Decidable subsets of the memory *)

  Instance MEM' u : Lens State (restr u) :=
    (restrLens u) ∘ MEM.



  (* TODO: Move to Lens.v (replacing useless variant) *)
  Hint Extern 2 (@Submixer _ (@lens2mixer _ _ (@compositeLens _ _ _ ?Ly ?Lx))
                           (@lens2mixer _ _ ?Lx)) =>
      apply sublens_comp' : typeclass_instances.

  Global Instance subset_mem u : (MEM' u | MEM).
  Proof.
    unfold MEM'. typeclasses eauto.
  Qed.

  Global Instance itest u f `((MEM | f)) : (MEM' u | f).
  Proof.
    transitivity MEM; typeclasses eauto.
  Qed.

  Instance MEM'' a : Lens State (available a -> option Cell) :=
    (pointLens a) ∘ MEM.

  Instance point_mem {a} : (MEM'' a | MEM).
  Proof.
    unfold MEM''. typeclasses eauto.
  Qed.

  Global Instance point_mem' {a u} (Hau: a ∈ u) : (MEM'' a | MEM' u).
  Proof.
    unfold MEM'', MEM'.
    apply sublens_comp.
    refine (pointLens_sublens Hau).
  Qed.

  Global Instance point_mem'' {a} : (MEM'' a | MEM' !{a}) :=
    point_mem' DSet.refl.

  Global Instance point_independent {a a'} (H:a<>a') :
    Independent (MEM'' a) (MEM'' a').
  Proof.
    unfold MEM''.
    apply composite_independent_r.
    refine (pointLens_independent H).
  Qed.


  (** *** Extract the boxed element from an [option] type or fail. *)

  (* TODO: Move to Mon.v ? *)
  Definition extr {X} (ox: option X) : M X :=
    match ox with
    | Some x => ret x
    | None => err
    end.
  Definition extr_spec := unfolded_eq (@extr).

  Global Instance confined_extr
         {X} (ox: option X) : Confined ⫫ (extr ox).
  Proof.
    typeclasses eauto.
  Qed.

  Global Opaque extr.


  (** ** [load] and [store] *)

  (** *** [load] *)

  Definition load (a: Addr): M Cell :=
    assert* available a as Ha in
    let* c := get' (MEM'' a) in
    extr (c Ha).

  Definition load_spec'' := unfolded_eq load.

  Proposition load_spec a :
    load a = assert* available a as Ha in
             let* mem := get' MEM in
             extr (mem a Ha).
  Proof.
    unfold load.
    destruct (decide (available a)) as [Ha|_];
      [ | reflexivity ].
    repeat rewrite get_spec.
    smon_rewrite.
  Qed.

  (* TODO: Move to Mon.v ? *)
  (** A (hopefully) safe way to express that [Confined] is closed under submixers. *)
  Ltac confined_tac' m t :=
    assert_fails (is_evar m);
    let Hconf := fresh "Hconf" in
    let f := fresh "fConf" in
    evar (f: Mixer State);
    assert (Confined f t) as Hconf;
    [ subst f; typeclasses eauto
    | eapply (confined_sub f _); typeclasses eauto ].
  Ltac confined_tac := match goal with
                         |- Confined ?m ?t => confined_tac' m t
                       end.
  Hint Extern 10 (Confined ?m ?t) =>
    confined_tac' m t : typeclass_instances.

  Global Instance confined_load {a} : Confined (MEM'' a) (load a).
  Proof. typeclasses eauto. Qed.

  Opaque load.


  (** *** [store] *)

  Definition store (a: Addr) (x: Cell) : M unit :=
    assert* available a in
    put' (MEM'' a) (fun _ => Some x).

  Definition store_spec'' := unfolded_eq store.

  Proposition store_spec a x :
    store a x = assert* available a in
                let* s := get' MEM in
                let s' a' H := if decide (a = a') then Some x else s a' H in
                put' MEM s'.
  Proof.
    unfold store.
    repeat rewrite get_spec.
    repeat rewrite put_spec.
    destruct (decide (available a)) as [Ha|_];
      [ | reflexivity ].
    smon_rewrite.
    apply bind_extensional. intro s.
    f_equal. cbn. unfold compose. f_equal.
    extensionality a'.
    destruct (decide (a = a')) as [[]|_];
      reflexivity.
  Qed.

  (* TODO: [unfold compose] is annoying. Use notation instead? *)

  Global Instance confined_store a x : Confined (MEM'' a) (store a x).
  Proof.
    typeclasses eauto.
  Qed.

  Opaque store.

  (** *** Reordering load and store operations *)

  Lemma store_load a x {Y} (f: unit -> Cell -> M Y) : let* u := store a x in
                                                 let* x' := load a in
                                                 f u x' = store a x;;
                                                          f tt x.
  Proof.
    rewrite
      store_spec'', load_spec'',
      extr_spec.
    smon_rewrite.
    destruct (decide (available a)) as [Ha|_];
      smon_rewrite;
      smon_rewrite. (* TODO: This should not be necessary! *)
  Qed.

  Lemma store_store a a' x x' Y (H: a <> a') (f: unit -> unit -> M Y) :
    let* u := store a x in
    let* v := store a' x' in
    f u v = let* v := store a' x' in
            let* u := store a x in
            f u v.
  Proof.
    rewrite store_spec''.
    destruct (decide (available a)) as [Ha|_];
      destruct (decide (available a')) as [Ha'|_];
      smon_rewrite.
    rewrite <- flip_put_put.
    - reflexivity.
    - apply (point_independent H).
  Qed.


  (** ** [loadMany] and [next] *)

  Open Scope vector.

  Proposition offset_inc (n: nat) a : offset n (offset 1 a) = offset (S n) a.
  Proof.
    setoid_rewrite <- Z_action_add.
    f_equal. lia.
  Qed.

  Definition nAfter (n: nat) (a: Addr) : DSet Addr :=
    def (fun a' => exists i, (i<n)%nat /\ offset i a = a').

  Proposition nAfter_zero n a : a ∈ nAfter (S n) a.
  Proof.
    apply def_spec. exists 0. split.
    - lia.
    - apply Z_action_zero.
  Qed.

  (* TODO: Repeat after section if necessary. *)
  Hint Extern 3 (_ ∈ nAfter _ _) => rapply nAfter_zero : typeclass_instances.

  Proposition nAfter_succ n a : nAfter n (offset 1 a) ⊆ nAfter (S n) a.
  Proof.
    unfold subset.
    intros a'.
    unfold nAfter.
    setoid_rewrite def_spec.
    intros [i [Hi Ho]].
    exists (S i).
    split.
    - lia.
    - rewrite <- offset_inc. exact Ho.
  Qed.

  Hint Extern 3 (_ ⊆ nAfter _ _) => rapply nAfter_succ : typeclass_instances.

  Definition nBefore n a := nAfter n (offset (-n) a).

  (* TODO: noind is used to circumvent what appears to be an Equation bug. *)
  Equations(noind) loadMany (n: nat) (_: Addr): M (Cells n) :=
    loadMany 0 _ := ret [];
    loadMany (S n) a :=
      let* x := load a in
      let* r := loadMany n (offset 1 a) in
      ret (x :: r).

  Global Instance subset_mem' {u v} {Huv: u ⊆ v} : (MEM' u | MEM' v).
  Proof.
    apply sublens_comp, submixer_subset.
    exact Huv.
  Qed.

  Global Instance confined_loadMany n a : Confined (MEM' (nAfter n a)) (loadMany n a).
  Proof.
    revert a.
    induction n;
      intros a;
      simp loadMany.
    - typeclasses eauto.
    - specialize (IHn (offset 1 a)).
      typeclasses eauto.
  Qed.

  (** [simp] does not work under binders (yet), and (for some reason)
      [setoid_rewrite] requires an unneccessary Addr argument. *)
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
    induction n; simp next.
    - simpl (offset _ _).
      setoid_rewrite Z_action_zero.
      simp_loadMany.
      smon_rewrite.
    - rewrite IHn. clear IHn.
      simp_loadMany.
      smon_rewrite.
      setoid_rewrite offset_inc.
      setoid_rewrite (confined_load _ _ _ _).
      reflexivity.
  Qed.

  Global Instance confined_next n : Confined (MEM * PC) (next n).
  Proof.
    rewrite next_spec.
    typeclasses eauto.
  Qed.

  (* TODO: Does this have a useful form? *)
  Global Instance confined_next' a n :
    Confined (MEM' (nAfter n a) * PC)
             (put' PC a;; next n).
  Proof.
    rewrite next_spec. smon_rewrite.
    typeclasses eauto.
  Qed.


  (** *** POP *)

  (** Pop a single cell. Later we will always pop multiple cells at once.
      Instead of marking the freed stack as undefined here, we will
      express this later in the corresponding [Cert]s. *)
  Definition pop : M Cell :=
    let* sp := get' SP in
    put' SP (offset 1 sp);;
    load sp.
  Definition pop_spec := unfolded_eq (pop).

  Global Instance confined_pop : Confined (MEM * SP) pop.
  Proof.
    apply confined_bind.
    typeclasses eauto.
    intros x.
    apply confined_bind.
    typeclasses eauto.
    intros [].
    typeclasses eauto.

  Qed.

  Global Instance confined_pop' sp :
    Confined (MEM'' sp * SP) (put' SP sp;;
                              pop).
  Proof.
    smon_rewrite.
    typeclasses eauto.
  Qed.

  Global Opaque pop.

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

  Lemma popMany_spec n : popMany n = let* sp := get' SP in
                                     put' SP (offset n sp);;
                                     loadMany n sp.
  Proof.
    induction n; simp popMany; simp_loadMany.
    - smon_rewrite.
      setoid_rewrite Z_action_zero.
      smon_rewrite.
    - rewrite IHn. clear IHn.
      rewrite pop_spec.
      smon_rewrite.
      setoid_rewrite (confined_load _ _ _ _).
      smon_rewrite.
      setoid_rewrite offset_inc.
      smon_rewrite.
  Qed.

  Global Instance confined_popMany n : Confined (MEM * SP) (popMany n).
  Proof.
    rewrite popMany_spec.
    typeclasses eauto.
  Qed.

  Global Instance confined_popMany' sp n :
    Confined (MEM' (nAfter n sp) * SP) (put' SP sp;;
                                        popMany n).
  Proof.
    rewrite popMany_spec.
    smon_rewrite.
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

  Lemma storeMany_action a u v :
    storeMany a (u ++ v) = storeMany a u;;
                           storeMany (offset (length u) a) v.
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
      lia_rewrite (1 + length u = S (length u)).
      reflexivity.
  Qed.

  Global Instance confined_storeMany a u :
    Confined (MEM' (nAfter (length u) a))
             (storeMany a u).
  Proof.
    (* TODO: Very similar to the proof of [confined_loadMany].*)
    revert a.
    induction u as [|x u IH];
      intros a;
      simp storeMany.
    - typeclasses eauto.
    - simpl length.
      apply confined_bind.
      + unshelve eapply confined_sublens, confined_store.
        apply sublens_comp.
        refine (pointLens_sublens (nAfter_zero (length u) a)).
      + intros [].
        eapply confined_sublens.
        apply IH.
        Unshelve.
        apply sublens_comp, subsetSublens, nAfter_succ.
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
    induction u as [|y u IH];
      intros a x;
      simp storeMany;
      smon_rewrite.

    cbn in H.
    rewrite storeMany_rev.
    setoid_rewrite <- bind_assoc.
    setoid_rewrite IH; [ | addressable_tac ].

    smon_rewrite.
    apply bind_extensional. intros [].
    setoid_rewrite <- bind_ret_tt.
    setoid_rewrite bind_assoc.
    rewrite store_store.
    - reflexivity.
    - apply not_eq_sym.
      rewrite <- Z_action_add.
      apply H.
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
      all: addressable_tac.
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
      rewrite storeMany_equation_2' at 1; [|addressable_tac].
      simp loadMany.
      smon_rewrite.
      rewrite store_load.
      rewrite <- bind_assoc.
      setoid_rewrite <- storeMany_equation_2'; [|addressable_tac].
      simp storeMany.
      smon_rewrite.
      apply bind_extensional. intros [].
      rewrite <- bind_assoc.
      rewrite IHn; [|addressable_tac].
      smon_rewrite.
  Qed.

  (* TODO: Prove this directly (and skip the lemma). *)
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
  Definition push_spec := unfolded_eq (push).

  Global Instance confined_push x : Confined (MEM * SP) (push x).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance confined_push' sp x :
    Confined (MEM'' (offset (-1) sp) * SP) (put' SP sp;;
                                            push x).
  Proof.
    smon_rewrite.
    typeclasses eauto.
  Qed.

  Global Opaque push.

  (** NB: Stores the elements in reversed order. *)
  Equations(noind) pushManyR (u: list Cell): M unit :=
    pushManyR [] := ret tt;
    pushManyR (x :: u) := push x;;
                         pushManyR u.

  Global Instance confined_pushManyR u :
    Confined (MEM * SP) (pushManyR u).
  Proof.
    induction u;
      simp pushManyR;
      typeclasses eauto.
  Qed.

  Proposition nBefore_zero n a : offset (-1) a ∈ nBefore (S n) a.
  Proof.
    unfold nBefore, nAfter.
    rewrite def_spec, bounded_ex_succ.
    left. setoid_rewrite <- Z_action_add.
    f_equal. lia.
  Qed.

  Proposition nBefore_succ n a : nBefore n (offset (-1) a) ⊆ nBefore (S n) a.
  Proof.
    unfold nBefore, nAfter.
    intros a'.
    repeat rewrite def_spec.
    repeat setoid_rewrite <- Z_action_add.
    rewrite bounded_ex_succ.
    lia_rewrite (forall i, -1 + (- n + i) = - S n + i).
    intros H. right. exact H.
  Qed.


  (***************)

  (* TODO: Move *)
  Global Instance sublens_prod_r
         {A X Y Z} (Lx: Lens A X) (Ly: Lens A Y) (Lz: Lens A Z)
         (Sxy: (Lx | Ly))
         (Ixz: Independent Lx Lz)
         (Iyz: Independent Ly Lz) : (Lx * Lz | Ly * Lz).
  Proof.
    destruct Sxy as [Lyx Hx].
    unshelve rewrite (prodLens_proper Hx).
    - reflexivity.
    - set (HH := prodLens_proper (@lens_refl _ _ (Lyx ∘ Ly)) (idLens_composite Lz) ).
      setoid_rewrite <- HH.

rewrite <- (idLens_composite Lz).


      apply prodSublens1'.


typeclasses eauto.


rewrite <- (compositeLens_associative Lz Ly Lyx).
    exact Lx.

    apply sublens_proper.
    rewrite Hx.
    intros xz.

  Global Instance confined_pushManyR' sp u :
    Confined (MEM' (nBefore (length u) sp) * SP) (put' SP sp;;
                                                  pushManyR u).
  Proof.
    revert sp.
    induction u as [|x r IH];
      simp pushManyR;
      [ typeclasses eauto | ].
    intros sp. simpl length. rewrite push_spec. smon_rewrite.
    setoid_rewrite (confined_store _ _ _ _ _).
    apply confined_bind.
    - apply confined_sublens.
      eapply confined_sublens.
      apply confined_store.
      Unshelve.
      apply sublens_comp.
      refine (pointLens_sublens (nBefore_zero _ sp)).
    - intros [].
      assert ( MEM' (nBefore (length r) sp) * SP
             | MEM' (nBefore (S (length r)) sp) * SP ) as H.
      +




      eapply (confined_sublens.
      apply IH.
      Unshelve.
      apply sublens_comp, subsetSublens, nAfter_succ.


      Opaque Confined.
      unfold MEM'.
      eapply (confined_sublens (Sab:=pointLens_sublens _)).


      typeclasses eauto.



typeclasses eauto.

    assert (put' SP sp;;
            push a;;
            pushManyR u = put' SP sp;;
                          push a;;
                          put' SP sp;;
                          pushManyR u).
      - setoid_rewrite <- (confined_push).


        smon_rewrite | ].



    rewrite nBefore_succ.




    typeclasses eauto.

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
      rewrite IH; [|addressable_tac].
      unfold pushMany.
      simpl rev.
      simp pushManyR.
      rewrite push_spec.
      smon_rewrite.
      apply bind_extensional. intros sp.

      setoid_rewrite <- (confined_storeMany _ _ _).
      setoid_rewrite <- (confined_storeMany _ _ _).
      smon_rewrite.
      setoid_rewrite <- Z_action_add.

      subst f.
      apply bind_extensional'.
      + f_equal. f_equal. cbn. lia.
      + intros [].
        setoid_rewrite (storeMany_action' _ [x] u); [|addressable_tac].
        simp storeMany.
        smon_rewrite.
        apply bind_extensional'.
        * f_equal. rewrite <- Z_action_add.
          f_equal. rewrite app_length.
          simpl length. lia.
        * intros [].
          f_equal.
          f_equal.
          rewrite app_length.
          simpl length.
          lia.
  Qed.

  Close Scope Z. (* Back to N for the rest of this file. *)


  (** ** Input *)

  Local Definition Input := Image InputColor.

  Definition readFrame (i: N) : M (N * N) :=
    put' INP i;;
    let img := nth (N.to_nat i) allInputImages noImage in
    ret (width img, height img).

  Definition readFrame_spec := unfolded_eq (readFrame).

  Global Opaque readFrame.

  Global Instance confined_readFrame i : Confined INP (readFrame i).
  Proof.
    rewrite readFrame_spec.
    typeclasses eauto.
  Qed.

  Definition readPixel (x y : N) : M InputColor :=
    let* i := get' INP in
    let img := nth (N.to_nat i) allInputImages noImage in
    assert* x < width img as Hx in
    assert* y < height img as Hy in
    ret (pixel img Hx Hy).

  Definition readPixel_spec := unfolded_eq (readPixel).

  Global Opaque readPixel.

  Global Instance confined_readPixel x y : Confined INP (readPixel x y).
  Proof.
    rewrite readPixel_spec.
    typeclasses eauto.
  Qed.


  (** ** Current output *)

  Definition extendSamples (l r: Sample) (sn: Sound) :=
  {|
    rate := rate sn;
    samples Hr := (l, r) :: (samples sn Hr);
  |}.

  Definition putChar (c: Char) : M unit :=
    let* chars := get' OUT_CHARS in
    put' OUT_CHARS (cons c chars).
  Definition putChar_spec := unfolded_eq (putChar).
  Global Opaque putChar.
  Global Instance confined_putChar c : Confined OUT_CHARS (putChar c).
  Proof. rewrite putChar_spec. typeclasses eauto. Qed.

  Definition putByte (b: Byte) : M unit :=
    let* bytes := get' OUT_BYTES in
    put' OUT_BYTES (cons b bytes).
  Definition putByte_spec := unfolded_eq (putByte).
  Global Opaque putByte.
  Global Instance confined_putByte c : Confined OUT_BYTES (putByte c).
  Proof. rewrite putByte_spec. typeclasses eauto. Qed.

  Definition addSample (l r: Sample) : M unit :=
    let* samples := get' OUT_SOUND in
    put' OUT_SOUND (extendSamples l r samples).
  Definition addSample_spec := unfolded_eq (addSample).
  Global Opaque addSample.
  Global Instance confined_addSample l r : Confined OUT_SOUND (addSample l r).
  Proof. rewrite addSample_spec. typeclasses eauto. Qed.

  Definition setPixel (x y: N) (c: OutputColor) : M unit :=
    let* img := get' OUT_IMAGE in
    assert* x < width img in
    assert* y < height img in
    put' OUT_IMAGE (updatePixel x y (Some c) img).
  Definition setPixel_spec := unfolded_eq (setPixel).
  Global Opaque setPixel.
  Global Instance confined_setPixel x y c : Confined OUT_IMAGE (setPixel x y c).
  Proof. rewrite setPixel_spec. typeclasses eauto. Qed.


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
  Definition extractImage_spec := unfolded_eq (extractImage).
  Global Opaque extractImage.

  Global Instance extractImage_confined img : Confined ⫫ (extractImage img).
  Proof. rewrite extractImage_spec. split. typeclasses eauto. Qed.

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
  Definition newFrame_spec := unfolded_eq (newFrame).
  Global Opaque newFrame.

  Global Instance confined_newFrame w r h :
    Confined (OUT_IMAGE * OUT_BYTES * OUT_CHARS * OUT_SOUND * LOG)
             (newFrame w r h).
  Proof.
    rewrite newFrame_spec.
    typeclasses eauto.
  Qed.

 End core_section.

End Core.
