From Assembly Require Import Init Lens.

Unset Suggest Proof Using.

Local Open Scope Z.

Notation Bits := Bvector.

Section bits_section.

  (** ** Basics *)

  Lemma pos_pred_double_z (x: positive) : Zpos (Pos.pred_double x) = 2 * (Zpos x) - 1.
  Proof.
    destruct x as [ x | x | ]; simpl; reflexivity.
  Qed.

  Lemma pos_pred_n_z (x: positive): Z.of_N (Pos.pred_N x) = Z.pred (Zpos x).
  Proof.
    destruct x as [ x | x | ]; reflexivity.
  Qed.

  Lemma pos_pred_n_injective : forall x y, Pos.pred_N x = Pos.pred_N y -> x = y.
  Proof.
    intros x y H.
    enough (Zpos x = Zpos y) as Hz.
    - injection Hz. tauto.
    - set (HH := f_equal Z.of_N H).
      do 2 rewrite pos_pred_n_z in HH.
      apply Z.pred_inj.
      exact HH.
  Qed.

  Lemma odd_double {z b} : Z.odd (Z.double z + Z.b2z b) = b.
  Proof.
    rewrite Z.add_comm, Z.odd_add_mul_2.
    destruct b; reflexivity.
  Qed.

  Proposition div2_double z : Z.div2 (Z.double z) = z.
  Proof.
    rewrite Z.div2_div, Z.double_spec, Z.mul_comm, Z_div_mult;
      auto with zarith.
  Qed.

  Proposition div2_double1 z : Z.div2 (Z.double z + 1) = z.
  Proof.
    rewrite Z.div2_div, Z.double_spec, Z.mul_comm, Z_div_plus_full_l;
      auto with zarith.
  Qed.

  Corollary div2_double2 z b : Z.div2 (Z.double z + Z.b2z b) = z.
  Proof.
    destruct b; simpl.
    - apply div2_double1.
    - rewrite Z.add_0_r. apply div2_double.
  Qed.


  (** ** Lenses *)

  #[refine] Instance lens_odd : Lens Z bool :=
  {
    proj z := Z.odd z;
    update z b := Z.double (Z.div2 z) + Z.b2z b;
  }.
  Proof.
    - intros z x.
      rewrite Z.add_comm.
      rewrite Z.odd_add_mul_2.
      destruct x; reflexivity.
    - intros z.
      symmetry.
      apply Z.div2_odd.
    - intros z x x'.
      rewrite div2_double2.
      reflexivity.
  Defined.

  #[refine] Instance lens_div2 : Lens Z Z :=
  {
    proj z := Z.div2 z;
    update z x := Z.double x + Z.b2z (Z.odd z);
  }.
  Proof.
    - intros z x. apply div2_double2.
    - intros z. symmetry. apply Z.div2_odd.
    - intros z x x'. do 2 f_equal. apply odd_double.
  Defined.

  Instance independent_odd_div2 : Independent lens_odd lens_div2.
  Proof.
    split.
    - intros z b. apply div2_double2.
    - intros z x. apply odd_double.
    - intros z b y. simpl.
      rewrite odd_double, div2_double2.
      reflexivity.
  Qed.

  #[refine] Instance bijection_odd_div2 : Bijection_lens (lens_prod independent_odd_div2) :=
    bijection_lens (fun oz => Z.double (snd oz) + Z.b2z (fst oz)) _.
  Proof.
    intros z [o x]. simpl.
    do 2 f_equal.
    rewrite Z.add_comm.
    rewrite Z.double_spec.
    rewrite Z.odd_add_mul_2.
    destruct o; reflexivity.
  Defined.

  Context (n: nat).

  Global Instance lens_bits : Lens Z (Bits n).
  Proof.
    apply (lens_vector lens_odd lens_div2 n).
  Defined.

  Instance lens_bits' : Lens Z Z.
  Proof.
    apply (lens_vector' lens_div2 n).
  Defined.

  Global Instance independent_bits : Independent lens_bits lens_bits'.
  Proof.
    apply (independent_vector n).
  (** This must be transparent for the definition
      of [bijection_bits] to go through. *)
  Defined.

  Global Instance bijection_bits : Bijection_lens (lens_prod independent_bits).
  Proof.
    apply (bijection_vector bijection_odd_div2).
  Defined.

End bits_section.

Arguments Bsign {_} _.
Coercion N.of_nat : nat >-> N.
Coercion Z.of_N : N >-> Z.

(** Including the direct coercion, [Z.of_nat], as well would create
problems (and a warning) since it is (unfortunately) not convertible to
the composite. Instead we will rely on [setoid_rewrite [<-] nat_N_Z] when
necessary. *)

Section bit_facts_section.

  Open Scope vector.

  (** ** Helpers *)

  Lemma pow2_equation_0 : 2^0 = 1.
  Proof. reflexivity. Qed.

  Lemma pow2_equation_1 : 2 ^ 0%nat = 1.
  Proof. simpl. exact pow2_equation_0. Qed.

  Lemma pow2_equation_2 n : 2^(S n) = 2 * (2^n).
  Proof.
    setoid_rewrite nat_N_Z.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r.
    - reflexivity.
    - apply Nat2Z.is_nonneg.
  Qed.

  Hint Rewrite
       pow2_equation_0
       pow2_equation_1
       pow2_equation_2 : pow2.

  Lemma pow2_pos (n: nat) : 0 < 2^n.
  Proof.
    setoid_rewrite nat_N_Z.
    apply Z.pow_pos_nonneg.
    - lia.
    - apply Nat2Z.is_nonneg.
  Qed.

  Corollary pow2_nonneg (n : nat) : 0 <= 2^n.
  Proof. apply Z.lt_le_incl, pow2_pos. Qed.


  (** ** Characterizations *)

  Definition toBits n : Z -> Bits n := proj (Lens:=lens_bits n).

  Proposition toBits_equation_1 z : toBits 0 z = [].
  Proof. reflexivity. Qed.

  Proposition toBits_equation_2 n z :
    toBits (S n) z = Z.odd z :: toBits n (Z.div2 z).
  Proof.
    unfold toBits. simpl.
    simp projN. simpl.
    reflexivity.
  Qed.

  Hint Rewrite
       toBits_equation_1
       toBits_equation_2 : toBits.

  Definition toRest n : Z -> Z := proj (Lens:=lens_bits' n).

  Proposition toRest_equation_1 z : toRest 0 z = z.
  Proof. reflexivity. Qed.

  Proposition toRest_equation_2 n z :
    toRest (S n) z = toRest n (Z.div2 z).
  Proof.
    unfold toRest.
    simpl.
    simp projN'.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite
       toRest_equation_1
       toRest_equation_2 : toRest.

  Lemma toRest_spec n z : toRest n z = z / 2 ^ n.
  Proof.
    revert z. induction n; intros z; simp toRest.
    - symmetry. apply Z.div_1_r.
    - rewrite IHn.
      rewrite Z.div2_div.
      simp pow2.
      rewrite Zdiv_Zdiv.
      + reflexivity.
      + lia.
      + apply pow2_nonneg.
  Qed.

  Definition insta {n} (u:Bits n) (z: Z) : Z :=
    inverse (Bijection:=bijection_bits n) (u, z).

  Proposition toBits_insta {n} (u: Bits n) z : toBits n (insta u z) = u.
  Proof. apply projX_inverse. Qed.

  Proposition toRest_insta {n} (u: Bits n) z : toRest n (insta u z) = z.
  Proof. apply projY_inverse. Qed.

  Proposition insta_equation_1 z : insta [] z = z.
  Proof. unfold insta. reflexivity. Qed.

  Arguments inverseN {_ _ _ _ _ _ _}.

  Proposition insta_equation_2 {n} (b:bool) (u:Bits n) z :
    insta (b::u) z = Z.double (insta u z) + Z.b2z b.
  Proof.
    unfold insta. simpl. simp inverseN.
    reflexivity.
  Qed.

  Hint Rewrite
       insta_equation_1
       @insta_equation_2 : insta.

  Proposition insta_bijection z {n} (u: Bits n) z' :
    toBits n z = u /\ toRest n z = z' <-> insta u z' = z.
  Proof.
    transitivity (proj (Lens:=lens_prod (independent_bits n)) z = (u, z')).
    - unfold toBits, toRest. simpl. split.
      + intros [H1 H2]. subst. reflexivity.
      + intros H. inversion H. tauto.
    - apply B_bijection.
  Qed.


  (** ** Update *)

  Lemma insta_spec {n} (u: Bits n) (z: Z) :
    insta u z = 2^n * z + update 0 u.
  Proof.
    revert u z. induction n; intros u z.
    - dependent elimination u.
      simp insta pow2. simpl update. simp updateN.
      lia.
    - dependent elimination u as [b :: u].
      simp insta pow2. simpl update. simp updateN.
      rewrite IHn. simpl update.
      set (x := updateN 0 u).
      rewrite Z.add_assoc.
      f_equal.
      setoid_rewrite Z.double_spec.
      rewrite Z.mul_add_distr_l.
      f_equal.
      + lia.
      + rewrite Z.add_0_r, div2_double.
        reflexivity.
  Qed.

  Corollary update_to_insta0 {n} (u: Bits n) : update 0 u = insta u 0.
  Proof. rewrite insta_spec. lia. Qed.

  Lemma update_spec {n} (u: Bits n) (z: Z) :
    update z u = 2^n * (z / 2^n) + insta u 0.
  Proof.
    transitivity (insta u (toRest n z)).
    - unfold insta, toRest.
      apply (B_injective (Bf:=bijection_bits n)).
      setoid_rewrite prod_proj_spec.
      f_equal.
      + rewrite proj_update.
        rewrite <- update_prodX.
        rewrite proj_update.
        reflexivity.
      + rewrite projY_updateX.
        rewrite <- (update_as_inverse z).
        rewrite prod_update_spec.
        rewrite proj_update.
        reflexivity.
    - rewrite insta_spec.
      rewrite toRest_spec.
      rewrite update_to_insta0.
      reflexivity.
  Qed.

  Lemma insta0_nonneg {n} (u: Bits n) : 0 <= insta u 0.
  Proof.
    induction n.
    - dependent elimination u. simp insta. lia.
    - dependent elimination u as [b :: u].
      simp insta.
      apply Z.add_nonneg_nonneg; [|destruct b; simpl; lia].
      specialize (IHn u).
      rewrite Z.double_spec.
      lia.
  Qed.

  Corollary update_nonneg {n} (x : N) (u : Bits n) : injected N (update (inj x) u).
  Proof.
    rewrite update_spec.
    simpl. decide as H.
    - apply Z.add_nonneg_nonneg;
        [| apply insta0_nonneg].
      apply Z.mul_nonneg_nonneg.
      + apply Z.lt_le_incl, pow2_pos.
      + apply Z.div_pos.
        * apply N2Z.is_nonneg.
        * apply pow2_pos.
    - apply some_is_some.
  Qed.


  (** ** Unsigned *)

  Instance lens_bits_N n : Lens N (Bits n) :=
    sublens (PX:=prism_N) (LY:=lens_bits n) update_nonneg.

  Definition bitsToN {n} (u: Bits n) : N := update 0%N u.

  Proposition ofN_bitsToN {n} (u: Bits n) : bitsToN u = insta u 0 :> Z.
  Proof.
    change Z.of_N with inj.
    rewrite <- update_to_insta0.
    change 0 with (inj 0%N).
    apply inj_prism_update.
  Qed.

  Lemma div2_reflects_lt x y : Z.div2 x < Z.div2 y -> x < y.
  Proof.
    intros H.
    setoid_rewrite Z.div2_odd.
    do 2 destruct (Z.odd _); simpl Z.b2z; lia.
  Qed.

  Lemma insta0_limit {n} (u: Bits n) : insta u 0 < 2 ^ n.
  Proof.
    induction n; dependent elimination u; simp insta pow2.
    - exact Z.lt_0_1.
    - apply div2_reflects_lt.
      rewrite div2_double2, div2_double.
      apply IHn.
  Qed.

  Corollary bitsToN_limit {n} (u: Bits n) : (bitsToN u < 2 ^ n)%N.
  Proof.
    apply N2Z.inj_lt.
    rewrite ofN_bitsToN, N2Z.inj_pow. simpl.
    rewrite nat_N_Z.
    setoid_rewrite <- nat_N_Z.
    apply insta0_limit.
  Qed.

  Proposition double_reflects_lt x y : Z.double x < Z.double y -> x < y.
  Proof. destruct x; destruct y; tauto. Qed.

  Lemma insta_toBits {n:nat} z (H0: 0 <= z) (H1: z < 2 ^ n) :
    insta (toBits n z) 0 = z.
  Proof.
    revert z H0 H1.
    induction n;
      simp pow2;
      intros z H0 H1;
      simp toBits;
      simp insta;
      [ lia | ].
    rewrite IHn.
    - symmetry. apply Z.div2_odd.
    - apply Z.div2_nonneg. exact H0.
    - apply double_reflects_lt.
      rewrite (Z.div2_odd z) in H1.
      setoid_rewrite Z.double_spec.
      destruct (Z.odd z); simpl Z.b2z in H1; lia.
  Qed.

 Corollary bitsToN_proj {n:nat} {x} (Hx: (x < 2 ^ n)%N) :
    bitsToN (proj x : Bits n) = x.
  Proof.
    apply N2Z.inj.
    rewrite ofN_bitsToN.
    unfold lens_bits_N.
    rewrite prism_proj_spec.
    apply insta_toBits.
    - apply N2Z.is_nonneg.
    - change 2 with (Z.of_N 2%N).
      setoid_rewrite nat_N_Z.
      rewrite <- nat_N_Z, <- N2Z.inj_pow.
      apply N2Z.inj_lt.
      exact Hx.
  Qed.

  Proposition toBits_bitsToN {n} (u: Bits n) : toBits n (bitsToN u) = u.
  Proof.
    rewrite ofN_bitsToN, toBits_insta. reflexivity.
  Qed.


  (** ** Signed *)

  Definition bitsToZ {n} (u: Bits (S n)) : Z := insta u (if Bsign u then -1 else 0).

  Proposition toBits_bitsToZ {n} (u: Bits (S n)) : toBits _ (bitsToZ u) = u.
  Proof. apply toBits_insta. Qed.

  (* "101" = -3 *)
  (* Compute bitsToZ [true; false; true]. *)

  Proposition sign_bitsToZ {n} (u: Bits (S n)) : bitsToZ u < 0 <-> Bsign u.
  Proof.
    unfold bitsToZ.
    split.
    - destruct (Bsign u); intro H; [apply true_is_true|].
      exfalso.
      apply (Zlt_not_le _ _ H).
      apply insta0_nonneg.
    - induction n.
      + dependent elimination u as [ [b] ].
        simp insta.
        destruct (_:bool); simpl; intro H; lia.
      + dependent elimination u as [b :: u].
        simpl Bsign. intros Hs. simp insta.
        apply div2_reflects_lt.
        rewrite div2_double2.
        simpl Z.div2.
        exact (IHn u Hs).
  Qed.

End bit_facts_section.

Notation B8 := (Bits 8).
Notation B16 := (Bits 16).
Notation B32 := (Bits 32).
Notation B64 := (Bits 64).


(** ** Bytes *)

Section bytes_section.

  Open Scope vector.
  Open Scope program_scope.

  Definition Bytes n := vector B8 n.

  (* It seems Equations is not able to handle these definitions yet,
     even though [dependent elimination] works as expected. *)

  Definition bitsToBytes {n} (u: Bits (n * 8)) : Bytes n.
  Proof.
    induction n.
    - exact [].
    - simpl in u.
      dependent elimination u as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u].
      exact ([b0; b1; b2; b3; b4; b5; b6; b7] :: IHn u).
  Defined.

  Proposition bitsToBytes_equation_1 : @bitsToBytes (0 * 8) [] = [].
  Proof. reflexivity. Qed.

  Proposition bitsToBytes_equation_2 {n} b0 b1 b2 b3 b4 b5 b6 b7 (u: Bits (n * 8)) :
    @bitsToBytes (S n) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u) =
    [b0; b1; b2; b3; b4; b5; b6; b7] :: bitsToBytes u.
  Proof. reflexivity. Qed.

  Hint Rewrite bitsToBytes_equation_1 @bitsToBytes_equation_2 : bitsToBytes.
  Opaque bitsToBytes.

  Definition bytesToBits {n} (u: Bytes n) : Bits (n * 8).
  Proof.
    induction n.
    - exact [].
    - dependent elimination u as [ [b0; b1; b2; b3; b4; b5; b6; b7] :: u].
      exact (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: IHn u).
  Defined.

  Proposition bytesToBits_equation_1 : bytesToBits [] = [].
  Proof. reflexivity. Qed.

  Proposition bytesToBits_equation_2 n b0 b1 b2 b3 b4 b5 b6 b7 (u: Bytes n) :
    @bytesToBits (S n) ([b0; b1; b2; b3; b4; b5; b6; b7] :: u) =
    b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bytesToBits u.
  Proof. reflexivity. Qed.

  Hint Rewrite bytesToBits_equation_1 @bytesToBits_equation_2 : bytesToBits.
  Opaque bytesToBits.

  #[refine] Instance bytes_bijection n : Bijection (@bitsToBytes n) := { inverse := (@bytesToBits n) }.
  Proof.
    all: induction n; intro u.
    1,3: dependent elimination u; reflexivity.
    - dependent elimination u as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u].
      simp bitsToBytes bytesToBits. rewrite IHn. reflexivity.
    - dependent elimination u as [ [b0; b1; b2; b3; b4; b5; b6; b7] :: u].
      simp bytesToBits bitsToBytes. rewrite IHn. reflexivity.
  Defined.

End bytes_section.
