From Assembly Require Import Init.

Unset Suggest Proof Using.

Local Open Scope Z.
Local Open Scope vector.

Notation Bits := Bvector.

Arguments Bsign {_} _.
Coercion N.of_nat : nat >-> N.
Coercion Z.of_N : N >-> Z.


(** ** Helpers *)

Proposition mul_nonneg (x y : Z) : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
  intros Hx Hy.
  rewrite <- (Z2N.id _ Hx).
  rewrite <- (Z2N.id _ Hy).
  rewrite <- N2Z.inj_mul.
  apply N2Z.is_nonneg.
Qed.

Lemma div_neg z x (Hx: 0 < x) : z / x < 0 <-> z < 0.
Proof.
  split.
  - intros H. apply Znot_ge_lt. intros Hz. contradict H.
    apply Zle_not_lt, Z.ge_le, Z_div_ge0; lia.
  - intros Hz. apply Znot_ge_lt. intros H.
    set (H1 := Z.mul_div_le z x Hx).
    set (H2 := mul_nonneg x (z/ x)).
    lia.
Qed.


(** *** Powers of two *)

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

Corollary pow2_nonneg (n: nat) : 0 <= 2^n.
Proof. apply Z.lt_le_incl, pow2_pos. Qed.

Corollary pow2_nonzero (n: nat) : 2^n <> 0.
Proof. apply Z.neq_sym, Z.lt_neq, pow2_pos. Qed.

Corollary pow2_div_zero (z: Z) (n: nat) : z / 2^n = 0 <-> 0 <= z < 2^n.
Proof.
  transitivity (0 <= z < 2 ^ n \/ 2 ^ n < z <= 0).
  - apply Z.div_small_iff, pow2_nonzero.
  - set (H := pow2_nonneg n). lia.
Qed.


(** *** Double and div2 *)

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

Lemma odd_double {z b} : Z.odd (Z.double z + Z.b2z b) = b.
Proof.
  rewrite Z.add_comm, Z.odd_add_mul_2.
  destruct b; reflexivity.
Qed.

Proposition double_neg z h : Z.double z + Z.b2z h < 0 <-> z < 0.
Proof.
  rewrite Z.double_spec.
  destruct h; simpl Z.b2z; lia.
Qed.

Proposition div2_odd (z: Z) : z = Z.double (Z.div2 z) + Z.b2z (Z.odd z).
Proof.
  rewrite Z.double_spec.
  apply Z.div2_odd.
Qed.

Proposition div2_reflects_lt x y : Z.div2 x < Z.div2 y -> x < y.
Proof.
  intros H.
  setoid_rewrite Z.div2_odd.
  do 2 destruct (Z.odd _); simpl Z.b2z; lia.
Qed.

Lemma div2_double_connection x y (Hx: 0 <= x) (Hy: 0 <= y) : Z.div2 x < y <-> x < Z.double y.
Proof.
  setoid_rewrite (div2_odd x) at 2.
  split.
  - intros H. apply div2_reflects_lt. rewrite div2_double2, div2_double. exact H.
  - setoid_rewrite Z.double_spec.
    rewrite Z.div2_div.
    destruct (Z.odd x); simpl Z.b2z; lia.
Qed.


(** ** To bits and back *)

(** *** Cleave *)

Equations cleave n (z: Z) : (Bits n) * Z :=
  cleave 0 z := ([], z);
  cleave (S n) z :=
    let (u, z') := cleave n (Z.div2 z) in
    (Z.odd z :: u, z').

Proposition cleave_action m n z :
  cleave (m + n) z = let (u, z') := cleave m z in
                     let (v, z'') := cleave n z' in
                     (u ++ v, z'').
Proof.
  revert z. induction m; intros z; cbn; simp cleave; cbn.
  - destruct (cleave n z); reflexivity.
  - rewrite IHm. clear IHm.
    destruct (cleave m (Z.div2 z)).
    destruct (cleave n z0).
    reflexivity.
Qed.

Lemma snd_cleave n z : snd (cleave n z) = z / 2^n.
Proof.
  revert z; induction n; intros z; simp cleave.
  - cbn. symmetry. apply Z.div_1_r.
  - specialize (IHn (Z.div2 z)).
    destruct (cleave n (Z.div2 z)) as [u z'].
    simpl snd in *.
    simp pow2.
    rewrite Z.div2_div, Z.div_div in IHn.
    + exact IHn.
    + lia.
    + apply pow2_pos.
Qed.

Corollary snd_cleave_neg n z : snd (cleave n z) < 0 <-> z < 0.
Proof.
  rewrite snd_cleave.
  apply div_neg, pow2_pos.
Qed.


(** *** Join *)

Equations join {n} (u: Bits n) (z: Z) : Z :=
  join [] z := z;
  join (h :: u) z := Z.double (join u z) + Z.b2z h.

Proposition join_action {m} (u: Bits m) {n} (v: Bits n) z :
  join u (join v z) = join (u ++ v) z.
Proof.
  induction m.
  - dependent elimination u. reflexivity.
  - dependent elimination u. cbn. simp join. rewrite IHm. reflexivity.
Qed.

Proposition join_diff {n} (u: Bits n) z1 z2 :
  join u z1 - join u z2 = 2^n * (z1 - z2).
Proof.
  induction n; simp pow2.
  - dependent elimination u. simp join.
    lia.
  - dependent elimination u as [Vector.cons (n:=n) h u].
    simp join.
    specialize (IHn u).
    rewrite <- Z.mul_assoc.
    rewrite <- IHn.
    clear IHn.
    setoid_rewrite Z.double_spec.
    destruct h; repeat simpl Z.b2z; lia.
Qed.

Corollary join_via_zero {n} (u: Bits n) z : join u z = 2^n * z + join u 0.
Proof.
  enough (join u z - join u 0 = 2^n * (z - 0)); [lia |].
  apply join_diff.
Qed.

Proposition join_neg {n} (u: Bits n) z : join u z < 0 <-> z < 0.
Proof.
  induction n.
  - dependent elimination u. tauto.
  - dependent elimination u as [Vector.cons (n:=n) h u].
    simp join.
    transitivity (join u z < 0).
    apply double_neg.
    exact (IHn u).
Qed.

Proposition join_zero {n} (u: Bits n) : 0 <= join u 0 < 2^n.
Proof.
  induction n.
  - dependent elimination u. simp join. cbn. lia.
  - dependent elimination u as [Vector.cons (n:=n) h u].
    simp join.
    specialize (IHn u).
    destruct IHn as [H1 H2].
    split.
    + rewrite Z.double_spec. destruct h; simpl Z.b2z; lia.
    + simp pow2. apply div2_reflects_lt.
      rewrite div2_double2, <- Z.double_spec, div2_double.
      exact H2.
Qed.

Corollary join_mod {n} (u: Bits n) z : join u z mod 2^n = join u 0.
Proof.
  symmetry.
  apply (Z.mod_unique_pos _ _ z).
  - apply join_zero.
  - apply join_via_zero.
Qed.


(** *** Bijection *)

Lemma join_cleave n z : uncurry join (cleave n z) = z.
Proof.
  unfold uncurry. revert z.
  induction n; intros z; simp cleave.
  - simp join. reflexivity.
  - specialize (IHn (Z.div2 z)).
    destruct (cleave n (Z.div2 z)).
    simp join. rewrite IHn.
    symmetry.
    apply div2_odd.
Qed.

Lemma cleave_join {n} (u: Bits n) z : cleave n (join u z) = (u, z).
Proof.
  revert z. induction n; intros z.
  - dependent elimination u. simp cleave join. reflexivity.
  - dependent elimination u as [Vector.cons (n:=n) h u].
    simp join cleave.
    rewrite div2_double2.
    rewrite IHn. clear IHn.
    f_equal.
    f_equal.
    apply odd_double.
Qed.


(** *** fromBits and toBits *)

Definition toBits n z := fst (cleave n z).

Definition fromBits {n} (u: Bits n) := join u 0.

Proposition toBits_fromBits {n} (u: Bits n) : toBits n (fromBits u) = u.
Proof.
  unfold fromBits, toBits.
  rewrite cleave_join.
  reflexivity.
Qed.

(* TODO: Standard property of sections. *)
Corollary fromBits_injective {n} (u u': Bits n) :
  fromBits u = fromBits u' -> u = u'.
Proof.
  intros H. setoid_rewrite <- toBits_fromBits.
  f_equal. exact H.
Qed.

Proposition fromBits_toBits_mod {n} z : fromBits (toBits n z) = z mod 2^n.
Proof.
  unfold fromBits, toBits.
  given (join_cleave n z) as Hj.
  destruct (cleave n z) as [u z'] eqn:Hz.
  cbn.
  symmetry.
  rewrite <- Hj.
  apply join_mod.
Qed.

Corollary toBits_congruence (n: nat) z z' :
  toBits n z = toBits n z' <-> z mod 2^n = z' mod 2^n.
Proof.
  split; intro H.
  - setoid_rewrite <- fromBits_toBits_mod.
    f_equal.
    exact H.
  - apply fromBits_injective.
    setoid_rewrite fromBits_toBits_mod.
    exact H.
Qed.

Corollary fromBits_toBits (n: nat) z : 0 <= z < 2^n <-> fromBits (toBits n z) = z.
Proof.
  rewrite fromBits_toBits_mod.
  setoid_rewrite Z.mod_small_iff; [| apply pow2_nonzero].
  split; [ tauto |].
  intros [H|H]; [exact H |].
  exfalso.
  given (pow2_pos n) as HH.
  lia.
Qed.

(* TODO: Remove? *)
Proposition join_spec {n} (u: Bits n) z : join u z = fromBits u + 2^n * z.
Proof.
  unfold fromBits.
  enough (join u z - join u 0 = 2 ^ n * (z - 0)); [lia|].
  apply join_diff.
Qed.


(** *** Via [N] *)

Definition bitsToN {n} (u: Bits n) : N := Z.to_N (fromBits u).

Lemma ofN_bitsToN {n} (u: Bits n) : Z.of_N (bitsToN u) = fromBits u.
Proof.
  unfold bitsToN. rewrite Z2N.id.
  - reflexivity.
  - unfold fromBits. apply join_zero.
Qed.


(** *** Signed integers *)

Local Notation signOffset u := (if Bsign u then -1 else 0).

Definition bitsToZ {n} (u: Bits (S n)) : Z := join u (signOffset u).

Definition butSign {n} (u: Bits (S n)) : Bits n.
Proof.
  induction n.
  - exact [].
  - dependent elimination u as [h :: u].
    exact (h :: (IHn u)).
Defined.

Proposition butSign_equation_1 s : butSign [s] = [].
Proof. reflexivity. Qed.

Proposition butSign_equation_2 {n} (u: Bits (S n)) h :
  butSign (h :: u) = h :: butSign u.
Proof. reflexivity. Qed.

Hint Rewrite butSign_equation_1 : butSign.
Hint Rewrite @butSign_equation_2 : butSign.
Opaque butSign.

Proposition bitsToZ_split {n} (u: Bits (S n)) :
  bitsToZ u = join (butSign u) (signOffset u).
Proof.
  unfold bitsToZ.
  induction n.
  - dependent elimination u as [h :: u].
    dependent elimination u.
    destruct h; reflexivity.
  - dependent elimination u as [h :: u].
    specialize (IHn u).
    simp butSign join.
    cbn.
    f_equal.
    f_equal.
    exact IHn.
Qed.

Corollary bitsToZ_range {n} (u: Bits (S n)):
  -2^n <= bitsToZ u < 2^(S n).
Proof.
  rewrite bitsToZ_split.
  set (H := join_zero (butSign u)).
  simp pow2.
  destruct (Bsign u); [rewrite join_via_zero |]; lia.
Qed.


(** *** Multiplication and addition *)

Local Proposition inj_0 : N.of_nat 0 = 0%N.
Proof. reflexivity. Qed.

Local Proposition inj_1 : N.of_nat 1 = 1%N.
Proof. reflexivity. Qed.

Local Proposition Ninj_1 : Z.of_N 1 = 1%Z.
Proof. reflexivity. Qed.

Hint Rewrite <- N.add_1_l Z.add_1_l : ZZ.

Hint Rewrite
     inj_0 inj_1
     Nnat.Nat2N.inj_add
     Nnat.Nat2N.inj_mul

     N2Z.inj_0 Ninj_1
     N2Z.inj_add
     N2Z.inj_mul

     Z.add_assoc
     Z.add_0_l Z.add_0_r
     Z.add_opp_l Z.add_opp_r

     Z.sub_0_l
     Z.sub_opp_l Z.sub_opp_r
     Z.sub_0_l Z.sub_0_r

     Z.opp_0
     Z.opp_involutive

     Z.mul_assoc
     Z.mul_0_l Z.mul_0_r
     Z.mul_1_l Z.mul_1_r
     Z.mul_opp_l Z.mul_opp_r

     Z.mul_add_distr_l Z.mul_add_distr_r
     Z.mul_sub_distr_l Z.mul_sub_distr_r

     Z.double_spec
     Z.div2_div

     pow2_equation_0
     pow2_equation_1
     pow2_equation_2
  : ZZ.

Section irel_section.

  Context {X Y} (f: X -> Y) (R: relation Y).

  Definition irel : relation X := fun x x' => R (f x) (f x').

  Instance irel_reflexive {HR: Reflexive R} : Reflexive irel.
  Proof. unfold irel. intros x. reflexivity. Qed.

  Instance irel_symmetric {HR: Symmetric R} : Symmetric irel.
  Proof. unfold irel. intros x y H. symmetry. exact H. Qed.

  Instance irel_transitive {HR: Transitive R} : Transitive irel.
  Proof. unfold irel. intros x y z Hxy Hyz. transitivity (f y); assumption. Qed.

  Instance irel_equivalence {HR: Equivalence R} : Equivalence irel.
  Proof. split; typeclasses eauto. Qed.

End irel_section.

(* TODO: move up *)
Proposition pow2_action (m n: nat) : 2%Z^(m + n)%nat = 2%Z^m * 2%Z^n.
Proof.
  setoid_rewrite nat_N_Z.
  rewrite Nat2Z.inj_add.
  apply Zpower_exp; apply Z.le_ge; apply Nat2Z.is_nonneg.
Qed.

Section cong_section.

  Context (n: nat).

  Definition cong := irel (fun (z:Z) => z mod 2^n) eq.

  Instance cong_equivalence : Equivalence cong.
  Proof.
    apply irel_equivalence.
    typeclasses eauto.
  Qed.

  Instance cong_add_proper : Proper (cong ==> cong ==> cong) Z.add.
  Proof.
    intros x x' Hx y y' Hy. unfold cong, irel in *.
    setoid_rewrite Z.add_mod; [ | apply pow2_nonzero ..].
    f_equal. f_equal; assumption.
  Qed.

  Instance cong_mul_proper : Proper (cong ==> cong ==> cong) Z.mul.
  Proof.
    intros x x' Hx y y' Hy. unfold cong, irel in *.
    setoid_rewrite Z.mul_mod; [ | apply pow2_nonzero ..].
    f_equal. f_equal; assumption.
  Qed.

  Corollary toBits_cong z z' : cong z z' <-> toBits n z = toBits n z'.
  Proof.
    unfold cong, irel.
    rewrite toBits_congruence.
    reflexivity.
  Qed.

  (** Essentially just transitivity and symmetry. *)
  Instance cong_cong_proper : Proper (cong ==> cong ==> iff) cong.
  Proof. typeclasses eauto. Qed.

  Proposition cong_mod (z: Z) (m: nat) (Hm: m >= n) : cong (z mod 2^m) z.
  Proof.
    unfold cong, irel.
    by_lia (m = n + (m - n))%nat as H.
    rewrite H at 1.
    rewrite pow2_action.
    rewrite <- Znumtheory.Zmod_div_mod.
    - reflexivity.
    - apply pow2_pos.
    - apply Z.mul_pos_pos; apply pow2_pos.
    - auto with zarith.
  Qed.

End cong_section.

Hint Rewrite cong_mod : cong.
Hint Rewrite <- toBits_cong : cong.


(** *** Transparency *)

(* TODO: Is this a good idea?
Transparent cleave.
Transparent join.
*)


(** ** Bytes *)

Notation B8 := (Bits 8).
Notation B16 := (Bits 16).
Notation B32 := (Bits 32).
Notation B64 := (Bits 64).

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

Lemma bitsToBytes_bytesToBits {n} (u: Bytes n) : bitsToBytes (bytesToBits u) = u.
Proof.
  induction n.
  - dependent elimination u; reflexivity.
  - dependent elimination u as [ [b0; b1; b2; b3; b4; b5; b6; b7] :: u].
    simp bytesToBits bitsToBytes. rewrite IHn. reflexivity.
Qed.

Lemma bytesToBits_bitsToBytes {n} (u: Bits (n * 8)) : bytesToBits (bitsToBytes u) = u.
Proof.
  induction n.
  - dependent elimination u; reflexivity.
  - dependent elimination u as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u].
    simp bitsToBytes bytesToBits. rewrite IHn. reflexivity.
Qed.
