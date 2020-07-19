From Assembly Require Import Init Binary.

Unset Suggest Proof Using.

Local Open Scope Z.
Local Open Scope vector.


(** *** Ring homomorphism *)

Local Definition add {n} (u v : Bits n) : Bits n :=
  toBits n (fromBits u + fromBits v).

Local Definition mul {n} (u v : Bits n) : Bits n :=
  toBits n (fromBits u * fromBits v).

Local Lemma inj_add n (x y : Z) : toBits n (x + y) = add (toBits n x) (toBits n y).
Proof.
  apply toBits_congruence.
  setoid_rewrite fromBits_toBits_mod.
  apply Z.add_mod.
  apply pow2_nonzero.
Qed.

Local Lemma inj_mul n (x y : Z) : toBits n (x * y) = mul (toBits n x) (toBits n y).
Proof.
  apply toBits_congruence.
  setoid_rewrite fromBits_toBits_mod.
  apply Z.mul_mod.
  apply pow2_nonzero.
Qed.
