From Assembly Require Import Mono.

Unset Suggest Proof Using.



Definition Cert (spec: M bool) :=
  exists (f: State -> nat), spec ⊑ let* s := get in
                           nSteps (f s).

(** In some cases we know exactly how many steps are needed. *)
Definition nCert n (spec: M bool) := spec ⊑ nSteps n.

Proposition nCert_is_Cert n (spec: M bool) : nCert n spec -> Cert spec.
Proof.
  unfold nCert, Cert.
  intros H.
  exists (fun _ => n).
  rewrite get_ret.
  exact H.
Qed.

Definition swallow1 (op: Z) : M unit :=
  let* pc := get' PC in
  let* x := load pc in
  assert* x = toBits 8 op in
  put' PC (offset 1 pc).

Open Scope vector.

Equations swallow {n} (ops: vector Z n) : M unit :=
  swallow [] := ret tt;
  swallow (op :: rest) :=
    swallow1 op;;
    swallow rest.

Lemma swallow_action {m n} (o1: vector Z m) (o2: vector Z n) :
  swallow (o1 ++ o2) = swallow o1;; swallow o2.
Proof.
  induction m.
  - dependent elimination o1.
    simp swallow.
    smon_rewrite.
    reflexivity.
  - dependent elimination o1 as [ @Vector.cons x m o1 ].
    simpl (swallow _).
    simp swallow.
    rewrite (IHm o1).
    rewrite bind_assoc.
    reflexivity.
Qed.

(* TODO: Move *)
Lemma assert_bind {P} {DP: Decidable P} {X} {mx: M X} {Y} {f: X -> M Y} :
  (assert* P in mx) >>= f = assert* P in (mx >>= f).
Proof.
  destruct (decide P); [ | rewrite err_bind ]; reflexivity.
Qed.

(* TODO: Move *)
Lemma assert_bind' {P} {DP: Decidable P} {X} {f: P -> M X} {Y} {g: X -> M Y} :
  (assert* P as H in f H) >>= g = assert* P as H in (f H >>= g).
Proof.
  destruct (decide P); [ | rewrite err_bind ]; reflexivity.
Qed.

(* TODO: Move *)
Opaque put'.

Lemma swallow_lemma {n} {ops: vector Z n} {X} {u: M X} {f: Bytes n -> M X} :
  u ⊑ f (Vector.map toB8 ops) -> swallow ops;; u ⊑ next n >>= f.
Proof.
  intros H.
  repeat setoid_rewrite bind_assoc.
  revert ops u f H.
  induction n; intros ops u f H; simp next.
  - dependent elimination ops. simp swallow.
    setoid_rewrite ret_bind. exact H.
  - dependent elimination ops as [Vector.cons (n:=n) x r].
    simp swallow.
    unfold swallow1.
    repeat setoid_rewrite bind_assoc.
    setoid_rewrite assert_bind.
    repeat crush.
    + srel_destruct Hst. assumption.
    + setoid_rewrite ret_bind.
      apply IHn. subst y0. exact H.
Qed.


(** ** ?? *)

(* TODO: Place inside section or module. *)
Import OpCodes.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

(* TODO: Move? *)
Opaque next.

Lemma next_helper (op: Z) (Hop: 0 <= op < 256) :
  (Vector.map toB8 [op] : Bytes 1) = Z.to_N op :> N.
Proof. (* TODO: automate? *)
  simpl Vector.map.
  remember (toB8 op) as u eqn:Hu.
  dependent elimination u as [[b0; b1; b2; b3; b4; b5; b6; b7]].
  simp bytesToBits. simpl. rewrite Hu.
  unfold bitsToN. f_equal.
  apply fromBits_toBits. cbn. lia.
Qed.

Lemma match_helper (op: Z) (Hop: 0 <= op < 256) :
  Z.of_N (bitsToN (bytesToBits (cells_to_bytes (Vector.map toB8 [op])))) = op.
Proof.
  unfold cells_to_bytes, id.
  rewrite next_helper;
    [ rewrite Z2N.id | ];
    lia.
Qed.

Ltac cert_start :=
  unfold nCert;
  simp nSteps;
  unfold chain, oneStep;
  setoid_rewrite bind_assoc;
  try setoid_rewrite bind_assoc;
  apply swallow_lemma;
  setoid_rewrite next_helper; [ | lia ];
  try (unfold cells_to_bytes, id;
       rewrite next_helper; try lia);
  simpl;
  repeat rewrite ret_bind;
  repeat crush.

Lemma cert_exit : nCert 1 (swallow [EXIT];;
                           terminated).
Proof. cert_start. Qed.

Lemma cert_nop : nCert 1 (swallow [NOP];;
                          not_terminated).
Proof. cert_start. Qed.

Lemma bind_ret_helper {X Y Z} {mx: M X} {y: Y} {f: Y -> M Z} :
  mx;; ret y >>= f = mx;; f y.
Proof.
  rewrite bind_assoc, ret_bind. reflexivity.
Qed.

Lemma cert_jump : nCert 1 (swallow [JUMP];;
                           let* a := pop64 in
                           put' PC a;;
                           not_terminated).
Proof.
  unfold nCert;
  simp nSteps;
  unfold chain, oneStep.
  setoid_rewrite bind_assoc at 3.
  apply swallow_lemma.
  rewrite match_helper; [ | lia ].
  rewrite bind_ret_helper.
  rewrite <- bind_assoc.
  apply (bind_propr _ _); [ | repeat crush ].
  simp oneStep'.
  apply (bind_propr _ _); repeat crush.
  rewrite ofN_bitsToN, toBits_fromBits.
  reflexivity.
Qed.

Lemma cert_id : nCert 0 (not_terminated).
Proof.
  unfold nCert.
  simp nSteps.
  repeat crush.
Qed.

Instance chain_propr : PropR chain.
Proof.
  intros u u' Hu v v' Hv.
  unfold chain.
  apply (bind_propr _ _).
  - exact Hu.
  - intros x x' Hx.
    cbv in Hx.
    subst x.
    destruct x'.
    + exact Hv.
    + repeat crush.
Qed.

Lemma ncert_comp m n (u: M bool) {Cu: nCert m u} (v: M bool) {Cv: nCert n v} :
  nCert (m + n) (chain u v).
Proof.
  unfold nCert in *.
  rewrite nSteps_action.
  apply chain_propr.
  - exact Cu.
  - exact Cv.
Qed.

(** To be continued.
It seems possible that we will need an extra axiom at some,
ensuring that [⊑] is transitive on [M bool], but we'll see. *)
