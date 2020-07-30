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
  smon_rewrite.
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
  - dependent elimination o1 as [ @Vector.cons x m o1 ].
    simpl (swallow _).
    simp swallow.
    rewrite (IHm o1).
    rewrite bind_assoc.
    reflexivity.
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
    crush.
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
  crush.

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
  apply (bind_propr _ _); [ | crush ].
  simp oneStep'.
  apply (bind_propr _ _); crush.
  rewrite ofN_bitsToN, toBits_fromBits.
  reflexivity.
Qed.

Lemma cert_id : nCert 0 (not_terminated).
Proof.
  unfold nCert.
  simp nSteps.
  crush.
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
    + crush.
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


(** ** Available stack *)

(* TODO: Where did we make it opaque. *)
Transparent put'.

(* TODO: Move
Corollary add_ret_tt {S: Type} {M: Type -> Type} {SM: SMonad S M} (mu: M unit) :
  mu = mu;; ret tt.
Proof.
  rewrite <- bind_ret at 1.
  apply bind_ext.
  intros [].
  reflexivity.
Qed.

(* TODO: Move *)
Lemma get_put' (S: Type) (M: Type -> Type) (SM: SMonad S M) :
  get >>= put = ret tt.
Proof.
  rewrite add_ret_tt at 1.
  rewrite bind_assoc, get_put, get_ret.
  reflexivity.
Qed.
*)

(* TODO: Move *)
Opaque get'.
Opaque put'.


Lemma store_none_less a : store a None ⊑ ret tt.
Proof.
  unfold store.
  destruct (Machine.available' a).
  - cbn.
    rewrite update_state, <- get_put.
    crush.
    srel_destruct Hst.
    repeat split;
      unfold lens_relation;
      [ rewrite proj_update; crush; apply Hst_mem
      | rewrite projY_updateX; assumption .. ].
  - apply (err_least _).
Qed.

(****)

Equations abandonedBefore (a: B64) (n: nat) : M unit :=
  abandonedBefore _ 0 := ret tt;
  abandonedBefore a (S n) :=
    let a' := offset (-1) a in
    store a' None;;
    abandonedBefore a' n.

Lemma abandonedBefore_less a n : abandonedBefore a n ⊑ ret tt.
Proof.
  revert a.
  induction n; intros a; simp abandonedBefore.
  - crush.
  - enough (ret tt = ret tt;; ret tt) as H.
    + rewrite H.
      apply (bind_propr _ _).
      * apply store_none_less.
      * crush. apply IHn.
    + setoid_rewrite bind_ret_tt.
      reflexivity.
Qed.

Definition abandoned n :=
  let* a := get' SP in
  abandonedBefore a (n * 8).

Transparent get'.

Corollary abandoned_less n : abandoned n ⊑ ret tt.
Proof.
  unfold abandoned, get'.
  cbn.
  rewrite bind_assoc.
  rewrite <- get_ret.
  crush.
  rewrite ret_bind.
  apply abandonedBefore_less.
Qed.

Opaque get'.

Lemma rel_ret_tt mu Y (my my' : M Y) :
  mu ⊑ ret tt -> my ⊑ my' -> mu;; my ⊑ my'.
Proof.
  intros Hu Hy.
  assert (my' = ret tt;; my') as H.
  - rewrite ret_bind. reflexivity.
  - rewrite H. crush; assumption.
Qed.

Corollary abandoning_pop :
  let* v := pop64 in
  abandoned 8;;
  ret v ⊑ pop64.
Proof.
  rewrite <- bind_ret.
  crush.
  apply rel_ret_tt.
  - apply abandoned_less.
  - crush.
Qed.


(** ** Is zero *)

Corollary chain_ret_true u : chain u (ret true) = u.
Proof.
  unfold chain.
  rewrite <- bind_ret.
  apply bind_extensional.
  intros [|]; reflexivity.
Qed.

Equations popN (n: nat) : M (vector B64 n) :=
  popN 0 := ret [];
  popN (S n) := let* h := pop64 in
                let* r := popN n in
                ret (h :: r).

Equations abandonedAfter (a: B64) (n: nat) : M unit :=
  abandonedAfter _ 0 := ret tt;
  abandonedAfter a (S n) :=
    store a None;;
    abandonedAfter (offset 1 a) n.

(* TODO: move *)
Corollary toBits_cong' n z : cong n (toBits n z) z.
Proof.
  rewrite ofN_bitsToN, fromBits_toBits_mod.
  apply cong_mod.
  lia.
Qed.

Hint Rewrite toBits_cong'.
(*
Hint Rewrite @ofN_bitsToN @fromBits_toBits_mod : cong.
Hint Rewrite @ofN_bitsToN @fromBits_toBits_mod : cong.
 *)

Hint Opaque cong : rewrite.

(* TODO: move *)

Existing Instance cong_equivalence.

Lemma abandonedAfter_action (a: B64) (m n: nat) :
  abandonedAfter a (m + n) = abandonedAfter a m;;
                             abandonedAfter (offset m a) n.
Proof.
  revert a; induction m; intros a.
  - unfold offset. cbn.
    rewrite ofN_bitsToN, toBits_fromBits.
    simp abandonedAfter.
    rewrite ret_bind.
    reflexivity.
  - simpl Init.Nat.add.
    simp abandonedAfter.
    rewrite bind_assoc.
    rewrite IHm.
    apply bind_extensional. intros [].
    apply bind_extensional. intros [].
    f_equal.
    unfold offset.

    autorewrite with cong.
    (** Hangs: [rewrite toBits_cong'] *)
    transitivity (m + (1 + a)).
    + apply cong_add_proper, toBits_cong'. reflexivity.
    + apply eq_cong. lia.
Qed.

(* TODO: move *)
Instance cong_toBits_proper n : Proper (cong n ==> eq) (toBits n).
Proof. intros z z' Hz. apply toBits_cong. exact Hz. Qed.

Corollary fromBits_toBits' n (u: Bits n) : toBits n u = u.
Proof. rewrite ofN_bitsToN. apply toBits_fromBits. Qed.

(* TODO: move *)
Proposition generalizer
      {MP1 : MachineParams1}
      {MP2 : MachineParams2}
      {X Y: Type}
      {mx: M X}
      {f: X -> M Y}
      {my: M Y}
      (H : mx >>= f = my)
      {Z: Type}
      (g: Y -> M Z) : let* x := mx in
                     let* y := f x in
                     g y = let* y := my in
                           g y.
Proof.
  rewrite <- bind_assoc.
  rewrite H.
  reflexivity.
Qed.

Opaque loadMany.

Transparent get' put'.
Lemma put_get_prime
      {MP1 : MachineParams1}
      {MP2 : MachineParams2}
      {X : Type}
      {LX: Lens State X} (x: X) : put' LX x;; get' LX = put' LX x;; ret x.
Proof.
  unfold get', put'.
  setoid_rewrite <- bind_ret.
  rewrite to_lensmonad_bind, put_get.
  reflexivity.
Qed.

(* TODO: Move *)
Lemma next_loadMany n:
  next n = let* pc := get' PC in
           let* ops := loadMany n pc in
           put' PC (offset n pc);;
           ret ops.
Proof.
  induction n; simp next.
  - unfold offset.
    cbn.
    setoid_rewrite loadMany_equation_1. (** [simp loadMany] does not work here. *)
    setoid_rewrite fromBits_toBits'.
    setoid_rewrite ret_bind.
    setoid_rewrite (generalizer get_put_prime).
    rewrite ret_bind.
    reflexivity.
  - rewrite IHn. clear IHn.
    setoid_rewrite loadMany_equation_2.
    repeat setoid_rewrite bind_assoc.

    setoid_rewrite <- bind_assoc at 1.
    Set Printing Implicit.
    setoid_rewrite (to_lensmonad_bind (LX:=PC)).
    setoid_rewrite (generalizer put_get).




  unfold next.




Lemma abandonedBefore_abandonedAfter a n :
  abandonedBefore a n = abandonedAfter (offset (-n) a) n.
Proof.
  revert a.
  induction n; intros a; simp abandonedBefore abandonedAfter; unfold offset.
  - reflexivity.
  - rewrite IHn.
    f_equal.
    + f_equal.
      f_equal.

      cbn.

Definition withAddrUndefined {X} (u : M X) (a: B64) : M X :=
  match decide (available a) with
  | right _ => u
  | left H =>
    let* mem := get' MEM in
    store a None;;
    let* res := u in
    store a (mem a H);;
    ret res
  end.

Equations withAddrsUndefined {X} (u : M X) (start: B64) n : M X :=
  withAddrsUndefined _ _ 0 := u;
  withAddrsUndefined u start 0 :=


Definition notAffectedBy {X} (u : M X) (a: B64) : Prop := forall (H: available a),
    let* e := get' MEM in
    store a None;;
    let* res := u in
    store a (e a H);;
    ret res = u.

(* PROBLEM: There's no way we can prove this with the existing axioms. *)
Instance notAffectedBy_decidable {X} (u : M X) (a: B64) :
  Decidable (notAffectedBy u a).
Proof.
  unfold notAffectedBy.





Lemma popN_abandoned_swallow {X} m n ops (rest: M X) :
  (let* v := popN n in
  abandoned (m + n);;
  swallow ops;;
  rest) =




Definition code_isZero := [PUSH1; 1; LT].

Lemma ncert_isZero :
  nCert 2 (let* x := pop64 in
           abandoned 2;;
           swallow code_isZero;;
           pushZ (if decide (x = 0 :> Z) then -1 else 0);;
           not_terminated).
Proof.
  unfold nCert, code_isZero.
  simp nSteps.
  setoid_rewrite chain_ret_true.
  unfold chain.




(** ** ??? *)

(* TODO: Rename? Move up? *)
Definition uphold (u: M bool) : M unit :=
  let* cont := u in
  assert* cont in
  ret tt.

Lemma uphold_chain
      {u u' v v': M bool} (Hu: u ⊑ u') (Hv: v ⊑ v') : uphold u;; v ⊑ chain u' v'.
Proof.
  unfold uphold, chain.
  rewrite bind_assoc.
  apply (bind_propr _ _).
  - exact Hu.
  - crush.
    destruct y; cbn; smon_rewrite.
    + exact Hv.
    + apply (err_least _).
Qed.

(* TODO *)
Context
  (TB: Transitive (@rel (M bool) _))
  (TU: Transitive (@rel (M unit) _))
.

Lemma uphold_lemma (u v w: M bool) :
  u;; not_terminated ⊑ uphold v;; w ->
  u;; not_terminated ⊑ chain v w.
Proof.
  (* This would have been easier with transitivity. *)
  unfold uphold, chain.
  intros H.



  setoid_rewrite assert_bind.







Lemma chain_prime u v : chain' u v ⊑ chain u v.



  -> m1;; not_terminated ⊑ chain v1 v2





  rewrite swallow_lemma.









(** To be continued.
It seems possible that we will need an extra axiom at some,
ensuring that [⊑] is transitive on [M bool], but we'll see. *)
