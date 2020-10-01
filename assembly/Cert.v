From Assembly Require Import DSet Mono.
Import DSetNotations.

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
    smon_rewrite.
    subst.
    exact (IHn r u (fun v => f (toB8 x :: v)) H).
Qed.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

Lemma cert_id : nCert 0 (not_terminated).
Proof.
  unfold nCert.
  simp nSteps.
  crush.
Qed.

(* TODO: Place inside section or module. *)
Import OpCodes.

(* TODO: Move? *)
Opaque next.

Open Scope Z.

Lemma next_helper (op: Z) (Hop: 0 <= op < 256) :
  (Vector.map toB8 [op] : Bytes 1) = Z.to_N op :> N.
Proof.
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
  unfold nCert; simp nSteps; unfold chain, oneStep.
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

Definition wipe (u: DSet Addr) : M unit :=
  put' (MEM' u) (fun _ _ _ => None).

Goal forall u, Confined (MEM' u) (wipe u).
  typeclasses eauto.
Qed.

(* TODO: Move *)
Proposition sub_put_spec {A B} {LA: Lens State A} {LB: Lens A B} (b: B) :
  put' (LB ∘ LA) b = let* a := get' LA in
                     put' LA (update a b).
Proof.
  setoid_rewrite put_spec'.
  setoid_rewrite get_spec.
  smon_rewrite.
Qed.

Lemma wipe_less u : wipe u ⊑ ret tt.
Proof.
  unfold wipe.
  unfold MEM'.
  rewrite sub_put_spec.
  assert (ret tt = get' MEM >>= put' MEM) as Hret;
    [ smon_rewrite
    | rewrite Hret; clear Hret ].
  crush.
  - apply getMem_propr.
  - cbn.
    destruct (decide (a ∈ u)).
    + exact I.
    + apply Hfg.
Qed.

Definition wipeStack n :=
  let* a := get' SP in
  wipe (nBefore (n * 8) a).

Corollary wipeStack_less n : wipeStack n ⊑ ret tt.
Proof.
  unfold wipeStack.
  rewrite get_spec.
  cbn.
  rewrite bind_assoc.
  rewrite <- get_ret.
  crush.
  rewrite ret_bind.
  apply wipe_less.
Qed.

Proposition rel_ret_tt mu Y (my my' : M Y) :
  mu ⊑ ret tt -> my ⊑ my' -> mu;; my ⊑ my'.
Proof.
  intros Hu Hy.
  assert (my' = ret tt;; my') as H.
  - rewrite ret_bind. reflexivity.
  - rewrite H. crush; assumption.
Qed.

Definition w_pop64 := let* v := pop64 in
                      wipeStack 1;;
                      ret v.

Corollary wiped_pop64 : w_pop64 ⊑ pop64.
Proof.
  unfold w_pop64.
  rewrite <- bind_ret.
  crush.
  apply rel_ret_tt.
  - apply wipeStack_less.
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

(**************** TODO: move **************)

Corollary toBits_cong' n z : cong n (toBits n z) z.
Proof.
  rewrite ofN_bitsToN, fromBits_toBits_mod.
  apply cong_mod.
  lia.
Qed.

Hint Opaque cong : rewrite.

Instance cong_equivalence n : Equivalence (cong n).
Proof.
  typeclasses eauto.
Qed.

Ltac cong_tac :=
  apply toBits_cong;
  rewrite toBits_cong';
  apply eq_cong;
  lia.

Lemma nAfter_action (a: B64) (m n: nat) :
  nAfter (m + n) a = (nAfter m a ∪ nAfter n (offset m a))%DSet.
Proof.
  revert a; induction m; intros a.
  - unfold offset. cbn.
    rewrite ofN_bitsToN, toBits_fromBits.
    apply extensionality. intro x.
    rewrite union_spec.
    unfold nAfter.
    setoid_rewrite def_spec.
    split.
    + intros H. right. exact H.
    + intros [H|H].
      * exfalso. destruct H as [i [H _]]. lia.
      * exact H.

  - unfold offset.
    apply extensionality. intro x.
    rewrite union_spec.
    unfold nAfter.
    setoid_rewrite def_spec.
    split.
    + intros [i [H1 H2]].
      by_lia (i < S m \/ S m <= i < S m + n)%nat as H.
      destruct H as [H|H].
      * left. exists i. split.
        -- exact H.
        -- exact H2.
      * right. exists (i - S m)%nat. split.
        -- lia.
        -- rewrite <- H2. cong_tac.
    + intros [[i [H1 H2]] | [i [H1 H2]]].
      * exists i. split.
        -- lia.
        -- exact H2.
      * exists (S m + i)%nat. split.
        -- lia.
        -- rewrite <- H2. cong_tac.
Qed.

Instance cong_toBits_proper n : Proper (cong n ==> eq) (toBits n).
Proof. intros z z' Hz. apply toBits_cong. exact Hz. Qed.

Corollary fromBits_toBits' n (u: Bits n) : toBits n u = u.
Proof. rewrite ofN_bitsToN. apply toBits_fromBits. Qed.

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

(* TODO: Move to Operations.v ? *)
Opaque loadMany.

(* TODO: Move to Mon.v *)
Lemma put_get_prime
      {MP1 : MachineParams1}
      {MP2 : MachineParams2}
      {X : Type}
      {LX: Lens State X} (x: X) : put' LX x;; get' LX = put' LX x;; ret x.
Proof.
  (* TODO: Use lens_transfer tactic *)
  setoid_rewrite get_spec.
  setoid_rewrite put_spec'.
  repeat rewrite <- bind_spec.
  smon_rewrite'.
Qed.

(***************** End move ******************)


Definition stdStart m n {o} (ops: vector Z o) : M (vector B64 n) :=
  let* v := popN n in
  wipeStack (m + n);;
  swallow ops;;
  ret v.

(** By putting [swallow] after [wipeStack] we ensure that [stdStart] fails
    if the operations overlap with (the relevant parts of) the stack. *)

Proposition nAfter_disjoint_spec u n a :
  u # nAfter n a <-> forall i, (i<n)%nat -> not (offset i a ∈ u).
Proof.
  unfold nAfter, disjoint.
  setoid_rewrite def_spec.
  split; intro H.
  - intros i Hi Ho.
    apply (H (offset i a)).
    split.
    + exact Ho.
    + now exists i.
  - intros x [Hx [i [Hi Ha]]].
    apply (H i Hi).
    unfold offset.
    rewrite Ha.
    exact Hx.
Qed.

(* TODO: Move. *)
(** Making this an instance confuses the proof search.
    Maybe this could somehow be made into an instance of [Proper] instead? *)
Proposition decidable_proper {P} {D: Decidable P} {Q} (H: Q <-> P) : Decidable Q.
Proof.
  destruct D; [left|right]; tauto.
Qed.

Instance nAfter_disjoint_decidable u n a : Decidable (u # nAfter n a).
Proof.
  refine (decidable_proper (nAfter_disjoint_spec _ _ _)).
Qed.

(* TODO: Move *)
Definition bounded_evidence
           P {DP: forall (x:nat), Decidable (P x)}
           n (H: exists x, (x < n)%nat /\ P x) : { x: nat | (x < n)%nat /\ P x }.
Proof.
  induction n.
  - exfalso. destruct H as [x [H1 H2]]. lia.
  - specialize (DP n). destruct DP as [H1|H2].
    + refine (exist _ n _). split; [lia | exact H1].
    + assert (exists (x: nat), (x < n)%nat /\ P x) as He.
      * destruct H as [x [Hsn Hx]].
        exists x. split; [ | exact Hx ].
        by_lia (x < n \/ x = n)%nat as Hn.
        destruct Hn as [Hn|Hn]; [ exact Hn | ].
        destruct Hn. exfalso. exact (H2 Hx).
      * specialize (IHn He).
        destruct IHn as [x [IH1 IH2]].
        refine (exist _ x _).
        split; [lia | exact IH2].
Defined.

Lemma bounded_all_neg P {DP: forall (x:nat), Decidable (P x)} n :
  not (forall x, (x < n)%nat -> P x) <-> (exists x, (x < n)%nat /\ not (P x)).
Proof.
  induction n; split; intro H.
  - exfalso. apply H. intros x Hx. exfalso. lia.
  - intros Ha. destruct H as [x [Hx Hp]]. lia.
  - destruct (decide (P n)) as [Hd|Hd].
    + assert (~ forall x : nat, (x < n)%nat -> P x) as Hnot.
      * intros Hno.
        apply H.
        intros x Hx.
        by_lia (x < n \/ x = n)%nat as H0.
        destruct H0 as [H1|H2].
        -- apply Hno. exact H1.
        -- destruct H2. exact Hd.
      * apply proj1 in IHn. specialize (IHn Hnot).
        destruct IHn as [x [Hx Hp]].
        exists x. split.
        -- lia.
        -- exact Hp.
    + exists n. split.
      * lia.
      * exact Hd.
  - destruct (decide (P n)) as [Hd|Hd].
    +

assert (exists x : nat, (x < n)%nat /\ ~ P x) as Hnot.
    * destruct H as [x [Hx Hp]].



  assert ({forall x, (x < n)%nat -> P x} + {exists x, (x < n)%nat /\ not (P x)}) as ae.
  - apply bounded_decidable0. typeclasses eauto.
  - destruct ae as [Ha|He].




  split.
  -


Proposition not_nAfter_disjoint_spec u n a :

  not (u # nAfter n a) <-> exists i, (i<n)%nat /\ offset i a ∈ u.
Proof.
  assert ({forall i, (i<n)%nat -> not (offset i a ∈ u)} + {exists i, (i<n)%nat /\ not (not (offset i a ∈ u))}) as s.
  - apply bounded_decidable0. typeclasses eauto.
  - destruct s as [Ha|He]; split; intro H.
    * admit.
    * admit.
    * setoid_rewrite decidable_raa in He. exact He.
    * unfold disjoint. intro HH.
      destruct H as [i [H1 H2]].
      apply (HH (offset i a)).
      split.
      -- exact H2.
      -- unfold nAfter. rewrite def_spec. exists i. now split.




destruct He as [i [H1 H2]].
      exists i. split.
      -- exact H1.
      -- apply decidable_raa in He.

Definition not_nAfter_disjoint_evidence u n a (H : not (u # nAfter n a)) : Addr.
Proof.
  rewrite nAfter_disjoint_spec in H.
  unfold disjoint, nAfter in H.

Defined.

Definition stdDis m n o :=
  let* sp := get' SP in
  let* pc := get' PC in
  assert* (nBefore m sp # nAfter o pc) in
  assert* (nAfter n sp # nAfter o pc) in
  ret tt.

(* TODO: Move / remove *)
Definition inc' L z :=
  let* a := get' L in
  put' L (offset z a).

(* TODO: move *)
Proposition assert_bind2
            P {DP: Decidable P}
            Q {DQ: Decidable Q}
            {X} (mx: M X) {Y} (f: X -> M Y) :
  let* x := (assert* P in assert* Q in mx) in
  f x = assert* P in
        assert* Q in
        let* x := mx in
        f x.
Proof.
  destruct (decide P);
    destruct (decide Q);
    smon_rewrite.
Qed.

Proposition stdStart_stdDis m n {o} (ops: vector Z o) :
  stdDis m n o;; stdStart m n ops = stdStart m n ops.
Proof.
  unfold stdDis, stdStart.
  smon_ext s.
  setoid_rewrite get_spec.
  repeat setoid_rewrite bind_assoc.
  setoid_rewrite assert_bind2.
  smon_rewrite.

  destruct (decide (nBefore _ _ # _)) as [H1|H1];
    [ destruct (decide (nAfter _ _ # _)) as [H2|H2] | ];
    [ rewrite ret_tt_bind; reflexivity
    | clear H1
    | ];
    rewrite bind_err.

  smon_rewrite.


Definition code_isZero := [PUSH1; 1; LT].

(* TODO *)
Opaque pushZ.

Lemma ncert_isZero :
  nCert 2 (let* v := stdStart 1 1 code_isZero in
           pushZ (if decide (Vector.hd v = 0 :> Z) then -1 else 0);;
           not_terminated).
Proof.
  unfold nCert;
    simp nSteps;
    unfold stdStart, chain, oneStep;
    setoid_rewrite chain_ret_true.
  (* TODO: smon_rewrite is too slow. *)
  repeat setoid_rewrite bind_assoc.
  simpl nBefore.



  apply swallow_lemma.
  unfold code_isZero.




let* x := pop64 in
           wipeStack 2;;
           swallow code_isZero;;
           pushZ (if decide (x = 0 :> Z) then -1 else 0);;
           not_terminated).
Proof.
  unfold nCert, code_isZero.
  simp nSteps.
  setoid_rewrite chain_ret_true.
  unfold chain.

Lemma ncert_isZero :
  nCert 2 (let* x := pop64 in
           wipeStack 2;;
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
