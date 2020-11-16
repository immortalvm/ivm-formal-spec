From Assembly Require Import DSet Mono.
Import DSetNotations.

Unset Suggest Proof Using.

Open Scope vector.

(* TODO: Place inside section or module. *)
Import OpCodes.

(* TODO: Move? *)
Opaque next.

Open Scope Z.

(********************)

(** The following holds in the initial smonad, see MonoExtras.v. *)

Parameter err_less_eq :
  forall {X} {RX: Rel X} (mx: M X) (Hmx: mx ⊑ err), mx = err.

Parameter RM_transitive :
  forall X (RX: Rel X) (RXT: Transitive RX),
    Transitive (RM X RX).

Parameter RM_antisymmetric :
  forall X (RX: Rel X) (RXT: Antisymmetric X eq RX),
    Antisymmetric (M X) eq (RM X RX).

(********************)


(** ** Preliminaries / to be moved *)

(* TODO: Delete / move to end of Operations.v. *)
(* Notation "⫫" := (@fstMixer State). *)

(* TODO: Move *)
Proposition sub_put_spec {A B} {LA: Lens State A} {LB: Lens A B} (b: B) :
  put' (LB ∘ LA) b = let* a := get' LA in
                     put' LA (update a b).
Proof.
  setoid_rewrite put_spec'.
  setoid_rewrite get_spec.
  smon_rewrite.
Qed.

(* TODO: Make definition in Operations.v global instead. *)
Global Ltac simp_loadMany := rewrite_strat (outermost (hints loadMany)).

(* TODO: Move to Operations.v ? *)
Opaque loadMany.
Opaque load.

Proposition postpone_assume P {DP: Decidable P} {X} (mx: M X) {Y} (f: X -> M Y) :
  assume P;;
  let* x := mx in
  f x = let* x := mx in
        assume P;;
        f x.
Proof.
  destruct (decide P) as [H|H]; smon_rewrite.
Qed.

Lemma assume_cons {A} (EA: EqDec A) (a a': A) n (u u': vector A n) {X} (mx: M X) :
  assume (a :: u = a' :: u');;
  mx = assume (a = a');;
       assume (u = u');;
       mx.
Proof.
  destruct (decide (a :: u = a' :: u')) as [He|He].
  - rewrite ret_bind.
    apply cons_inj in He.
    destruct He as [Ha Hu].
    decided Ha.
    decided Hu.
    now do 2 rewrite ret_bind.
  - destruct (decide (a = a')) as [Ha|Ha];
      destruct (decide (u = u')) as [Hu|Hu].
    1: exfalso. congruence.
    all: smon_rewrite.
Qed.


(* TODO: Move to Init.v ? *)

Proposition vector_map_equation_1 {A B} (f: A -> B) : Vector.map f [] = [].
Proof.
  reflexivity.
Qed.

Proposition vector_map_equation_2 {A B} (f: A -> B) (x: A) {n} (u: vector A n) : Vector.map f (x :: u) = f x :: Vector.map f u.
Proof.
  reflexivity.
Qed.

Hint Rewrite @vector_map_equation_1 : map.
Hint Rewrite @vector_map_equation_2 : map.

Opaque Vector.map.


Lemma next_1_helper (op: Z) (Hop: 0 <= op < 256) :
  (Vector.map toB8 [op] : Bytes 1) = Z.to_N op :> N.
Proof.
  simp map.
  remember (toB8 op) as u eqn:Hu.
  dependent elimination u as [[b0; b1; b2; b3; b4; b5; b6; b7]].
  simp bytesToBits. simpl. rewrite Hu.
  unfold bitsToN. f_equal.
  apply fromBits_toBits. cbn. lia.
Qed.

Lemma step_match_helper (op: Z) (Hop: 0 <= op < 256) :
  Z.of_N (bitsToN (bytesToBits (cells_to_bytes (Vector.map toB8 [op])))) = op.
Proof.
  unfold cells_to_bytes, id.
  rewrite next_1_helper;
    [ rewrite Z2N.id | ];
    lia.
Qed.


Proposition chain_ret_true u : chain u (ret true) = u.
Proof.
  unfold chain.
  rewrite <- bind_ret.
  apply bind_extensional.
  intros [|]; reflexivity.
Qed.

(* TODO: Move *)
Corollary toBits_cong' n z : cong n (toBits n z) z.
Proof.
  rewrite ofN_bitsToN, fromBits_toBits_mod.
  apply cong_mod.
  lia.
Qed.

(* TODO: Move *)
Hint Opaque cong : rewrite.

(* TODO: Move *)
Instance cong_equivalence n : Equivalence (cong n).
Proof.
  typeclasses eauto.
Qed.

(* TODO: Move *)
Ltac cong_tac :=
  apply toBits_cong;
  rewrite toBits_cong';
  apply eq_cong;
  lia.

(* TODO: Move *)
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

(* TODO: Move *)
Instance cong_toBits_proper n : Proper (cong n ==> eq) (toBits n).
Proof. intros z z' Hz. apply toBits_cong. exact Hz. Qed.

(* TODO: Move *)
Corollary fromBits_toBits' n (u: Bits n) : toBits n u = u.
Proof. rewrite ofN_bitsToN. apply toBits_fromBits. Qed.

(* TODO: Move *)
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

(* TODO: Move. *)
(** Making this an instance confuses the proof search.
    Maybe this could somehow be made into an instance of [Proper] instead? *)
Proposition decidable_proper {P} {D: Decidable P} {Q} (H: Q <-> P) : Decidable Q.
Proof.
  destruct D; [left|right]; tauto.
Qed.

(* TODO: Move *)
Lemma bounded_all_neg P {DP: forall (x:nat), Decidable (P x)} n :
  not (forall x, (x < n)%nat -> P x) -> (exists x, (x < n)%nat /\ not (P x)).
Proof.
  induction n; intro H.
  - exfalso. apply H. intros x Hx. exfalso. lia.
  - destruct (decide (P n)) as [Hd|Hd].
    + assert (~ forall x : nat, (x < n)%nat -> P x) as Hnot.
      * intros Hno.
        apply H.
        intros x Hx.
        by_lia (x < n \/ x = n)%nat as H0.
        destruct H0 as [H1|H2].
        -- apply Hno. exact H1.
        -- destruct H2. exact Hd.
      * specialize (IHn Hnot).
        destruct IHn as [x [Hx Hp]].
        exists x. split.
        -- lia.
        -- exact Hp.
    + exists n. split.
      * lia.
      * exact Hd.
Qed.

(* TODO: Move. Are there better ways to do this? *)
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

Instance nAfter_disjoint_decidable u n a : Decidable (u # nAfter n a).
Proof.
  refine (decidable_proper (nAfter_disjoint_spec _ _ _)).
Qed.

Proposition not_nAfter_disjoint_spec u n a :
  not (u # nAfter n a) -> exists i, (i<n)%nat /\ offset i a ∈ u.
Proof.
  rewrite nAfter_disjoint_spec.
  intros H.
  apply bounded_all_neg in H.
  - setoid_rewrite decidable_raa in H. exact H.
  - typeclasses eauto.
Qed.

Definition not_nAfter_disjoint_evidence u n a (H : not (u # nAfter n a)) :
  { x: Addr | x ∈ u /\ exists i, (i < n)%nat /\ offset i a = x }.
Proof.
  apply not_nAfter_disjoint_spec in H.
  apply bounded_evidence in H; [ | typeclasses eauto ].
  destruct H as [i [Hi Hu]].
  refine (exist _ (offset i a) _).
  split.
  - exact Hu.
  - now exists i.
Defined.


(* TODO: Move to Binary.v *)
(** Cf. [bitsToBytes] *)
Definition bytesToLongs {n} (u: Bytes (n * 8)) : vector B64 n.
Proof.
  induction n.
  - exact [].
  - simpl in u.
    dependent elimination u as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u].
    exact ((b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) :: IHn u).
Defined.

Proposition bytesToLongs_equation_1 : @bytesToLongs (0 * 8) [] = [].
Proof. reflexivity. Qed.

Proposition bytesToLongs_equation_2 {n} b0 b1 b2 b3 b4 b5 b6 b7 (u: Bytes (n * 8)) :
  @bytesToLongs (S n) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u) =
  (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7) :: bytesToLongs u.
Proof. reflexivity. Qed.

Hint Rewrite bytesToLongs_equation_1 @bytesToLongs_equation_2 : bytesToLongs.
Opaque bytesToLongs.


Equations popN (n: nat) : M (vector B64 n) :=
  popN 0 := ret [];
  popN (S n) := let* h := pop64 in
                let* r := popN n in
                ret (h :: r).

(* TODO: Move *)
Opaque popMany.

Proposition bytesToBits_equation_2' {n} b (u: Bytes n) :
  @bytesToBits (S n) (b :: u) = b ++ bytesToBits u.
Proof.
  dependent elimination b as [b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: []].
  simp bytesToBits.
  reflexivity.
Qed.

(* Proposition append_nil {A} {n} (u: vector A n) : u ++ [] = u. *)

Proposition bytesToLongs_equation_2' {n} b0 b1 b2 b3 b4 b5 b6 b7 (u: Bytes (n * 8)) :
  @bytesToLongs (S n) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: u) =
  (([b0; b1; b2; b3; b4; b5; b6; b7] : Bytes 8) : B64) :: bytesToLongs u.
Proof.
  (* TODO: Can this be done more elegantly? *)
  simp bytesToLongs.
  repeat rewrite bytesToBits_equation_2'.
  repeat f_equal.
  dependent elimination b7 as [c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: []].
  reflexivity.
Qed.

Proposition popN_spec n :
  popN n = let* u := popMany (n * 8) in
           ret (bytesToLongs u).
Proof.
  induction n.
  - simp popMany. smon_rewrite.
  - simp popN.
    change (S n * 8)%nat with (S (S (S (S (S (S (S (S (n * 8)))))))))%nat.
    setoid_rewrite IHn.
    unfold pop64.
    simp popMany.
    smon_rewrite.
    setoid_rewrite bytesToLongs_equation_2'.
    reflexivity.
Qed.


Proposition nAfter_empty a : nAfter 0 a = ∅%DSet.
Proof.
  apply extensionality.
  intros x.
  unfold nAfter.
  rewrite def_spec.
  transitivity False.
  - split.
    + intros [i [Hi _]]. lia.
    + tauto.
  - set (H := @empty_spec _ x). tauto.
Qed.

Proposition simp_assume P {DP: Decidable P} {X} (mx: M X) :
  assume P;; mx = if decide P
                  then mx
                  else err.
Proof.
  destruct (decide P) as [H|H]; smon_rewrite.
Qed.

Ltac simp_assume := setoid_rewrite simp_assume.

(* TODO: Move *)
Instance decidable_iff {P Q} (H: P <-> Q) {DP: Decidable P} : Decidable Q.
Proof.
  destruct DP; [left|right]; tauto.
Qed.

(* Presumably in coq-hott this could be an actual instance of Proper. *)
Proposition decide_proper
            {P Q}
            {DP: Decidable P}
            {DQ: Decidable Q}
            (H: P <-> Q)
            {X} (x x':X) :
  (if decide P then x else x') = (if decide Q then x else x').
Proof.
  destruct (decide P) as [Hp|Hp];
    destruct (decide Q) as [Hq|Hq];
    reflexivity || tauto.
Qed.

(* TODO: Move *)
Proposition decide_true
          {P} {DP: Decidable P} (H: P) {X} (x x':X) :
  (if decide P then x else x') = x.
Proof.
  decided H. reflexivity.
Qed.


(***************************************************************************************)


(** ** Certified programs *)

Definition Cert (spec: M bool) :=
  exists (f: State -> nat), spec ⊑ let* s := get in
                           nSteps (f s).

(** In most cases we know exactly how many steps are needed. *)
Definition nCert n (spec: M bool) := spec ⊑ nSteps n.

Proposition nCert_is_Cert n (spec: M bool) : nCert n spec -> Cert spec.
Proof.
  unfold nCert, Cert.
  intros H.
  exists (fun _ => n).
  smon_rewrite.
  exact H.
Qed.

Local Notation not_terminated := (ret true) (only parsing).
Local Notation terminated := (ret false) (only parsing).

Lemma cert_id : nCert 0 not_terminated.
Proof.
  unfold nCert.
  simp nSteps.
  crush.
Qed.


(** *** Asserting next operations and move PC *)

Definition swallow1 (op: Z) : M unit :=
  let* pc := get' PC in
  let* x := load pc in
  assume (x = toB8 op);;
  put' PC (offset 1 pc).

Equations swallow {n} (ops: vector Z n) : M unit :=
  swallow [] := ret tt;
  swallow (op :: rest) :=
    swallow1 op;;
    swallow rest.

Lemma swallow_spec {n} (ops: vector Z n) :
  swallow ops = let* pc := get' PC in
                let* u := loadMany n pc in
                assume (u = Vector.map toB8 ops);;
                put' PC (offset n pc).
Proof.
  (* TODO: Simplify *)
  induction n.
  - dependent elimination ops.
    simp swallow map.
    simp_loadMany.
    unfold offset.
    smon_rewrite. setoid_rewrite toBits_ofN_bitsToN.
    smon_rewrite.
  - dependent elimination ops as [ @Vector.cons z n ops ].
    simp swallow map. unfold swallow1. rewrite IHn.
    simp_loadMany.
    smon_rewrite.

    apply bind_extensional. intros pc.
    apply bind_extensional. intros op.

    do 3 setoid_rewrite postpone_assume.
    smon_rewrite.
    setoid_rewrite <- confined_put;
      [ | apply (confined_neutral (m:=MEM));
          typeclasses eauto ].

    apply bind_extensional. intros u.
    simpl Vector.map.
    Opaque Vector.map.

    unfold Cells. (* TODO: How can we avoid having to remember this everywhere? *)
    setoid_rewrite assume_cons.
    destruct (decide (op = toB8 z)) as [Hop|Hop]; [ | smon_rewrite ].
    subst op.
    destruct (decide _) as [Hu|Hu]; [ | smon_rewrite ].
    subst u.
    smon_rewrite.
    setoid_rewrite <- Z_action_add.
    do 2 f_equal.
    lia.
Qed.

Instance confined_swallow {n} (ops: vector Z n) :
  Confined (MEM * PC) (swallow ops).
Proof.
  rewrite swallow_spec.
  typeclasses eauto.
Qed.

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
    crush.
    smon_rewrite.
    subst.
    exact (IHn r u (fun v => f (toB8 x :: v)) H).
Qed.


(** ** Basics *)

Ltac cert_start :=
  unfold nCert;
  simp nSteps;
  unfold chain, oneStep;
  repeat setoid_rewrite bind_assoc;
  apply swallow_lemma;
  setoid_rewrite next_1_helper; [ | lia ];
  try (unfold cells_to_bytes, id;
       rewrite next_1_helper; try lia);
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
  setoid_rewrite bind_assoc at 2.
  apply swallow_lemma.
  rewrite step_match_helper; [ | lia ].
  rewrite bind_ret_helper.
  rewrite <- bind_assoc.
  apply (bind_propr _ _ _); [ | crush ].
  simp oneStep'.
  apply (bind_propr _ _ _); crush.
  rewrite ofN_bitsToN, toBits_fromBits.
  reflexivity.
Qed.

Instance chain_propr : PropR chain.
Proof.
  intros u u' Hu v v' Hv.
  unfold chain.
  apply (bind_propr _ _ _).
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


(** ** Mark memory as undefined *)

Definition wipe (u: DSet Addr) : M unit :=
  put' (MEM' u) (fun _ _ _ => None).

Goal forall u, Confined (MEM' u) (wipe u).
  typeclasses eauto.
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

Proposition rel_ret_tt
            mu Y (my my' : M Y)
            `(mu ⊑ ret tt)
            `(my ⊑ my') : mu;; my ⊑ my'.
Proof.
  assert (my' = ret tt;; my') as HH.
  - rewrite ret_bind. reflexivity.
  - rewrite HH. crush; assumption.
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


(** ** Standard cert start *)

Definition stdStart m n {o} (ops: vector Z o) : M (vector B64 n) :=
  let* v := popN n in
  wipeStack (m + n);;
  swallow ops;;
  ret v.

(** By putting [swallow] after [wipeStack] we ensure that [stdStart] fails
    if the operations overlap with (the relevant parts of) the stack. *)

Definition stdDis m n o :=
  let* sp := get' SP in
  let* pc := get' PC in
  assume (nBefore (m * 8) sp # nAfter o pc);;
  assume (nAfter (n * 8) sp # nAfter o pc);;
  ret tt.



(* TODO: Move *)

(** In VectorSpec.v: [shiftin_last] *)


Proposition rew_cons [X m n x] [u: vector X m] [HS: S m = S n] (H: m = n) :
  rew HS in (x :: u) = x :: rew H in u.
Proof.
  destruct H. revert HS. apply EqDec.UIP_K. reflexivity.
Qed.

Proposition shiftin_spec [X n] [x: X] [u: vector X n] (H: (n + 1 = S n)%nat) :
  shiftin x u = rew H in (u ++ [x]).
Proof.
  induction u.
  - revert H. apply EqDec.UIP_K. reflexivity.
  - cbn in *.
    set (HH := Nat.succ_inj _ _ H). rewrite (rew_cons HH).
    f_equal. exact (IHu HH).
Qed.

(** We would have preferred to call this [shiftout_shiftin], but we stick
to the same naming pattern of VectorSpec. *)

Proposition shiftin_shiftout
            [X n] (x: X) (u: vector X n) :
  shiftout (shiftin x u) = u.
Proof.
  induction u.
  - reflexivity.
  - cbn. rewrite IHu. reflexivity.
Qed.

Proposition last_shiftout_shifting [X n] (u: vector X (S n)) :
  shiftin (Vector.last u) (shiftout u) = u.
Proof.
  induction n.
  - dependent elimination u as [[x]]. reflexivity.
  - dependent elimination u as [x :: u].
    cbn. f_equal. exact (IHn u).
Qed.

(** Cf. [List.rev_ind]. *)
Proposition vec_rev_ind
            [A : Type]
            (P : forall {n}, vector A n -> Prop)
            (H_nil: P [])
            (H_cons: forall {n} (u: vector A n) x, P u -> P (shiftin x u))
            {n} (u: vector A n) : P u.
Proof.
  induction n.
  - dependent elimination u. exact H_nil.
  - specialize (H_cons n (shiftout u) (Vector.last u) (IHn (shiftout u))).
    rewrite last_shiftout_shifting in H_cons. exact H_cons.
Qed.

Corollary vec_rev_ind'
          [A : Type]
          (P : forall {n}, vector A n -> Prop)
          (H_nil: P [])
          (H_cons: forall {n} (u: vector A n) x, P u -> P (u ++ [x]))
          {n} (u: vector A n) : P u.
Proof.
  induction u using vec_rev_ind.
  - exact H_nil.
  - set (H := Nat.add_1_r n).
    rewrite (shiftin_spec H).
    destruct H.
    exact (H_cons n u x IHu).
Qed.

Proposition swallow_equation_3 (n : nat) (z : Z) (u : vector Z n) :
  swallow (shiftin z u) = swallow u;;
                          swallow1 z.
Proof.
  set (H := Nat.add_1_r n).
  rewrite (shiftin_spec H).
  destruct H. cbn.
  rewrite swallow_action. simp swallow.
  setoid_rewrite bind_ret_tt.
  reflexivity.
Qed.

Hint Rewrite swallow_equation_3 : swallow.

Hint Rewrite nAfter_empty : nAfter.

(* TODO: Move *)
Proposition nAfter_equation_2 a n :
  nAfter (S n) a = (!{ a } ∪ nAfter n (offset 1 a))%DSet.
Proof.
  unfold nAfter.
  unfold union.
  apply extensionality.
  intros x.
  setoid_rewrite def_spec.
  split.
  - intros [i [Hi Hx]].
    by_lia (i = n \/ i < n) as Hii.
    destruct Hii as [Hi1|Hi2].
Admitted.

Proposition wipe_swallow_precondition u {n} (ops: vector Z n) :
  wipe u;;
  swallow ops = let* pc := get' PC in
                assume (u # nAfter n pc);;
                wipe u;;
                swallow ops.
Proof.
  induction ops using vec_rev_ind.
  - simp_assume.
    smon_ext s.
    unfold Addr.
    rewrite get_spec.
    smon_rewrite.
    apply bind_extensional. intros [].
    rewrite decide_true.
    + reflexivity.
    + now rewrite nAfter_empty.

  - simp swallow.
    rewrite <- bind_assoc.
    rewrite IHops at 1.
    rewrite bind_assoc.
    smon_ext' PC pc.
    repeat rewrite lens_put_get.
    destruct (decide (u # nAfter n pc)) as [Hd|Hd].
    + destruct (decide (u # nAfter (S n) pc)) as [Hd'|Hd'].
      * smon_rewrite.
      * smon_rewrite.
        assert (offset n pc ∈ u) as Hu.
        -- clear IHops.
           apply not_nAfter_disjoint_spec in Hd'.
           destruct Hd' as [i [Hi Hu]].
           by_lia (i = n \/ i < n) as Hii.
           destruct Hii as [[]|Hii]; [exact Hu|].
           contradict Hd.
           unfold disjoint.
           intros Hd.
           apply (Hd (offset i pc)).
           split.
           ++ exact Hu.
           ++ unfold nAfter.
              rewrite def_spec.
              exists i.
              split.
              ** lia.
              ** reflexivity.
        -- rewrite swallow_spec.

(********* Continue from here *********)

    setoid_rewrite nAfter_empty.
    unfold nAfter.


setoid_rewrite nAfter_spec.

  smon_ext s. rewrite get_spec. smon_rewrite. apply bind_extensional. intros [].
  set (pc := proj _).
  destruct (decide _) as [H|H]; smon_rewrite.
    apply not_nAfter_disjoint_evidence in H.
  destruct H as [x [Hx [i [Hi Ho]]]];
    subst x.



Proposition stdStart_stdDis m n {o} (ops: vector Z o) :
  stdDis m n o;; stdStart m n ops = stdStart m n ops.
Proof.
  unfold stdDis, stdStart.
  smon_ext s.
  setoid_rewrite get_spec.
  repeat setoid_rewrite bind_assoc.
  smon_rewrite.

  destruct (decide (nBefore _ _ # _)) as [H0|H];
    [ destruct (decide (nAfter _ _ # _)) as [H0'|H] | ];
    [ smon_rewrite | | ];
    apply not_nAfter_disjoint_evidence in H;
    destruct H as [x [Hx [i [Hi Ho]]]];
    subst x.

  - setoid_rewrite popN_spec.
    setoid_rewrite popMany_spec.
    smon_rewrite.

    setoid_rewrite <- (confined_loadMany _ _ _ _ _).
    setoid_rewrite get_spec at 1.
    smon_rewrite.

    set (sp := (@proj _ _ SP s)).
    set (pc := (@proj _ _ PC s)).
    set (sp' := (toB64 ((n * 8)%nat + sp))).

    do 2 (setoid_rewrite <- (confined_put SP sp');
          (* TODO: Why is this needed? *)
          [ | apply (confined_neutral (Hm:=independent_MEM_SP));
              typeclasses eauto ] ).

    setoid_rewrite <- (confined_put SP sp');
      [ | apply (confined_neutral (m := MEM * PC)); typeclasses eauto ].


          (* TODO: Why is this needed? *)
          [ | apply (confined_neutral (Hm:=independent_MEM_SP));
              typeclasses eauto ] ).

          setoid_rewrite <- (confined_put SP sp');
      (* TODO: Why is this needed? *)
      [ | apply (confined_neutral (Hm:=independent_MEM_SP));
          typeclasses eauto ].

    admit.


    setoid_rewrite get_spec.
    setoid_rewrite get_spec.



unfold wipe.


  smon_rewrite.



(** ** Zero check *)

(* TODO: Move / remove *)
Definition inc' L z :=
  let* a := get' L in
  put' L (offset z a).

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
           not_terminated}.
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
  apply (bind_propr _ _ _).
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
