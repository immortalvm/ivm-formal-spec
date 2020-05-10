Require Import Utf8.

Require Import Equations.Equations.
Set Equations With UIP.

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.


(** ** Error/state monad *)

Declare Scope monad_scope.

Reserved Notation "ma >>= f" (at level 69, left associativity).

Class SMonad (S: Type) (m: Type -> Type): Type :=
{
  ret {A} : A -> m A;
  bind {A B} (_: m A) : (A -> m B) -> m B
    where "ma >>= f" := (bind ma f);

  monad_right A (ma: m A) : ma >>= ret = ma;
  monad_left A (a: A) B (f: A -> m B) : ret a >>= f = f a;
  monad_assoc A (ma: m A) B f C (g: B -> m C) : (ma >>= f) >>= g = ma >>= (fun a => f a >>= g);

  err {A} : m A;
  err_right A (ma: m A) B : ma >>= (fun _ => err) = (err : m B);
  err_left A B (f: A -> m B) : err >>= f = err;

  get : m S;
  put (s: S) : m unit;
  put_put s s' : put s >>= (fun _ => put s') = put s';
  put_get s B (f: S -> m B) : put s >>= (fun _ => get >>= f) = put s >>= fun _ => f s;
  get_put B (f: S -> m B) : get >>= (fun s => put s >>= (fun _ => f s)) = get >>= f;
  get_ret B (mb: m B) : get >>= (fun _ => mb) = mb;
  get_get B (f: S -> S -> m B) : get >>= (fun s => get >>= (fun s' => f s s')) = get >>= (fun s => f s s);
}.

(* Note to self:
* Order of associativity switched since ivm.v.
* I had to move the [B] argument to [bind] to make it an instance of [Proper] (see below).
*)

Notation "ma >>= f" := (bind ma f) : monad_scope.

(* We prefer a notation which does not require do-end blocks. *)
Notation "'let*' a := ma 'in' mb" := (bind ma (fun a => mb))
                                       (at level 60, right associativity,
                                        format "'[hv' let*  a  :=  ma  'in'  '//' mb ']'") : monad_scope.
Notation "ma ;; mb" := (bind ma (fun _ => mb))
                         (at level 60, right associativity,
                          format "'[hv' ma ;;  '//' mb ']'") : monad_scope.


Section state_section.

  Context (S: Type).

  Open Scope monad_scope.

  Section m_section.

    Context m `{SM: SMonad S m}.

    Global Instance bind_proper {A B}:
      Proper ( eq ==> pointwise_relation A eq ==> eq ) (@bind S m SM A B).
    Proof.
      intros ma ma' H_ma f f' H_f. f_equal.
      - exact H_ma.
      - apply functional_extensionality. intros a. f_equal.
    Qed.

    (* TODO: Is this really needed (or even useful)? *)
    Global Instance put_proper : Proper ( eq ==> eq ) (@put S m SM).
    Proof.
      intros s s' Hs. f_equal. exact Hs.
    Qed.

    Global Instance ret_proper A : Proper ( eq ==> eq ) (@ret S m SM A).
    Proof.
      intros a a' Ha. f_equal. exact Ha.
    Qed.

  End m_section.


  Class SMorphism m0 `{SM0: SMonad S m0} m1 `{SM1: SMonad S m1} (F: forall {A}, m0 A -> m1 A) :=
  {
    morph_ret A (a: A) : F (ret a) = ret a;
    morph_bind A (ma: m0 A) B (f: A -> m0 B) : F (ma >>= f) = (F ma) >>= (fun x => F (f x));
    morph_err A : F (err : m0 A) = err;
    morph_get : F get = get;
    morph_put s : F (put s) = put s;
  }.


  (** Initial SMonad *)

  Definition EST A : Type := S -> option (S * A).

  #[refine]
  Global Instance est_smonad : SMonad S EST :=
  {
    ret A a s := Some (s, a);
    bind A B ma f s :=
      match ma s with
      | None => None
      | Some (s', a) => f a s'
      end;
    err _ _ := None;
    get s := Some (s, s);
    put s _ := Some (s, tt);
  }.
  Proof.
    - intros A ma.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - intros A a B f.
      apply functional_extensionality. intros s.
      reflexivity.
    - intros A ma B f C g.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - intros A ma B.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Defined.

  Definition from_est {m} `{SMonad S m} {A} (ma: EST A) : m A :=
    let* s := get in
    match ma s with
    | None => err
    | Some (s', a) => put s';; ret a
    end.

  Lemma est_characterization A (ma: EST A) : from_est ma = ma.
  Proof.
    unfold from_est.
    simpl.
    apply functional_extensionality. intros s.
    destruct (ma s) as [[s' a]|]; reflexivity.
  Qed.

  Lemma est_unique m `{SMonad S m} F `{SMorphism EST (SM0:=est_smonad) m F} A (ma: EST A) : F A ma = from_est ma.
  Proof.
    rewrite <- est_characterization at 1.
    unfold from_est at 1.
    rewrite morph_bind, morph_get. unfold from_est. f_equal.
    apply functional_extensionality. intros s.
    destruct (ma s) as [[s' a]|].
    - rewrite morph_bind, morph_put. f_equal.
      apply functional_extensionality. intros [].
      rewrite morph_ret. reflexivity.
    - rewrite morph_err. reflexivity.
  Qed.

  Global Instance est_morphism m `{SMonad S m}: SMorphism EST m (@from_est m _).
  Proof.
    split.
    - intros A a. unfold from_est. simpl.
      rewrite get_put, get_ret. reflexivity.
    - intros A ma B f.
      unfold from_est.
      simpl.
      rewrite monad_assoc.
      f_equal.
      apply functional_extensionality. intros s.
      destruct (ma s) as [[s' a]|].
      + rewrite -> monad_assoc, monad_left, put_get.
        destruct (f a s') as [[s'' b]|].
        * rewrite <- monad_assoc, put_put. reflexivity.
        * rewrite err_right. reflexivity.
      + rewrite err_left. reflexivity.
    - intros A.
      unfold from_est. simpl. rewrite err_right. reflexivity.
    - unfold from_est. simpl.
      rewrite get_put, monad_right. reflexivity.
    - intros s.
      unfold from_est. simpl.
      rewrite get_ret, <- monad_right. f_equal.
      apply functional_extensionality. intros []. reflexivity.
  Qed.

End state_section.


(** ** Projections *)

Class Proj (S: Type) (X: Type) :=
{
  proj: S -> X;
  update: S -> X -> S;
  proj_update (s: S) (x: X) : proj (update s x) = x;
  update_proj (s: S) : update s (proj s) = s;
  update_update (s: S) (x: X) (x': X) : update (update s x) x' = update s x';
}.

Section proj_section.

  Open Scope monad_scope.

  Context {S: Type}
          (m: Type -> Type) `{SM: SMonad S m}
          {X: Type} `(PM: Proj S X).

  #[refine]
  Global Instance proj_smonad: SMonad X m :=
  {
    ret := @ret S m SM;
    bind := @bind S m SM;
    err := @err S m SM;
    get := let* s := get in ret (proj s);
    put x := let* s := get in put (update s x);
  }.
  Proof.
    (* Trivial *)
    - intros A ma. rewrite monad_right. reflexivity.
    - intros A a B f. rewrite monad_left. reflexivity.
    - intros A ma B f C g. rewrite monad_assoc. reflexivity.
    - intros A ma B. rewrite err_right. reflexivity.
    - intros A ma B. rewrite err_left. reflexivity.

    (* Almost trivial *)
    - intros x x'.
      rewrite monad_assoc.
      f_equal. apply functional_extensionality. intros s.
      rewrite put_get, put_put, update_update. reflexivity.
    - intros x B f.
      repeat rewrite monad_assoc.
      f_equal. apply functional_extensionality. intros s.
      rewrite put_get, proj_update, monad_left.
      reflexivity.
    - intros B f.
      repeat setoid_rewrite monad_assoc.
      setoid_rewrite monad_left.
      rewrite get_get.
      setoid_rewrite update_proj.
      setoid_rewrite get_put.
      reflexivity.
    - intros B mb.
      rewrite monad_assoc.
      setoid_rewrite monad_left.
      rewrite get_ret.
      reflexivity.
    - intros B f.
      repeat setoid_rewrite monad_assoc.
      repeat setoid_rewrite monad_left.
      rewrite get_get.
      reflexivity.
  Defined.

End proj_section.

Class Disjoint {S: Type}
      {X: Type} (PX: Proj S X)
      {Y: Type} (PY: Proj S Y) : Prop :=
{
  projY_updateX (s: S) (x: X) : proj (update s x) = proj s :> Y;
  projX_updateY (s: S) (y: Y) : proj (update s y) = proj s :> X;
  disjoint_commute (s: S) (x: X) (y: Y) :
    update (update s x) y = update (update s y) x;
}.

(** To see that [disjoint_commute] does not follow from the other
    properties, consider a square staircase. *)

Section product_section.

  Context {X Y: Type}.

  (* Since this instance is in a section and not marked global,
     it is removed from the instance database below. *)

  Program Instance proj_fst : Proj (X * Y) X :=
  {
    proj := fst;
    update s x := (x, snd s);
  }.

  Program Instance proj_snd : Proj (X * Y) Y :=
  {
    proj := snd;
    update s y := (fst s, y);
  }.

  Program Instance disjoint_projs : Disjoint proj_fst proj_snd.

  Context {S} (Hx: Proj S X) (Hy: Proj S Y) {Hd: Disjoint Hx Hy}.

  Instance disjoint_symm : Disjoint Hy Hx.
  Proof.
    split.
    - apply projX_updateY.
    - apply projY_updateX.
    - symmetry. apply disjoint_commute.
  Qed.

  #[refine]
  Instance proj_prod : Proj S (X * Y) :=
  {
    proj s := (proj s, proj s);
    update s pair := update (update s (fst pair)) (snd pair);
  }.
  Proof.
    - intros s [x y]. simpl.
      rewrite projX_updateY, proj_update, proj_update.
      reflexivity.
    - intros. simpl.
      do 2 rewrite update_proj.
      reflexivity.
    - intros s [x y] [x' y']. simpl.
      do 2 (rewrite disjoint_commute, update_update).
      reflexivity.
  Defined.

  Context Z (Hz: Proj S Z) (Hdx: Disjoint Hx Hz) (Hdy: Disjoint Hy Hz).

  Instance disjoint_prod : Disjoint proj_prod Hz.
  Proof.
    split.
    - intros s [x y].
      simpl.
      transitivity (proj (update s x)).
      + rewrite projY_updateX. reflexivity.
      + rewrite projY_updateX. reflexivity.
    - intros s z. simpl. f_equal.
      + rewrite projX_updateY. reflexivity.
      + rewrite projX_updateY. reflexivity.
    - intros s [x y] z. simpl.
      rewrite disjoint_commute, (disjoint_commute (Disjoint:=Hdx)). reflexivity.
  Qed.

End product_section.


(* From Equations.Init. *)
Notation "&{ x : A & y }" := (@sigma A (fun x : A => y)%type) (x at level 99).

Notation "&( x , .. , y & z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
    (right associativity, at level 4,
     format "&( x ,  .. ,  y  &  z )").

Import Coq.Lists.List.ListNotations.
Open Scope list_scope.

Equations pairwise_disjoint {S: Type} (Ts: list &{ X : Type & Proj S X }) : Prop :=
  pairwise_disjoint [] := True;
  pairwise_disjoint (p :: rest) := List.Forall (fun q => Disjoint (pr2 p) (pr2 q)) rest
                                  /\ pairwise_disjoint rest.



(** The projections from a record type have the same property.

Assuming functional extensionality and proof irrelevance, we also have the
converse: If [Proj S X] then [S ≅ X * S'] where [S' = { f: X -> S | forall x y,
update (f x) y = f y }]. *)

Require Coq.Logic.ProofIrrelevance.

Section inv_proj_section.

  Import Coq.Logic.ProofIrrelevance.

  Context S X (PX: Proj S X).

  Definition S' := { f: X -> S | forall x y, update (f x) y = f y }.

  #[refine]
  Instance inv_proj : Proj S S' :=
  {
    proj s := exist _ (update s) _;
    update s f := proj1_sig f (proj s);
  }.
  Proof.
    - intros x y. rewrite update_update. reflexivity.
    - intros s [f H].
      simpl.
      apply eq_sig_hprop.
      + intros. apply proof_irrelevance.
      + simpl. apply functional_extensionality. intros x.
        rewrite H. reflexivity.
    - intro s. simpl.
      rewrite update_proj. reflexivity.
    - intros s [f Hf] [g Hg]. simpl.
      rewrite <- (Hf (proj s)), proj_update. reflexivity.
  Defined.

  Instance inv_proj_disjoint : Disjoint inv_proj PX.
  Proof.
    split.
    - intros s [f Hf]. simpl.
      rewrite <- (Hf (proj s)), proj_update. reflexivity.
    - intros s x. simpl.
      apply eq_sig_hprop.
      + intros. apply proof_irrelevance.
      + simpl. apply functional_extensionality. intros x'.
        rewrite update_update. reflexivity.
    - intros s [f Hf] x. simpl.
      rewrite proj_update, Hf. reflexivity.
  Qed.

  Lemma inv_proj_inv (s: S) :
    let (fH, x) := proj (Proj:=proj_prod _ _) s in
    proj1_sig fH x = s.
  Proof.
    simpl. rewrite update_proj. reflexivity.
  Qed.

End inv_proj_section.


(** No side-effects *)

Section no_side_effects_section.

  Open Scope monad_scope.

  Context (S: Type)
          (m: Type -> Type)
          {M: SMonad S m}.

  Class NoSideEffects {A} (ma: m A) : Prop :=
    noSideEffects: forall B (mb: m B), ma;; mb = mb.

  Global Instance noEff_unit {A} (ma: m A) (H: ma;; ret tt = ret tt): NoSideEffects ma.
  Proof.
    intros B mb.
    transitivity (ma;; ret tt;; mb).
    - setoid_rewrite monad_left. reflexivity.
    - rewrite <- monad_assoc, H, monad_left. reflexivity.
  Qed.

  Global Instance noEff_ret {A} (x: A) : NoSideEffects (ret x).
  Proof.
    apply noEff_unit. rewrite monad_left. reflexivity.
  Qed.

  Global Instance noEff_bind
           {A B} (ma: m A) (f: A -> m B)
           {Ha: NoSideEffects ma}
           {Hb: forall x, NoSideEffects (f x)} : NoSideEffects (bind ma f).
  Proof.
    intros C mc.
    rewrite monad_assoc.
    setoid_rewrite Hb.
    rewrite Ha.
    reflexivity.
  Qed.

End no_side_effects_section.

Existing Instance est_smonad.

(** [NoSideEffects get] does not hold in general.
    (Think about logging/monitoring.) *)

Instance noEff_get {S} : NoSideEffects S (EST S) get.
Proof.
  intros B mb.
  simpl.
  apply functional_extensionality.
  intros s.
  reflexivity.
Qed.


(** The trivial [SMonad] *)

Section trivial_smonad_section.

  Context (S: Type).

  Local Ltac crush :=
    repeat (match goal with
            | [|- unit] => exact tt
            | [|- forall (_:unit),_] => intros []
            | [|- ?x = ?y :> unit] => destruct x; destruct y
            end
            || intro
            || reflexivity
            || assumption).

  #[refine]
  Instance trivial_smonad : SMonad S (fun _ => unit) := { }.
  all: crush.
  Defined.

  (** Clearly, this is the terminal [SMonad]. Moreover, this means that
      there are non-trivial "termination properties" that hold in all
      [SMonads]. Thus, we shall express and prove such properties only for
      the initial [SMonad]. *)

End trivial_smonad_section.
