Require Import Utf8.

Require Import Equations.Equations.
Set Equations With UIP.

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Import Assembly.Convenience.


(** ** Error/state monad *)

Declare Scope monad_scope.

Reserved Notation "ma >>= f" (at level 69, left associativity).

(* TODO: Rename?
   monad_right -> bind_ret
   monad_left  -> ret_bind
   monad_assoc -> bind_assoc
   err_right -> bind_err
   err_left -> err_bind *)

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


(** ** Rewriting *)

Open Scope monad_scope.

Instance bind_proper {S m} {SM: SMonad S m} {A B}:
  Proper ( eq ==> pointwise_relation A eq ==> eq ) (@bind S m SM A B).
Proof.
  intros ma ma' H_ma f f' H_f. f_equal.
  - exact H_ma.
  - apply functional_extensionality. intros a. f_equal.
Qed.

Lemma unit_lemma {A} (f: unit -> A) : f = fun _ => f tt.
Proof.
  apply functional_extensionality. intros []. reflexivity.
Qed.

Lemma monad_right' {S m} {SM: SMonad S m} (mu: m unit) : mu;; ret tt = mu.
Proof.
  rewrite <- monad_right.
  setoid_rewrite unit_lemma.
  reflexivity.
Qed.

Lemma put_put' {S m} {SM: SMonad S m} (s s' : S) {B} (f: unit -> m B) :
  put s;; (put s' >>= f) = put s' >>= f.
Proof.
  rewrite <- monad_assoc, put_put.
  reflexivity.
Qed.

Create HintDb smon discriminated.

(** As of Coq 8.11.1, [rewrite_strat] does not work reliably with "hints"
    and "repeat", see https://github.com/coq/coq/issues/4197.
    See also: https://stackoverflow.com/a/39348396 *)

Hint Rewrite @monad_right using (typeclasses eauto) : smon.
Hint Rewrite @monad_right' using (typeclasses eauto) : smon.
Hint Rewrite @monad_left using (typeclasses eauto) : smon.
Hint Rewrite @monad_assoc using (typeclasses eauto) : smon.
Hint Rewrite @err_right using (typeclasses eauto) : smon.
Hint Rewrite @err_left using (typeclasses eauto) : smon.
Hint Rewrite @put_put using (typeclasses eauto) : smon.
Hint Rewrite @put_put' using (typeclasses eauto) : smon.
Hint Rewrite @put_get using (typeclasses eauto) : smon.
Hint Rewrite @get_put using (typeclasses eauto) : smon.
Hint Rewrite @get_ret using (typeclasses eauto) : smon.
Hint Rewrite @get_get using (typeclasses eauto) : smon.

(** For some reason [rewrite_strat (repeat (outermost (hints smon)))]
    stops prematurely. *)
(* Ltac smon_rewrite := repeat (rewrite_strat (choice (outermost (hints smon)) (outermost unit_lemma))). *)

Ltac smon_rewrite1 := rewrite_strat (choice (outermost (hints smon))
                                    (* Add more special cases here if necessary. *)
                                    (choice (outermost get_put)
                                    (choice (outermost get_get)
                                            (outermost unit_lemma)))).

Ltac smon_rewrite := repeat smon_rewrite1.

Goal forall {S m A B} {SM: SMonad S m} (g: S -> A) (f: A -> m B),
    let* s := get in put s;; f (g s) = let* s := get in f (g s).
  intros S m A B SM g f.
  smon_rewrite.
  reflexivity.
Qed.

Section state_section.

  Context (S: Type).

  (* TODO: Is this really needed (or even useful)?
  Section m_section.

    Context m `{SM: SMonad S m}.

    Global Instance put_proper : Proper ( eq ==> eq ) (@put S m SM).
    Proof.
      intros s s' Hs. f_equal. exact Hs.
    Qed.

    Global Instance ret_proper A : Proper ( eq ==> eq ) (@ret S m SM A).
    Proof.
      intros a a' Ha. f_equal. exact Ha.
    Qed.

  End m_section.
   *)

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
      + smon_rewrite.
        destruct (f a s') as [[s'' b]|]; now smon_rewrite.
      + now smon_rewrite.
    - intros A.
      unfold from_est. simpl. now smon_rewrite.
    - unfold from_est. simpl. now smon_rewrite.
    - intros s. unfold from_est. simpl. now smon_rewrite.
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

(** Cf. [smon_rewrite] above. *)
Create HintDb proj discriminated.
Hint Rewrite @proj_update using (typeclasses eauto) : proj.
Hint Rewrite @update_proj using (typeclasses eauto) : proj.
Hint Rewrite @update_update using (typeclasses eauto) : proj.
Ltac proj_rewrite1 := rewrite_strat (outermost (hints proj)).
Ltac proj_rewrite := repeat proj_rewrite1.

Section proj_section.

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
    all: intros; repeat (proj_rewrite1 || smon_rewrite1); reflexivity.
  Defined.

End proj_section.

Class Independent {S: Type}
      {X: Type} (PX: Proj S X)
      {Y: Type} (PY: Proj S Y) : Prop :=
{
  projY_updateX (s: S) (x: X) : proj (update s x) = proj s :> Y;
  projX_updateY (s: S) (y: Y) : proj (update s y) = proj s :> X;
  independent_commute (s: S) (x: X) (y: Y) :
    update (update s x) y = update (update s y) x;
}.

(** To see that [independent_commute] does not follow from the other
    properties, consider a square staircase. *)

Create HintDb independent discriminated.
Hint Rewrite @projY_updateX using (typeclasses eauto) : independent.
Hint Rewrite @projX_updateY using (typeclasses eauto) : independent.
Hint Rewrite @independent_commute using (typeclasses eauto) : independent.
Ltac independent_rewrite1 := rewrite_strat (outermost (hints independent)).
Ltac independent_rewrite := repeat independent_rewrite1.

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

  Program Instance independent_projs : Independent proj_fst proj_snd.

  Context {S} (PX: Proj S X) (PY: Proj S Y) {Hd: Independent PX PY}.

  #[refine]
  Instance proj_prod : Proj S (X * Y) :=
  {
    proj s := (proj s, proj s);
    update s pair := update (update s (fst pair)) (snd pair);
  }.
  Proof.
    all: idestructs; now repeat (independent_rewrite1 || proj_rewrite || simpl).
  Defined.

  Context Z (PZ: Proj S Z) (Hdx: Independent PX PZ) (Hdy: Independent PY PZ).

  Global Instance independent_prod : Independent proj_prod PZ.
  Proof.
    split.
    - intros s [x y]. simpl.
      transitivity (proj (update s x)); now independent_rewrite.
    - intros s z. simpl. f_equal; now independent_rewrite.
    - intros s [x y] z. simpl. now independent_rewrite.
  Qed.

  (** Beware: We do not make this global sine together with
      [independent_commute] it can send [typeclasses eauto]
      into an infinite loop. *)
  Instance independent_symm : Independent PY PX.
  Proof.
    split; intros; now independent_rewrite.
  Qed.

End product_section.

(** The projections from a record type have the same property. *)

Section relation_section.

  Context {S X} (HX: Proj S X).

  Definition aligned (s s' : S) :=
    update s (proj s') = s'.

  (** In other words, [aligned s s'] means that [s] and [s'] are equal
      except for their projections onto [X]. *)

  Instance aligned_equivalence : Equivalence aligned.
  Proof.
    split.
    - intros s. unfold aligned. rewrite update_proj. reflexivity.
    - intros s s'. unfold aligned. intros H. rewrite <- H.
      rewrite update_update, update_proj. reflexivity.
    - intros s1 s2 s3. unfold aligned. intros H12 H23.
      rewrite <- H12 in H23.
      rewrite update_update in H23.
      exact H23.
  Qed.

  Context (R: relation X).

  Definition proj_relation : relation S :=
    fun s s' => aligned s s' /\ R (proj s) (proj s').

  Global Instance proj_relation_reflexive {H_reflexive: Reflexive R} : Reflexive proj_relation.
  Proof.
    unfold proj_relation. intros s. split; reflexivity.
  Qed.

  Global Instance proj_relation_symmetric {H_symmetric: Symmetric R} : Symmetric proj_relation.
  Proof.
    unfold proj_relation. intros s s' [? ?].
    split; symmetry; assumption.
  Qed.

  Global Instance proj_relation_transitive {H_transitive: Transitive R} : Transitive proj_relation.
  Proof.
    unfold proj_relation. intros s1 s2 s3 [? ?] [? ?].
    split.
    - transitivity s2; assumption.
    - transitivity (proj s2); assumption.
  Qed.

End relation_section.

Require Import Assembly.Convenience.

Section proper_section.

  Context {S} {RS: relation S}.

  Local Notation M := (EST S).

  Definition est_relation {A} (RA: relation A) : relation (M A) :=
    (RS ==> option_relation (prod_relation RS RA))%signature.

  Local Notation RM := (est_relation).

  Global Instance ret_propR {A} (RA: relation A) : Proper (RA ==> RM RA) (@ret _ M _ A).
  Proof.
    intros a a' Ha.
    intros s s' Hs.
    simpl.
    split; assumption.
  Qed.

  Global Instance bind_propR {A B} (RA: relation A) (RB: relation B) :
    Proper (RM RA ==> (RA ==> RM RB) ==> RM RB) (@bind _ M _ A B).
  Proof.
    intros ma ma' Hma f f' Hf.
    intros s s' Hs. simpl.
    specialize (Hma s s' Hs).
    destruct (ma s) as [(t,a)|]; destruct (ma' s') as [(t',a')|].
    - destruct Hma as [Ht Ha].
      exact (Hf _ _ Ha _ _ Ht).
    - contradict Hma.
    - exact I.
    - exact I.
  Qed.

  Global Instance err_propR {A} (RA: relation A): Proper (RM RA) err.
  Proof.
    intros s s' Hs. exact I.
  Qed.

  Global Instance get_propR : Proper (RM RS) get.
  Proof.
    intros s s' Hs.
    split; assumption.
  Qed.

  Global Instance put_propR : Proper (RS ==> RM eq) put.
  Proof.
    intros s s' Hs.
    intros t t' Ht.
    split.
    - assumption.
    - reflexivity.
  Qed.

End proper_section.
