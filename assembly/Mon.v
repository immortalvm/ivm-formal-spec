Require Import Utf8.

Require Import Equations.Equations.
Set Equations With UIP.

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Import Assembly.Convenience.
Require Import Assembly.Dec.


(** ** Error/state monad *)

Declare Scope monad_scope.

Reserved Notation "ma >>= f" (at level 69, left associativity).

Class SMonad (S: Type) (m: Type -> Type): Type :=
{
  ret {A} : A -> m A;
  bind {A B} (_: m A) : (A -> m B) -> m B
    where "ma >>= f" := (bind ma f);

  bind_ret A (ma: m A) : ma >>= ret = ma;
  ret_bind A (a: A) B (f: A -> m B) : ret a >>= f = f a;
  bind_assoc A (ma: m A) B f C (g: B -> m C) : (ma >>= f) >>= g = ma >>= (fun a => f a >>= g);

  err {A} : m A;
  bind_err A (ma: m A) B : ma >>= (fun _ => err) = (err : m B);
  err_bind A B (f: A -> m B) : err >>= f = err;

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

Notation "'assert*' P 'in' result" :=
  (if (decision P%type) then result else err)
    (at level 60, right associativity,
     format "'[hv' assert*  P  'in'  '//' result ']'") : monad_scope.

Notation "'assert*' P 'as' H 'in' result" :=
  (match (decision P%type) with
   | left H => result
   | right _ => err
   end) (at level 60, right associativity,
         format "'[hv' assert*  P  'as'  H  'in'  '//' result ']'") : monad_scope.


(** ** Rewriting *)

Open Scope monad_scope.

Instance bind_proper {S m} {SM: SMonad S m} {A B}:
  Proper ( eq ==> pointwise_relation A eq ==> eq ) (@bind S m SM A B).
Proof using.
  intros ma ma' H_ma f f' H_f. f_equal.
  - exact H_ma.
  - extensionality a. f_equal.
Qed.

Lemma unit_lemma {A} (f: unit -> A) : f = fun _ => f tt.
Proof using.
  extensionality x. destruct x. reflexivity.
Qed.

Lemma bind_ret' {S m} {SM: SMonad S m} (mu: m unit) : mu;; ret tt = mu.
Proof using.
  rewrite <- bind_ret.
  setoid_rewrite unit_lemma.
  reflexivity.
Qed.

Lemma put_put' {S m} {SM: SMonad S m} (s s' : S) {B} (f: unit -> m B) :
  put s;; (put s' >>= f) = put s' >>= f.
Proof using.
  rewrite <- bind_assoc, put_put.
  reflexivity.
Qed.

Create HintDb smon discriminated.

(** As of Coq 8.11.1, [rewrite_strat] does not work reliably with "hints"
    and "repeat", see https://github.com/coq/coq/issues/4197.
    See also: https://stackoverflow.com/a/39348396 *)

Hint Rewrite @bind_ret using (typeclasses eauto) : smon.
Hint Rewrite @bind_ret' using (typeclasses eauto) : smon.
Hint Rewrite @ret_bind using (typeclasses eauto) : smon.
Hint Rewrite @bind_assoc using (typeclasses eauto) : smon.
Hint Rewrite @bind_err using (typeclasses eauto) : smon.
Hint Rewrite @err_bind using (typeclasses eauto) : smon.
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
      extensionality s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - intros A a B f.
      extensionality s.
      reflexivity.
    - intros A ma B f C g.
      extensionality s.
      destruct (ma s) as [[s' a]|]; reflexivity.
    - intros A ma B.
      extensionality s.
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
  Proof using.
    unfold from_est.
    simpl.
    extensionality s.
    destruct (ma s) as [[s' a]|]; reflexivity.
  Qed.

  Lemma est_unique m `{SMonad S m} F `{SMorphism EST (SM0:=est_smonad) m F} A (ma: EST A) : F A ma = from_est ma.
  Proof using.
    rewrite <- est_characterization at 1.
    unfold from_est at 1.
    rewrite morph_bind, morph_get. unfold from_est. f_equal.
    extensionality s.
    destruct (ma s) as [[s' a]|].
    - rewrite morph_bind, morph_put. f_equal.
      extensionality u. destruct u.
      rewrite morph_ret. reflexivity.
    - rewrite morph_err. reflexivity.
  Qed.

  Global Instance est_morphism m `{SMonad S m}: SMorphism EST m (@from_est m _).
  Proof using.
    split.
    - intros A a. unfold from_est. simpl.
      rewrite get_put, get_ret. reflexivity.
    - intros A ma B f.
      unfold from_est.
      simpl.
      rewrite bind_assoc.
      f_equal.
      extensionality s.
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
  Proof using Hdx Hdy.
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
  Proof using Hd.
    split; intros; now independent_rewrite.
  Qed.

End product_section.

(** The projections from a record type have the same property. *)
