From Assembly Require Import Init Lens.

Unset Suggest Proof Using.


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
  (if (decide P%type) then result else err)
    (at level 60, right associativity,
     format "'[hv' assert*  P  'in'  '//' result ']'") : monad_scope.

Notation "'assert*' P 'as' H 'in' result" :=
  (match (decide P%type) with
   | left H => result
   | right _ => err
   end) (at level 60, right associativity,
         format "'[hv' assert*  P  'as'  H  'in'  '//' result ']'") : monad_scope.


(** ** Rewriting *)

Open Scope monad_scope.

Instance bind_proper {S m} {SM: SMonad S m} {A B}:
  Proper ( eq ==> pointwise_relation A eq ==> eq ) (@bind S m SM A B).
Proof.
  intros ma ma' H_ma f f' H_f. f_equal.
  - exact H_ma.
  - extensionality a. f_equal.
Qed.

Lemma unit_lemma {A} (f: unit -> A) : f = fun _ => f tt.
Proof.
  extensionality x. destruct x. reflexivity.
Qed.

Lemma bind_ret' {S m} {SM: SMonad S m} (mu: m unit) : mu;; ret tt = mu.
Proof.
  rewrite <- bind_ret.
  setoid_rewrite unit_lemma.
  reflexivity.
Qed.

Lemma put_put' {S m} {SM: SMonad S m} (s s' : S) {B} (f: unit -> m B) :
  put s;; (put s' >>= f) = put s' >>= f.
Proof.
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

  Definition EST A : Type := S -> option (A * S).

  #[refine]
  Global Instance est_smonad : SMonad S EST :=
  {
    ret A a s := Some (a, s);
    bind A B ma f s :=
      match ma s with
      | None => None
      | Some (a, s') => f a s'
      end;
    err _ _ := None;
    get s := Some (s, s);
    put s _ := Some (tt, s);
  }.
  Proof.
    - intros A ma.
      extensionality s.
      destruct (ma s) as [[a s']|]; reflexivity.
    - intros A a B f.
      extensionality s.
      reflexivity.
    - intros A ma B f C g.
      extensionality s.
      destruct (ma s) as [[a s']|]; reflexivity.
    - intros A ma B.
      extensionality s.
      destruct (ma s) as [[a s']|]; reflexivity.
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
    | Some (a, s') => put s';; ret a
    end.

  Lemma est_characterization A (ma: EST A) : from_est ma = ma.
  Proof.
    unfold from_est.
    simpl.
    extensionality s.
    destruct (ma s) as [[a s']|]; reflexivity.
  Qed.

  Lemma est_unique m `{SMonad S m} F `{SMorphism EST (SM0:=est_smonad) m F} A (ma: EST A) : F A ma = from_est ma.
  Proof.
    rewrite <- est_characterization at 1.
    unfold from_est at 1.
    rewrite morph_bind, morph_get. unfold from_est. f_equal.
    extensionality s.
    destruct (ma s) as [[a s']|].
    - rewrite morph_bind, morph_put. f_equal.
      extensionality u. destruct u.
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
      rewrite bind_assoc.
      f_equal.
      extensionality s.
      destruct (ma s) as [[a s']|].
      + smon_rewrite.
        destruct (f a s') as [[b s'']|]; now smon_rewrite.
      + now smon_rewrite.
    - intros A.
      unfold from_est. simpl. now smon_rewrite.
    - unfold from_est. simpl. now smon_rewrite.
    - intros s. unfold from_est. simpl. now smon_rewrite.
  Qed.

End state_section.


(** ** Lenses *)

Section lens_section.

  Context {S: Type}
          (m: Type -> Type) `{SM: SMonad S m}
          {X: Type} `(LX: Lens S X).

  #[refine]
  Global Instance smonad_lens: SMonad X m :=
  {
    ret := @ret S m SM;
    bind := @bind S m SM;
    err := @err S m SM;
    get := let* s := get in ret (proj s);
    put x := let* s := get in put (update s x);
  }.
  Proof.
    all: intros; repeat (lens_rewrite1 || smon_rewrite1); reflexivity.
  Defined.

End lens_section.
