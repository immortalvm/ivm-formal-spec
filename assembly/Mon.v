From Assembly Require Import Init Lens.

Unset Suggest Proof Using.


(** ** Error/state monad *)

Declare Scope monad_scope.

Reserved Notation "ma >>= f" (at level 69, left associativity).

Class SMonad (S: Type) (M: Type -> Type): Type :=
{
  ret {X} : X -> M X;
  bind {X Y} (mx: M X) (f: X -> M Y) : M Y
    where "mx >>= f" := (bind mx f);

  bind_ret {X} (mx: M X) : mx >>= ret = mx;
  ret_bind {X} (x: X) {Y} (f: X -> M Y) : ret x >>= f = f x;
  bind_assoc {X} (mx: M X) {Y} f {Z} (g: Y -> M Z) : (mx >>= f) >>= g = mx >>= (fun x => f x >>= g);
  bind_extensional {X Y} (f g: X -> M Y) (Hfg: forall x, f x = g x) (mx: M X) : mx >>= f = mx >>= g;

  err {X} : M X;
  bind_err {X} (mx: M X) {Y} : mx >>= (fun _ => err) = (err : M Y);
  err_bind {X Y} (f: X -> M Y) : err >>= f = err;

  get : M S;
  put (s: S) : M unit;
  put_put s s' : put s >>= (fun _ => put s') = put s';
  put_get s : put s >>= (fun _ => get) = put s >>= (fun _ => ret s);
  get_put : get >>= put = ret tt;
  get_ret : get >>= (fun _ => ret tt) = ret tt;
  get_get Y (f: S -> S -> M Y) : get >>= (fun s => get >>= (fun s' => f s s')) =
                               get >>= (fun s => f s s);
}.

Notation "mx >>= f" := (bind mx f) : monad_scope.

(** [get_get] expresses that the current state is deterministic.
    Presumably, it is derivable from the other axioms if we assume:
[[
    forall {X Y} {mxy mxy': M (X * Y)}
        (H1: let* xy := mxy in
             ret (fst xy) = let* xy := mxy' in
                            ret (fst xy))
        (H2: let* xy := mxy in
             ret (snd xy) = let* xy := mxy' in
                            ret (snd xy)) : mxy = mxy'.
]]
*)

(* Note to self:
* Order of associativity switched since ivm.v.
* I had to move the [B] argument to [bind] to make it an instance of [Proper] (see below).
*)

(* We prefer a notation which does not require do-end blocks. *)
Notation "'let*' x := mx 'in' my" := (bind mx (fun x => my))
                                       (at level 60, right associativity,
                                        format "'[hv' let*  x  :=  mx  'in'  '//' my ']'") : monad_scope.
Notation "mx ;; my" := (bind mx (fun _ => my))
                         (at level 60, right associativity,
                          format "'[hv' mx ;;  '//' my ']'") : monad_scope.

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

Open Scope monad_scope.


(** ** Basics *)

Section Basics.

  Context S M {SM: SMonad S M}.

  Global Instance bind_proper {X Y}:
    Proper ( eq ==> pointwise_relation X eq ==> eq ) (@bind S M SM X Y).
  Proof.
    intros mx mx' Hmx f f' Hf. destruct Hmx.
    apply bind_extensional, Hf.
  Qed.

  Proposition bind_unit (mu: M unit) {Y} (f: unit -> M Y) :
    mu >>= f = mu;; f tt.
  Proof. apply bind_extensional. intros []. reflexivity. Qed.

  Corollary bind_ret_tt (mu: M unit) : mu;; ret tt = mu.
  Proof.
    setoid_rewrite <- bind_unit. apply bind_ret.
  Qed.

  Proposition put_put' s s' Y (f: unit -> unit -> M Y) :
    let* x := put s in
    let* y := put s' in
    f x y = put s';;
            f tt tt.
  Proof.
    setoid_rewrite bind_unit.
    setoid_rewrite (bind_unit (put s') _).
    setoid_rewrite <- bind_assoc.
    setoid_rewrite put_put.
    reflexivity.
  Qed.

  Proposition put_get' s Y (f: unit -> S -> M Y) :
    let* x := put s in
    let* s' := get in
    f x s' = put s;;
             f tt s.
  Proof.
    setoid_rewrite bind_unit.
    setoid_rewrite <- bind_assoc.
    setoid_rewrite put_get.
    setoid_rewrite bind_assoc.
    setoid_rewrite ret_bind.
    reflexivity.
  Qed.

  Proposition get_put' Y (f: S -> unit -> M Y) :
    let* s := get in
    let* x := put s in
    f s x = let* s := get in
            f s tt.
  Proof.
    setoid_rewrite bind_unit.
    transitivity (let* s := get in
                  let* s' := get in
                  put s';;
                  f s tt).
    - setoid_rewrite get_get.
      reflexivity.
    - setoid_rewrite <- bind_assoc.
      setoid_rewrite get_put.
      setoid_rewrite ret_bind.
      reflexivity.
  Qed.

  Proposition ret_tt_bind {X} (mx: M X) : ret tt;; mx = mx.
  Proof. apply ret_bind. Qed.

  Proposition get_ret' Y (my: M Y) : get;; my = my.
  Proof.
    setoid_rewrite <- ret_tt_bind at 3.
    setoid_rewrite <- bind_assoc.
    setoid_rewrite get_ret.
    apply ret_bind.
  Qed.

End Basics.

(** This is not really used for rewriting, though. *)
Create HintDb smon discriminated.

Hint Rewrite @bind_ret : smon.
Hint Rewrite @ret_bind : smon.
Hint Rewrite @bind_assoc : smon.
Hint Rewrite @bind_err : smon.
Hint Rewrite @err_bind : smon.

Hint Rewrite @put_put : smon.
Hint Rewrite @put_get : smon.
Hint Rewrite @get_put : smon.
Hint Rewrite @get_ret : smon.
Hint Rewrite @get_get : smon.

Hint Rewrite @bind_unit : smon.
Hint Rewrite @bind_ret_tt : smon.
Hint Rewrite @put_put' : smon.
Hint Rewrite @put_get' : smon.
Hint Rewrite @get_put' : smon.
Hint Rewrite @get_ret' : smon.

(*
Ltac smon_rewrite1 := rewrite_strat (outermost (hints smon)).
 *)

Ltac smon_rewrite1 := rewrite_strat
                        (* Add more special cases here when necessary. *)
                        (choice (outermost bind_ret)
                        (choice (outermost ret_bind)
                        (choice (outermost bind_assoc)
                        (choice (outermost bind_err)

                        (choice (outermost put_put)
                        (choice (outermost get_put)
                        (choice (outermost get_get)

                        (choice (outermost put_put')
                        (choice (outermost put_get')
                        (choice (outermost get_put')

                        (* This should have been sufficient *)
                        (outermost (hints smon)))))))))))).

Ltac smon_rewrite := repeat smon_rewrite1; try reflexivity.

Goal forall {S M X Y} {SM: SMonad S M} (g: S -> X) (f: X -> M Y),
    let* s := get in put s;; f (g s) = let* s := get in f (g s).
  intros S M X Y SM g f.
  smon_rewrite.
Qed.

Section Initial.

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
    all: try reflexivity.
    all: intros;
      extensionality s;
      destruct (mx s) as [[a s']|];
      reflexivity || f_equal.
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
      rewrite get_put', get_ret'. reflexivity.
    - intros A ma B f.
      unfold from_est.
      simpl.
      rewrite bind_assoc.
      f_equal.
      extensionality s.
      destruct (ma s) as [[a s']|].
      + smon_rewrite.
        destruct (f a s') as [[b s'']|];
          smon_rewrite.
      + smon_rewrite.
    - intros A.
      unfold from_est. simpl. smon_rewrite.
    - unfold from_est. simpl. smon_rewrite.
    - intros s. unfold from_est. simpl. smon_rewrite.
  Qed.

End Initial.


(** ** Lenses *)

Section Lens.

  Context {S: Type}
          (M: Type -> Type) `{SM: SMonad S M}
          {X: Type} `(LX: Lens S X).

  #[refine]
  Global Instance smonad_lens: SMonad X M :=
  {
    ret := @ret S M SM;
    bind := @bind S M SM;
    err := @err S M SM;
    get := let* s := get in ret (proj s);
    put x := let* s := get in put (update s x);
  }.
  Proof.
    all: intros; repeat (lens_rewrite1 || smon_rewrite1); try reflexivity.
    - apply bind_extensional. assumption.
  Defined.

End Lens.
