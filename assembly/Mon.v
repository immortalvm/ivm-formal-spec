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

(* TODO: For some reason this is only used for parsing. *)
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

  Proposition bind_extensional'
              {X} {mx mx': M X} (Hmx: mx = mx')
              {Y} (f f' : X -> M Y) (Hf: forall x, f x = f' x) :
    mx >>= f = mx' >>= f'.
  Proof.
    subst mx.
    apply bind_extensional.
    exact Hf.
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
    let* u := put s in
    f s u = let* s := get in
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

  Proposition assert_bind {P} {DP: Decidable P} {X} {mx: M X} {Y} {f: X -> M Y} :
    (assert* P in mx) >>= f = assert* P in (mx >>= f).
  Proof.
    destruct (decide P); [ | rewrite err_bind ]; reflexivity.
  Qed.

  Proposition assert_bind' {P} {DP: Decidable P} {X} {f: P -> M X} {Y} {g: X -> M Y} :
    (assert* P as H in f H) >>= g = assert* P as H in (f H >>= g).
  Proof.
    destruct (decide P); [ | rewrite err_bind ]; reflexivity.
  Qed.

End Basics.

Ltac smon_rewrite :=
  try (rewrite_strat (outermost <- bind_ret));
  try rewrite <- bind_ret;
  repeat (setoid_rewrite bind_assoc
          || setoid_rewrite assert_bind
          || setoid_rewrite assert_bind');
  repeat (setoid_rewrite ret_bind);
  repeat (setoid_rewrite err_bind);
  repeat (setoid_rewrite bind_err);
  repeat (setoid_rewrite bind_unit);
  repeat (setoid_rewrite put_put'
          || setoid_rewrite put_get'
          || setoid_rewrite get_put'
          || setoid_rewrite get_ret'
          || setoid_rewrite get_get);
  repeat (setoid_rewrite bind_ret
          || setoid_rewrite bind_ret_tt);
  try reflexivity.

Goal forall {S M X Y} {SM: SMonad S M} (g: S -> X) (f: X -> M Y),
    let* s := get in put s;; f (g s) = let* s := get in f (g s).
  intros S M X Y SM g f.
  smon_rewrite.
Qed.


(** ** Lenses *)

Section lens_section.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}
          {X: Type} (LX: Lens S X).

  #[refine]
  Global Instance smonad_lens: SMonad X M | 10 :=
  {
    ret := @ret S M SM;
    bind := @bind S M SM;
    err := @err S M SM;
    get := let* s := get in ret (proj s);
    put x := let* s := get in put (update s x);
  }.
  Proof.
    all: intros; repeat (lens_rewrite1 || smon_rewrite).
    - apply bind_extensional. assumption.
  Defined.

  Definition get' := get (SMonad := smonad_lens).
  Definition put' := put (SMonad := smonad_lens).

  (** The definitions above are arguably too strict since they mean that
  the machine cannot have additional state such as logging. One might
  consider using a weaker notion of lenses, but it is probably better to
  work up to the equivalence relation [s⊑s' /\ s'⊑s], see Mono.v. The
  current approach essentially corresponds to using the quotient type. *)

  Proposition to_lens_bind: @bind _ _ SM = @bind _ _ smonad_lens.
  Proof. reflexivity. Qed.

  Proposition get_get_prime Y (f: X -> X -> M Y) : let* x := get' in
                                                 let* x' := get' in
                                                 f x x' = let* x := get' in
                                                          f x x.
  Proof.
    unfold get'.
    rewrite to_lens_bind.
    apply get_get.
  Qed.

  Lemma get_put_prime Y (f: X -> unit -> M Y) :
    let* x := get' in
    let* u := put' x in
    f x u = let* x := get' in
            f x tt.
  Proof.
    unfold get', put'.
    rewrite to_lens_bind, get_put'.
    reflexivity.
  Qed.

  (* TODO: Is this the most natural lemma? *)
  Proposition update_state
              (f: X -> X) : let* x := get' in
                           put' (f x) = let* s := get in
                                        put (update s (f (proj s))).
  Proof. unfold get'. cbn. smon_rewrite. Qed.

End lens_section.

Section lenses_section.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}
          {X: Type} (LX: Lens S X)
          {Y: Type} (LY: Lens S Y).

  Proposition flip_get_get {A} (f: X -> Y -> M A) :
    let* x := get' LX in
    let* y := get' LY in
    f x y = let* y := get' LY in
            let* x := get' LX in
            f x y.
  Proof. smon_rewrite. Qed.

  Context {HI: Independent LX LY}.

  Proposition flip_put_get {A} (x: X) (f: unit -> Y -> M A) :
    let* u := put' LX x in
    let* y := get' LY in
    f u y = let* y := get' LY in
            let* u := put' LX x in
            f u y.
  Proof.
    smon_rewrite.
    independent_rewrite.
    reflexivity.
  Qed.

  Proposition flip_put_put {A} (x: X) (y: Y) (f: unit -> unit -> M A) :
    let* u := put' LX x in
    let* v := put' LY y in
    f u v = let* v := put' LY y in
            let* u := put' LX x in
            f u v.
  Proof.
    smon_rewrite.
    independent_rewrite.
    reflexivity.
  Qed.

End lenses_section.

Global Opaque get' put'.
