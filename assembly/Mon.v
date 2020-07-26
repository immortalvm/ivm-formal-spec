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

Section basics_section.

  Context {S M} {SM: SMonad S M}.

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

End basics_section.

Ltac smon_rewrite0 :=
  try (rewrite_strat (outermost <- bind_ret));
  try rewrite <- bind_ret;
  repeat (setoid_rewrite bind_assoc
          || setoid_rewrite assert_bind
          || setoid_rewrite assert_bind');
  repeat (setoid_rewrite ret_bind);
  repeat (setoid_rewrite err_bind);
  repeat (setoid_rewrite bind_err);
  repeat (setoid_rewrite bind_unit);
  (** For some reason, [setoid_rewrite bind_unit] does not always work. *)
  repeat match goal with
           |- context [ ?m >>= fun (x:unit) => _ ] => setoid_rewrite (bind_unit m)
         end;
  repeat (setoid_rewrite put_put'
          || setoid_rewrite put_get'
          || setoid_rewrite get_put'
          || setoid_rewrite get_ret'
          || setoid_rewrite get_get);
  repeat (setoid_rewrite bind_ret
          || setoid_rewrite bind_ret_tt).

Ltac smon_rewrite :=
  smon_rewrite0;
  try reflexivity.

Ltac smon_rewrite' :=
  repeat (independent_rewrite1
          || lens_rewrite1
          || reflexivity
          || smon_rewrite0 ).

Goal forall {S M X Y} {SM: SMonad S M} (g: S -> X) (f: X -> M Y),
    let* s := get in put s;; f (g s) = let* s := get in f (g s).
  intros S M X Y SM g f.
  smon_rewrite.
Qed.


(** ** Lens monads *)

Section lensmonad_section.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}.

  (* TODO: Move? *)
  Lemma smonad_extensional {X} (mx mx': M X)
        (H: forall s, put s;; mx = put s;; mx') : mx = mx'.
  Proof.
    transitivity (let* s := get in
                  put s;;
                  mx);
      [ smon_rewrite | ].
    transitivity (let* s := get in
                  put s;;
                  mx');
      [ | smon_rewrite ].
    apply bind_extensional.
    exact H.
  Qed.

  Context {A: Type} (LA: Lens S A).

  Arguments proj {_ _ _}.
  Arguments update {_ _ _}.

  Class Confined {X} (mx: M X) : Prop :=
    confined : forall (t: S -> S), mx = let* s := get in
                                  put (update (t s) (proj s));;
                                  let* x := mx in
                                  let* s' := get in
                                  put (update s (proj s'));;
                                  ret x.

  #[refine]
  Global Instance lensmonad: SMonad A M | 10 :=
  {
    ret := @ret S M SM;
    bind := @bind S M SM;
    err := @err S M SM;
    get := let* s := get in ret (proj s);
    put a := let* s := get in put (update s a);
  }.
  Proof.
    all: intros; smon_rewrite'.
    - apply bind_extensional. assumption.
  Defined.

  Definition get' : M A := get.
  Proposition get_spec : get' = get.
  Proof. reflexivity. Qed.
  Global Opaque get'.

  Definition put' : A -> M unit := put.
  Proposition put_spec : put' = put.
  Proof. reflexivity. Qed.
  Global Opaque put'.

  (** For some reason, we sometimes have to use this variant with
  [setoid_rewrite]. *)
  Proposition put_spec' (a: A) : put' a = put a.
  Proof. rewrite put_spec. reflexivity. Qed.

  (** The definitions above are arguably too strict since they mean that
  the machine cannot have additional state such as logging. One might
  consider using a weaker notion of lenses, but it is probably better to
  work up to the equivalence relation [s⊑s' /\ s'⊑s], see Mono.v. The
  current approach essentially corresponds to using the quotient type. *)

  Proposition bind_spec: @bind _ _ SM = @bind _ _ lensmonad.
  Proof. reflexivity. Qed.

  (* TODO: Remove or reformulate? *)
  Proposition update_state (f: A -> A) :
    let* a := get' in
    put' (f a) = let* s := get in
                 put (update s (f (proj s))).
  Proof.
    rewrite get_spec, put_spec.
    smon_rewrite.
  Qed.

  (* TODO: Prove statless -> confined instead? *)
  Global Instance confined_ret {X} (x: X) : Confined (ret x).
  Proof.
    unfold Confined.
    intros t.
    smon_rewrite'.
  Qed.

  Global Instance confined_bind
         {X Y} (mx: M X) (f: X -> M Y)
         {Hmx: Confined mx}
         {Hf: forall x, Confined (f x)} : Confined (mx >>= f).
  Proof.
    unfold Confined in *. intros t.
    rewrite (Hmx t) at 1.
    setoid_rewrite (Hmx id) at 2. unfold id.
    smon_rewrite'.
    apply bind_extensional. intros s.
    setoid_rewrite (Hf _ (fun _ => t s)) at 1.
    smon_rewrite'.
  Qed.

  Global Instance confined_err {X} : Confined (err : M X).
  Proof.
    intros t.
    smon_rewrite.
  Qed.

  Global Instance confined_get : Confined get'.
  Proof.
    intros t.
    rewrite get_spec.
    smon_rewrite'.
  Qed.

  Global Instance confined_put a : Confined (put' a).
  Proof.
    intros t.
    rewrite put_spec.
    smon_rewrite'.
  Qed.

End lensmonad_section.


(** ** Independence *)

Section independence_section.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}
          {A: Type} (LA: Lens S A)
          {B: Type} (LB: Lens S B).

  Proposition flip_get_get {X} (f: A -> B -> M X) :
    let* a := get' LA in
    let* b := get' LB in
    f a b = let* b := get' LB in
            let* a := get' LA in
            f a b.
  Proof.
    setoid_rewrite get_spec.
    smon_rewrite.
  Qed.

  Context {HI: Independent LA LB}.

  Proposition flip_put_get (a: A) {X} (f: unit -> B -> M X) :
    let* u := put' LA a in
    let* b := get' LB in
    f u b = let* b := get' LB in
            let* u := put' LA a in
            f u b.
  Proof.
    rewrite get_spec, put_spec.
    smon_rewrite'.
  Qed.

  Proposition flip_put_put (a: A) (b: B) {X} (f: unit -> unit -> M X) :
    let* u := put' LA a in
    let* v := put' LB b in
    f u v = let* v := put' LB b in
            let* u := put' LA a in
            f u v.
  Proof.
    setoid_rewrite put_spec'.
    smon_rewrite'.
  Qed.

  Section confined_section.

    Context {X} (mx: M X) {Hmx: Confined LA mx}.
    Context {Y: Type}.

    Proposition get_confined (f: B -> X -> M Y) :
      let* b := get' LB in
      let* x := mx in
      f b x = let* x := mx in
              let* b := get' LB in
              f b x.
    Proof.
      apply smonad_extensional. intros s.
      rewrite get_spec.
      setoid_rewrite (Hmx id). unfold id.
      smon_rewrite'.
    Qed.

    Proposition put_confined b (f: unit -> X -> M Y) :
      let* u := put' LB b in
      let* x := mx in
      f u x = let* x := mx in
              let* u := put' LB b in
              f u x.
    Proof.
      apply smonad_extensional. intros s.
      rewrite put_spec.
      setoid_rewrite (Hmx id) at 1. unfold id.
      setoid_rewrite (Hmx (fun _ => update LB s b)) at 2.
      smon_rewrite'.
      apply bind_extensional'; [ | reflexivity ].
      (* TODO: automate *)
      f_equal.
      rewrite <- independent_commute.
      lens_rewrite.
      reflexivity.
    Qed.

  End confined_section.

End independence_section.
