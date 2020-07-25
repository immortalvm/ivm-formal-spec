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
          || setoid_rewrite bind_ret_tt);
  try reflexivity.

Goal forall {S M X Y} {SM: SMonad S M} (g: S -> X) (f: X -> M Y),
    let* s := get in put s;; f (g s) = let* s := get in f (g s).
  intros S M X Y SM g f.
  smon_rewrite.
Qed.


(** ** "Stateless" effects *)

Section stateless_section.

  Context {S M} {SM: SMonad S M}.

  Class Stateless {X} (mx: M X) : Prop :=
    stateless : forall f, mx = let* s := get in
                          put (f s);;
                          let* x := mx in
                          put s;;
                          ret x.

  Global Instance stateless_ret {X} (x: X) : Stateless (ret x).
  Proof.
    unfold Stateless. intros f. smon_rewrite.
  Qed.

  Global Instance stateless_bind
         {X Y} (mx: M X) (f: X -> M Y)
         {Hmx: Stateless mx}
         {Hf: forall x, Stateless (f x)} : Stateless (mx >>= f).
  Proof.
    unfold Stateless in *. intros g.
    rewrite (Hmx g) at 1.
    setoid_rewrite (Hmx id) at 2. unfold id. smon_rewrite.
    setoid_rewrite (Hf _ g) at 1. smon_rewrite.
  Qed.

  Global Instance stateless_err {X} : Stateless (err : M X).
  Proof.
    unfold Stateless. intros f. smon_rewrite.
  Qed.

  Lemma get_stateless {X} (mx: M X) {Hmx: Stateless mx} {Y} (f: S -> X -> M Y) :
    let* s := get in
    let* x := mx in
    f s x = let* x := mx in
            let* s := get in
            f s x.
  Proof.
    setoid_rewrite (Hmx id). smon_rewrite.
  Qed.

  Lemma put_stateless (s: S) {X} (mx: M X) {Hmx: Stateless mx} {Y} (f: unit -> X -> M Y) :
    let* u := put s in
    let* x := mx in
    f u x = let* x := mx in
            let* u := put s in
            f u x.
  Proof.
    setoid_rewrite (Hmx (fun _ => s)). smon_rewrite.
  Qed.

  Instance stateless_unit
           (mu: M unit)
           (H: forall f, mu = let* s := get in
                         put (f s);;
                         mu;;
                         put s) : Stateless mu.
  Proof.
    unfold Stateless. intros f.
    smon_rewrite. apply H.
  Qed.

End stateless_section.


(** ** Lens monads *)

Section lensmonad_section.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}
          {A: Type} (LA: Lens S A).

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
    all: intros; repeat (lens_rewrite1 || smon_rewrite).
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

  (* TODO: Reformulate? *)
  Proposition update_state (f: A -> A) :
    let* a := get' in
    put' (f a) = let* s := get in
                 put (update s (f (proj s))).
  Proof.
    rewrite get_spec, put_spec.
    smon_rewrite.
  Qed.

  Class Stateless' {X} (mx : M X) :=
  {
    stateless' :> Stateless (S:=A) mx;
  }.

  Global Instance stateless_ret' {X} (x: X) : Stateless' (ret x).
  Proof.
    split.
    apply (stateless_ret (SM:=lensmonad)).
  Qed.

  Global Instance stateless_bind'
         {X Y} (mx: M X) (f: X -> M Y)
         {Hmx: Stateless' mx}
         {Hf: forall x, Stateless' (f x)} : Stateless' (mx >>= f).
  Proof.
    split.
    apply (stateless_bind (SM:=lensmonad)).
    - apply Hmx.
    - apply Hf.
  Qed.

  Global Instance stateless_err' {X} : Stateless' (err : M X).
  Proof.
    split.
    apply (stateless_err (SM:=lensmonad)).
  Qed.


  Proposition get_stateless'
              {X} (mx: M X) {Hmx: Stateless' mx}
              {Y} (f: A -> X -> M Y) :
    let* a := get' in
    let* x := mx in
    f a x = let* x := mx in
            let* a := get' in
            f a x.
  Proof.
    rewrite get_spec, bind_spec.
    apply get_stateless, Hmx.
  Qed.

  Proposition put_stateless'
              {a: A} {X} (mx: M X) {Hmx: Stateless' mx}
              {Y} (f: unit -> X -> M Y) :
    let* u := put' a in
    let* x := mx in
    f u x = let* x := mx in
            let* u := put' a in
            f u x.
  Proof.
    rewrite put_spec, bind_spec.
    apply put_stateless, Hmx.
  Qed.


  Class Confined {X} (mx: M X) : Prop :=
    convined : forall (f: S -> S), mx = let* s := get in
                                  put (update (f s) (proj s));;
                                  let* x := mx in
                                  let* s' := get in
                                  put (update s (proj s'));;
                                  ret x.






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
    smon_rewrite.
    independent_rewrite.
    reflexivity.
  Qed.

  Proposition flip_put_put (a: A) (b: B) {X} (f: unit -> unit -> M X) :
    let* u := put' LA a in
    let* v := put' LB b in
    f u v = let* v := put' LB b in
            let* u := put' LA a in
            f u v.
  Proof.
    setoid_rewrite put_spec'.
    smon_rewrite.
    independent_rewrite.
    reflexivity.
  Qed.

  Global Instance stateless_get : Stateless' LB (get' LA).
  Proof.
    split.
    rewrite get_spec.
    unfold Stateless.
    intros f.
    cbn.
    smon_rewrite.
    independent_rewrite.
    lens_rewrite.
    smon_rewrite.
  Qed.

  Global Instance stateless_put a : Stateless' LB (put' LA a).
  Proof.
    split.
    rewrite put_spec.
    unfold Stateless.
    intros f.
    cbn.
    smon_rewrite.
    independent_rewrite.
    lens_rewrite.
    reflexivity.
  Qed.




End independence_section.
