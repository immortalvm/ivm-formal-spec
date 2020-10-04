From Assembly Require Export Lens.

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
  get_get {Y} (f: S -> S -> M Y) : get >>= (fun s => get >>= (fun s' => f s s')) =
                                 get >>= (fun s => f s s);
}.

Notation "mx >>= f" := (bind mx f) : monad_scope.

(** [bind_extensional] is derivable if we assume functional
extensionality.

[get_get] expresses that the current state is deterministic.
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

(* We prefer a notation which does not require do-end blocks. *)
Notation "'let*' x := mx 'in' my" := (bind mx (fun x => my))
                                       (at level 60, right associativity,
                                        format "'[hv' let*  x  :=  mx  'in'  '//' my ']'") : monad_scope.
Notation "mx ;; my" := (bind mx (fun _ => my))
                         (at level 60, right associativity,
                          format "'[hv' mx ;;  '//' my ']'") : monad_scope.

Notation "'assume' P" :=
  (match (decide P%type) with
   | left p => ret p
   | right _ => err
   end) (at level 50) : monad_scope.

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

  Proposition get_put' {Y} (f: S -> unit -> M Y) :
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

  Proposition get_ret' {X} (mx: M X) : get;; mx = mx.
  Proof.
    setoid_rewrite <- ret_tt_bind at 3.
    setoid_rewrite <- bind_assoc.
    setoid_rewrite get_ret.
    apply ret_bind.
  Qed.

  Corollary smonad_ext {X} (mx mx': M X)
        (H: forall s, put s;; mx = put s;; mx') : mx = mx'.
  Proof.
    setoid_rewrite <- get_ret'.
    setoid_rewrite <- (get_put' (fun _ _ => _)).
    apply bind_extensional.
    exact H.
  Qed.

End basics_section.


(** *** Automation

This is a mess. We often need [setoid_rewrite] and/or [rewrite_strat], but
they appear buggy. Hence, we also use [rewrite] some places to increase
the success rate. *)

Ltac smon_rewrite0 :=
  try (rewrite_strat (outermost <- bind_ret));
  try rewrite <- bind_ret;
  repeat (rewrite bind_assoc
          || setoid_rewrite bind_assoc);
  repeat (setoid_rewrite ret_bind);
  repeat (setoid_rewrite err_bind);
  repeat (setoid_rewrite bind_err);
  repeat (setoid_rewrite bind_unit);
  repeat match goal with
           |- context [ ?m >>= fun (x:unit) => _ ] => setoid_rewrite (bind_unit m)
         end.

Ltac smon_rewrite1_basics :=
  repeat (setoid_rewrite put_put'
          || setoid_rewrite put_get'
          || setoid_rewrite get_put'
          || setoid_rewrite get_ret'
          || setoid_rewrite get_get).

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac2 mutable smon_rewrite1 () :=
  ltac1:(smon_rewrite1_basics).

Ltac smon_rewrite2 :=
  repeat (rewrite bind_ret (* [setoid_rewrite] is not always sufficient! *)
          || setoid_rewrite bind_ret
          || setoid_rewrite bind_ret_tt
          || setoid_rewrite ret_bind).

Ltac smon_rewrite :=
  smon_rewrite0;
  ltac2:(smon_rewrite1 ());
  smon_rewrite2;
  try reflexivity.

Ltac smon_rewrite' :=
  repeat (lens_rewrite1
          || reflexivity
          || smon_rewrite0; ltac2:(smon_rewrite1()));
  smon_rewrite2.

Goal forall {S M X Y} {SM: SMonad S M} (g: S -> X) (f: X -> M Y),
    let* s := get in put s;; f (g s) = let* s := get in f (g s).
  intros S M X Y SM g f.
  smon_rewrite.
Qed.

Ltac smon_ext s := apply smonad_ext; intros s.


(** ** Lens monads *)

Section lensmonad_section.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}
          {A: Type} (La: Lens S A).

  (** *** Definition *)

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
  Definition get_spec := unfolded_eq (@get').
  Global Opaque get'.

  Definition put' : A -> M unit := put.
  Definition put_spec := unfolded_eq (@put').
  (** For some reason, we sometimes have to use this variant with
  [setoid_rewrite]. *)
  Proposition put_spec' (a: A) : put' a = put a.
  Proof. reflexivity. Qed.
  Global Opaque put'.

  (** The definitions above are arguably too strict since they mean that
  the machine cannot have additional state such as logging. One might
  consider using a weaker notion of lenses, but it is probably better to
  work up to the equivalence relation [s⊑s' /\ s'⊑s], see Mono.v. The
  current approach essentially corresponds to using the quotient type. *)

  Proposition bind_spec: @bind _ _ lensmonad = @bind _ _ SM.
  Proof. reflexivity. Qed.


  (** *** Rewrite rules for [get'] and [put']. *)

  Ltac lens_transfer :=
    try setoid_rewrite get_spec;
    try setoid_rewrite put_spec';
    repeat rewrite <- bind_spec;
    smon_rewrite.

  Proposition lens_put_put a a' Y (f: unit -> unit -> M Y) :
    let* x := put' a in
    let* y := put' a' in
    f x y = put' a';;
            f tt tt.
  Proof. lens_transfer. Qed.

  Proposition lens_put_get a Y (f: unit -> A -> M Y) :
    let* x := put' a in
    let* a' := get' in
    f x a' = put' a;;
             f tt a.
  Proof. lens_transfer. Qed.

  Proposition lens_get_put {Y} (f: A -> unit -> M Y) :
    let* a := get' in
    let* u := put' a in
    f a u = let* a := get' in
            f a tt.
  Proof. lens_transfer. Qed.

  Proposition lens_get_ret {X} (mx: M X) : get';; mx = mx.
  Proof. lens_transfer. Qed.

  Proposition lens_get_get Y (f: A -> A -> M Y) :
    let* a := get' in
    let* a' := get' in
    f a a' = let* a := get' in
             f a a.
  Proof. lens_transfer. Qed.

  Corollary smonad_ext' {X} (mx mx': M X)
        (H: forall a, put' a;; mx = put' a;; mx') : mx = mx'.
  Proof.
    setoid_rewrite <- lens_get_ret.
    setoid_rewrite <- (lens_get_put (fun _ _ => _)).
    apply bind_extensional.
    exact H.
  Qed.

End lensmonad_section.

Section mixer_section.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}.

  Definition putM (m: Mixer S) (s: S) : M unit :=
    let* s' := get in
    put (m s' s).

  Definition putM_spec := unfolded_eq (@putM).
  Definition putM_spec' {m} a := unfolded_eq (@putM m a).

  Proposition putM_specL {A} (L: Lens S A) (s: S) :
    putM L s = put' L (proj s).
  Proof.
    reflexivity.
  Qed.

  Proposition putM_putM (m: Mixer S) s s' {X} (f: unit -> unit -> M X) :
    let* x := putM m s in
    let* y := putM m s' in
    f x y = putM m s';;
            f tt tt.
  Proof.
    rewrite putM_spec.
    smon_rewrite'.
  Qed.

  Global Opaque putM.

End mixer_section.

Ltac smon_ext' La a := apply (smonad_ext' La); intros a.

Ltac smon_rewrite1_lens :=
  setoid_rewrite lens_put_put
  || setoid_rewrite lens_put_get
  || setoid_rewrite lens_get_put
  || setoid_rewrite lens_get_ret
  || setoid_rewrite lens_get_get.

Ltac2 Set smon_rewrite1 := fun _ =>
  ltac1:(smon_rewrite1_basics);
  ltac1:(repeat smon_rewrite1_lens).


Set Typeclasses Unique Instances. (* ! *)


(** ** Neutral and confined computations *)

Section defs_section.

  Arguments get' {_ _ _ _ _}.
  Arguments put' {_ _ _ _ _}.

  Context {S M} {SM: SMonad S M}.

  Class Neutral {X} (m: Mixer S) (mx: M X) : Prop :=
    neutral : forall ss, mx = let* s := get in
                         putM m ss;;
                         let* x := mx in
                         putM m s;;
                         ret x.

  Arguments Neutral {_ _}.

  Class Confined {X} (m: Mixer S) (mx: M X) : Prop :=
    confined : forall {Y} (my: M Y) (Hmy: Neutral my)
                 {Z} (f: X -> Y -> M Z),
      let* y := my in
      let* x := mx in
      f x y = let* x := mx in
              let* y := my in
              f x y.

End defs_section.


Section neutral_section.

  Arguments get' {_ _ _ _ _}.
  Arguments put' {_ _ _ _ _}.
  Arguments Neutral {_ _ _ _ _}.
  Arguments Confined {_ _ _ _ _}.

  Context {S: Type}
          {M: Type -> Type}
          {SM: SMonad S M}
          (m: Mixer S).

  Global Instance neutral_if (b: bool) {X} (mx mx': M X)
         {Hmx: Neutral mx}
         {Hmx': Neutral mx'} : Neutral (if b then mx else mx').
  Proof.
    destruct b; assumption.
  Qed.

  Global Instance neutral_option
         {X} (ox: option X) {Y}
         (f: X -> M Y) {Hf: forall x, Neutral (f x)}
         (my: M Y) {Hmy: Neutral my} :
    Neutral (match ox with
              | Some x => f x
              | None => my
              end).
  Proof.
    destruct ox; [apply Hf | apply Hmy].
  Qed.

  Global Instance neutral_sumbool
         {P Q} (pq: {P} + {Q}) {X}
         (f: P -> M X) {Hf: forall p, Neutral (f p)}
         (g: Q -> M X) {Hg: forall q, Neutral (g q)} :
    Neutral (match pq with
              | left p => f p
              | right q => g q
              end).
  Proof.
    destruct pq; [apply Hf | apply Hg].
  Qed.

  Global Instance neutral_ret {X} (x: X) : Neutral (ret x).
  Proof.
    intros aa. rewrite putM_spec. smon_rewrite'.
  Qed.

  Global Instance neutral_bind
         {X Y} (mx: M X) (f: X -> M Y)
         {Hmx: Neutral mx}
         {Hf: forall x, Neutral (f x)} : Neutral (mx >>= f).
  Proof.
    unfold Neutral in *. intros aa.
    setoid_rewrite (Hmx aa). smon_rewrite.
    setoid_rewrite (Hf _ aa).
    rewrite putM_spec. smon_rewrite'.
  Qed.

  Global Instance neutral_err {X} : Neutral (err : M X).
  Proof.
    intros aa. smon_rewrite.
  Qed.


  (** *** Confined **)

  Global Instance confined_if (b: bool) {X} (mx mx': M X)
         {Hmx: Confined mx}
         {Hmx': Confined mx'} : Confined (if b then mx else mx').
  Proof.
    destruct b; assumption.
  Qed.

  Global Instance confined_option
         {X} (ox: option X) {Y}
         (f: X -> M Y) {Hf: forall x, Confined (f x)}
         (my: M Y) {Hmy: Confined my} :
    Confined (match ox with
              | Some x => f x
              | None => my
              end).
  Proof.
    destruct ox; [apply Hf | apply Hmy].
  Qed.

  Global Instance confined_sumbool
         {P Q} (pq: {P} + {Q}) {X}
         (f: P -> M X) {Hf: forall p, Confined (f p)}
         (g: Q -> M X) {Hg: forall q, Confined (g q)} :
    Confined (match pq with
              | left p => f p
              | right q => g q
              end).
  Proof.
    destruct pq; [apply Hf | apply Hg].
  Qed.

  Global Instance confined_ret {X} (x: X) : Confined (ret x).
  Proof.
    unfold Confined. intros. smon_rewrite.
  Qed.

  Global Instance confined_bind
         {X Y} {mx: M X} {f: X -> M Y}
         {Hmx: Confined mx}
         {Hf: forall x, Confined (f x)} : Confined (mx >>= f).
  Proof.
    unfold Confined in *.
    intros C mc Hmc D g.
    smon_rewrite.
    rewrite (Hmx C mc Hmc D). clear Hmx.
    apply bind_extensional. intros x.
    rewrite Hf.
    - reflexivity.
    - exact Hmc.
  Qed.

  Global Instance confined_err {X} : Confined (err : M X).
  Proof.
    unfold Confined. intros. smon_rewrite.
  Qed.

  Global Instance confined_putM s : Confined (putM m s).
  Proof.
    unfold Confined. intros. smon_rewrite.
    setoid_rewrite (Hmy s). rewrite putM_spec.
    smon_rewrite'.
  Qed.

End neutral_section.

Arguments confined_bind {_ _ _ _ _ _ _ _} _ _.

Section lens_section.

  Arguments get' {_ _ _ _ _}.
  Arguments put' {_ _ _ _ _}.

  Context {S} {M: Type -> Type} {SM: SMonad S M}
          {A} (La: Lens S A).

  Lemma lensNeutral {X} (mx: M X) :
    Neutral La mx <-> (forall a, mx = let* a' := get' in
                               put' a;;
                               let* x := mx in
                               put' a';;
                               ret x).
  Proof.
    unfold Neutral.
    rewrite get_spec, put_spec, putM_spec. split.
    - intros H a.
      smon_ext s.
      setoid_rewrite (H (update s a)).
      smon_rewrite. cbn. lens_rewrite.
    - intros H s.
      setoid_rewrite (H (proj s)).
      smon_rewrite. cbn. lens_rewrite.
  Qed.

  Global Instance confined_get : Confined La get'.
  Proof.
    unfold Confined. intros. smon_ext s.
    rewrite lensNeutral in Hmy.
    setoid_rewrite (Hmy (proj s)).
    smon_rewrite.
  Qed.

  Global Instance confined_put a : Confined La (put' a).
  Proof.
    unfold Confined. intros. smon_ext s.
    rewrite lensNeutral in Hmy.
    setoid_rewrite (Hmy (proj s)).
    smon_rewrite.
  Qed.

End lens_section.


(** ** Sublenses and propriety *)

Section sublens_section.

  Context {S M} {SM: SMonad S M}.

  Global Instance lens_get_proper {A} :
    Proper (@lensEq S A ==> eq) get'.
  Proof.
    intros La La' Hla.
    setoid_rewrite get_spec. cbn.
    setoid_rewrite Hla.
    reflexivity.
  Qed.

  Global Instance lens_put_proper {A} :
    Proper (@lensEq S A ==> eq ==> eq) put'.
  Proof.
    intros La La' Hla
           a a' Ha.
    destruct Ha.
    setoid_rewrite put_spec'. cbn.
    setoid_rewrite Hla.
    reflexivity.
  Qed.


  (** *** Neutral *)

  Global Instance neutral_proper_sub {X} :
    Proper (@Submixer S ==> @eq (M X) ==> flip impl) Neutral | 15.
  Proof.
    intros m m' Hm
           mx mx' Hmx
           H s.
    destruct Hmx.
    setoid_rewrite (H s). rewrite putM_spec.
    smon_rewrite'.
  Qed.

  Global Instance neutral_proper {X} :
    Proper (@mixerEq S ==> @eq (M X) ==> iff) Neutral | 15.
  Proof.
    intros m m' Hm
           mx mx' Hmx.
    destruct Hmx.
    split;
      intro H;
      refine (neutral_proper_sub _ _ _ _ _ eq_refl H);
      rewrite Hm;
      reflexivity.
  Qed.

  (* TODO: Useful? *)
  Global Instance neutral_proper' {A X} :
    Proper (@lensEq S A ==> @eq (M X) ==> iff) Neutral | 15.
  Proof.
    intros La La' Hla
           mx mx' Hmx.
    rewrite Hla, Hmx.
    reflexivity.
  Qed.

  (* TODO: Useful? *)
  Instance neutral_composite
           {A} {La: Lens S A}
           {B} {Lb: Lens A B}
           {X} (mx: M X) {Hmx: Neutral La mx} : Neutral (Lb ∘ La) mx.
  Proof.
    rewrite sublens_comp'. exact Hmx.
  Qed.


  (** *** Confined *)

  Global Instance confined_proper_sub {X} :
    Proper (@Submixer S ==> @eq (M X) ==> impl) Confined | 15.
  Proof.
    intros m m' Hm
           mx mx' Hmx Hc
           Y my Hmy
           Z f.
    destruct Hmx.
    (* Does not work: [rewrite Hm in Hmy.] *)
    assert (Neutral m my) as H.
    - rewrite Hm. exact Hmy.
    - apply Hc. exact H.
  Qed.

  Global Instance Confined_proper2 {X}:
    Proper (@mixerEq S ==> @eq (M X) ==> iff) Confined | 15.
  Proof.
    set (Hsub := @eq_submixer_subrelation).
    intros f f' Hf
           mx mx' Hmx.
    destruct Hmx.
    split.
    - now rewrite Hf.
    - now rewrite <- Hf.
  Qed.

  (** *** Corollaries *)

  Global Instance neutral_sub
           {X} {mx: M X} {g: Mixer S} (Hmx: Neutral g mx)
           (f: Mixer S) {Hs: (f | g)}: Neutral f mx.
  Proof.
    rewrite Hs. exact Hmx.
  Qed.

  Global Instance confined_sub
           {X} {mx: M X} {f: Mixer S} (Hmx: Confined f mx)
           (g: Mixer S) {Hs: (f | g)} : Confined g mx.
  Proof.
    rewrite Hs in Hmx. exact Hmx.
  Qed.

End sublens_section.

(* TODO: How useful is this? *)
Arguments lens_get_proper {_ _ _ _ _ _} _.
Arguments lens_put_proper {_ _ _ _ _ _} _ {_ _} _.
Arguments neutral_proper {_ _ _ _ _ _} _ {_ _} _.


(** ** Independence *)

Section independence_section1.

  Context {S: Type}
          {M: Type -> Type} `{SM: SMonad S M}
          {A: Type} (La: Lens S A)
          {B: Type} (Lb: Lens S B).

  (** This holds even if La and Lb are dependent. *)
  Proposition flip_get_get {X} (f: A -> B -> M X) :
    let* b := get' Lb in
    let* a := get' La in
    f a b = let* a := get' La in
            let* b := get' Lb in
            f a b.
  Proof.
    setoid_rewrite get_spec.
    smon_rewrite.
  Qed.

  (** Extra assumption used for lens ordering in order to avoid loops. *)
  Definition flip_get_get' {Hi: Independent La Lb} {X} (f: A -> B -> M X) :=
    flip_get_get f.
  Opaque flip_get_get'.

  Context {Hi: Independent La Lb}.

  Proposition flip_put_get (a: A) {X} (f: unit -> B -> M X) :
    let* u := put' La a in
    let* b := get' Lb in
    f u b = let* b := get' Lb in
            let* u := put' La a in
            f u b.
  Proof.
    rewrite get_spec, put_spec.
    smon_rewrite'.
  Qed.

  Proposition flip_put_put (a: A) (b: B) {X} (f: unit -> unit -> M X) :
    let* v := put' Lb b in
    let* u := put' La a in
    f u v = let* u := put' La a in
            let* v := put' Lb b in
            f u v.
  Proof.
    setoid_rewrite put_spec'.
    smon_rewrite'.
  Qed.

End independence_section1.

Ltac smon_rewrite1_independent :=
  match goal with
  | Hi: Independent (lens2mixer ?La) (lens2mixer ?Lb) |- _ =>
    setoid_rewrite (flip_get_get' La Lb (Hi:=Hi))
    || setoid_rewrite (flip_put_get La Lb (Hi:=Hi))
    || setoid_rewrite <- (flip_put_get La Lb (Hi:=Hi))
    || setoid_rewrite (flip_put_put La Lb (Hi:=Hi))
  end.

Ltac2 Set smon_rewrite1 := fun _ =>
  ltac1:(smon_rewrite1_basics);
  ltac1:(repeat (smon_rewrite1_lens || smon_rewrite1_independent)).

Section independence_section2.

  Context {S M} {SM: SMonad S M}
          {A} (La: Lens S A)
          {B} (Lb: Lens S B)
          {Hi: Independent La Lb}.

  Global Instance neutral_get : Neutral La (get' Lb).
  Proof.
    apply lensNeutral. intros aa. smon_rewrite.
  Qed.

  Global Instance neutral_put b : Neutral La (put' Lb b).
  Proof.
    apply lensNeutral. intros aa. smon_rewrite.
  Qed.

End independence_section2.

Section independence_section3.

  Context {S M} {SM: SMonad S M}
          {m m': Mixer S}
          {Hm: Independent' m m'}.

  Global Instance neutral_putM s : Neutral m (putM m' s).
  Proof.
    intros t.
    rewrite putM_spec.
    smon_rewrite.
    (* TODO: [mixer_rewrite] ought to be sufficient here. *)
    set (H := independent' Hm).
    setoid_rewrite <- Mixer.independent.
    mixer_rewrite.
  Qed.

  Global Instance confined_neutral
         {X} (mx: M X) {Hmx: Confined m mx} : Neutral m' mx.
  Proof.
    set (keeper := let* s0 := get in
                   ret (let* s1 := get in
                        put (m' s1 s0))).
    assert (Neutral m keeper) as Hk.
    - intros ss. subst keeper. rewrite putM_spec. smon_rewrite'.
    - intros ss. transitivity (let* closure := keeper in
                               putM m' ss;;
                               let* x := mx in
                               closure;;
                               ret x).
      + setoid_rewrite Hmx; [ | typeclasses eauto ].
        setoid_rewrite Hmx; [ | typeclasses eauto ].
        subst keeper. rewrite putM_spec. smon_rewrite'.
      + subst keeper. rewrite putM_spec. smon_rewrite. smon_rewrite.
  Qed.

  (** The proof above is an indication how [get'] and [put'] can be
  generalized from lenses to mixers using function types. *)

End independence_section3.
