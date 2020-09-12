From Assembly Require Export Init.

Unset Suggest Proof Using.

Declare Scope lens_scope.
Delimit Scope lens_scope with lens.

Ltac mixer_rewrite0 := rewrite_strat (repeat (outermost (hints mixer))).
Tactic Notation "mixer_rewrite0" "in" hyp(H) :=
  rewrite_strat (repeat (outermost (hints mixer))) in H.


(** * Mixers

[Mixer] represents lenses with the target type abstracted away.
I don't know if this has an established name. *)

Class Mixer A :=
{
  mixer: A -> A -> A;
  mixer_id x : mixer x x = x;
  mixer_left x y z : mixer (mixer x y) z = mixer x z;
  mixer_right x y z : mixer x (mixer y z) = mixer x z;
}.

Bind Scope lens_scope with Mixer.

Hint Rewrite @mixer_id : mixer.
Hint Rewrite @mixer_left : mixer.
Hint Rewrite @mixer_right : mixer.

Coercion mixer : Mixer >-> Funclass.

Proposition mixer_assoc {A} {f: Mixer A} {x y z} : f (f x y) z = f x (f y z).
Proof.
  intros. mixer_rewrite0. reflexivity.
Qed.

Program Instance fstMixer {A} : Mixer A :=
{
  mixer x _ := x;
}.

Program Instance sndMixer {A} : Mixer A :=
{
  mixer _ y := y;
}.

Section hide_instance_section.

  (** This too easily *)

  #[refine] Instance oppMixer {A} (f: Mixer A) : Mixer A :=
  {
    mixer x y := f y x;
  }.
  Proof.
    all: intros; mixer_rewrite0; reflexivity.
  Defined.

End hide_instance_section.


(** ** Equality *)

Section equality_section.

  Context {A : Type}.

  (** Equivalent to "f = g" if we assume extensionality and proof irrelevance. *)
  Definition mixerEq (f g: Mixer A) : Prop := forall x y, f x y = g x y.

  (** Useful to have as separate fact. *)
  Proposition mixer_refl {f: Mixer A} : mixerEq f f.
  Proof.
    intros a x. reflexivity.
  Qed.

  Global Instance mixerEq_equivalence : Equivalence mixerEq.
  Proof.
    split.
    - intro f. exact mixer_refl.
    - intros f g Hfg x y. rewrite Hfg. reflexivity.
    - intros f g h Hfg Hgh x y.
      transitivity (g x y).
      + apply Hfg.
      + apply Hgh.
  Qed.

  Instance mix_proper :
    Proper (mixerEq ==> eq ==> eq ==> eq) (@mixer A).
  Proof.
    repeat intro.
    repeat subst.
    intuition.
  Qed.

End equality_section.

(* "\simeq" : Same level and associativity as "=". *)
Notation "f ≃ g" := (mixerEq f g) (at level 70, no associativity) : type_scope.

Proposition opp_fstMixer {A} : oppMixer fstMixer ≃ @sndMixer A.
Proof.
  intros x y. reflexivity.
Qed.

Proposition opp_oppMixer {A} (f: Mixer A) : oppMixer (oppMixer f) ≃ f.
Proof.
  intros x y. reflexivity.
Qed.


(** ** Submixers *)

Set Typeclasses Unique Instances.

Class Submixer {A} (f g: Mixer A) : Prop :=
  submixer x y z : f (g x y) z = g x (f y z).

Unset Typeclasses Unique Instances.

(* Cf. the notation for Z.divide. *)
Notation "( f | g )" := (Submixer f g) : type_scope.

(** Adding [@submixer] as a rewrite hint may cause loops,
    see the tactic [mixer_rewrite] for a more conservative solution. *)

Instance submixer_proper {A} :
  Proper (@mixerEq A ==> @mixerEq A ==> iff) Submixer.
Proof.
  intros f f' Hf g g' Hg.
  split; intros H x y z.
  - repeat rewrite <- Hf.
    repeat rewrite <- Hg.
    rewrite submixer.
    reflexivity.
  - repeat rewrite Hf.
    repeat rewrite Hg.
    rewrite submixer.
    reflexivity.
Qed.

(* TODO: This causes some problems when we want a different submixer. *)
Instance submixer_refl {A} {f: Mixer A} : (f | f).
Proof. repeat intro. apply mixer_assoc. Qed.

Instance submixer_reflexive {A} : Reflexive (@Submixer A).
Proof.
  intro. apply submixer_refl.
Qed.

Instance eq_submixer_subrelation {A} : subrelation (@mixerEq A) (@Submixer A).
Proof.
  intros f g H. rewrite H. reflexivity.
Qed.

(** *** Rewriting *)

Proposition submixer_left {A} {f g: Mixer A} {Hs: (f|g)} x y z :
  g (f x y) z = g x z.
Proof.
  transitivity (g (g x (f x y)) z).
  - rewrite <- submixer, mixer_id. reflexivity.
  - rewrite mixer_left. reflexivity.
Qed.

(*
Corollary submixer_left' {A} {f g: Mixer A} {Hs: (f|g)} x y :
  g (f x y) x = x.
Proof.
  rewrite submixer_left. apply mixer_id.
Qed.
*)

Proposition submixer_right {A} {f g: Mixer A} {Hs: (f|g)} x y z :
  f x (g y z) = f x z.
Proof.
  transitivity (f x (f (g y z) z)).
  - rewrite submixer, mixer_id. reflexivity.
  - rewrite mixer_right. reflexivity.
Qed.

(*
Corollary submixer_right' {A} {f g: Mixer A} {Hs: (f|g)} x y :
  f x (g y x) = x.
Proof.
  rewrite submixer_right.
  apply mixer_id.
Qed.
*)

(* TODO: Rename? *)
Proposition submixer_right2 {A} {f g: Mixer A} {Hs: (f|g)} x y :
  g x (f x y) = f x y.
Proof.
  now rewrite <- Hs, mixer_id.
Qed.


(** ** Independence *)

(* TODO: Is it better to use a parse-only notation? *)
Class Independent {A} (f g: Mixer A) :=
  independent x y z : f (g x z) y = g (f x y) z.

Proposition independent_spec {A} (f g: Mixer A) :
  Independent f g <-> (f | oppMixer g).
Proof.
  split; intros H x y z; apply H.
Qed.

Proposition independent_symm' {A} {f g: Mixer A} : Independent f g -> Independent g f.
Proof.
  intros H x y z; symmetry; apply H.
Qed.

(** This can be used with [setoid_rewrite]. *)
Corollary independent_symm {A} (f g: Mixer A) : Independent f g <-> Independent g f.
Proof.
  split; apply independent_symm'.
Qed.

Proposition independent_left {A} (f g: Mixer A) {Hi: Independent f g} x y :
  g (f x y) x = f x y.
Proof.
  rewrite <- Hi. mixer_rewrite0. reflexivity.
Qed.


(** *** Add symmetry hint while avoiding loops. *)

Section indie_section.

  Context {A} (f g: Mixer A).

  Class Independent' :=
    independent' : Independent f g.

  Global Instance independent_forward (Hi: Independent f g): Independent' := Hi.

  Global Instance independent_backward (Hi: Independent g f): Independent' :=
    independent_symm' Hi.

  Context {Hi: Independent'}.

  Proposition independent_right x y z : g x (f y z) = g x y.
  Proof.
    transitivity (g x (f (g y y) z)); [ now mixer_rewrite0 | ].
    set (H := independent').
    rewrite independent.
    now mixer_rewrite0.
  Qed.

End indie_section.

Arguments independent_right {_ _ _ _}.

Corollary independent_right2
          {A} {f g h: Mixer A} {Hi: Independent' f g} {Hi': Independent' f h}
          x y z u:
  g x (h (f y z) u) = g x (h y u).
Proof.
  rewrite <- Hi', independent_right. reflexivity.
Qed.

Arguments independent' {_ _ _} _.


(** ** Rewrite/reduction tactic *)

Ltac mixer_rewrite1 :=
  let H := fresh "Hmr" in
  match goal with

  | [ |- context [ @mixer _ ?f _ (@mixer _ ?g _ _)] ] =>
    first
      [ assert (f | g) as H;
        (* f x (g y z)  ~>  f x z *)
        [ typeclasses eauto
        | setoid_rewrite (@submixer_right _ f g H) ]

      | assert (g | f) as H;
        (* f x (g x y)  ~>  g x y *)
        [ typeclasses eauto
        | setoid_rewrite (@submixer_right2 _ g f H) ]

      | assert (Independent' g f) as H;
        (* f x (g y z)  ~>  f x y *)
        [ typeclasses eauto
        | setoid_rewrite (@independent_right _ g f H) ] ]

  | [ |- context [ @mixer _ ?f (@mixer _ ?g _ _) _] ] =>
    first
      [ assert (g | f) as H;
        (* f (g x y) z  ~>  f x z *)
        [ typeclasses eauto
        | setoid_rewrite (@submixer_left _ g f H) ]

      | assert (f | g) as H;
        (* f (g x y) z  ~>  g x (f y z) *)
        [ typeclasses eauto
        | setoid_rewrite (H _ _ _) ]

      | assert (Independent f g) as H;
        (* f (g x z) y  ~>  g (f x y) z *)
        [ typeclasses eauto
        | setoid_rewrite (H _ _ _) ]

      | assert (Independent g f) as H;
        (* g (f x y) x  ~>  f x y *)
        [ typeclasses eauto
        | setoid_rewrite (@independent_left _ g f H) ] ]

  | [ |- context [ @mixer _ ?f _ (@mixer _ ?g (@mixer _ ?h _ _) _)] ] =>
    assert (Independent' h f) as H; [ typeclasses eauto | ];
    let H' := fresh "Hmr" in
    assert (Independent' h g) as H'; [ typeclasses eauto | ];
    (* f x (g (h y z) u)  ~>  f x (g y u) *)
    setoid_rewrite (@independent_right2 _ h f g H H')

  | [ |- context [ @mixer _ ?f _ _ ] ] =>
    (* f x x  ~>  x *)
    setoid_rewrite mixer_id
  end.

Ltac mixer_rewrite := repeat mixer_rewrite1; try reflexivity.
Ltac mixer_rewrite' := repeat intro; cbn; mixer_rewrite.


(** ** More submixer properties *)

Lemma submixer_antisymm {A} {f g: Mixer A} (Hs: (f|g)) (Hs': (g|f)) : f ≃ g.
Proof.
  intros a a'.
  transitivity (g (f a a') (f a a')).
  - now mixer_rewrite0.
  - mixer_rewrite.
Qed.

(** Avoid [Instance] to control proof search. *)
Lemma submixer_trans {A} {f g h : Mixer A} : (f | g) -> (g | h) -> (f | h).
Proof.
  intros Hfg Hgh x y z.
  transitivity (f (g (h x y) (h x y)) z).
  - now mixer_rewrite0.
  - mixer_rewrite.
Qed.

Instance submixer_transitive {A} : Transitive (@Submixer A).
Proof.
  intros f g h. apply submixer_trans.
Qed.

Instance submixer_least {A} (f: Mixer A) : (fstMixer | f).
Proof. mixer_rewrite'. Qed.


(** *** Propriety *)

Instance independent_proper_sub0 {A} {f: Mixer A} :
  Proper (@Submixer A ==> flip impl) (Independent f).
Proof.
  intros g g' Hg
         H x y z.
  rewrite <- (mixer_id (Mixer:=g') x) at 2.
  rewrite H.
  rewrite Hg.
  rewrite <- H.
  mixer_rewrite.
Qed.

Instance independent_proper_sub {A} :
  Proper (@Submixer A ==> @Submixer A ==> flip impl) (@Independent A).
Proof.
  (* The rewrites use [independent_proper_sub0]. *)
  intros f f' Hf
         g g' Hg.
  rewrite Hg. setoid_rewrite independent_symm.
  rewrite Hf. reflexivity.
Qed.

Instance independent_proper {A} :
  Proper (@mixerEq A ==> @mixerEq A ==> iff) (@Independent A).
Proof.
  (* The direct proof is not much longer. *)
  intros f f' Hf
         g g' Hg.
  split; intro H.
  - rewrite <- Hf, <- Hg. exact H.
  - rewrite Hf, Hg. exact H.
Qed.


(** ** Products *)

Section prod_section.

  Context {A} (f g: Mixer A) {Hi: Independent' f g}.

  Local Instance ind_prod : Independent f g := independent' Hi.

  #[refine] Global Instance prodMixer : Mixer A :=
  {
    mixer x y := g (f x y) y;
  }.
  Proof.
    all: abstract mixer_rewrite'.
  Defined.

  Global Instance submixer_prod1 : (f | prodMixer).
  Proof. mixer_rewrite'. Qed.

  Global Instance submixer_prod2 : (g | prodMixer).
  Proof. mixer_rewrite'. Qed.

  Global Instance submixer_prod3
         {h: Mixer A}
         (Hf: (f | h))
         (Hg: (g | h)) : (prodMixer | h).
  Proof. mixer_rewrite'. Qed.

  (** Thus, [prodMixer] is the least upper bound w.r.t. [(_ | _)]. *)

  Global Instance independent_prod
         {h: Mixer A}
         (Hf: Independent f h)
         (Hg: Independent g h) : Independent prodMixer h.
  Proof.
    intros x y z. cbn. mixer_rewrite.
  Qed.

End prod_section.

(* "\times" : The same level and associativity as "*". *)
Infix "×" := prodMixer (at level 40, left associativity) : lens_scope.

Section flip_section.

  Context {A} (f g: Mixer A)
          {Hi: Independent' f g}
          {Hi': Independent' g f}.

  (* [Hi'] follows from [Hi], but assuming it makes the propositions more
  general. *)

  Local Instance ind_flip : Independent f g := independent' Hi.

  Proposition prodMixer_comm : g × f ≃ f × g.
  Proof.
    intros x y. cbn.
    clear Hi'. (* Avoid rewrite loop *)
    mixer_rewrite.
  Qed.

  Global Instance submixer_prod0 : (f × g | g × f).
  Proof.
    rewrite prodMixer_comm. reflexivity.
  Qed.

End flip_section.

(** I am not sure how to make this an actual instance of [Proper]. *)
Proposition prodMixer_proper {A}
            {f f': Mixer A} (Hf: f ≃ f')
            {g g': Mixer A} (Hg: g ≃ g')
            {Hi: Independent f g}
            (* [Hi'] follows from [Hi] *)
            {Hi': Independent f' g'} :
  f × g ≃ f' × g'.
Proof.
  intros x y. cbn. rewrite Hf, Hg. reflexivity.
Qed.

Section more_prod_section.

  Context {A: Type}.

  Instance prodMixer_proper_sub
              {f f': Mixer A} (Hf: (f | f'))
              {g g': Mixer A} (Hg: (g | g'))
              {Hi: Independent f g} (* redundant, but convenient *)
              {Hi': Independent f' g'} :
    (f × g | f' × g').
  Proof.
    intros x y z. cbn.
    assert (Independent f g') as H; [ rewrite Hf; exact Hi' | ].
    assert (Independent f' g) as H'; [ rewrite Hg; exact Hi' | ].
    mixer_rewrite.
  Qed.

  (** The following variants are safer for proof search. *)

  Context (f g h: Mixer A).

  Global Instance submixer_prod_l
         {Hfg: (f | g)}
         {Hfh: Independent f h} (* redundant *)
         {Hgh: Independent g h} : (f × h | g × h).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance submixer_prod_r
         {Hfg: Independent f g} (* redundant *)
         {Hfh: Independent f h}
         {Hgh: (g | h)} : (f × g | f × h).
  Proof.
    typeclasses eauto.
  Qed.

End more_prod_section.
