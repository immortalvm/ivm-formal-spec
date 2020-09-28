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


(** ** Equality *)

(** Equivalent to "f = g" if we assume extensionality and proof irrelevance. *)
Definition mixerEq {A} (f g: Mixer A) : Prop := forall x y, f x y = g x y.

(* "\simeq" : Same level and associativity as "=". *)
Notation "f ≃ g" := (mixerEq f g) (at level 70, no associativity) : type_scope.

Section equality_section.

  Context {A : Type}.

  (** Useful to have as separate fact. *)
  Proposition mixer_refl {f: Mixer A} : f ≃ f.
  Proof.
    intros a x. reflexivity.
  Qed.

  Global Instance mixerEq_equivalence : Equivalence (@mixerEq A).
  Proof.
    split.
    - intro f. exact mixer_refl.
    - intros f g Hfg x y. rewrite Hfg. reflexivity.
    - intros f g h Hfg Hgh x y.
      transitivity (g x y).
      + apply Hfg.
      + apply Hgh.
  Qed.

  (* TODO: Is this safe? *)
  Global Instance mixer_proper :
    Proper (@mixerEq A ==> eq ==> eq ==> eq) (@mixer A).
  Proof.
    repeat intro.
    repeat subst.
    intuition.
  Qed.

End equality_section.



(** ** Submixers *)

Set Typeclasses Unique Instances.

Class Submixer {A} (f g: Mixer A) : Prop :=
  submixer x y z : f (g x y) z = g x (f y z).

Unset Typeclasses Unique Instances.

(** Adding [@submixer] as a rewrite hint may cause loops. *)

(* Cf. the notation for Z.divide. *)
Notation "( f | g )" := (Submixer f g) : type_scope.

Section submixer_section.

  Context {A: Type}.

  (** Making this a global instance is somewhat problematic since
      [Submixer] is itself a class. *)
  #[global] Instance submixer_proper :
    Proper (@mixerEq A ==> @mixerEq A ==> iff) (@Submixer A).
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

  Global Instance submixer_refl {f: Mixer A} : (f | f).
  Proof. repeat intro. apply mixer_assoc. Qed.

  Global Instance submixer_reflexive : Reflexive (@Submixer A).
  Proof.
    intro. apply submixer_refl.
  Qed.

  (** Not global by the same argument as for [submixer_proper]. *)
  Instance eq_submixer_subrelation : subrelation (@mixerEq A) (@Submixer A).
  Proof.
    intros f g H. rewrite H. reflexivity.
  Qed.

  (** *** Rewriting *)

  Proposition submixer_left {f g: Mixer A} {Hs: (f|g)} x y z :
    g (f x y) z = g x z.
  Proof.
    transitivity (g (g x (f x y)) z).
    - rewrite <- submixer, mixer_id. reflexivity.
    - rewrite mixer_left. reflexivity.
  Qed.

  Proposition submixer_right {f g: Mixer A} {Hs: (f|g)} x y z :
    f x (g y z) = f x z.
  Proof.
    transitivity (f x (f (g y z) z)).
    - rewrite submixer, mixer_id. reflexivity.
    - rewrite mixer_right. reflexivity.
  Qed.

  Proposition submixer_right' {f g: Mixer A} {Hs: (f|g)} x y :
    g x (f x y) = f x y.
  Proof.
    now rewrite <- Hs, mixer_id.
  Qed.

End submixer_section.


(** ** Independence *)

Section independence_section.

  Context {A: Type}.

  Class Independent (f g: Mixer A) :=
    independent x y z : f (g x z) y = g (f x y) z.

  Global Instance independent_symmetric : Symmetric Independent.
  Proof.
    intros f g H x y z; symmetry; apply H.
  Qed.

  (** This can be used with [setoid_rewrite]. *)
  Corollary independent_symm (f g: Mixer A) : Independent f g <-> Independent g f.
  Proof.
    split; apply independent_symmetric.
  Qed.

  Proposition independent_left (f g: Mixer A) {Hi: Independent f g} x y :
    g (f x y) x = f x y.
  Proof.
    rewrite <- Hi. mixer_rewrite0. reflexivity.
  Qed.


  (** The following is used to add symmetry hints while avoiding loops. *)

  Context (f g: Mixer A).

  Class Independent' :=
    independent' : Independent f g.

  Global Instance independent_forward (Hi: Independent f g): Independent' := Hi.

  Global Instance independent_backward (Hi: Independent g f): Independent' :=
    independent_symmetric g f Hi.

  Context {Hi: Independent'}.

  Proposition independent_right x y z : g x (f y z) = g x y.
  Proof.
    transitivity (g x (f (g y y) z)); [ now mixer_rewrite0 | ].
    set (H := independent').
    rewrite independent.
    now mixer_rewrite0.
  Qed.

End independence_section.

Arguments independent_right {_ _ _ _}.

Corollary independent_right2
          {A} {f g h: Mixer A} {Hi: Independent' f g} {Hi': Independent' f h}
          x y z u:
  g x (h (f y z) u) = g x (h y u).
Proof.
  rewrite <- Hi', independent_right. reflexivity.
Qed.

Arguments independent' {_ _ _} _.

Instance independent_symmetric' {A} : Symmetric (@Independent' A).
Proof.
  intros f g H.
  apply independent_backward, independent'.
  exact H.
Qed.


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
        | setoid_rewrite (@submixer_right' _ g f H) ]

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

Instance fstMixer_independent {A} (f: Mixer A) : Independent fstMixer f.
Proof.
  mixer_rewrite'.
Qed.


(** ** More submixer properties *)

Lemma submixer_antisymm {A} {f g: Mixer A} (Hs: (f|g)) (Hs': (g|f)) : f ≃ g.
Proof.
  intros a a'.
  transitivity (g (f a a') (f a a')).
  - now mixer_rewrite0.
  - mixer_rewrite.
Qed.

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

Proposition submixer_fst {A} (f: Mixer A) : (fstMixer | f).
Proof. mixer_rewrite'. Qed.


(** *** Propriety *)

Section propriety_section.

  Context {A: Type}.

  Instance independent_proper_sub0 {f: Mixer A} :
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

  #[global] Instance independent_proper_sub :
    Proper (@Submixer A ==> @Submixer A ==> flip impl) (@Independent A).
  Proof.
    (* The rewrites use [independent_proper_sub0]. *)
    intros f f' Hf
           g g' Hg.
    rewrite Hg. setoid_rewrite independent_symm.
    rewrite Hf. reflexivity.
  Qed.

  #[global] Instance independent_proper :
    Proper (@mixerEq A ==> @mixerEq A ==> iff) (@Independent A).
  Proof.
    (* The direct proof is not much longer. *)
    set (Hsub := @eq_submixer_subrelation).
    intros f f' Hf
           g g' Hg.
    split; intro H.
    - rewrite <- Hf, <- Hg. exact H.
    - rewrite Hf, Hg. exact H.
  Qed.

End propriety_section.


(** ** Products *)

Section prod_section.

  Context {A} (f g: Mixer A) {Hi: Independent' f g}.

  Instance ind_prod : Independent f g := independent' Hi.

  #[refine] Global Instance prodMixer : Mixer A :=
  {
    mixer x y := g (f x y) y;
  }.
  Proof.
    all: abstract mixer_rewrite'.
  Defined.

  Instance submixer_prod1 : (f | prodMixer).
  Proof. mixer_rewrite'. Qed.

  Instance submixer_prod2 : (g | prodMixer).
  Proof. mixer_rewrite'. Qed.

  Global Instance submixer_prod_right
         (h: Mixer A)
         {Hf: (f | h)}
         {Hg: (g | h)} : (prodMixer | h).
  Proof. mixer_rewrite'. Qed.

  (** Thus, [prodMixer] is a least upper bound w.r.t. [Submixer]. *)

  Global Instance submixer_prod_left1
         (h: Mixer A) {Hf: (h | f)} : (h | prodMixer).
  Proof.
    transitivity f.
    - exact Hf.
    - exact submixer_prod1.
  Qed.

  Global Instance submixer_prod_left2
         (h: Mixer A) {Hg: (h | g)} : (h | prodMixer).
  Proof.
    transitivity g.
    - exact Hg.
    - exact submixer_prod2.
  Qed.

  Instance independent_prod
           (h: Mixer A)
           {Hf: Independent f h}
           {Hg: Independent g h} : Independent prodMixer h.
  Proof.
    intros x y z. cbn. mixer_rewrite.
  Qed.

  Global Instance independent_prod'
           (h: Mixer A)
           {Hf: Independent' f h}
           {Hg: Independent' g h} : Independent' prodMixer h.
  Proof.
    apply independent_forward, independent_prod.
    - apply Hf.
    - apply Hg.
  Qed.

  Global Instance independent_prod''
           (h: Mixer A)
           {Hf: Independent' h f}
           {Hg: Independent' h g} : Independent' h prodMixer.
  Proof.
    symmetry.
    apply independent_prod';
      symmetry;
      assumption.
  Qed.


End prod_section.

(* "\times" : The same level and associativity as "*". *)
Infix "×" := prodMixer (at level 40, left associativity) : lens_scope.

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
