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

Section hide_instance_section.

Instance submixer_refl {A} {f: Mixer A} : (f | f).
Proof. repeat intro. apply mixer_assoc. Qed.

End hide_instance_section.

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

Ltac mixer_rewrite1 :=
  let H := fresh in
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
        | setoid_rewrite (@submixer_right2 _ g f H) ] ]

  | [ |- context [ @mixer _ ?f (@mixer _ ?g _ _) _] ] =>
    first
      [ assert (g | f) as H;
        (* f (g x y) z  ~>  f x z *)
        [ typeclasses eauto
        | setoid_rewrite (@submixer_left _ g f H) ]

      | assert (f | g) as H;
        (* f (g x y) z  ~>  g x (f y z) *)
        [ typeclasses eauto
        | setoid_rewrite (H _ _ _) ] ]

  | [ |- context [ @mixer _ ?f _ _ ] ] =>
    (* f x x  ~>  x *)
    setoid_rewrite mixer_id
  end.

Ltac mixer_rewrite := repeat mixer_rewrite1;
                      try reflexivity.

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






(** ** Rewriting *)

(* TODO: Move or remove *)
Ltac2 bool2str (b: bool) := match b with
                         | true => "true"
                         | false => "false"
                         end.

(* TODO: Move or remove *)
Ltac2 of_oconstr oc :=
  match oc with
  | Some c => Message.concat (Message.of_string "Some ") (Message.of_constr c)
  | None => Message.of_string "None"
  end.

Context {A} (f g h: Mixer A).

CoInductive _give_up {A} (f: Mixer A) (g: Mixer A) : Prop :=
  _independent_ctor1.

Ltac2 mlLookup (f: constr) (g: constr) :=
  match! goal with
  | [ sub: (?f' | ?g') |- _ ] =>
    match and (Constr.equal f f') (Constr.equal g g') with
    | true => Some (Control.hyp sub)
    | false => Control.zero Match_failure
    end
  | [ _: _give_up ?f' ?g' |- _ ] =>
    match and (Constr.equal f f') (Constr.equal g g') with
    | true => None
    | false => Control.zero Match_failure
    end
  (*   | [ |- _ ] => let sub := Fresh.in_goal @sub in *)
  (*               set ($sub := ltac2:(typeclasses_eauto) : ($f | $g)); *)
  (* Some (Control.hyp sub) *)
  | [ |- _ ] => None
  end.

Context (Hfg : (f | g)).
Goal forall (Hfh: (f | h)), False.
  intros.

Ltac2 Eval mlLookup 'f 'g.




Ltac2 Type mlList := ((constr * constr * constr option) list).

(** Inspired by Ltac2.Pattern.v *)
Ltac2 rec mlCheck0 (ml: mlList) (f: constr) (g: constr) :=
  match ml with
  | [] => None
  | entry :: ml' =>
    match entry with
    | (f', g', fact) =>
      match and (Constr.equal f f') (Constr.equal g g') with
      | true => Some fact
      | false => mlCheck0 ml' f g
      end
    end
  end.

Ltac2 mlCheck (ml: mlList) (f: constr) (g: constr) :=
  match mlCheck0 ml f g with
  | Some x => ml, x
  | None =>
    let p := fun _ => let h := Fresh.in_goal @hyp in
                   set ($h := ltac2:(typeclasses_eauto) : ($f | $g));
                   Some (Control.hyp h) in
    let next := fun _ => None in
    let hy := Control.plus p next in
    (f, g, hy) :: ml, hy
end.


Ltac2 Eval mlCheck (('f, 'g, Some 'id) :: []) 'f 'g.

Ltac2 Eval mlCheck [] 'f 'g.

Goal forall (Hfg : (f | g)), False.
  intros.

  Ltac2 Eval mlCheck [] 'f 'g.

  Ltac2 Eval match mlCheck [] 'f 'g with
             | (_, oc) => Message.print (of_oconstr oc)
             end.

  set (H := ltac2:(match mlCheck [] 'f 'g with
                   | (_, h) => match h with
                              | Some hh => exact $hh (* (@eq_refl bool) (* hh *) *)
                              | _ => exact (@eq_refl unit)
                              end
                   end)).



  let h := ltac1:(exact I) in
  Message.print (Message.of_string "abc").

 | ];
    Some (Control.hyp h) in





  intros.

Ltac2 Eval mlCheck [] 'f 'g.




Ltac2 Eval
match! goal with
| [hyp: (?f'|?g') |- _] => match and (Constr.equal 'f f') (Constr.equal 'g g') with
                         | true => Message.print (Message.of_ident hyp)
                         | false => Message.print (Message.of_string "A'")
                         end
| [|- _] => Message.print (Message.of_string "B")
end.



Ltac2 Eval
match! goal with
| [hypo: (?f'|?g') |- _] => Some (Control.hyp hyp)
| [|- _] => None
end.




Set Default Proof Mode "Classic". (***********)



(** ** Independence *)

(* TODO: Is it better to use a parse-only notation? *)
Definition Independent {A} (f g: Mixer A) := (f | oppMixer g).

Proposition independent_symm {A} (f g: Mixer A) : Independent f g <-> Independent g f.
Proof.
  split; intros H x y z; symmetry; apply H.
Qed.

Proposition independent
            {A} {f g: Mixer A}
            {Hi: Independent f g}
            {x y z} : f (g x z) y = g (f x y) z.
Proof. apply Hi. Qed.





(** *** Add symmetry hint while avoiding loops. *)

Local Corollary independent_symm_imp {A} (f g: Mixer A) : Independent f g -> Independent g f.
Proof.
  apply independent_symm.
Qed.

CoInductive _independent_type1 {A} (f: Mixer A) (g: Mixer A) : Prop :=
  _independent_ctor1.

Ltac independent_symm_guard f g :=
  lazymatch goal with
  | [ _ : _independent_type1 f g |- _ ] => fail
  | _ => let iltt := fresh "iltt" in
        assert (iltt:=_independent_ctor1 f g)
  end.

Hint Extern 10 (Independent ?f ?g) =>
  independent_symm_guard f g;
  apply independent_symm_imp : typeclass_instances.

(** **** Tests *)

Goal forall {A} (f g: Mixer A) (H: Independent f g), Independent g f.
  (* Symmetry found *)
  typeclasses eauto.
Qed.

Goal forall {A} (f g: Mixer A), Independent f g.
  (* foop avoided. *)
  assert_fails (typeclasses eauto).
Abort.


(** *** Use [independent] rewrite in one direction only *)

Inductive _independent_type2 {A} (f: Mixer A) (g: Mixer A) : Prop :=
  _independent_ctor2 (Hi: Independent f g) :
    _independent_type2 f g.

Arguments _independent_ctor2 {_} _ _ {_}.

(* TODO: Not very elegant *)
Ltac rewrite_independent :=
  match goal with
    |- context [ @mixer _ ?g (@mixer _ ?f _ _) _ ] =>
    let indeq := fresh "indeq" in
    assert (indeq:=@eq_refl _ (_independent_ctor2 f g));
    lazymatch goal with
    | [ _ : _independent_ctor2 _ _ (Hi := (let _ := _ in @independent_symm_imp _ _ _ _)) = _ |- _ ] =>
      fail
    | [ _ : _independent_ctor2 _ _ (Hi := ?Hi) = _ |- _ ] =>
      clear indeq;
      setoid_rewrite (@independent _ f g Hi)
    end
  end.

(** [rewrite_independent] only works if the mixers are not bound variables.
    This restriction can probably be avoided, but it does not matter to us. *)

(** **** Test *)

Goal forall {A} (f g: Mixer A) (H: Independent f g) a x y, f (g a y) x = g (f a x) y.
  intros.
  (* Rewrites once, but not twice (i.e. not back to the original). *)
  progress rewrite_independent.
  assert_fails (progress rewrite_independent).
  reflexivity.
Qed.


(** *** Propriety *)

Instance independent_proper_sub0 {A} {f: Mixer A} :
  Proper (@Submixer A ==> flip impl) (Independent f).
Proof.
  intros g g' Hg
         H x y z.
  rewrite <- (mixer_id (Mixer:=g') x) at 2.
  rewrite Hg.
  rewrite <- H.
  rewrite <- Hg.
  rewrite H.
  rewrite mixer_id.
  reflexivity.
Qed.

Instance independent_proper_sub {A} :
  Proper (@Submixer A ==> @Submixer A ==> flip impl) (@Independent A).
Proof.
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


(** *** Rewrite tactics *)

Ltac mixer_rewrite1 := mixer_rewrite0
                       || rewrite_independent
                       || match goal with
                         | H : @Submixer ?A ?f ?g |- _ => setoid_rewrite (@submixer A f g H)
                         end.
Ltac mixer_rewrite := repeat mixer_rewrite1;
                      try reflexivity.


(** ** Products *)

Proposition independent_right {A} (f g: Mixer A) (Hi: Independent f g) x y z :
  f x (g y z) = f x y.
Proof.
  transitivity (f x (g (f y y) z)); [ mixer_rewrite | ].
  rewrite independent.
  mixer_rewrite.
Qed.

(* TODO: This is not very robust. *)
Hint Rewrite @independent_right using typeclasses eauto : mixer.

Section prod_section.

  Context {A} (f g: Mixer A) {Hi: Independent f g}.

  #[refine] Global Instance prodMixer : Mixer A :=
  {
    mixer x y := g (f x y) y;
  }.
  Proof.
    all: abstract (intros; mixer_rewrite).
  Defined.

  Global Instance submixer_prod1 : (f | prodMixer).
  Proof.
    intros x y z. cbn. mixer_rewrite.
  Qed.

  Global Instance submixer_prod2 : (g | prodMixer).
  Proof.
    intros x y z. cbn. mixer_rewrite.
  Qed.

  Global Instance submixer_prod3
         {h: Mixer A}
         (Hf: (f | h))
         (Hg: (g | h)) : (prodMixer | h).
  Proof.
    intros x y z. cbn. mixer_rewrite.
  Qed.

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
          {Hi: Independent f g}.

  (* This follows from [Hi], but assuming it makes the statements below
     more general. *)
  Context {Hi': Independent g f}.

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


(** *** Proper products *)

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

Proposition prodMixer_proper_sub {A}
            {f f': Mixer A} (Hf: (f | f'))
            {g g': Mixer A} (Hg: (g | g'))
            (* [Hi] follows from [Hi'] *)
            {Hi: Independent f g}
            {Hi': Independent f' g'} :
  (f × g | f' × g').
Proof.
  intros x y z. cbn.
  assert (Independent f g'); [ rewrite Hf; exact Hi' | ].
  assert (Independent f' g); [ rewrite Hg; exact Hi' | ].
  mixer_rewrite.
Qed.


(** *** More product submixers

Used to improve automatic proof search. *)

Section more_prod_section.

  Context {A} (f g h: Mixer A).

  Global Instance submixer_prod_l
         {Hfg: (f | g)}
         {Hfh: Independent f h} (* follows from Hgh *)
         {Hgh: Independent g h} : (f × h | g × h).
  Proof.
    apply (prodMixer_proper_sub _ _).
  Qed.

  Global Instance submixer_prod_r
         {Hfg: Independent f g} (* follows from Hgh *)
         {Hfh: Independent f h}
         {Hgh: (g | h)} : (f × g | f × h).
  Proof.
    apply (prodMixer_proper_sub _ _).
  Qed.




End more_prod_section.
