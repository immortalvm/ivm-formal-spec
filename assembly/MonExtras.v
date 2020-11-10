From Assembly Require Import Init Lens Mon LensExtras.

Unset Suggest Proof Using.


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


(** ** The trivial [SMonad] *)

Section trivial_section.

  Context (S: Type).

  Local Ltac crush :=
    repeat (match goal with
            | [|- unit] => exact tt
            | [|- forall (_:unit),_] => intros []
            | [|- ?x = ?y :> unit] => destruct x; destruct y
            end
            || intro
            || reflexivity
            || assumption).

  #[refine]
  Instance trivial_smonad : SMonad S (fun _ => unit) := { }.
  all: crush.
  Defined.

  (** Clearly, this is the terminal [SMonad]. Moreover, this means that
      there are non-trivial "termination properties" that hold in all
      [SMonads]. Thus, we shall express and prove such properties only for
      the initial [SMonad]. *)

End trivial_section.
