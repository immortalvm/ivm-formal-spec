From Assembly Require Import Init Lens.

Unset Suggest Proof Using.


(** ** Vector lenses *)

Section lens_vector_section.

  Open Scope vector.

  Context {A X: Type} {LX: Lens A X} {LA: Lens A A}.

  Equations projN n (_: A) : vector X n :=
    projN 0 _ := [];
    projN (S n) a := (proj a :: projN n (proj a)).

  Equations projN' `(nat) `(A) : A :=
    projN' 0 a := a;
    projN' (S n) a := (projN' n (proj a)).

  Arguments update : clear implicits.
  Arguments update {_ _} _ _ _.

  Equations updateN {n} `(A) `(vector X n) : A :=
    updateN (n:=S n) a (x :: r) := (update LX (update LA a (updateN (proj a) r)) x);
    updateN a _ := a.

  Equations updateN' (n:nat) `(A) `(A) : A :=
    updateN' (S n) a a' := update LA a (updateN' n (proj a) a');
    updateN' _ _ a' := a'.

  Context {IXA: Independent LX LA}.

  #[refine] Instance lens_vector n : Lens A (vector X n) :=
  {
    proj a := projN n a;
    update a x := updateN a x;
  }.
  Proof.
    - induction n; intros a x; dependent elimination x.
      + reflexivity.
      + simp projN updateN.
        rewrite proj_update. f_equal.
        rewrite <- (IHn (proj a)). f_equal.
        rewrite projY_updateX, proj_update.
        reflexivity.
    - induction n; intros a.
      + reflexivity.
      + simp projN updateN.
        rewrite IHn. lens_rewrite. reflexivity.
    - induction n; intros a x x';
        dependent elimination x;
        dependent elimination x'.
      + reflexivity.
      + simp projN updateN.
        independent_rewrite.
        lens_rewrite. rewrite IHn. reflexivity.
  Defined.

  #[refine] Instance lens_vector' n : Lens A A :=
  {
    proj a := projN' n a;
    update a x := updateN' n a x;
  }.
  Proof.
    - induction n; intros a x.
      + reflexivity.
      + simp projN' updateN'.
        rewrite proj_update, IHn.
        reflexivity.
    - induction n; intros a.
      + reflexivity.
      + simp projN' updateN'.
        rewrite IHn. lens_rewrite. reflexivity.
    - induction n; intros a x x'.
      + reflexivity.
      + simp updateN'.
        lens_rewrite. rewrite IHn. reflexivity.
  Defined.

  Instance independent_vector n : Independent (lens_vector n) (lens_vector' n).
  Proof.
    induction n; [split; reflexivity|].
    destruct IHn as [IH1 IH2 IH3].
    simpl in IH1, IH2, IH3.
    split.
    - intros a x. dependent elimination x. simpl.
      simp projN' updateN.
      independent_rewrite.
      lens_rewrite.
      rewrite IH1.
      reflexivity.
    - intros a y. simpl.
      simp projN updateN'.
      lens_rewrite.
      rewrite IH2.
      f_equal.
      independent_rewrite.
      reflexivity.
    - intros a x y.
      simpl.
      dependent elimination x.
      simp updateN updateN'.
      independent_rewrite.
      lens_rewrite.
      rewrite IH3.
      reflexivity.
  Qed.

  Context (Bp: Bijection_lens (lens_prod IXA)).
  Existing Instance lens_prod.

  Equations inverseN {n} `(vector X n) `(A) : A :=
    inverseN (n:=S n) (x :: r) a := inverse (x, inverseN r a);
    inverseN _ a := a.

  #[refine] Instance bijection_vector n : Bijection_lens (lens_prod (independent_vector n)) :=
    bijection_lens (fun va => inverseN (fst va) (snd va)) _.
  Proof.
    intros a [v a']. simpl. revert a v a'.
    induction n; intros a v a'; dependent elimination v; simp inverseN.
    - reflexivity.
    - simp updateN' updateN.
      independent_rewrite.
      lens_rewrite.
      rewrite IHn.
      rewrite <- (update_as_inverse a).
      simpl.
      independent_rewrite1.
      reflexivity.
  Defined.

End lens_vector_section.

Arguments lens_vector : clear implicits.
Arguments lens_vector {_ _} _ _ {_} _.

Arguments lens_vector' : clear implicits.
Arguments lens_vector' {_} _ _.
