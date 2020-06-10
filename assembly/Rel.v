From Assembly Require Import Basics.


(** ** Relations ***)

Class Rel (X: Type) := rel : relation X.

Infix "⊑" := rel (at level 70).
Arguments rel : clear implicits.
Arguments rel {_} _.


(** ** Basics *)

Section basics_section.

  Context {X: Type}.

  Instance true_relation : Rel X | 30 := fun _ _ => True.

  Instance true_relation_equivalence : Equivalence true_relation.
  Proof using.
    split; intro; intros; exact I.
  Qed.

  (* Fallback to Leibniz' equality. *)
  Global Instance eq_relation : Rel X | 20 := eq.

  (* Is this useful? *)
  Global Instance eq_Rel_equivalence : Equivalence eq_relation := eq_equivalence.

  Context (RX: Rel X).

  Global Instance option_relation : Rel (option X) | 5 :=
    fun x x' =>
      match x, x' with
      | None, _ => True
      | Some _, None => False
      | Some x, Some x' => x ⊑ x'
      end.

  Global Instance option_relation_reflexive {HrX: Reflexive RX} : Reflexive option_relation.
  Proof using.
    unfold option_relation. intros [x|]; reflexivity.
  Qed.

  Global Instance option_relation_transitive {HtX: Transitive RX} : Transitive option_relation.
  Proof using.
    intros [x|] [y|] [z|] Hxy Hyz; cbn in *; try assumption.
    - transitivity y; assumption.
    - exfalso. assumption.
  Qed.

  Context {Y} (RY: Rel Y).

  Global Instance fun_relation : Rel (X -> Y) | 10 :=
    fun f f' => forall (x x': X), x ⊑ x' -> f x ⊑ f' x'.

  Global Instance prod_relation : Rel (X * Y) | 5 :=
    fun p p' =>
      match p, p' with
      | (x, y), (x', y') => x ⊑ x' /\ y ⊑ y'
      end.

  Global Instance prod_relation_reflexive {HrX: Reflexive RX} {HrY: Reflexive RY} : Reflexive prod_relation.
  Proof using.
    intros [x y]. cbn. split; reflexivity.
  Qed.

  Global Instance prod_relation_symmetric {HsX: Symmetric RX} {HsY: Symmetric RY} : Symmetric prod_relation.
  Proof using.
    intros [x y] [x1 y1] [Hx Hy]. split; symmetry; assumption.
  Qed.

  Global Instance prod_relation_transitive {HtX: Transitive RX} {HtY: Transitive RY} : Transitive prod_relation.
  Proof using.
    intros [x1 y1] [x2 y2] [x3 y3] [Hx12 Hy12] [Hx23 Hy23].
    split.
    - transitivity x2; assumption.
    - transitivity y2; assumption.
  Qed.

  Context (RX': Rel X).

  Instance and_relation : Rel X | 30 := fun x x' => RX x x' /\ RX' x x'.

  Instance and_reflexive {HrX: Reflexive RX} {HrX': Reflexive RX'} : Reflexive and_relation.
  Proof using.
    intros x; split; reflexivity.
  Qed.

  Instance and_symmetric {HrX: Symmetric RX} {HrX': Symmetric RX'} : Symmetric and_relation.
  Proof using.
    intros x y [H H']; split; symmetry; assumption.
  Qed.

  Instance and_transitive {HrX: Transitive RX} {HrX': Transitive RX'} : Transitive and_relation.
  Proof using.
    intros x1 x2 x3 [H12 H12'] [H23 H23']; split; transitivity x2; assumption.
  Qed.

End basics_section.


(** ** Lenses *)

Section lens_section.

  Context {S X} (LX: Lens S X).

  Context {RX: Rel X}.

  Definition lens_relation : relation S := fun s s' => proj s ⊑ proj s'.

  Global Instance lens_relation_reflexive {HrX: Reflexive RX} : Reflexive lens_relation.
  Proof using.
    unfold lens_relation. intros s. reflexivity.
  Qed.

  Global Instance lens_relation_symmetric {HsX: Symmetric RX} : Symmetric lens_relation.
  Proof using.
    unfold lens_relation. intros s s' H.
    symmetry; assumption.
  Qed.

  Global Instance lens_relation_transitive {HtX: Transitive RX} : Transitive lens_relation.
  Proof using.
    unfold lens_relation. intros s1 s2 s3 H12 H23.
    transitivity (proj s2); assumption.
  Qed.

End lens_section.


(** ** Proper operations in [EST] *)

(** Like [Proper], but for [Rel]. *)
Class PropR {X: Type} {RX: Rel X} (x: X) := propR : x ⊑ x.

Section proper_section.

  Context {S} {RS: Rel S}.

  Local Notation M := (EST S).

  Context {A} {RA: Rel A}.

  Global Instance est_relation: Rel (M A).
  Proof.
    typeclasses eauto.
  Defined.

  (** Make sure we got what we wanted. *)
  Goal est_relation = fun_relation RS (option_relation (prod_relation RS RA)).
    reflexivity.
  Qed.

  Local Notation RM := (est_relation).

  Lemma ret_propr : PropR (@ret _ M _ A).
  Proof using.
    intros a a' Ha.
    intros s s' Hs.
    simpl.
    split; assumption.
  Qed.

  Context {B} {RB: Rel B}.

  Global Instance bind_propr: PropR (@bind _ M _ A B).
  Proof using.
    intros ma ma' Hma f f' Hf.
    intros s s' Hs. simpl.
    specialize (Hma s s' Hs).
    destruct (ma s) as [(t,a)|]; destruct (ma' s') as [(t',a')|].
    - destruct Hma as [Ht Ha].
      exact (Hf _ _ Ha _ _ Ht).
    - contradict Hma.
    - exact I.
    - exact I.
  Qed.

  Global Instance err_propr: PropR (err : M A).
  Proof using.
    intros s s' Hs. exact I.
  Qed.

  Global Instance get_propr : PropR (get : M S).
  Proof using.
    intros s s' Hs.
    split; assumption.
  Qed.

  Global Instance put_propr : PropR (put : S -> M unit).
  Proof using.
    intros s s' Hs.
    intros t t' Ht.
    split.
    - assumption.
    - reflexivity.
  Qed.

End proper_section.
