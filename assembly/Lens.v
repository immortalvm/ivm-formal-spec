Require Import Utf8.

Require Import Equations.Equations.
Set Equations With UIP.

Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.
Require Import Assembly.Convenience.
Require Import Assembly.Dec.

Class Proj (S: Type) (X: Type) :=
{
  proj: S -> X;
  update: S -> X -> S;
  proj_update (s: S) (x: X) : proj (update s x) = x;
  update_proj (s: S) : update s (proj s) = s;
  update_update (s: S) (x: X) (x': X) : update (update s x) x' = update s x';
}.

(** Cf. [smon_rewrite] above. *)
Create HintDb proj discriminated.
Hint Rewrite @proj_update using (typeclasses eauto) : proj.
Hint Rewrite @update_proj using (typeclasses eauto) : proj.
Hint Rewrite @update_update using (typeclasses eauto) : proj.
Ltac proj_rewrite1 := rewrite_strat (outermost (hints proj)).
Ltac proj_rewrite := repeat proj_rewrite1.

Class Independent {S: Type}
      {X: Type} (PX: Proj S X)
      {Y: Type} (PY: Proj S Y) : Prop :=
{
  projY_updateX (s: S) (x: X) : proj (update s x) = proj s :> Y;
  projX_updateY (s: S) (y: Y) : proj (update s y) = proj s :> X;
  independent_commute (s: S) (x: X) (y: Y) :
    update (update s x) y = update (update s y) x;
}.

(** To see that [independent_commute] does not follow from the other
    properties, consider a square staircase. *)

Create HintDb independent discriminated.
Hint Rewrite @projY_updateX using (typeclasses eauto) : independent.
Hint Rewrite @projX_updateY using (typeclasses eauto) : independent.
Hint Rewrite @independent_commute using (typeclasses eauto) : independent.
Ltac independent_rewrite1 := rewrite_strat (outermost (hints independent)).
Ltac independent_rewrite := repeat independent_rewrite1.

Section product_section.

  Context {X Y: Type}.

  (* Since this instance is in a section and not marked global,
     it is removed from the instance database below. *)

  Program Instance proj_fst : Proj (X * Y) X :=
  {
    proj := fst;
    update s x := (x, snd s);
  }.

  Program Instance proj_snd : Proj (X * Y) Y :=
  {
    proj := snd;
    update s y := (fst s, y);
  }.

  Program Instance independent_projs : Independent proj_fst proj_snd.

  Context {S} (PX: Proj S X) (PY: Proj S Y) {Hd: Independent PX PY}.

  #[refine]
  Instance proj_prod : Proj S (X * Y) :=
  {
    proj s := (proj s, proj s);
    update s pair := update (update s (fst pair)) (snd pair);
  }.
  Proof.
    all: idestructs; now repeat (independent_rewrite1 || proj_rewrite || simpl).
  Defined.

  Context Z (PZ: Proj S Z) (Hdx: Independent PX PZ) (Hdy: Independent PY PZ).

  Global Instance independent_prod : Independent proj_prod PZ.
  Proof using Hdx Hdy.
    split.
    - intros s [x y]. simpl.
      transitivity (proj (update s x)); now independent_rewrite.
    - intros s z. simpl. f_equal; now independent_rewrite.
    - intros s [x y] z. simpl. now independent_rewrite.
  Qed.

  (** Beware: We do not make this global sine together with
      [independent_commute] it can send [typeclasses eauto]
      into an infinite loop. *)
  Instance independent_symm : Independent PY PX.
  Proof using Hd.
    split; intros; now independent_rewrite.
  Qed.

End product_section.

(** The projections from a record type have the same property. *)
