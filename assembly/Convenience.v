Require Import Utf8.


(** Options *)

Notation as_bool x := (if x then true else false).

Definition is_some {A} (x: option A) : Prop := if x then True else False.

Coercion is_some : option >-> Sortclass.

Lemma none_not_some {A B} : (None : option A) -> B.
Proof. easy. Qed.

Lemma not_some_none {A} {opt: option A} : not opt -> opt = None.
Proof.
  destruct opt as [x|].
  - intro F. contradict F. exact I.
  - intros _. reflexivity.
Qed.

Arguments exist {_} {_}.

Lemma some_some {A} {opt: option A} : opt -> {x | opt = Some x}.
Proof.
  destruct opt as [x|].
  - intros _. exact (exist x (@eq_refl (option A) (Some x))).
  - easy.
Qed.


(** Tactics *)

Require Export Coq.micromega.Lia.

Tactic Notation "by_lia" constr(P) "as" ident(H) := assert P as H; [lia|].

Ltac derive name term :=
  let H := fresh in
  let A := type of term in
  assert A as H;
  [ exact term | ];
  clear name;
  rename H into name.

(** Borrowed from http://ropas.snu.ac.kr/gmeta/source/html/LibTactics.html. *)
Ltac destructs H :=
let X := fresh in
let Y := fresh in
first [ destruct H as [X Y]; destructs X; destructs Y | idtac ].

Ltac idestructs := repeat (let X := fresh in intro X; destructs X).


(** ** Vectors and lists *)

Require Export Coq.Vectors.Vector.

Arguments Vector.nil {A}.
Arguments Vector.cons : default implicits.
Coercion Vector.to_list : Vector.t >-> list.

Export Coq.Vectors.Vector.VectorNotations.
(* Close Scope vector. *)

Require Export Coq.Lists.List.
Export ListNotations.
Open Scope list_scope.

Lemma to_list_equation_1: forall A, nil%vector = nil :> list A.
Proof. reflexivity. Qed.

Lemma to_list_equation_2: forall A n (x: A) (u: Vector.t A n), (x :: u)%vector = x :: u :> list A.
Proof. reflexivity. Qed.

Hint Rewrite to_list_equation_1 : to_list.
Hint Rewrite to_list_equation_2 : to_list.

Require Export Equations.Equations.

Derive Signature NoConfusion NoConfusionHom for Vector.t.

Lemma to_list_injective {A n} (u v: Vector.t A n) : u = v :> list A -> u = v.
Proof.
  induction n as [|n IH]; depelim u; depelim v.
  - easy.
  - simp to_list. intro Heq.
    f_equal; [|apply (IH u v)]; congruence.
Qed.


(** ** Relations *)

Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.

Section relation_section.

  Context {X} (RX: relation X).

  Definition option_relation : relation (option X) :=
    fun x x' => match x, x' with
             | None, _ => True
             | Some _, None => False
             | Some x, Some x' => RX x x'
             end.

  Global Instance option_relation_reflexive {HrX: Reflexive RX} : Reflexive option_relation.
  Proof.
    unfold option_relation. intros [x|]; reflexivity.
  Qed.

  Global Instance option_relation_transitive {HtX: Transitive RX} : Transitive option_relation.
  Proof.
    unfold option_relation.
    intros [x|] [y|] [z|] Hxy Hyz; try assumption.
    - transitivity y; assumption.
    - exfalso. assumption.
  Qed.

  Context {Y} (RY: relation Y).

  Definition prod_relation : relation (X * Y) :=
    fun xy xy' => match xy, xy' with (x,y), (x',y') => RX x x' /\ RY y y' end.

  Global Instance prod_relation_reflexive {HrX: Reflexive RX} {HrY: Reflexive RY} : Reflexive prod_relation.
  Proof.
    intros [x y]. split; reflexivity.
  Qed.

  Global Instance prod_relation_symmetric {HrX: Symmetric RX} {HrY: Symmetric RY} : Symmetric prod_relation.
  Proof.
    intros [x y] [x1 y1] [Hx Hy]. split; symmetry; assumption.
  Qed.

  Global Instance prod_relation_transitive {HrX: Transitive RX} {HrY: Transitive RY} : Transitive prod_relation.
  Proof.
    intros [x1 y1] [x2 y2] [x3 y3] [Hx12 Hy12] [Hx23 Hy23].
    split.
    - transitivity x2; assumption.
    - transitivity y2; assumption.
  Qed.

End relation_section.
