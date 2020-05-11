Require Import Utf8.

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

Require Export Coq.micromega.Lia.

Tactic Notation "by_lia" constr(P) "as" ident(H) := assert P as H; [lia|].

Ltac derive name term :=
  let H := fresh in
  let A := type of term in
  assert A as H;
  [ exact term | ];
  clear name;
  rename H into name.

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
