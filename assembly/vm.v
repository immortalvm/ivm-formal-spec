(* coqc -Q . Assembly mon.v && coqc -Q . Assembly bits.v *)

Require Import Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

From Assembly Require Import mon bits.

(* Cf. the 'sigma' type of Equations. *)
Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.

Set Implicit Arguments.

Open Scope monad_scope.


Notation "'assert*' b res" := (if b then res else err) (at level 70).

Notation "'assert*' H ':=' b res" :=
  (match Sumbool.sumbool_of_bool b with
   | left H => res
   | right _ => err
   end) (at level 70).


(** ** Core *)

Module Type machine_type.

  (** This abstraction simplifies some of the definitions below (that
      otherwise tend to hang), possibly because we avoid coercions. *)

  Context
    (Addr: Type)
    `{H_eqdec: EqDec Addr}
    (available: Addr -> bool)
    (offset: Z -> Addr -> Addr) (* This should be a group action. *)
    (Cell: Type)

    (InputColor: Type)
    (allInputImages: list (Image InputColor))

    (OutputColor: Type)
    (Char: Type)
    (Byte: Type)
    (Sample: Type).

End machine_type.


Module core_module (MT: machine_type).

  Import MT.
  Existing Instance H_eqdec.

  Definition Memory := forall (a: Addr), available a -> option Cell.

  Context (M: Type -> Type)
          `(mem_mon: SMonad Memory M).

  Existing Instance mem_mon.

  Definition load (a: Addr): M Cell :=
    assert* H := available a
    let* s := get in
    match s a H with
    | Some x => ret x
    | _ => err
    end.

  Definition store0 (a: Addr) (o: option Cell) : M unit :=
    assert* available a
    let* s := get in
    let s' a' H := if eq_dec a a' then o else s a' H in
    put s'.

  Definition store a x := store0 a (Some x).

End core_module.
