From Assembly Require Import Basics Rel.

Unset Suggest Proof Using.

Section proper_section.

  Context (S: Type) {RS: Rel S}.

  Instance est_relation {X} {RX: Rel X}: Rel (EST S X).
  Proof.
    typeclasses eauto.
  Defined.

  (** Make sure we got what we wanted. *)
  Goal @est_relation = fun A RA => fun_relation RS (option_relation (prod_relation RA RS)).
    reflexivity.
  Qed.

  Instance est_pmon : SMonadPropR S (EST S).
  Proof.
    split.
    - intros
        X RX
        a a' Ha
        s s' Hs.
      simpl.
      split; assumption.

    - intros X Y RX RY.
      intros ma ma' Hma f f' Hf.
      intros s s' Hs. simpl.
      specialize (Hma s s' Hs).
      destruct (ma s) as [(a,t)|]; destruct (ma' s') as [(a',t')|].
      + destruct Hma as [Ht Ha].
        exact (Hf _ _ Ht _ _ Ha).
      + contradict Hma.
      + exact I.
      + exact I.

    - intros X RX mx
             s s' Hs.
      exact I.

    - intros s s' Hs.
      split; assumption.

    - intros s s' Hs.
      intros t t' Ht.
      now split.
  Qed.

End proper_section.
