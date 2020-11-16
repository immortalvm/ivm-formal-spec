From Assembly Require Export Basics Rel MonExtras.

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

  Context {RRS: Reflexive RS}.
  Existing Instance RRS.

  Proposition err_less_eq {X} {RX: Rel X} (mx: EST S X) (Hmx: mx ⊑ err) : mx = err.
  Proof.
    extensionality s.
    specialize (Hmx s s (RRS s)).
    destruct (mx s) as [[x s']|].
    - exfalso. exact Hmx.
    - reflexivity.
  Qed.

  Context {TRS: Transitive RS}.
  Existing Instance TRS.

  Instance est_transitive A {RA: Rel A} {TRA: Transitive RA}: Transitive (@est_relation A RA).
  Proof.
    typeclasses eauto.
  Qed.

  Context {ARS: Antisymmetric S eq RS}.

  Global Instance prod_relation_antisymm
           {X Y} {RX: Rel X} {RY: Rel Y}
           (ARX: Antisymmetric X eq RX)
           (ARY: Antisymmetric Y eq RY) :
    Antisymmetric (X * Y) eq (prod_relation RX RY).
  Proof.
    intros [x y] [x' y'] [Hx Hy] [Hx' Hy'].
    f_equal.
    - apply (ARX _ _ Hx Hx').
    - apply (ARY _ _ Hy Hy').
  Qed.

  Global Instance option_relation_antisymm
           {X} {RX: Rel X} (ARX: Antisymmetric X eq RX) :
    Antisymmetric (option X) eq (option_relation RX).
  Proof.
    intros [x|] [x'|] H H'.
    - f_equal. exact (ARX _ _ H H').
    - exfalso. exact H.
    - exfalso. exact H'.
    - reflexivity.
  Qed.

  Instance fun_relation_antisymm
           {X} {RX: Rel X} (RRX: Reflexive RX)
           {Y} {RY: Rel Y} (ARY: Antisymmetric Y eq RY) : Antisymmetric (X -> Y) eq (fun_relation RX RY).
  Proof.
    intros f g Hfg Hgf.
    extensionality x.
    apply (ARY (f x) (g x)).
    - exact (Hfg x x (RRX x)).
    - exact (Hgf x x (RRX x)).
  Qed.

  Global Instance less_antisym {X} {RX: Rel X} {ARX: Antisymmetric X eq RX} : Antisymmetric (EST S X) eq est_relation.
  Proof.
    typeclasses eauto.
  Qed.

End proper_section.
