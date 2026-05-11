From Stdlib Require Import Arith Strings.Byte List Lia.
Import ListNotations.

Module Util.

  Lemma nth_in_index_lt_length {A}: forall a index, forall l: list A,
    nth_error l index = Some a ->
    index < length l.
  Proof.
    induction index; simpl; intros; destruct l; try discriminate; simpl.
    - lia.
    - rewrite <- Nat.succ_lt_mono.
      now apply IHindex.
  Qed.

  Lemma app_l_eq_length {A}: forall n, forall l1 l2 l3 l4: list A,
    l1 ++ l2 = l3 ++ l4 ->
    length l1 = n -> length l3 = n ->
    l1 = l3.
  Proof.
    induction n; intros.
    - apply length_zero_iff_nil in H0, H1.
      congruence.
    - destruct l1, l3; simpl in *; try lia.
      inversion H. subst.
      specialize (IHn l1 l2 l3 l4 H4 ltac:(lia) ltac:(lia)).
      congruence.
  Qed.

End Util.

Export Util.
