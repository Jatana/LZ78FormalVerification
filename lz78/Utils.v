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

  Lemma firstn_sublist_length_leq {A}: forall p s: list A,
    firstn (length p) s = p ->
    length p <= length s.
  Proof.
    induction p; intros s Hfn; simpl in *.
    - lia.
    - destruct s; simpl in *.
      + discriminate.
      + apply le_n_S, IHp.
        congruence.
  Qed.

  Lemma app_l_eq_length {A}: forall n, forall l1 l2 l3 l4: list A,
    l1 ++ l2 = l3 ++ l4 ->
    length l1 = n ->
    length l3 = n ->
    l1 = l3.
  Proof.
    induction n; intros * Heq Hlen1 Hlen3.
    - apply length_zero_iff_nil in Hlen1, Hlen3.
      congruence.
    - destruct l1, l3; simpl in *; try lia.
      inversion Heq. subst.
      specialize (IHn l1 l2 l3 l4 H1 ltac:(lia) ltac:(lia)).
      congruence.
  Qed.

  Lemma nth_error_some {A : Type}: forall i (l1 : list A) (l2 : list A) x,
    nth_error l1 i = Some x ->
    nth_error (l1 ++ l2) i = Some x.
  Proof.
    induction i; intros * H; destruct l1; simpl in *; auto; inversion H.
  Qed.

  Lemma skipn_length {A : Type} : forall n (l l' : list A) x,
    skipn n l = x :: l' ->
    length l >= S n.
  Proof.
    induction n; intros * H. simpl in *.
    - rewrite H.
      simpl. lia.
    - destruct l; simpl.
      + inversion H.
      + specialize (IHn _ _ _ H). lia.
  Qed.

End Util.

Export Util.
