From Stdlib Require Import Arith Strings.Byte List Lia.
Import ListNotations.

Module Util.

  (* returns s[p:p + l) *)
  Fixpoint slice {A : Type} (p l : nat) (s : list A) : list A :=
    match s, p with
    | cons hd tl, S q => slice q l tl
    | cons hd tl, 0 => match l with
                       | 0 => nil
                       | S k => hd :: (slice 0 k tl)
                       end
    | _, _ => nil
    end.

  Definition slice_std {A : Type} (p l : nat) (s : list A) : list A :=
    firstn l (skipn p s).

  Lemma slice_slice_std {A : Type} : forall s: list A, forall p l,
    slice p l s = slice_std p l s.
  Proof.
    unfold slice_std.
    induction s; simpl; intros.
    - now rewrite skipn_nil, firstn_nil.
    - destruct p, l; simpl; try f_equal; try auto.
  Qed.

  Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (s t : list A) : bool :=
    match (s, t) with
    | (cons s1 s2, cons t1 t2) => (eqb s1 t1) && (list_eqb eqb s2 t2)
    | (nil, nil) => true
    | _ => false
    end.

  Lemma list_eqb_implies_equality {A : Type} (eqb : A -> A -> bool) :
    forall s t, (forall x y, eqb x y = true <-> x = y) -> list_eqb eqb s t = true -> s = t.
  Proof.
    intros.
    revert t H0.
    induction s; intros; destruct t; simpl.
    - reflexivity.
    - discriminate.
    - discriminate.
    - simpl in H0.
      apply andb_prop in H0 as [? ?].
      rewrite (IHs t H1).
      destruct (eqb a a0) eqn:?.
      + specialize (H a a0).
        f_equal.
        tauto.
      + discriminate.
  Qed.

  Lemma equality_implies_length_eq {A : Type} (eqb : A -> A -> bool) :
    forall s t,
    list_eqb eqb s t = true -> length s = length t.
  Proof.
    induction s, t; simpl; intros.
    - trivial.
    - discriminate.
    - discriminate.
    - f_equal. apply IHs.
      apply andb_prop in H. destruct H.
      assumption.
  Qed.

  Lemma length_slice {A : Type} :
    forall s: list A, forall p l,
    length (slice p l s) = min l (length s - p).
  Proof.
    induction s; destruct p; simpl; intros.
    - lia.
    - lia.
    - destruct l; simpl.
      + trivial.
      + f_equal.
        specialize (IHs 0 l).
        lia.
    - apply IHs.
  Qed.

  Lemma slice_zero_length {A : Type} :
    forall s: list A, forall p,
    slice p 0 s = [].
  Proof.
    induction s; simpl; intros.
    - trivial.
    - destruct p.
      + trivial.
      + apply IHs.
  Qed.

  Lemma slice_slice {A : Type} :
    forall s: list A, forall p1 l1 p2 l2,
    slice p2 l2 (slice p1 l1 s) = slice (p1 + p2) (min l2 (l1 - p2)) s.
  Proof.
    induction s; simpl; intros.
    - trivial.
    - repeat match goal with
             | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?; simpl
             | [ |- _ ] => trivial || lia
             end.
      + assert (Heq: Nat.min l2 0 = 0) by lia. rewrite Heq.
        rewrite slice_zero_length. reflexivity.
      + f_equal.
        specialize (IHs 0 n 0 n0). rewrite IHs.
        assert (Heq0: 0 + 0 = 0) by lia. rewrite Heq0.
        assert (Heq1: n - 0 = n) by lia. rewrite Heq1.
        reflexivity.
  Qed.

  Lemma slice_eq {A : Type} :
    forall s: list A, forall l : nat,
    s = (slice 0 l s) ++ (slice l ((length s) - l) s).
  Proof.
    induction s; intros.
    - reflexivity.
    - destruct l; simpl.
      + specialize (IHs (length s)).
        assert (length s - length s = 0) by lia.
        rewrite H in IHs.
        rewrite slice_zero_length in IHs.
        rewrite app_nil_r in IHs.
        rewrite <- IHs.
        reflexivity.
      + rewrite <- IHs.
        reflexivity.
  Qed.

  Lemma slice_l_length {A : Type} :
    forall s: list A, forall l,
    length s <= l ->
    slice 0 l s = s.
  Proof.
    intros.
    pose proof (slice_eq s l) as Hs.
    assert (Hl: length s - l = 0) by lia.
    rewrite Hl in Hs.
    rewrite slice_zero_length in Hs.
    rewrite app_nil_r in Hs.
    auto.
  Qed.

  Lemma slice_p_l_length {A : Type} :
    forall s: list A, forall l p,
    (length s) - p <= l ->
    slice p l s = slice p ((length s) - p) s.
  Proof.
    induction s; intros; simpl.
    - reflexivity.
    - destruct p eqn:?.
      + destruct l eqn:?.
        * inversion H.
        * simpl in H.
          rewrite (slice_l_length s n ltac:(lia)).
          rewrite (slice_l_length s (length s) ltac:(lia)).
          reflexivity.
      + simpl in H.
        auto.
  Qed.

End Util.

Export Util.
