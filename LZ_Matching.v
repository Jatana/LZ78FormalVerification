From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils.
Import ListNotations.

Module Matching.

  Fixpoint find_match' {A : Type} (eqb : A -> A -> bool) (s t : list A) (p : nat) : option nat :=
    if (list_eqb eqb (slice p (length t) s) t)
    then Some p
    else match p with
         | S q => find_match' eqb s t q
         | 0 => None
         end.

  Definition find_match {A : Type} (eqb : A -> A -> bool) (s t : list A) : option nat :=
    find_match' eqb s t (length s).

  Lemma find_match_corr' {A : Type} (eqb : A -> A -> bool) (s t : list A) (n p : nat) :
    find_match' eqb s t p = Some n ->
    list_eqb eqb (slice n (length t) s) t = true.
  Proof.
    induction p; simpl; intros;
    match goal with
    | [ H: context[if ?c then _ else _] |- _ ] => destruct c eqn:?
    end.
    - injection H as H. subst.
      assumption.
    - discriminate.
    - injection H as H. subst.
      assumption.
    - eapply IHp. assumption.
  Qed.

  Lemma find_match_corr {A : Type} (eqb : A -> A -> bool) (s t : list A) (n : nat) :
    find_match eqb s t = Some n ->
    list_eqb eqb (slice n (length t) s) t = true /\
    ((length t >= 1) -> n <= length s - length t).
  Proof.
    assert (H: find_match eqb s t = Some n -> list_eqb eqb (slice n (length t) s) t = true). {
      intros.
      eapply find_match_corr'.
      unfold find_match in *.
      eassumption.
    }
    intro H0.
    specialize (H H0).
    pose proof (equality_implies_length_eq eqb (slice n (length t) s) t H) as H2.
    rewrite slice_size in H2.
    split.
    - assumption.
    - lia.
  Qed.

  Fixpoint find_largest_match' (before after: list byte) (l : nat) : option (nat * nat) :=
    match l with
    | 2 => None
    | 1 => None
    | 0 => None
    | S k =>
        let suff := (slice ((length before) - 4098) 4098 before) in
        let m := find_match Byte.eqb suff (slice 0 l after) in
        match m with
        | None => find_largest_match' before after k
        | Some p => Some (l, (length suff) - p)
        end
    end.

  (* returns 3 <= length <= 18, 3 <= offset <= 4098 *)
  Definition find_largest_match (before after: list byte): option (nat * nat) :=
    find_largest_match' before after (min (length after) 18).

  Definition one : byte := "1"%byte.
  Definition zero : byte := "0"%byte.

  Example find_largest_match_test1 : find_largest_match [zero; one; one; zero; one] [zero; one; one; zero] = Some (4, 5).
  Proof. reflexivity. Qed.

  Example find_largest_match_test2 : find_largest_match [zero; one] [zero] = None.
  Proof. reflexivity. Qed.

  Lemma find_largest_match_corr1' : forall s t l len off,
    l <= 18 ->
    find_largest_match' s t l = Some (len, off) ->
    3 <= len <= 18.
  Proof.
    intros s t l. revert s t.
    induction l; simpl; intros;
    repeat match goal with
           | [ H: context[match ?e with _ => _ end] |- _ ] => destruct e; simpl
           | [ |- _ ] => discriminate
           end.
           - injection H0 as H0. lia.
           - eapply IHl.
             + lia.
             + eassumption.
  Qed.

  Lemma find_largest_match_corr1 : forall s t len off,
    find_largest_match s t = Some (len, off) ->
    3 <= len <= 18.
  Proof.
    intros. unfold find_largest_match in *.
    assert (Nat.min (length t) 18 <= 18) by lia.
    eapply find_largest_match_corr1'; eassumption.
  Qed.

  Lemma find_largest_match_corr2' : forall s t l len off,
    length t >= 3 ->
    find_largest_match' s t l = Some (len, off) ->
    3 <= off <= 4098.
  Proof.
    intros s t l. revert s t.
    induction l; simpl; intros.
    - discriminate.
    - do 2 (destruct l; try discriminate).
      remember (slice (length s - 4098) 4098 s) as suff.
      remember (slice 0 (S (S (S l))) t) as pref.
      destruct (find_match eqb suff pref) eqn:Hd.
      + inversion H0. split.
        * assert (list_eqb Byte.eqb (slice n (length pref) suff) pref = true) by
            (now apply find_match_corr).
          specialize (equality_implies_length_eq eqb (slice n (length pref) suff) pref H1) as Heq.
          assert (length pref = length (slice 0 (S (S (S l))) t)) by (now f_equal).
          specialize (slice_size t 0 (S (S (S l)))) as Hsize.
          rewrite <- H4 in Hsize.
          assert ((length pref) >= 3). {
            destruct pref.
            - simpl in Hsize.
              destruct t. inversion H.
              destruct t; simpl in H, Hsize; lia.
            - destruct pref.
              + simpl in Hsize.
                destruct t. inversion H.
                destruct t; simpl in H, Hsize; lia.
              + destruct pref.
                * simpl in Hsize.
                  destruct t. inversion H.
                  destruct t; simpl in H, Hsize.
                  -- lia.
                  -- destruct t; simpl in H, Hsize; lia.
                * simpl. lia.
          }
          assert (length (slice n (length pref) suff) >= 3) by lia.
          specialize (slice_size suff n (length pref)) as Hslice.
          rewrite Hslice in H6. lia.
        * specialize (slice_size s (length s - 4098) 4098) as HH.
          assert (length suff = length (slice (length s - 4098) 4098 s)) by (now f_equal).
          rewrite <- H1 in HH. lia.
      + eapply IHl; eassumption.
  Qed.

  Lemma find_largest_match_corr2 : forall s t len off,
    find_largest_match s t = Some (len, off) ->
    3 <= off <= 4098.
  Proof.
    intros. unfold find_largest_match in *.
    do 3 try destruct t; try discriminate.
    assert (length (b :: b0 :: b1 :: t) >= 3) by (simpl; lia).
    eapply find_largest_match_corr2'; eassumption.
  Qed.

  Lemma find_largest_match_corr3' (s t : list byte) (n l len off : nat) :
    find_largest_match' s t l = Some (len, off) ->
    l <= length t ->
    list_eqb Byte.eqb (slice ((length s) - off) len s) (slice 0 len t) = true /\
    len <= length t.
  Proof.
    revert s t n len off.
    induction l; simpl; intros.
    - discriminate.
    - do 2 (destruct l; try discriminate).
      destruct (find_match eqb (slice (length s - 4098) 4098 s)
                               (slice 0 (S (S (S l))) t)) eqn:Hd.
      + inversion H; subst. clear H.
        remember (slice (length s - 4098) 4098 s) as suff.
        remember (slice 0 (S (S (S l))) t) as pref.
        specialize (find_match_corr Byte.eqb suff pref n0 Hd) as Hslice.
        specialize (slice_slice s (length s - 4098) 4098 n0 (length pref)) as Hdouble.
        rewrite Heqsuff in Hslice. rewrite Hdouble in Hslice.
        destruct Hslice as (Hslice1 & Hslice2).
        assert (length t >= 3) by lia.
        assert (length pref >= 1). {
          specialize (slice_size t 0 (S (S (S l)))) as Hpref_size.
          rewrite <- Heqpref in Hpref_size.
          lia.
        }
        specialize (Hslice2 H1).
        rewrite <- Heqsuff in Hslice2.
        assert ((length s - (length suff - n0)) = (length s - 4098 + n0)). {
          specialize (slice_size s (length s - 4098) 4098) as Hsuff_size.
          rewrite <- Heqsuff in Hsuff_size.
          lia.
        }
        rewrite H2.
        assert (length pref = (S (S (S l)))).
        specialize (slice_size t 0 (S (S (S l)))) as Hpref_size.
        rewrite <- Heqpref in Hpref_size. lia.
        rewrite H3 in Hslice1.
        assert ((4098 - n0) >= length pref). {
          specialize (equality_implies_length_eq Byte.eqb (slice (length s - 4098 + n0)
                     (Nat.min (S (S (S l))) (4098 - n0)) s) pref Hslice1) as Hlength_eq.
          specialize (slice_size s (length s - 4098 + n0) (Nat.min (S (S (S l))) (4098 - n0))) as Hlen.
          rewrite Hlen in Hlength_eq.
          lia.
        }
        rewrite H3 in H4.
        assert (Nat.min (S (S (S l))) (4098 - n0) = (S (S (S l)))) by lia.
        rewrite H5 in Hslice1.
        split; assumption.
      + apply IHl; assumption || lia.
  Qed.

  Lemma find_largest_match_corr3 (s t : list byte) (len off : nat) :
    find_largest_match s t = Some (len, off) ->
    list_eqb Byte.eqb (slice ((length s) - off) len s) (slice 0 len t) = true /\ len <= length t.
  Proof.
    intros. unfold find_largest_match in H.
    eapply find_largest_match_corr3'.
    - eassumption.
    - eassumption.
    - lia.
  Qed.

End Matching.

Export Matching.
