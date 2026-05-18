From Stdlib Require Import Arith List Lia Bool.
Require Import Utils.
Import ListNotations.

Module Dict.

  Definition dict_type := list (list bool).
  Definition empty_dict: dict_type := [[]].

  Definition num_bits_for_dict (dict_size: nat) :=
    if dict_size <=? 1 then 1
    else (Nat.log2 (dict_size - 1)) + 1.

  Fixpoint prefix_eq (p s: list bool) :=
    match p, s with
    | [], _ => true
    | _, [] => false
    | ph :: pt, sh :: st => if eqb ph sh then prefix_eq pt st else false
    end.

  Fixpoint find_largest_prefix' (dict: dict_type) (s: list bool) (index best_index best_len: nat) :=
    match dict with
    | [] => (best_index, best_len)
    | d :: ds =>
        let l := length d in
        if andb (prefix_eq d s) (best_len <? l) then
          find_largest_prefix' ds s (S index) index l
        else find_largest_prefix' ds s (S index) best_index best_len
    end.

  Definition find_largest_prefix (dict: dict_type) (s: list bool) :=
    find_largest_prefix' dict s 0 0 0.


  Lemma num_bits_for_dict_lower_bound: forall n,
    n <= 2 ^ (num_bits_for_dict n).
  Proof.
    intros.
    unfold num_bits_for_dict.
    destruct (n <=? 1) eqn:?.
    - apply leb_complete in Heqb.
      rewrite Nat.pow_1_r.
      lia.
    - apply leb_complete_conv in Heqb.
      pose proof (Nat.log2_spec (n - 1) ltac:(lia)) as [_ H2log].
      apply Nat.lt_sub_lt_add_l in H2log.
      assert (1 + 2 ^ S (Nat.log2 (n - 1)) = S (2 ^ S (Nat.log2 (n - 1)))) by lia.
      rewrite H in H2log.
      rewrite Nat.lt_succ_r in H2log.
      etransitivity.
      + exact H2log.
      + assert (Hp: 256 = 2^8) by now cbv.

        assert ((S (Nat.log2 (n - 1))) = ((Nat.log2 (n - 1) + 1))).
        lia.
        rewrite H0.
        lia.
  Qed.

  Lemma num_bits_for_dict_gt_one: forall dict_size,
    1 <= num_bits_for_dict dict_size.
  Proof.
    intros.
    unfold num_bits_for_dict.
    destruct (dict_size <=? 1); lia.
  Qed.

  Lemma prefix_eq_correctness: forall p s,
    prefix_eq p s = true <-> firstn (length p) s = p.
  Proof.
    induction p; simpl; intros.
    - tauto.
    - destruct s.
      + split; intros; discriminate.
      + split; intros; destruct (eqb a b) eqn:Heqb.
        * apply eqb_prop in Heqb.
          f_equal.
          -- auto.
          -- apply IHp. assumption.
        * discriminate.
        * apply IHp.
          injection H as H.
          assumption.
        * rewrite eqb_false_iff in Heqb.
          injection H as H.
          rewrite H in Heqb.
          contradiction.
  Qed.

  Lemma find_largest_prefix_correctness': forall ds dict s index bindex blen oindex olen,
    find_largest_prefix' ds s index bindex blen = (oindex, olen) ->
    nth_error dict bindex = Some (firstn blen s) ->
    blen <= length s ->
    (forall i, nth_error ds i = nth_error dict (index + i)) ->
    olen <= length s /\ nth_error dict oindex = Some (firstn olen s).
  Proof.
    induction ds; intros * Hflp Hnth Hlen Hfa; simpl in *.
    - inversion Hflp. subst.
      tauto.
    - destruct (prefix_eq a s && (blen <? length a))%bool eqn:?.
      + apply andb_prop in Heqb as [Hpr Hblen].
        apply prefix_eq_correctness in Hpr.
        rewrite Nat.ltb_lt in Hblen.
        eapply IHds.
        * eassumption.
        * rewrite Hpr.
          specialize (Hfa 0).
          simpl in Hfa.
          rewrite Nat.add_0_r in Hfa.
          congruence.
        * now apply firstn_sublist_length_leq.
        * intro i.
          specialize (Hfa (S i)).
          rewrite nth_error_cons_succ in Hfa.
          assert (Hr: index + S i = S index + i) by lia.
          rewrite Hr in Hfa.
          eassumption.
      + eapply IHds; try eassumption.
        intro i.
        specialize (Hfa (S i)).
        rewrite nth_error_cons_succ in Hfa.
        assert (Hr: index + S i = S index + i) by lia.
        rewrite Hr in Hfa.
        eassumption.
  Qed.

  Lemma find_largest_prefix_correctness: forall dict s index len,
    find_largest_prefix dict s = (index, len) ->
    nth_error dict 0 = Some [] ->
    len <= length s /\ nth_error dict index = Some (firstn len s).
  Proof.
    unfold find_largest_prefix.
    intros * Hflp Hfst.
    pose proof (find_largest_prefix_correctness' dict dict s 0 0 0 index len Hflp) as Hs.
    simpl in *.
    specialize (Hs Hfst ltac:(lia)).
    auto.
  Qed.

  Lemma find_largest_prefix_corr1' : forall dict s index best_index best_len n l,
    find_largest_prefix' dict s index best_index best_len = (n, l) -> l >= best_len.
  Proof.
    induction dict.
      - intros. simpl in H. inversion H. lia.
      - intros. simpl in H. destruct (best_len <? length a) eqn:Hineq.
        * destruct (prefix_eq a s && true).
          + rewrite Nat.ltb_lt in Hineq. assert (l >= length a). 2: { lia. }
            eapply IHdict. exact H.
          + rewrite Nat.ltb_lt in Hineq. eapply IHdict. exact H.
        * Search (_ <? _ = false). rewrite Nat.ltb_ge in Hineq. 
          replace (prefix_eq a s && false) with (false) in H.
            + eapply IHdict. exact H.
            + destruct (prefix_eq a s); auto.
  Qed.   

  Lemma find_largest_prefix_opt': forall dict s t index best_index best_len n l,
    (find_largest_prefix' dict (s ++ t) index best_index best_len) = (n, l)
      -> In s dict -> l >= length s.
  Proof.
    induction dict.
      - intros. inversion H0.
      - intros. inversion H0.
        + subst. simpl in H. assert (prefix_eq s (s ++ t) = true).
          * apply prefix_eq_correctness. Search (firstn _ _ = _). replace (length s) with (length s + 0) by (ltac:(lia)). erewrite firstn_app_2.
            simpl. Search (_ ++ []). rewrite app_nil_r. reflexivity.
          * rewrite H1 in H. destruct (best_len <? length s) eqn:Hbound.
            -- simpl in H. Search (_ <? _ = true). rewrite Nat.ltb_lt in Hbound.
               eapply find_largest_prefix_corr1'. exact H.
            -- replace (true && false) with (false) in H. 2: { auto. }
               rewrite Nat.ltb_ge in Hbound. assert (l >= best_len). 2: { lia. }
               eapply find_largest_prefix_corr1'. exact H.
        + simpl in H. destruct (prefix_eq a (s ++ t) && (best_len <? length a)).
          * eapply IHdict. exact H. exact H1.
          * eapply IHdict. exact H. exact H1.
  Qed.

  Lemma find_largest_prefix_opt: forall dict s t index len,
    find_largest_prefix dict (s ++ t) = (index, len)
      -> In s dict -> len >= length s.
  Proof.
    intros. unfold find_largest_prefix in H. 
    eapply find_largest_prefix_opt'. exact H. exact H0.
  Qed.


  Lemma num_bits_for_dict_mono : forall a b,
      a <= b ->
      num_bits_for_dict a <= num_bits_for_dict b.
  Proof.
    intros. unfold num_bits_for_dict.
    destruct (a <=? 1) eqn:Ha;
    destruct (b <=? 1) eqn:Hb; try lia.
    2: {
      apply Nat.add_le_mono; try lia.
      apply Nat.log2_le_mono. lia.
    }
    rewrite Nat.leb_nle in Ha. 
    rewrite Nat.leb_le in Hb. lia.
  Qed.

End Dict.

Export Dict.
