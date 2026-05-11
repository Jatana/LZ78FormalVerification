From Stdlib Require Import Arith Strings.Byte List Lia.
Import ListNotations.

Module Dict.

  Definition dict_type := list (list byte).
  Definition empty_dict: dict_type := [[]].

  Definition num_bytes_for_dict (dict_size: nat) :=
    if dict_size <=? 1 then 1
    else (Nat.log2 (dict_size - 1) / 8) + 1.

  Fixpoint prefix_eq (p s: list byte) :=
    match p, s with
    | [], _ => true
    | _, [] => false
    | ph :: pt, sh :: st => if Byte.eqb ph sh then prefix_eq pt st else false
    end.

  Fixpoint find_largest_prefix' (dict: dict_type) (s: list byte) (index best_index best_len: nat) :=
    match dict with
    | [] => (best_index, best_len)
    | d :: ds =>
        let l := length d in
        if andb (prefix_eq d s) (best_len <? l) then
          find_largest_prefix' ds s (S index) index l
        else find_largest_prefix' ds s (S index) best_index best_len
    end.

  Definition find_largest_prefix (dict: dict_type) (s: list byte) :=
    find_largest_prefix' dict s 0 0 0.


  Lemma num_bytes_for_dict_lower_bound: forall n,
    n <= 256 ^ (num_bytes_for_dict n).
  Proof.
    intros.
    unfold num_bytes_for_dict.
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
        rewrite Hp.
        rewrite <- Nat.pow_mul_r by lia.
        apply Nat.pow_le_mono_r. lia.
        rewrite Nat.mul_add_distr_l.
        pose proof (Nat.div_mod_eq (Nat.log2 (n - 1)) 8).
        pose proof (Nat.mod_upper_bound (Nat.log2 (n - 1)) 8 ltac:(lia)).
        lia.
  Qed.

  Lemma num_bytes_for_dict_gt_one: forall dict_size,
    1 <= num_bytes_for_dict dict_size.
  Proof.
    intros.
    unfold num_bytes_for_dict.
    destruct (dict_size <=? 1); lia.
  Qed.

  Lemma prefix_eq_correctness: forall p s,
    prefix_eq p s = true <-> firstn (length p) s = p.
  Proof.
    induction p; simpl; intros.
    - tauto.
    - destruct s.
      + split; intros; discriminate.
      + split; intros; destruct (a =? b)%byte eqn:Heqb.
        * apply byte_dec_bl in Heqb.
          f_equal.
          -- auto.
          -- apply IHp. assumption.
        * discriminate.
        * apply IHp.
          injection H as H.
          assumption.
        * apply eqb_false in Heqb.
          injection H as H.
          rewrite H in Heqb.
          contradiction.
  Qed.

  Lemma find_largest_prefix_correctness: forall dict s index len,
    find_largest_prefix dict s = (index, len) ->
    In [] dict ->
    len <= length s /\ nth_error dict index = Some (firstn len s).
  Proof.
  Admitted.

  Lemma num_bytes_for_dict_mono : forall a b,
      a <= b ->
      num_bytes_for_dict a <= num_bytes_for_dict b.
  Proof.
    intros. unfold num_bytes_for_dict.
    destruct (a <=? 1) eqn:Ha;
    destruct (b <=? 1) eqn:Hb; try lia.
    2: {
      apply Nat.add_le_mono; try lia.
      apply Nat.Div0.div_le_mono; try lia.        
      apply Nat.log2_le_mono. lia.
    }
    rewrite Nat.leb_nle in Ha. 
    rewrite Nat.leb_le in Hb. lia.
  Qed.

End Dict.

Export Dict.
