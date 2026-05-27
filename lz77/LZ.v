From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Matching LZ_Tokens.
Import ListNotations.

Module Impl.

  Fixpoint compress_aux (before after: list byte) (l: nat): list Token :=
    match after, l with
    | [], _ => []
    | hd :: tl, 0 =>
        match (find_largest_match before after) with
        | None => Lit hd :: compress_aux (before ++ [hd]) tl 0
        | Some (length, offset) => Ref length offset :: compress_aux (before ++ [hd]) tl (length - 1)
        end
    | hd :: tl, S x => compress_aux (before ++ [hd]) tl x
    end.

  Definition compress (s: list byte): list Token :=
    compress_aux [] s 0.

  Fixpoint decompress_aux (acc : list byte) (l : list Token) : list byte :=
    match l with
    | [] => acc
    | Lit b :: tl => decompress_aux (acc ++ [b]) tl
    | Ref len off :: tl => decompress_aux (acc ++ (slice ((length acc) - off) len acc)) tl
    end.

  Definition decompress (l : list Token) : list byte :=
    decompress_aux [] l.

  Definition compress_to_bytes s :=
    nat_to_bytes (length s) ++ (tokens_to_bytes (compress s)).

  Definition decompress_from_bytes s :=
    let (len, compressed) := bytes_to_nat s in
    decompress (bytes_to_tokens compressed).


  Lemma compress_produces_valid_tokens: forall after before l,
    Forall valid_token (compress_aux before after l).
  Proof.
    induction after; intros; simpl.
    - constructor.
    - destruct l.
      + destruct (find_largest_match before (a :: after)) eqn:?.
        * destruct p as [len off].
          constructor.
          -- pose proof (find_largest_match_length_bounds before (a :: after) len off Heqo).
             pose proof (find_largest_match_offset_bounds before (a :: after) len off Heqo).
             simpl. tauto.
          -- apply IHafter.
        * constructor.
          -- constructor.
          -- apply IHafter.
      + apply IHafter.
  Qed.

  Lemma compress_rolls : forall l before after,
      compress_aux before after l
      = compress_aux (before ++ (slice 0 l after)) (slice l (length after) after) 0.
  Proof.
    induction l; intros.
    - assert ((slice 0 0 after) = []). {
        specialize (length_slice after 0 0) as H.
        inversion H.
        destruct (slice 0 0) eqn:Hd; simpl.
        - now rewrite Hd.
        - discriminate.
      }
      rewrite H.
      rewrite app_nil_r.
      assert (((slice 0 (length after) after)) = after) by (eapply slice_l_length; lia).
      now rewrite H0.
    - destruct after; simpl.
      + reflexivity.
      + assert ((slice l (S (length after)) after) = (slice l ((length after)) after)). {
        specialize (slice_p_l_length after (S (length after)) l) as Hslice.
        assert (length after - l <= S (length after)) by lia.
        specialize (Hslice H). rewrite Hslice. clear Hslice.
        specialize (slice_p_l_length after ((length after)) l) as Hslice.
        assert (length after - l <= (length after)) by lia.
        specialize (Hslice H0).
        now rewrite Hslice.
      }
      rewrite H.
      assert (b :: slice 0 l after = [b] ++ slice 0 l after) by reflexivity.
      rewrite H0. clear H0.
      specialize (IHl (before ++ [b]) after).
      now rewrite app_assoc.
  Qed.

  Theorem compress_decompress_correctness_aux: forall n before after,
    length after <= n ->
    decompress_aux before (compress_aux before after 0) = before ++ after.
  Proof.
    induction n; simpl; intros.
    - inversion H.
      apply length_zero_iff_nil in H1.
      subst. simpl.
      rewrite app_nil_r. reflexivity.
    - destruct after.
      + simpl. rewrite app_nil_r. reflexivity.
      + simpl. destruct (find_largest_match before (_ :: after)) eqn:?.
        -- destruct p as [len off]; simpl.
           assert ((compress_aux (before ++ [b]) after (len - 1))
                   = (compress_aux (before ++ [b] ++ (slice 0 (len - 1) after))
                        (slice (len - 1) (length after) after) 0)).
           {
             rewrite compress_rolls.
             rewrite app_assoc.
             reflexivity.
           }
           rewrite H0.
           pose proof (find_largest_match_eq before (b :: after) len off Heqo).
           assert (slice (length before - off) len before = slice 0 len (b :: after)).
           {
            destruct H1 as (H1 & _). eapply list_eqb_implies_equality.
            split; [apply byte_dec_bl | apply byte_dec_lb]. exact H1.
           }
           rewrite H2.
           assert (slice 0 len (b :: after) = [b] ++ slice 0 (len - 1) after).
           {
             simpl. destruct len.
             specialize (find_largest_match_length_bounds before (b :: after) 0 off Heqo) as Hcor. lia.
             apply f_equal. simpl. assert (len - 0 = len) by lia. rewrite H3. reflexivity.
           }
           rewrite H3.
           assert (before ++ b :: after
                   = (before ++ [b] ++ slice 0 (len - 1) after)
                       ++ (slice (len - 1) (length after) after)).
           {
             assert ((((before ++ [b]) ++ (slice 0 (len - 1) after))
                        ++ (slice (len - 1) (length after) after))
                     = ((before ++ [b]) ++ (slice 0 (len - 1) after)
                          ++ (slice (len - 1) (length after) after))).
             {
               rewrite app_assoc. reflexivity.
             }
             rewrite app_assoc. rewrite H4.
             assert ((before ++ b :: after) = ((before ++ [b]) ++ after)).
             {
               assert (b :: after = [b] ++ after) by reflexivity.
               rewrite H5. rewrite app_assoc. reflexivity.
             }
             rewrite H5. apply f_equal. clear H4 H5 H3 H2 H1 H0 Heqo IHn.
             specialize (slice_eq after (len - 1)) as Hseq.
             assert ((slice (len - 1) (length after) after)
                     = slice (len - 1) (length after - (len - 1)) after).
             {
               eapply slice_p_l_length. lia.
             }
             rewrite H0. exact Hseq.
           }
           rewrite H4.
           eapply IHn.
           pose proof (length_slice after (len - 1) (length after)).
           rewrite H5.
           simpl in H.
           lia.
        -- simpl.
           specialize (IHn (before ++ [b]) after).
           assert ((before ++ [b]) ++ after = before ++ b :: after).
           {
             assert (b :: after = [b] ++ after) by reflexivity.
             rewrite H0. rewrite app_assoc. reflexivity.
           }
           rewrite H0 in IHn.
           eapply IHn.
           simpl in H.
           lia.
  Qed.

  Theorem compress_decompress_correctness: forall s,
    decompress (compress s) = s.
  Proof.
    unfold compress, decompress.
    intros.
    pose proof (compress_decompress_correctness_aux (length s) [] s ltac:(lia)).
    rewrite app_nil_l in H.
    exact H.
  Qed.

  Theorem compress_to_bytes_correctness: forall s,
    decompress_from_bytes (compress_to_bytes s) = s.
  Proof.
    intros.
    unfold decompress_from_bytes, compress_to_bytes.
    destruct s.
    - reflexivity.
    - rewrite nat_to_bytes_correctness, tokens_to_bytes_to_tokens_correctness.
      + apply compress_decompress_correctness.
      + apply compress_produces_valid_tokens.
      + simpl. lia.
  Qed.

  Lemma compress_weight_upper_bound : forall n before after,
    length after <= n ->
    list_sum (map token_weight (compress_aux before after 0)) <= length after.
  Proof.
    induction n; intros; destruct after; simpl; try lia.
    - inversion H.
    - destruct (find_largest_match before (b :: after)) as [[len off] | _] eqn:Hd.
      + rewrite compress_rolls.
        specialize (find_largest_match_length_bounds _ _ _ _ Hd) as Hlength.
        apply le_n_S.
        specialize (find_largest_match_eq _ _ _ _ Hd) as Hcor.
        destruct Hcor as (Hcor1 & Hcor2).
        do 2 (destruct after; simpl in Hcor2; try lia).
        do 2 apply le_n_S.
        etransitivity.
        * apply IHn.
          do 3 (destruct len; try lia).
          simpl in H |- *.
          rewrite length_slice.
          lia.
        * do 3 (destruct len; try lia).
          simpl in H |- *.
          rewrite length_slice.
          match goal with
          | [ |- _ <= ?fn ?a ] => assert (He: fn a = length after) by reflexivity; rewrite He
          end.
          lia.
      + eapply le_n_S, IHn.
        simpl in H. lia.
  Qed.

  Lemma compress_bytes_upper_bound_aux: forall before after,
      length (tokens_to_bytes (compress_aux before after 0))
      <= (9 * length after + 7) / 8.
  Proof.
    intros. specialize (compress_weight_upper_bound (length after) before after ltac:(lia)) as H.
    pose proof (compress_produces_valid_tokens after before 0) as Hv.
    specialize (tokens_to_bytes_bounded_by_weight (length (compress_aux before after 0))
                (compress_aux before after 0) Hv ltac:(lia)) as H'.
    etransitivity. exact H'.
    apply Nat.Div0.div_le_mono.
    lia.
  Qed.

  Theorem compress_bytes_upper_bound: forall s,
    length (compress_to_bytes s) <= (9 * length s + 7) / 8 + Nat.log2 (length s) / 7 + 1.
  Proof.
    unfold compress_to_bytes, compress.
    intros.
    rewrite length_app.
    pose proof (compress_bytes_upper_bound_aux [] s) as Hub.
    pose proof (nat_to_bytes_length (length s)) as Hl.
    lia.
  Qed.

End Impl.

Export Impl.
