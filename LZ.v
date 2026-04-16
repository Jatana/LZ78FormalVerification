From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Matching LZ_Tokens.
Import ListNotations.

Module Impl.

  Fixpoint compress' (before after: list byte) (l: nat): list Token :=
    match after, l with
    | [], _ => []
    | hd :: tl, 0 => 
        match (find_largest_match before after) with 
        | None => Lit hd :: compress' (before ++ [hd]) tl 0
        | Some (length, offset) => Ref length offset :: compress' (before ++ [hd]) tl (length - 1)
        end
    | hd :: tl, S x => compress' (before ++ [hd]) tl x
    end.

  Definition compress (s: list byte): list Token :=
    compress' [] s 0.

  Fixpoint decompress' (acc : list byte) (l : list Token) : list byte :=
    match l with
    | [] => acc
    | Lit b :: tl => decompress' (acc ++ [b]) tl
    | Ref len off :: tl => decompress' (acc ++ (slice ((length acc) - off) len acc)) tl
    end.

  Definition decompress (l : list Token) : list byte :=
    decompress' [] l.

  Lemma compress_rolls : forall l before after, compress' before after l = compress' (before ++ (slice 0 l after)) (slice l (length after) after) 0.
  Proof.
    induction l.
      - intros. assert ((slice 0 0 after) = []). {
        specialize (slice_size after 0 0) as H. inversion H. destruct (slice 0 0) eqn:Hd.
        simpl. rewrite Hd. reflexivity. inversion H1. 
      }
        rewrite H. Search (_ ++ []). rewrite app_nil_r. assert (((slice 0 (length after) after)) = after). {
          eapply slice_l_length. lia.
        }
        rewrite H0. reflexivity.
      - intros. destruct after. simpl. reflexivity.
        simpl. assert ((slice l (S (length after)) after) = (slice l ((length after)) after)). {
          specialize (slice_p_l_length after (S (length after)) l) as Hslice.
          assert (length after - l <= S (length after)) by lia.
          specialize (Hslice H). rewrite Hslice. clear Hslice.

          specialize (slice_p_l_length after ((length after)) l) as Hslice.
          assert (length after - l <= (length after)) by lia.
          specialize (Hslice H0). rewrite Hslice.
          
          reflexivity.
        }
        rewrite H. assert (b :: slice 0 l after = [b] ++ slice 0 l after). simpl. reflexivity.
        rewrite H0. clear H0. specialize (IHl (before ++ [b]) after). rewrite app_assoc. exact IHl.
  Qed.

  Theorem correctness': forall n before after,
    length after <= n ->
    decompress' before (compress' before after 0) = before ++ after.
  Proof.
    induction n; simpl; intros.
    - inversion H.
      apply length_zero_iff_nil in H1. subst.
      simpl.
      rewrite app_nil_r. reflexivity.
    - destruct after.
      + simpl. rewrite app_nil_r. reflexivity.
      + simpl. destruct (find_largest_match before (_ :: after)) eqn:?.
        -- destruct p as [len off]; simpl.
           assert ((compress' (before ++ [b]) after (len - 1))
           = (compress' (before ++ [b] ++ (slice 0 (len - 1) after)) (slice (len - 1) (length after) after) 0)). {
             rewrite compress_rolls.
             Search ((_ ++ _) ++ _).
             rewrite app_assoc.
             reflexivity.
           }
           rewrite H0.
           pose proof (find_largest_match_corr3 before (b :: after) len off Heqo).
           assert (slice (length before - off) len before = slice 0 len (b :: after)). {
            destruct H1 as (H1 & _). eapply list_eqb_implies_equality.
            split; [apply byte_dec_bl | apply byte_dec_lb]. exact H1.
           }
           rewrite H2.
           assert (slice 0 len (b :: after) = [b] ++ slice 0 (len - 1) after). {
            simpl. destruct len. specialize (find_largest_match_corr1 before (b :: after) 0 off Heqo) as Hcor. lia.
            apply f_equal. simpl. assert (len - 0 = len) by lia. rewrite H3. reflexivity.
           }
           rewrite H3.
           assert (before ++ b :: after = (before ++ [b] ++ slice 0 (len - 1) after) ++ (slice (len - 1) (length after) after)). {
             assert ((((before ++ [b]) ++ (slice 0 (len - 1) after)) ++ (slice (len - 1) (length after) after)) = ((before ++ [b]) ++ (slice 0 (len - 1) after) ++ (slice (len - 1) (length after) after))). {
                rewrite app_assoc. reflexivity.
              }
              rewrite app_assoc. rewrite H4.
              assert ((before ++ b :: after) = ((before ++ [b]) ++ after)). {
                assert (b :: after = [b] ++ after). simpl. reflexivity.
                rewrite H5. rewrite app_assoc. reflexivity.
              }
              rewrite H5. apply f_equal. clear H4 H5 H3 H2 H1 H0 Heqo IHn.
              specialize (slice_eq after (len - 1)) as Hseq. 
              assert ((slice (len - 1) (length after) after) = slice (len - 1) (length after - (len - 1)) after). {
                eapply slice_p_l_length. lia.
              }
              rewrite H0. exact Hseq.
             }
           rewrite H4.
           eapply IHn.
           pose proof (slice_size after (len - 1) (length after)).
           rewrite H5.
           simpl in H.
           lia.
        -- simpl.
           specialize (IHn (before ++ [b]) after).
           assert ((before ++ [b]) ++ after = before ++ b :: after). {
            assert (b :: after = [b] ++ after). {
              simpl. reflexivity.
            }
            rewrite H0. rewrite app_assoc. reflexivity.
           }
           rewrite H0 in IHn.
           eapply IHn.
           simpl in H.
           lia.
  Qed.
  
  Theorem correctness: forall s,
    decompress (compress s) = s.
  Proof.
    unfold compress, decompress.
    intros.
    pose proof (correctness' (length s) [] s ltac:(lia)).
    rewrite app_nil_l in H.
    exact H.
  Qed.


  Definition compress_to_bytes s :=
    nat_to_bytes (length s) ++ (tokens_to_bytes (compress s)).
  
  Definition symb_weight := 
    fun x : Token => match x with 
      | Lit _ => 1
      | Ref _ _ => 3
    end.

  Lemma weight_bound : forall n before after,
    length after <= n -> 
    list_sum (map symb_weight (compress' before after 0)) <= length after.
  Proof.
    induction n.
      - intros. destruct after. 
        -- simpl. lia.
        -- inversion H.  
      - intros. destruct after.
        -- simpl. lia.
        -- simpl. destruct (find_largest_match before (b :: after)) eqn:Hd. destruct p.
          --- simpl. rewrite compress_rolls. specialize (find_largest_match_corr1 _ _ _ _ Hd) as Hlength.
              Search (S _ <= S _). apply le_n_S. Search (S _ <= _ -> _ <= _).
              specialize (find_largest_match_corr3 _ _ _ _ Hd) as Hcor.
              destruct Hcor as (Hcor1 & Hcor2).
              destruct after. simpl in Hcor2. lia.
              destruct after. simpl in Hcor2. lia.
              simpl. apply le_n_S. apply le_n_S.
              etransitivity. apply IHn. destruct n0. lia. destruct n0. lia. destruct n0. lia.
              simpl. 
              rewrite slice_size. simpl in H. lia.
              destruct n0. lia. destruct n0. lia. destruct n0. lia.
              simpl.
              rewrite slice_size. simpl in H. lia.
          --- simpl. apply le_n_S. eapply IHn. simpl in H. lia.   
  Qed.

  Lemma chunk_lemma : forall seq fl' n,
    length seq <= 8 -> n <= 8 ->
    (tokens_to_bytes_chunk_len seq n fl') <= ((list_sum (map symb_weight seq))).
  Proof.
    induction seq.
      - intros. simpl. destruct n; lia.
      - intros. simpl. destruct n. 
        -- lia.
        -- destruct a.
          --- simpl. replace (tokens_to_bytes_chunk_len seq n (fl' * 2 + 1) + 1) with (S (tokens_to_bytes_chunk_len seq n (fl' * 2 + 1))) by lia.
              apply le_n_S. eapply IHseq. simpl in H. lia. lia.
          --- simpl.  replace (tokens_to_bytes_chunk_len seq n (fl' * 2) + 2) with (S (S (tokens_to_bytes_chunk_len seq n (fl' * 2)))) by lia.
              do 2 apply le_n_S. etransitivity. eapply IHseq. simpl in H. lia.
              lia. lia.                     
  Qed.

  Lemma tokens_to_bytes_bounded_by_weight : forall seq,
    length (tokens_to_bytes seq) <= (9 * (list_sum (map symb_weight seq)) + 7) / 8.
  Proof.

  Admitted.

  Lemma upperbound'': forall before after,
    length (tokens_to_bytes (compress' before after 0)) <= (9 * (length after) + 7) / 8.
  Proof.
    intros. specialize (weight_bound before after) as H.
    specialize (tokens_to_bytes_bounded_by_weight (compress' before after 0)) as H'.
    assert ((9 * (list_sum (map symb_weight (compress' before after 0))) + 7) / 8 <= (9 * (length after) + 7) / 8).
    - Search (_ / _ <= _ / _). apply Nat.Div0.div_le_mono. lia.
    - etransitivity. exact H'. exact H0.
  Qed.

  Lemma upperbound': forall s,
    length (tokens_to_bytes (compress s)) <= (9 * length s + 7) / 8.
  Proof.
    intros. eapply upperbound''.
  Qed.

  Theorem upperbound: forall s,
    length (compress_to_bytes s) <= 9 * length s / 8 + 8 * Nat.log2 (length s) / 7.
  Proof.
    unfold compress_to_bytes.
    intros.
    rewrite length_app.
    pose proof (upperbound' s) as Hub.
    pose proof (nat_to_bytes_length (length s)) as Hl.
    lia.
  Qed.

End Impl.

Section Tests.
  Import Impl.

  Definition empty : list byte := [].
  Definition literals : list byte := ["010"%byte; "011"%byte].
  Definition compressed_literals : list Token := [Lit "010"%byte; Lit "011"%byte].
  Definition repeating : list byte := [zero; one; one; zero; one; zero; one; one; zero].
  Definition overlapping : list byte := [zero; one; zero; one; zero; one].
  Definition compressed_repeating : list Token := [Lit zero; Lit one; Lit one; Lit zero; Lit one; Ref 4 5].
  Definition compressed_overlapping : list Token := [Lit zero; Lit one; Lit zero; Lit one; Lit zero; Lit one].
  
  Example compress_empty_test :
    compress empty = [].
  Proof. reflexivity. Qed.
  
  Example decompress_empty_test :
    decompress [] = empty.
  Proof. reflexivity. Qed.
  
  Example compress_literals_test :
    compress literals = compressed_literals.
  Proof. reflexivity. Qed.
  
  Example decompress_literals_test :
    decompress compressed_literals = literals.
  Proof. reflexivity. Qed.
  
  Example compress_repetition_test :
    compress repeating = compressed_repeating.
  Proof. reflexivity. Qed.
  
  Example decompress_overlap_test :
    decompress compressed_overlapping = overlapping.
  Proof. reflexivity. Qed.
  
  Example correctness_empty :
    decompress (compress empty) = empty.
  Proof. reflexivity. Qed.
  
  Example correctness_simple :
    decompress (compress [zero]) = [zero].
  Proof. reflexivity. Qed.
  
  Example correctness_repeating :
    decompress (compress repeating) = repeating.
  Proof. reflexivity. Qed.
  
  Example correctness_overlapping :
    decompress (compress overlapping) = overlapping.
  Proof. reflexivity. Qed.

End Tests.
