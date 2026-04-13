From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Matching LZ_Tokens LZ_Expand.
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
             admit.
           }
           rewrite H0.
           pose proof (find_largest_match_corr3 before (b :: after) len off Heqo).
           assert (slice (length before - off) len before = slice 0 len (b :: after)) by admit.
           rewrite H2.
           assert (slice 0 len (b :: after) = [b] ++ slice 0 (len - 1) after) by admit.
           rewrite H3.
           assert (before ++ b :: after = (before ++ [b] ++ slice 0 (len - 1) after) ++ (slice (len - 1) (length after) after)) by admit.
           rewrite H4.
           eapply IHn.
           pose proof (slice_size after (len - 1) (length after)).
           rewrite H5.
           simpl in H.
           lia.
        -- simpl.
           specialize (IHn (before ++ [b]) after).
           assert ((before ++ [b]) ++ after = before ++ b :: after) by admit.
           rewrite H0 in IHn.
           eapply IHn.
           simpl in H.
           lia.
  Admitted.
  
  Theorem correctness: forall s,
    decompress (compress s) = s.
  Proof.
    unfold compress, decompress.
    intros.
    pose proof (correctness' (length s) [] s ltac:(lia)).
    rewrite app_nil_l in H.
    exact H.
  Qed.

  Theorem upperbound: forall s,
    length (tokens_to_bytes_with_length (compress s)) <= 9 * length s / 8 + 8 * Nat.log2 (length s) / 7.
  Proof.
  Admitted.

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
