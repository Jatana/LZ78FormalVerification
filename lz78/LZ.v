From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Dict LZ_Tokens.
Import ListNotations.

Module Impl.

  Fixpoint compress' (fuel: nat) (dict: dict_type) (s: list byte) :=
    match fuel with
    | 0 => []
    | S fuel =>
        match s with
        | [] => []
        | _ =>
            let (index, len) := find_largest_prefix dict s in
            match skipn len s with
            | [] => [Last index]
            | next :: rest =>
                Tok index next :: compress' fuel (dict ++ [firstn len s ++ [next]]) rest
            end
        end
    end.

  Definition compress (s: list byte) :=
    compress' (length s) empty_dict s.

  Definition compress_to_bytes (s: list byte) :=
    tokens_to_bytes (compress s).

  Fixpoint decompress' (dict: dict_type) (tokens: list Token) :=
    match tokens with
    | [] => []
    | Tok index next :: rest =>
        match nth_error dict index with
        | Some s => s ++ [next] ++ decompress' (dict ++ [s ++ [next]]) rest
        | None => [] (* Should not happen *)
        end
    | Last index :: rest =>
        match nth_error dict index with
        | Some s => s
        | None => [] (* Should not happen *)
        end
    end.

  Definition decompress (tokens: list Token) :=
    decompress' empty_dict tokens.

  Definition decompress_from_bytes (s: list byte) :=
    decompress (bytes_to_tokens s).


  Lemma compress'_valid_tokens: forall fuel s dict n,
    length s <= fuel ->
    nth_error dict 0 = Some [] ->
    length dict <= n ->
    valid_tokens (compress' fuel dict s) n.
  Proof.
    induction fuel; intros * Hlen Hfst Hd; simpl in *; try constructor.
    destruct s; try constructor.
    destruct (find_largest_prefix dict (b :: s)) as [index len] eqn:Hflp.
    destruct (skipn len (b :: s)) eqn:Hsk; simpl.
    - destruct (find_largest_prefix_correctness dict (b :: s) index len Hflp Hfst) as [_ Hnth].
      apply nth_in_index_lt_length in Hnth.
      pose proof (num_bytes_for_dict_lower_bound n).
      lia.
    - split.
      + destruct (find_largest_prefix_correctness dict (b :: s) index len Hflp Hfst) as [_ Hnth].
        apply nth_in_index_lt_length in Hnth.
        pose proof (num_bytes_for_dict_lower_bound n).
        lia.
      + apply IHfuel.
        * pose proof (length_skipn len (b :: s)) as Hlsk.
          rewrite Hsk in Hlsk.
          simpl in Hlen, Hlsk.
          destruct len; lia.
        * destruct (dict ++ [firstn len (b :: s) ++ [b0]]) eqn:?.
          -- apply app_eq_nil in Heql0.
             destruct Heql0 as [_ Hw].
             discriminate.
          -- destruct dict eqn:?.
             ++ discriminate.
             ++ rewrite <- app_comm_cons in Heql0.
                congruence.
        * rewrite length_app.
          simpl.
          lia.
  Qed.

  Lemma compress_correctness': forall fuel dict s,
    length s <= fuel ->
    nth_error dict 0 = Some [] ->
    decompress' dict (compress' fuel dict s) = s.
  Proof.
    induction fuel; simpl; intros dict s Hlen Hfst.
    - inversion Hlen.
      now apply length_zero_iff_nil in H0.
    - destruct s; try reflexivity.
      destruct (find_largest_prefix dict (b :: s)) as [index len] eqn:?.
      pose proof (find_largest_prefix_correctness dict (b :: s) index len Heqp Hfst) as [_ Hs].
      pose proof (firstn_skipn len (b :: s)) as Hfs.
      destruct (skipn len (b :: s)) eqn:?; simpl.
      + rewrite app_nil_r in Hfs.
        rewrite Hfs in Hs.
        now rewrite Hs.
      + rewrite <- Hfs, Hs, app_inv_head_iff.
        f_equal.
        destruct dict; try discriminate.
        assert (Hd: (l0 :: dict) ++ [firstn len (firstn len (b :: s) ++ b0 :: l) ++ [b0]] = 
                (l0 :: dict) ++ [firstn len (b :: s) ++ [b0]]). {
         rewrite app_inv_head_iff.
         f_equal.
         now rewrite app_inv_tail_iff, Hfs.
        }
        rewrite Hd.
        eapply IHfuel.
        * rewrite <- Hfs, length_app, length_cons in Hlen.
          lia.
        * assumption.
  Qed.

  Theorem compress_correctness: forall s,
      decompress_from_bytes (compress_to_bytes s) = s.
  Proof.
    intros.
    unfold compress_to_bytes, decompress_from_bytes.
    rewrite (tokens_to_bytes_correctness (compress s)).
    - eapply compress_correctness'.
      + lia.
      + unfold empty_dict.
        reflexivity.
    - apply compress'_valid_tokens; unfold empty_dict; simpl; auto.
  Qed.

  Lemma compress'_length_le_fuel: forall fuel dict s,
      length (compress' fuel dict s) <= fuel.
  Proof.
    induction fuel as [|fuel IH]; intros dict s; simpl.
    - lia.
    - destruct s as [|b s]; simpl.
      + lia.
      + destruct (find_largest_prefix dict (b :: s)) as [index len].
        destruct (skipn len (b :: s)) as [|next rest]; simpl.
        * lia.
        * specialize (IH (dict ++ [firstn len (b :: s) ++ [next]]) rest).
          lia.
  Qed.

  Theorem compress_length_upperbound: forall s,
      length (compress s) <= length s.
  Proof.
    intros s.
    unfold compress.
    apply compress'_length_le_fuel.
  Qed.

  Lemma tokens_to_bytes'_length_bound: forall tokens dict_size max_dict_size,
      dict_size + length tokens <= max_dict_size ->
      length (tokens_to_bytes' dict_size tokens)
        <= length tokens * (num_bytes_for_dict max_dict_size + 1).
  Proof.
    induction tokens as [|tok rest IH]; intros dict_size max_dict_size Hbound.
    - simpl. lia.
    - assert (Hdict : dict_size <= max_dict_size) by lia.
      pose proof (num_bytes_for_dict_mono dict_size max_dict_size Hdict) as Hmono.
      destruct tok as [index next | index]; simpl in *.
      + rewrite length_app.
        rewrite length_nat_to_k_bytes. simpl.
        assert (Hrec: S dict_size + length rest <= max_dict_size) by lia.
        specialize (IH (S dict_size) max_dict_size Hrec).
        lia.
      + rewrite length_nat_to_k_bytes.
        lia.
  Qed.

  Theorem compress_to_bytes_upperbound: forall s,
      length (compress_to_bytes s)
        <= length s * (num_bytes_for_dict (S (length s)) + 1).
  Proof.
    intros s.
    unfold compress_to_bytes, tokens_to_bytes.
    eapply Nat.le_trans.
    2: {
      apply Nat.mul_le_mono_r.
      apply compress_length_upperbound.
    }
    apply tokens_to_bytes'_length_bound.
    pose proof (compress_length_upperbound s) as Hclub.
    simpl in *.
    now apply Nat.succ_le_mono in Hclub.
  Qed. 

End Impl.

Export Impl.
