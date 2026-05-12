From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Dict LZ_Tokens.
Import ListNotations.

Module Impl.

  Fixpoint compress' (fuel: nat) (dict: dict_type) (s: list bool) :=
    match fuel with
    | 0 => []
    | S fuel =>
        match s with
        | [] => []
        | _ =>
            let (index, len) := find_largest_prefix dict s in
            match skipn len s with
            | [] => [Last index (firstn len s)]
            | next :: rest =>
                Tok index (firstn len s) next :: compress' fuel (dict ++ [firstn len s ++ [next]]) rest
            end
        end
    end.

  Definition agreement (dict: dict_type) (tokens: list Token) :=
    forall index phr next,
      In (Tok index phr next) tokens ->
      In (phr ++ [next]) dict.

  Definition get_phrase (t: Token) := 
    match t with
    | Tok _ phrase next => phrase ++ [next]
    | Last _ phrase => phrase
    end.

  Definition phrases_differ (tokens tokens': list Token) := 
    forall i j t1 t2,
      nth_error tokens i = Some t1 ->
      nth_error tokens' j = Some t2 ->
      get_phrase t1 <> get_phrase t2.

  Definition compress (s: list bool) :=
    compress' (length s) empty_dict s.

  Definition compress_to_bits (s: list bool) :=
    tokens_to_bits (compress s).

  Fixpoint decompress' (dict: dict_type) (tokens: list Token) :=
    match tokens with
    | [] => []
    | Tok index _ next :: rest =>
        match nth_error dict index with
        | Some s => s ++ [next] ++ decompress' (dict ++ [s ++ [next]]) rest
        | None => [] (* Should not happen *)
        end
    | Last index _ :: rest =>
        match nth_error dict index with
        | Some s => s
        | None => [] (* Should not happen *)
        end
    end.

  Definition decompress (tokens: list Token) :=
    decompress' empty_dict tokens.

  Lemma decompress'_indep : forall tokens tokens' dict,
      list_eq token_equiv tokens tokens' -> (decompress' dict tokens) = (decompress' dict tokens').
  Proof.
    induction tokens.
      - intros. simpl in H. destruct tokens'. 
        -- auto.
        -- inversion H.
      - intros.
        simpl.
        simpl in H. destruct tokens'.
          + inversion H.
          + destruct H as (Ha & Hb). unfold token_equiv in Ha. destruct a eqn:Hd.
            * destruct t eqn:Hdt.
              -- inversion Ha. subst. simpl. destruct (nth_error dict index0).
                ++ erewrite IHtokens. reflexivity. assumption.
                ++ reflexivity.
              -- inversion Ha.
            * destruct t eqn:Hdt.
              -- inversion Ha.
              -- inversion Ha. reflexivity.
  Qed.

  Lemma decompress_indep : forall tokens tokens',
    list_eq token_equiv tokens tokens' -> (decompress tokens) = (decompress tokens').
  Proof.
    intros. unfold decompress. eapply decompress'_indep. assumption.
  Qed.

  Definition decompress_from_bits (s: list bool) :=
    decompress (bits_to_tokens s).


  Lemma compress'_valid_tokens: forall fuel s dict n,
    length s <= fuel ->
    In [] dict ->
    length dict <= n ->
    valid_tokens (compress' fuel dict s) n.
  Proof.
    induction fuel; intros * Hlen Hin Hd; simpl in *; try constructor.
    destruct s; try constructor.
    destruct (find_largest_prefix dict (b :: s)) as [index len] eqn:Hflp.
    destruct (skipn len (b :: s)) eqn:Hsk; simpl.
    - destruct (find_largest_prefix_correctness dict (b :: s) index len Hflp Hin) as [_ Hnth].
      apply nth_in_index_lt_length in Hnth.
      pose proof (num_bits_for_dict_lower_bound n).
      lia.
    - split.
      + destruct (find_largest_prefix_correctness dict (b :: s) index len Hflp Hin) as [_ Hnth].
        apply nth_in_index_lt_length in Hnth.
        pose proof (num_bits_for_dict_lower_bound n).
        lia.
      + apply IHfuel.
        * pose proof (length_skipn len (b :: s)) as Hlsk.
          rewrite Hsk in Hlsk.
          simpl in Hlen, Hlsk.
          destruct len; lia.
        * apply in_or_app.
          now left.
        * rewrite length_app.
          simpl.
          lia.
  Qed.

  Lemma compress_correctness': forall fuel dict s,
    length s <= fuel ->
    In [] dict ->
    decompress' dict (compress' fuel dict s) = s.
  Proof.
    induction fuel; simpl; intros dict s Hlen Hin.
    - inversion Hlen.
      now apply length_zero_iff_nil in H0.
    - destruct s; try reflexivity.
      destruct (find_largest_prefix dict (b :: s)) as [index len] eqn:?.
      pose proof (find_largest_prefix_correctness dict (b :: s) index len Heqp Hin) as [_ Hs].
      pose proof (firstn_skipn len (b :: s)) as Hfs.
      destruct (skipn len (b :: s)) eqn:?; simpl.
      + rewrite app_nil_r in Hfs.
        rewrite Hfs in Hs.
        now rewrite Hs.
      + rewrite <- Hfs, Hs, app_inv_head_iff.
        f_equal.
        assert (Hlf: length l <= fuel). {
          rewrite <- Hfs, length_app, length_cons in Hlen.
          lia.
        }
        assert (Hinapp: In [] (dict ++ [firstn len (b :: s) ++ [b0]])). {
          apply in_or_app.
          now left.
        }
        specialize (IHfuel (dict ++ [firstn len (b :: s) ++ [b0]]) l Hlf Hinapp).
        assert (Hd: dict ++ [firstn len (firstn len (b :: s) ++ b0 :: l) ++ [b0]] = 
                dict ++ [firstn len (b :: s) ++ [b0]]). {
         rewrite app_inv_head_iff.
         f_equal.
         now rewrite app_inv_tail_iff, Hfs.
        }
        now rewrite Hd.
  Qed.

  Theorem compress_correctness: forall s,
      decompress_from_bits (compress_to_bits s) = s.
  Proof.
    intros.
    unfold compress_to_bits, decompress_from_bits.
    pose proof (tokens_to_bits_correctness (compress s)).
    erewrite decompress_indep. 2: {
      apply H.
      eapply compress'_valid_tokens.
        - lia.
        - simpl. apply or_introl. reflexivity.
        - simpl. lia.    
    }
    - eapply compress_correctness'.
      + lia.
      + unfold empty_dict.
        simpl.
        now left.
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

  Lemma tokens_to_bits'_length_bound: forall tokens dict_size max_dict_size,
      dict_size + length tokens <= max_dict_size ->
      length (tokens_to_bits' dict_size tokens)
        <= length tokens * (num_bits_for_dict max_dict_size + 1).
  Proof.
    induction tokens as [|tok rest IH]; intros dict_size max_dict_size Hbound.
    - simpl. lia.
    - assert (Hdict : dict_size <= max_dict_size) by lia.
      pose proof (num_bits_for_dict_mono dict_size max_dict_size Hdict) as Hmono.
      destruct tok as [index next | index]; simpl in *.
      + rewrite length_app.
        rewrite length_nat_to_k_bits. simpl.
        assert (Hrec: S dict_size + length rest <= max_dict_size) by lia.
        specialize (IH (S dict_size) max_dict_size Hrec).
        lia.
      + rewrite length_nat_to_k_bits.
        lia.
  Qed.

  Theorem compress_to_bits_upperbound: forall s,
      length (compress_to_bits s)
        <= length s * (num_bits_for_dict (S (length s)) + 1).
  Proof.
    intros s.
    unfold compress_to_bits, tokens_to_bits.
    eapply Nat.le_trans.
    2: {
      apply Nat.mul_le_mono_r.
      apply compress_length_upperbound.
    }
    apply tokens_to_bits'_length_bound.
    pose proof (compress_length_upperbound s).
    simpl in *.
    now apply Nat.succ_le_mono in H.
  Qed. 

  Lemma compress'_eq_concat_phrases: forall fuel dict s tokens,
    length s <= fuel ->
    compress' fuel dict s = tokens ->
    s = concat (map get_phrase tokens).
  Proof. Admitted.

  Lemma compress'_agreement: forall fuel dict s tokens,
    length s <= fuel ->
    compress' fuel dict s = tokens ->
    agreement dict tokens.
  Proof. Admitted.

  Lemma compress'_cor2 (fuel: nat) (dict: dict_type) (s: list bool)
                       (tokens prev_tokens: list Token) (i j: nat) (t1 t2: Token):
    length s <= fuel ->
    compress' fuel dict s = tokens ->
    agreement dict prev_tokens ->
    phrases_differ prev_tokens tokens /\ phrases_differ tokens tokens.
  Proof. Admitted.

  Lemma comb (tokens: list Token) :
    (phrases_differ tokens tokens) ->
    length (concat (map get_phrase tokens)) >= (length tokens) * (Nat.log2 (length tokens) - 3).
  Proof. Admitted.

End Impl.
