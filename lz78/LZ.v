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

  Definition not_last (t : Token) :=
    match t with
      | Tok _ _ _ => True
      | Last _ _  => False
    end.

  Definition phrases_differ (tokens tokens': list Token) := 
    forall i j t1 t2,
      nth_error tokens i = Some t1 ->
      nth_error tokens' j = Some t2 ->
      not_last t1 -> not_last t2 ->
      get_phrase t1 <> get_phrase t2.

  Definition phrases_differ_one (tokens: list Token) := 
    forall i j t1 t2,
      (i <> j) ->
      nth_error tokens i = Some t1 ->
      nth_error tokens j = Some t2 ->
      not_last t1 -> not_last t2 ->
      get_phrase t1 <> get_phrase t2.

  Definition compress (s: list bool) :=
    compress' (length s) empty_dict s.

  Print empty_dict.

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
      pose proof (num_bits_for_dict_lower_bound n).
      lia.
    - split.
      + destruct (find_largest_prefix_correctness dict (b :: s) index len Hflp Hfst) as [_ Hnth].
        apply nth_in_index_lt_length in Hnth.
        pose proof (num_bits_for_dict_lower_bound n).
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
        * simpl.
          assumption.
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
        - reflexivity.
        - simpl. lia.
    }
    - eapply compress_correctness'.
      + lia.
      + unfold empty_dict.
        reflexivity.
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

  Lemma compress'_eq_concat_phrases: forall fuel s dict tokens,
    length s <= fuel ->
    nth_error dict 0 = Some [] ->
    compress' fuel dict s = tokens ->
    s = concat (map get_phrase tokens).
  Proof.
    induction fuel. 
      - intros. simpl in H0. subst. simpl. inversion H. Search (length _ = 0). eapply length_zero_iff_nil. assumption.
      - intros. simpl in H0. destruct s. 
        + subst. simpl. reflexivity.
        + destruct (find_largest_prefix dict (b :: s)) eqn:Hd. destruct (skipn n0 (b::s)) eqn:Hd2.
            * subst. simpl. rewrite Hd. rewrite Hd2. simpl. Search (_ ++ []). rewrite app_nil_r. specialize (find_largest_prefix_correctness _ _ _ _ Hd H0) as Hcor.
              Search (skipn _ _ = []). assert (length (b :: s) <= n0).
                -- apply skipn_all_iff. assumption.
                -- Search (firstn _ _ = _ ). symmetry. eapply firstn_all2. assumption.
            * simpl in H1. rewrite Hd in H1. rewrite Hd2 in H1. rewrite <- H1.
              simpl. erewrite <- IHfuel with (s := l) (dict := dict ++ [firstn n0 (b :: s) ++ [b0]]).
                -- rewrite <- app_assoc. Search (firstn). change ([b0] ++ l) with (b0 :: l).
                   rewrite <- Hd2. symmetry. eapply firstn_skipn.
                -- simpl in H. Search (skipn). specialize (length_skipn n0 (b::s)) as Hlen. rewrite Hd2 in Hlen.
                   simpl in Hlen. destruct n0. lia. lia.
                -- simpl. destruct (dict ++ [firstn n0 (b :: s) ++ [b0]]) eqn:Hdc.
                  ++ Search (_ = []). specialize (app_eq_nil _ _  Hdc) as (Hcontr1 & _). rewrite Hcontr1 in H0. assumption.
                  ++ destruct dict. 
                    ** inversion H0.
                    ** inversion H0. subst. simpl in Hdc. inversion Hdc. reflexivity.
                -- reflexivity.
  Qed.

  Lemma compress'_agreement: forall fuel s dict tokens,
    length s <= fuel ->
    compress' fuel dict s = tokens ->
    agreement dict tokens.
  Proof.
    induction fuel.
      - intros. inversion H. destruct s.  2: { simpl in H2. lia. } 
        simpl in H0. rewrite <- H0. unfold agreement. intros. inversion H1.
      - intros. simpl in H0. destruct s. rewrite <- H0. unfold agreement. intros. inversion H1.
        destruct (find_largest_prefix dict (b :: s)) eqn:Hd. destruct (skipn n0 (b::s)) eqn:Hd2.
          * rewrite <- H0. unfold agreement. intros. inversion H1.
            +    


  Admitted.

  Lemma agreement_app : forall dict tokens phr next n,
    agreement dict tokens -> agreement (dict ++ [phr ++ [next]]) (tokens ++ [Tok n phr next]).
  Proof.
    intros.
    unfold agreement. intros. unfold agreement in H. Search (In _ (_ ++ _ )). apply in_or_app.
    specialize (in_app_or _ _ _ H0) as Hcase. destruct Hcase as [H1 | H2].
      - left. eapply H. exact H1.
      - right. inversion H2. 
        * inversion H1. subst. constructor. constructor.
        * inversion H1.
  Qed.

  Lemma nth_error_some_0 {A : Type}: forall (l1 : list A) (l2 : list A) x,
    nth_error l1 0 = Some x -> nth_error (l1 ++ l2) 0 = Some x.
  Proof.
    intros. destruct l1.
      - inversion H.
      - simpl. simpl in H. assumption.
  Qed. 

  Lemma nth_error_some {A : Type}: forall i (l1 : list A) (l2 : list A) x,
    nth_error l1 i = Some x -> nth_error (l1 ++ l2) i = Some x.
  Proof.
    induction i.
    intros. apply nth_error_some_0. assumption.
    intros. destruct l1.
      - inversion H.
      - simpl. simpl in H. apply IHi. assumption.  
  Qed. 

  Lemma skipn_length {A : Type} : forall n (l l' : list A) x,
    skipn n l = x :: l' -> length l >= S n.
  Proof.
    induction n.
      - intros. simpl in H. rewrite H. simpl. lia. 
      - intros. simpl in H. destruct l. 
        * inversion H.
        * simpl. specialize (IHn _ _ _ H). lia.
  Qed.
    
  Lemma compress'_cor2 : forall fuel dict s tokens prev_tokens,
    length s <= fuel ->
    compress' fuel dict s = tokens ->
    agreement dict prev_tokens ->
    nth_error dict 0 = Some [] ->
    phrases_differ prev_tokens tokens /\ phrases_differ_one tokens.
  Proof.
    induction fuel.
      - intros. inversion H. destruct s.  2: { simpl in H. lia. }
        simpl in H0. subst. unfold phrases_differ. unfold phrases_differ_one. split.
          + intros. Search (nth_error). rewrite nth_error_nil in H3. inversion H3.
          + intros. rewrite nth_error_nil in H3. inversion H3.
      - intros. simpl in H0. destruct s.
        + subst. simpl. split. unfold phrases_differ. unfold phrases_differ_one. intros. rewrite nth_error_nil in H3. inversion H3.
          unfold phrases_differ. unfold phrases_differ_one. intros. rewrite nth_error_nil in H3. inversion H3.
        + destruct (find_largest_prefix dict (b :: s)) eqn:Hd. destruct (skipn n0 (b::s)) eqn:Hd2.
          * subst. split. unfold phrases_differ. intros. 
            destruct j. 2: { simpl in H3. rewrite nth_error_nil in H3. inversion H3. }
            simpl in H3. inversion H3. subst. simpl. unfold agreement in H1.
            Search (In). destruct t1.
              -- unfold not_last in H5. contradiction.
              -- unfold not_last in H5. contradiction.
              -- unfold phrases_differ_one. intros. destruct i. simpl in H3. inversion H3. subst. unfold not_last in H5. contradiction.
                 simpl in H3. Search (nth_error [] _). rewrite nth_error_nil in H3. inversion H3.
          * destruct tokens. inversion H0.
            specialize (IHfuel (dict ++ [firstn n0 (b :: s) ++ [b0]]) l tokens (prev_tokens ++ [Tok n (firstn n0 (b :: s)) b0])).
            assert (length l <= fuel). {
              Search (skipn _ _). specialize (length_skipn n0 (b :: s)) as Hlen. rewrite Hd2 in Hlen. assert (length (b0 :: l) <= S fuel - n0) by lia. simpl in H3. destruct n0; lia.
            }
            specialize (IHfuel H3). clear H3.
            inversion H0. specialize (IHfuel H5). 
            assert (agreement (dict ++ [firstn n0 (b :: s) ++ [b0]]) (prev_tokens ++ [Tok n (firstn n0 (b :: s)) b0])). {
              eapply agreement_app. assumption. 
            }
            specialize (IHfuel H3). clear H3. 
            assert (nth_error (dict ++ [firstn n0 (b :: s) ++ [b0]]) 0 = Some []). {
              eapply nth_error_some. assumption.
            }
            specialize (IHfuel H3). clear H3.
            destruct IHfuel as (IHfuel1 & IHfuel2).

            split. unfold phrases_differ. intros. unfold agreement in H1. destruct j.
                -- simpl in H6. inversion H6. clear H6. simpl. intros Hcontr. destruct t1. 2: { inversion H7. } simpl in Hcontr.
                   clear IHfuel1 IHfuel2 H H0 H5 H7 H8 H4. specialize (nth_error_In _ _ H3) as Hin. specialize (H1 _ _ _ Hin).
                   specialize (find_largest_prefix_opt dict ((firstn n0 (b :: s)) ++ [b0]) l n n0) as Hopt.
                   assert ((firstn n0 (b :: s) ++ [b0]) ++ l = b :: s). {
                    Search (firstn _ _). rewrite <- app_assoc. change ([b0] ++ l) with (b0 :: l). rewrite <- Hd2. 
                    rewrite firstn_skipn. reflexivity.
                   }
                   rewrite H in Hopt. specialize (Hopt Hd). rewrite <- Hcontr in Hopt. specialize (Hopt H1). rewrite Hcontr in Hopt. 
                   Search (skipn _ _ = _). specialize (skipn_length _ _ _ _ Hd2) as Hlen. Search firstn. specialize (firstn_length_le (b :: s)) as Hbound.
                   specialize (Hbound n0). assert (n0 <= length (b :: s)) by lia. specialize (Hbound H0). Search (length (_ ++ _) = length _ + length _). rewrite length_app in Hopt.
                   rewrite Hbound in Hopt. simpl in Hopt. lia.
                   
                -- Search (nth_error (_ :: _) (S _) = nth_error _ _). rewrite nth_error_cons_succ in H6.
                   rewrite H5 in H6. unfold phrases_differ in IHfuel1. specialize (IHfuel1 i j t1 t2). apply IHfuel1.
                   eapply nth_error_some. do 4 assumption. assumption. assumption. assumption.

                -- rewrite H5. clear H5. clear H0. unfold phrases_differ_one. intros. destruct i.
                  ** destruct j.
                    ++ auto.
                    ++ rewrite nth_error_cons_succ in H5. unfold phrases_differ in IHfuel1. specialize (IHfuel1 (length prev_tokens) j t1 t2).
                       Search (nth_error _ _). specialize (nth_error_app2 prev_tokens [Tok n (firstn n0 (b :: s)) b0]) as Hlem.
                       specialize (Hlem (length prev_tokens) ltac:(lia)). replace ((length prev_tokens - length prev_tokens)) with 0  in Hlem by lia.
                       rewrite Hlem in IHfuel1. simpl in IHfuel1. simpl in H3. rewrite H3 in IHfuel1. specialize (IHfuel1 eq_refl H5 H6 H7). assumption.
                  ** destruct j.
                    ++ rewrite nth_error_cons_succ in H3. unfold phrases_differ in IHfuel1. specialize (IHfuel1 (length prev_tokens) i t2 t1).
                       Search (nth_error _ _). specialize (nth_error_app2 prev_tokens [Tok n (firstn n0 (b :: s)) b0]) as Hlem.
                       specialize (Hlem (length prev_tokens) ltac:(lia)). replace ((length prev_tokens - length prev_tokens)) with 0  in Hlem by lia.
                       rewrite Hlem in IHfuel1. simpl in IHfuel1. simpl in H5. rewrite H5 in IHfuel1. specialize (IHfuel1 eq_refl H3 H7 H6). symmetry. assumption.
                    ++ unfold phrases_differ_one in IHfuel2.   rewrite nth_error_cons_succ in H3. rewrite nth_error_cons_succ in H5.
                       specialize (IHfuel2 i j t1 t2 ltac:(lia) H3 H5 H6 H7). assumption.
  Qed.

  Lemma comb (tokens: list Token) :
    (phrases_differ tokens tokens) ->
    length (concat (map get_phrase tokens)) >= (length tokens) * (Nat.log2 (length tokens) - 3).
  Proof. Admitted.

End Impl.
