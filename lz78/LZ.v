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

  Lemma decompress'_indep : forall tokens tokens' dict,
      list_eq token_equiv tokens tokens' ->
      decompress' dict tokens = decompress' dict tokens'.
  Proof.
    induction tokens; intros * H; simpl in *; destruct tokens'; try tauto.
    destruct H as (Ha & Hb).
    unfold token_equiv in Ha.
    destruct a eqn:Hd, t eqn:Hdt; simpl; subst; try tauto.
    inversion Ha. subst.
    destruct (nth_error dict index0).
    + erewrite IHtokens; auto.
    + reflexivity.
  Qed.

  Lemma decompress_indep : forall tokens tokens',
    list_eq token_equiv tokens tokens' ->
    decompress tokens = decompress tokens'.
  Proof.
    intros. unfold decompress.
    eapply decompress'_indep. assumption.
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

  Theorem compress_to_bits_upperbound_simple: forall s,
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
    induction fuel; intros * Hlen Hnth Hc; subst; simpl in *.
    - inversion Hlen.
      now apply length_zero_iff_nil.
    - destruct s.
      + reflexivity.
      + destruct (find_largest_prefix dict (b :: s)) eqn:Hd, (skipn n0 (b :: s)) eqn:Hd2; simpl in *.
        * rewrite app_nil_r.
          specialize (find_largest_prefix_correctness _ _ _ _ Hd Hnth) as Hcor.
          assert (length (b :: s) <= n0) by now apply skipn_all_iff.
          symmetry.
          now apply firstn_all2.
        * rewrite <- IHfuel with (s := l) (dict := dict ++ [firstn n0 (b :: s) ++ [b0]]).
          -- rewrite <- app_assoc.
             change ([b0] ++ l) with (b0 :: l).
             rewrite <- Hd2.
             symmetry.
             eapply firstn_skipn.
          -- specialize (length_skipn n0 (b :: s)) as Hlsn.
             rewrite Hd2 in Hlsn.
             simpl in Hlsn.
             destruct n0; lia.
          -- destruct (dict ++ [firstn n0 (b :: s) ++ [b0]]) eqn:Hdc.
             ++ specialize (app_eq_nil _ _  Hdc) as (Hcontr1 & _).
                now rewrite Hcontr1 in Hnth.
             ++ destruct dict; inversion Hnth; subst.
                simpl in Hdc.
                now inversion Hdc.
          -- reflexivity.
  Qed.

  Lemma compress'_phrases_differ: forall fuel dict s tokens prev_tokens,
    length s <= fuel ->
    compress' fuel dict s = tokens ->
    agreement dict prev_tokens ->
    nth_error dict 0 = Some [] ->
    phrases_differ prev_tokens tokens /\ phrases_differ_one tokens.
  Proof.
    induction fuel.
      - intros. inversion H. destruct s.  2: { simpl in H. lia. }
        simpl in H0. subst. unfold phrases_differ. unfold phrases_differ_one. split.
          + intros. rewrite nth_error_nil in H3. inversion H3.
          + intros. rewrite nth_error_nil in H3. inversion H3.
      - intros. simpl in H0. destruct s.
        + subst. simpl. split. unfold phrases_differ. unfold phrases_differ_one. intros. rewrite nth_error_nil in H3. inversion H3.
          unfold phrases_differ. unfold phrases_differ_one. intros. rewrite nth_error_nil in H3. inversion H3.
        + destruct (find_largest_prefix dict (b :: s)) eqn:Hd. destruct (skipn n0 (b::s)) eqn:Hd2.
          * subst. split. unfold phrases_differ. intros. 
            destruct j. 2: { simpl in H3. rewrite nth_error_nil in H3. inversion H3. }
            simpl in H3. inversion H3. subst. simpl. unfold agreement in H1.
            destruct t1.
              -- unfold not_last in H5. contradiction.
              -- unfold not_last in H5. contradiction.
              -- unfold phrases_differ_one. intros. destruct i. simpl in H3. inversion H3. subst. unfold not_last in H5. contradiction.
                 simpl in H3. rewrite nth_error_nil in H3. inversion H3.
          * destruct tokens. inversion H0.
            specialize (IHfuel (dict ++ [firstn n0 (b :: s) ++ [b0]]) l tokens (prev_tokens ++ [Tok n (firstn n0 (b :: s)) b0])).
            assert (length l <= fuel). {
              specialize (length_skipn n0 (b :: s)) as Hlen. rewrite Hd2 in Hlen. assert (length (b0 :: l) <= S fuel - n0) by lia. simpl in H3. destruct n0; lia.
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
                    rewrite <- app_assoc. change ([b0] ++ l) with (b0 :: l). rewrite <- Hd2. 
                    rewrite firstn_skipn. reflexivity.
                   }
                   rewrite H in Hopt. specialize (Hopt Hd). rewrite <- Hcontr in Hopt. specialize (Hopt H1). rewrite Hcontr in Hopt. 
                   specialize (skipn_length _ _ _ _ Hd2) as Hlen. specialize (firstn_length_le (b :: s)) as Hbound.
                   specialize (Hbound n0). assert (n0 <= length (b :: s)) by lia. specialize (Hbound H0). rewrite length_app in Hopt.
                   rewrite Hbound in Hopt. simpl in Hopt. lia.
                   
                -- rewrite nth_error_cons_succ in H6.
                   rewrite H5 in H6. unfold phrases_differ in IHfuel1. specialize (IHfuel1 i j t1 t2). apply IHfuel1.
                   eapply nth_error_some. do 4 assumption. assumption. assumption. assumption.

                -- rewrite H5. clear H5. clear H0. unfold phrases_differ_one. intros. destruct i.
                  ** destruct j.
                    ++ auto.
                    ++ rewrite nth_error_cons_succ in H5. unfold phrases_differ in IHfuel1. specialize (IHfuel1 (length prev_tokens) j t1 t2).
                       specialize (nth_error_app2 prev_tokens [Tok n (firstn n0 (b :: s)) b0]) as Hlem.
                       specialize (Hlem (length prev_tokens) ltac:(lia)). replace ((length prev_tokens - length prev_tokens)) with 0  in Hlem by lia.
                       rewrite Hlem in IHfuel1. simpl in IHfuel1. simpl in H3. rewrite H3 in IHfuel1. specialize (IHfuel1 eq_refl H5 H6 H7). assumption.
                  ** destruct j.
                    ++ rewrite nth_error_cons_succ in H3. unfold phrases_differ in IHfuel1. specialize (IHfuel1 (length prev_tokens) i t2 t1).
                       specialize (nth_error_app2 prev_tokens [Tok n (firstn n0 (b :: s)) b0]) as Hlem.
                       specialize (Hlem (length prev_tokens) ltac:(lia)). replace ((length prev_tokens - length prev_tokens)) with 0  in Hlem by lia.
                       rewrite Hlem in IHfuel1. simpl in IHfuel1. simpl in H5. rewrite H5 in IHfuel1. specialize (IHfuel1 eq_refl H3 H7 H6). symmetry. assumption.
                    ++ unfold phrases_differ_one in IHfuel2.   rewrite nth_error_cons_succ in H3. rewrite nth_error_cons_succ in H5.
                       specialize (IHfuel2 i j t1 t2 ltac:(lia) H3 H5 H6 H7). assumption.
  Qed.

  Definition different (l : list (list bool)) := forall i j a b,
  i <> j -> nth_error l i = Some a -> nth_error l j = Some b -> a <> b.
  
  Definition equal_len_n (n : nat) (l : list bool) := if (length l =? n) then 1 else 0.

  Definition equal_or_less_len_n (n : nat) (l : list bool) := (length l <=? n).

  Definition amount_geq_n (l : list nat) (n : nat) := list_sum (map (fun x => if (x <? n) then 0 else 1) l).

  Fixpoint gen_array (n : nat) := match n with
    | 0 => []
    | S x => S x :: (gen_array x)
    end.

  Lemma comb_diff : forall a l,
    different (a :: l) -> different l.
  Proof.
    intros.
    unfold different. intros. unfold different in H. specialize (H (S i) (S j) (a0) (b) ltac:(lia) H1 H2). assumption.
  Qed.

  Lemma comb_diff_add : forall a b l,
    different (a :: l) -> In b l -> a <> b.
  Proof.
    intros.
    Search (nth_error). specialize (In_nth_error _ _ H0) as Hin. destruct Hin as (n & Hin).
    unfold different in H. specialize (H 0 (S n) a b ltac:(lia) ltac:(constructor)). simpl in H. specialize (H Hin). assumption.
  Qed.  

  Lemma comb_partition : forall l f l1 l2,
    partition f l = (l1, l2) -> different l -> different l1 /\ different l2.
  Proof.
    induction l.
      - intros. unfold different. inversion H. subst. split; intros; rewrite nth_error_nil in H2; inversion H2.
      - intros. simpl in H. destruct (f a) eqn:Hfa. 
        * destruct (partition f l) eqn:Hp. inversion H. subst. clear H. specialize (IHl f l0 l2 Hp). assert (different l). eapply comb_diff. exact H0.
          specialize (IHl H). split. 2: { destruct IHl as (_ & IHl). assumption. }
          unfold different. intros. destruct i. destruct j.
            + auto. 
            + simpl in H3. Search nth_error. specialize (nth_error_In _ _ H3) as Hin. Search partition. assert (In b l). eapply elements_in_partition. exact Hp. apply or_introl. exact Hin.
              simpl in H2. inversion H2. subst. clear H2. eapply comb_diff_add. exact H0. exact H4.
            + destruct j.
              -- simpl in H3. inversion H3. clear H3. subst. simpl in H2. specialize (nth_error_In _ _ H2) as Hin.    
                 assert (In a0 l). eapply elements_in_partition. exact Hp. apply or_introl. assumption. 
                 symmetry. eapply comb_diff_add. exact H0. exact H3.
              -- simpl in H2. simpl in H3. destruct IHl as (IHl & _). eapply IHl. assert (i <> j). lia. exact H4.
                 exact H2. exact H3.
        * destruct (partition f l) eqn:Hp. inversion H. subst. clear H. specialize (IHl f l1 l3 Hp). assert (different l). eapply comb_diff. exact H0.
          specialize (IHl H). split. destruct IHl as (IHl & _). assumption.
          unfold different. intros. destruct i. destruct j.
            + auto. 
            + simpl in H3. Search nth_error. specialize (nth_error_In _ _ H3) as Hin. Search partition. assert (In b l). eapply elements_in_partition. exact Hp. apply or_intror. exact Hin.
              simpl in H2. inversion H2. subst. clear H2. eapply comb_diff_add. exact H0. exact H4.
            + destruct j.
              -- simpl in H3. inversion H3. clear H3. subst. simpl in H2. specialize (nth_error_In _ _ H2) as Hin.    
                 assert (In a0 l). eapply elements_in_partition. exact Hp. apply or_intror. assumption. 
                 symmetry. eapply comb_diff_add. exact H0. exact H3.
              -- simpl in H2. simpl in H3. destruct IHl as (_ & IHl). eapply IHl. assert (i <> j). lia. exact H4.
                 exact H2. exact H3.
  Qed.

  Lemma filter_preserv_diff : forall l f,
    different l -> different (filter f l).
  Proof.
    intros. Search filter. destruct (partition f l) eqn:Hp. specialize (comb_partition _ _ _ _ Hp H) as Hpart.
    Search partition. specialize (partition_as_filter f l) as H3. rewrite H3 in Hp. inversion Hp.
    rewrite H1. destruct Hpart as (Hpart & _). assumption.
  Qed. 

  Definition split_func (l : list bool) := match l with 
    | true :: lst => true
    | false :: lst => false
    | _ => true
    end.

  Definition drop_first (l : list bool) := match l with
    | _ :: y => y
    | _ => []
  end.

  Lemma partition_forall: forall (l : list (list bool)) f p l1 l2,
    partition f l = (l1, l2) -> Forall p l -> Forall p l1 /\ Forall p l2.
  Proof.
    intros. split.
      - eapply Forall_forall. intros. assert (In x l). Search partition. eapply elements_in_partition. exact H. apply or_introl. exact H1.
        Search Forall. eapply Forall_forall. exact H0. exact H2.
      - eapply Forall_forall. intros. assert (In x l). Search partition. eapply elements_in_partition. exact H. apply or_intror. exact H1.
        Search Forall. eapply Forall_forall. exact H0. exact H2.
  Qed.

  Lemma length_dec : forall l k l1,
    Forall (fun x : list bool => length x = S k) l ->
    l1 = (map drop_first l) -> Forall (fun x : list bool => length x = k) l1.
  Proof.
    induction l.
      - intros. subst. constructor.
      - intros. subst. constructor.
        + inversion H. subst. destruct a. simpl in H2. lia. simpl in H2. unfold drop_first. lia.
        + eapply IHl. inversion H. subst. exact H3. reflexivity.
  Qed.

  Lemma diff_preserv : forall l (b : bool) l1,
    different l -> Forall (fun x => match x with
    | s :: _ => b = s
    | _ => False
    end) l -> l1 = (map drop_first l) -> different l1.
  Proof.
    intros. unfold different. intros. unfold different in H. specialize (H i j (b :: a) (b :: b0) H2).
    Search (nth_error (map _ _)). remember (nth_error l i) as x. specialize (nth_error_map (drop_first) i l) as Hnth1.
    subst. destruct (nth_error l i) eqn:Hd1. 2: { simpl in Hnth1. rewrite H3 in Hnth1. inversion Hnth1. }
    simpl in Hnth1. rewrite H3 in Hnth1. inversion Hnth1. subst. Search (nth_error). specialize (nth_error_In _ _ Hd1) as Hin.
    specialize (Forall_forall (fun x : list bool => match x with
| [] => False
| s :: _ => b = s
end) l) as Hfor. destruct Hfor as (Hfor & _). specialize (Hfor H0 l0 Hin). destruct l0. simpl. auto. simpl in H. subst. specialize (H eq_refl).

  remember (nth_error l j) as y. specialize (nth_error_map (drop_first) j l) as Hnth2.
      subst. destruct (nth_error l j) eqn:Hd2. 2: { simpl in Hnth2. rewrite H4 in Hnth2. inversion Hnth2. }
      simpl in Hnth2. rewrite H4 in Hnth2. inversion Hnth2. subst. Search (nth_error). specialize (nth_error_In _ _ Hd2) as Hin2.
      specialize (Forall_forall (fun x : list bool => match x with
  | [] => False
  | s :: _ => b1 = s
  end) l) as Hfor. destruct Hfor as (Hfor & _). specialize (Hfor H0 l1 Hin2). destruct l1. simpl. auto. simpl in H. subst. specialize (H eq_refl).
    
     simpl. unfold "<>". intros. subst. auto.
  Qed.


  Print Forall.
  Lemma comb4 : forall k (l : list (list bool)), Forall (fun x => length x = k) l -> different l -> length l <= 2^k.
  Proof.
    induction k.
      - intros. change (2^0) with 1. destruct l. simpl. lia. simpl. inversion H. subst.
        destruct l0. simpl. lia. unfold different in H0. inversion H4. subst. destruct l. 2 : { simpl in H3. lia. }
        destruct l0. 2: { simpl in H5. lia. } simpl. specialize (H0 0 1 [] [] ltac:(lia) ltac:(constructor) ltac:(constructor)).
        exfalso. eapply H0. reflexivity.
      - intros. destruct (partition split_func l) as [l1 l2] eqn:Hspl. 
        Search partition.
        specialize (partition_as_filter split_func l) as Hfilt. Search Forall. assert ((Forall (fun x : list bool => length x = S k) l1) /\ (Forall (fun x : list bool => length x = S k) l2)) as Hlen.
        eapply partition_forall. exact Hspl. exact H. 
        remember (map (fun x => match x with
          | _ :: y => y
          | _ => []
        end) l1) as l1' eqn:Hr1. 
        remember (map (fun x => match x with
          | _ :: y => y
          | _ => []
        end) l2) as l2' eqn:Hr2.
        specialize (IHk l1') as IHk1.
        specialize (IHk l2') as IHk2.
        destruct Hlen as (Hlen1 & Hlen2).
        assert (Forall (fun x : list bool => length x = k) l1'). eapply length_dec. exact Hlen1. exact Hr1.
        specialize (IHk1 H1). clear H1.
        assert (Forall (fun x : list bool => length x = k) l2'). eapply length_dec. exact Hlen2. exact Hr2.
        specialize (IHk2 H1). clear H1.

        Search filter. specialize (filter_In split_func) as Hfin1. specialize (Hfin1) with (l := l). 
        rewrite Hspl in Hfilt. inversion Hfilt. clear Hfilt.

        specialize (comb_partition _ _ _ _ Hspl H0) as Hdiff. destruct Hdiff as (Hdiff1 & Hdiff2).
        assert (different l1'). eapply diff_preserv with (b := true). exact Hdiff1. apply Forall_forall. intros. rewrite <- H2 in Hfin1. 
        specialize (Hfin1 x). destruct (Hfin1) as (Hfin11 & _). specialize (Hfin11 H1). destruct Hfin11 as (Hin3 & Hspltrue).
        unfold split_func in Hspltrue. destruct x. 
          ++ specialize (Forall_forall (fun x : list bool => length x = S k) l1) as Hfor3. destruct Hfor3 as (Hfor3 & _).
             specialize (Hfor3 Hlen1 [] H1). simpl in Hfor3. lia.
          ++ destruct b. auto. symmetry. assumption.
          ++ exact Hr1.
          ++ specialize (IHk1 H1).

        specialize (filter_In (fun x : list bool => negb (split_func x))) as Hfin2. specialize (Hfin2) with (l := l). 

        assert (different l2'). eapply diff_preserv with (b := false). exact Hdiff2. apply Forall_forall. intros. rewrite <- H3 in Hfin2. 
        specialize (Hfin2 x). destruct (Hfin2) as (Hfin11 & _). specialize (Hfin11 H4). destruct Hfin11 as (Hin3 & Hspltrue).
        unfold split_func in Hspltrue. destruct x.
          ** simpl in Hspltrue. inversion Hspltrue. 
          ** destruct b. simpl in Hspltrue. inversion Hspltrue. reflexivity.
          ** exact Hr2. 
          ** specialize (IHk2 H4). Search partition. specialize (partition_length split_func l Hspl) as Hpartlen. 
             Search (length (map _ _) = length _). assert (length l1' = length l1). rewrite Hr1. eapply length_map. 
             assert (length l2' = length l2). rewrite Hr2. eapply length_map.
             Search (_ ^ (S _)). rewrite Nat.pow_succ_r'. lia.
  Qed.

  Search filter.

  Lemma filter_filter_length {A : Type} : forall (f : A -> bool) l,
   length (filter f (filter f l)) = length (filter f l).
  Proof.
    intros.
    specialize (filter_length f (filter f l)) as H.
    assert (length (filter (fun x : A => negb (f x)) (filter f l)) = 0).
    2 : {
      lia.
    }
    destruct (filter (fun x : A => negb (f x)) (filter f l)) eqn:Hd.
    simpl. lia.
    specialize (filter_In (fun x : A => negb (f x)) a (filter f l)) as (Hfin1 & _).
    rewrite Hd in Hfin1. simpl in Hfin1. specialize (Hfin1 ltac:(apply or_introl;reflexivity)).
    specialize (filter_In f a l) as (Hfin2 & _).
    destruct Hfin1 as (Ha & Hb).
    specialize (Hfin2 Ha).
    destruct Hfin2 as (_ & Hc).
    rewrite Hc in Hb.
    simpl in Hb.
    inversion Hb.
  Qed.

  Lemma comb2 : forall n l,
    (different l) -> length (filter (equal_or_less_len_n n) l) <= 2^(n + 1) - 1.
  Proof.
    induction n.
      - intros. change (2 ^ (0 + 1) - 1) with (2^0). eapply comb4.
          * eapply Forall_forall. intros. Search filter. specialize (filter_In (equal_or_less_len_n 0) x l) as Hin.
            destruct Hin as (Hin1 & _). specialize (Hin1 H0). destruct Hin1 as (_ & Hin1).
            unfold equal_or_less_len_n in Hin1. destruct x. simpl. reflexivity.
            simpl in Hin1. inversion Hin1.
          * eapply filter_preserv_diff. assumption.
      - intros.  destruct (partition (equal_or_less_len_n n) (filter (equal_or_less_len_n (S n)) l)) eqn:Hp.
        specialize (IHn l0). assert (different (filter (equal_or_less_len_n (S n)) l)). {
          eapply filter_preserv_diff. assumption.
        }
        specialize (comb_partition _ _ _ _ Hp H0) as Hpart.
        destruct Hpart as (Hpart1 & Hpart2).
        specialize (IHn Hpart1).
        specialize (comb4 (S n) l1 ) as Hexact.
        assert (Forall (fun x : list bool => length x = S n) l1). {
          eapply Forall_forall.
          intros.
          Search partition. 
          assert (Forall (fun x => length x <= S n) (filter (equal_or_less_len_n (S n)) l) ). {
              eapply Forall_forall. intros.  Search filter. specialize (filter_In (equal_or_less_len_n (S n)) x0 l) as Hfin.
              destruct Hfin as (Hfin1 & _). specialize (Hfin1 H2).
              destruct Hfin1 as (_ & Hfin1). unfold equal_or_less_len_n in Hfin1.
              Search ((_ <=? _) = true). eapply leb_complete. assumption.
            }
            specialize (partition_forall (filter (equal_or_less_len_n (S n)) l) (equal_or_less_len_n n) (fun x : list bool => length x <= S n)) as Hpart_prop.
            specialize (Hpart_prop l0 l1 Hp H2).
            Search partition.
            specialize (partition_as_filter (equal_or_less_len_n n) (filter (equal_or_less_len_n (S n)) l)) as Hfilt.
            rewrite Hfilt in Hp.
            inversion Hp.
            Search filter.
            clear Hfilt.
            specialize (filter_In (fun x : list bool => negb (equal_or_less_len_n n x)) x (filter (equal_or_less_len_n (S n)) l)) as Hin.
            destruct Hin as (Hin1 & _).
            rewrite H5 in Hin1. specialize (Hin1 H1).
            destruct Hin1 as (_ & Hin1).
            Search (negb _ = true). rewrite Bool.negb_true_iff in Hin1.
            unfold equal_or_less_len_n in Hin1.
            Search ((_ <=? _) = false).
            specialize (leb_complete_conv _ _ Hin1) as Hless.
            destruct Hpart_prop as (Hpart_prop1 & Hpart_prop2).
            rewrite Forall_forall in Hpart_prop2.
            specialize (Hpart_prop2 x H1). lia.
        }
    specialize (Hexact H1 Hpart2).
    Search partition.
    specialize (partition_length _ _ Hp) as Hlen.
    rewrite Hlen.
    Search (_ ^ _). replace (S n + 1) with (S (S n)) by lia. rewrite Nat.pow_succ_r'.
    specialize (partition_as_filter (equal_or_less_len_n n) (filter (equal_or_less_len_n (S n)) l)) as Hfilt.
    rewrite Hp in Hfilt. inversion Hfilt. rewrite <- H4. rewrite <- H3. clear H4 Hfilt.
    Search filter.
    rewrite H3 in IHn.
    rewrite filter_filter_length in IHn.
    rewrite <- H3 in IHn.
    rewrite Nat.pow_succ_r'.
    replace (n + 1) with (S n) in IHn by lia.
    rewrite Nat.pow_succ_r' in IHn.
    rewrite Nat.pow_succ_r' in Hexact.
    lia.
  Qed.

  Definition equal_or_greater_len_n (n : nat) (l : list bool) :=
    n <=? length l.

  Lemma diff_lb : forall n l,
    (different l) -> length (filter (equal_or_greater_len_n n) l) >= length l + 1 - 2^(n).
  Proof.
    intros.
    destruct n.
      - replace (2^0) with 1. 2: { Search (_ ^ 0). rewrite Nat.pow_0_r. reflexivity. }
        replace (length l + 1 - 1) with (length l) by lia.
        Search filter. specialize (filter_length (equal_or_greater_len_n 0) l) as Hflt.
        destruct (filter (fun x : list bool => negb (equal_or_greater_len_n 0 x))) eqn:Hd.
        simpl in Hd. simpl in Hflt. lia.
        Search filter. 
        specialize (filter_In (fun x : list bool => negb (equal_or_greater_len_n 0 x)) l0 l) as Hin. 
        destruct Hin as (Hin1 & _).
        rewrite Hd in Hin1.
        simpl in Hin1. specialize (Hin1 ltac:(apply or_introl;reflexivity)).
        destruct Hin1 as (_ & Hin1). inversion Hin1.
      - destruct (partition (equal_or_greater_len_n (S n)) l) eqn:Hd.
        specialize (partition_as_filter (equal_or_greater_len_n (S n)) l) as Hfilt.
        Search filter.
        specialize (filter_ext (fun x : list bool => negb (equal_or_greater_len_n (S n) x)) (equal_or_less_len_n n)) as Hext.
        assert ((forall a : list bool, (fun x : list bool => negb (equal_or_greater_len_n (S n) x)) a = equal_or_less_len_n n a)). {
          intros. unfold equal_or_greater_len_n. unfold equal_or_less_len_n.
          Search (negb (_ <=? _)).
          rewrite <- Nat.ltb_antisym.
          Search (_ <? _). destruct ((length a <? S n)) eqn:Hdd.
          Search (_ <? _ = true).
          rewrite Nat.ltb_lt in Hdd.
          symmetry. Search (_ <=? _). rewrite Nat.leb_le. lia.
          Search (_ <? _ = false). rewrite Nat.ltb_ge in Hdd.
          symmetry. Search (_ <=? _). rewrite leb_iff_conv.
          lia.
        }
        specialize (Hext H0). clear H0.
        specialize (Hext l).
        specialize (comb2 n l H) as Hdiff.
        specialize (partition_length (equal_or_greater_len_n (S n)) l Hfilt) as Hlen.
        rewrite Hext in Hlen.
        rewrite Hlen.
        Search (_ <= _ -> _ <= _ -> _ <= _).
        replace (S n) with (n + 1). 2: { lia. }
        assert (2^(n + 1) >= 2). {
          replace (n + 1) with (S n). 2: { lia. }
          Search (_ ^ _). rewrite Nat.pow_succ_r'. Search (_ ^ _). 
          specialize (Nat.pow_lt_mono_r 2 0 n (ltac:(lia))) as HH.
          destruct n. replace (2^0) with 1. lia. Search (_ ^ 0). rewrite Nat.pow_0_r. reflexivity.
          specialize (HH ltac:(lia)). rewrite Nat.pow_0_r in HH. lia.
        }
        lia.
  Qed.

  Search list_sum.

  Lemma list_sum_dec : forall f (g : list bool -> nat) l,
    list_sum (map g (filter f l)) <= list_sum (map g l).
  Proof.
    induction l.
      - simpl. lia.
      - simpl. destruct (f a).
        -- simpl. lia.
        -- simpl. lia.
  Qed.

  Lemma arith1 : forall a b c,
    a >= b -> c * a >= c * b.
  Proof.
    intros.
    induction c. lia.
    lia.
  Qed.

  Lemma sum_of_at_least_k : forall l k,
    (forall x, In x l -> (equal_or_greater_len_n k x) = true) -> list_sum (map (@length (bool)) l) >= k * (length l).
  Proof.
    intros.
    induction l.
      - intros. simpl. lia.
      - intros. simpl. assert ((forall x : list bool, In x l -> equal_or_greater_len_n k x = true)).
        intros. specialize (H x). Search In. 
        simpl in H. specialize (H ltac:(apply or_intror;assumption)).
        assumption.
        specialize (IHl H0). specialize (H a). simpl in H. specialize (H ltac:(apply or_introl;reflexivity)).
        unfold equal_or_greater_len_n in H. Search ((_ <=? _) = true). rewrite Nat.leb_le in H.
        lia.
  Qed.

  (* Lemma inequality : forall n,
    (Nat.log2 n - Nat.log2 (Nat.log2 n)) * (n + 1 - 2 ^ (Nat.log2 n - Nat.log2 (Nat.log2 n))) >=
n * (Nat.log2 n - 10 * Nat.log2 (Nat.log2 n) - 10).
  Proof.
    intros.
  Admitted. *)

  (* Lemma length_lower_bound (l : list (list bool)) : 
    different l -> list_sum (map (@length (bool)) l) >= (length l) * (Nat.log2(length l) - 10 * (Nat.log2 (Nat.log2 (length l))) - 10).
  Proof.
    remember (length l) as n.
    intros.
    specialize (diff_lb (Nat.log2 n - (Nat.log2 (Nat.log2 n))) l H) as Hlb.
    specialize (list_sum_dec (equal_or_greater_len_n (Nat.log2 n - Nat.log2 (Nat.log2 n))) (@length (bool)) l) as Hdec.
    assert ((list_sum (map (length (A:=bool)) (filter (equal_or_greater_len_n (Nat.log2 n - Nat.log2 (Nat.log2 n))) l))) >= n * (Nat.log2 n - 10 * Nat.log2 (Nat.log2 n) - 10)).
    2 : {
      lia.
    }
    clear Hdec.
    remember (filter (equal_or_greater_len_n (Nat.log2 n - Nat.log2 (Nat.log2 n))) l) as l'.
    Search filter.
    specialize (filter_In (equal_or_greater_len_n (Nat.log2 n - Nat.log2 (Nat.log2 n)))) as Hin.
    specialize Hin with (l := l).
    rewrite <- Heql' in Hin.
    clear Heql'.
    specialize (sum_of_at_least_k l' (Nat.log2 n - Nat.log2 (Nat.log2 n))) as sumk.
    assert ((forall x : list bool, In x l' -> equal_or_greater_len_n (Nat.log2 n - Nat.log2 (Nat.log2 n)) x = true)).
    intros. specialize (Hin x).
    destruct (Hin) as (Hin1 & _).
    specialize (Hin1 H0).
    destruct Hin1 as (_ & Hin2).
    assumption.
    specialize (sumk H0).
    clear H0.

    assert ((Nat.log2 n - Nat.log2 (Nat.log2 n)) * length l' >= n * (Nat.log2 n - 10 * Nat.log2 (Nat.log2 n) - 10)). 2: { lia. }

    assert ((Nat.log2 n -  Nat.log2 (Nat.log2 n)) * (length l') >= (Nat.log2 n - Nat.log2 (Nat.log2 (n))) * (length l + 1 - 2 ^ (Nat.log2 n - Nat.log2 (Nat.log2 n)))).
    Search (_ * _ <= _ * _).
    Search (_ >= _ <-> _ <= _).
    eapply arith1. assumption.
    assert ((Nat.log2 n - Nat.log2 (Nat.log2 n)) * (length l + 1 - 2 ^ (Nat.log2 n - Nat.log2 (Nat.log2 n))) >= n * (Nat.log2 n - 10 * Nat.log2 (Nat.log2 n) - 10)).
    2 : { lia. }
    rewrite <- Heqn.
    clear. 
    apply inequality.
  Qed. *)
    (* Search (_ ^ (_ - _)).
    erewrite Nat.pow_sub_r. 2: { lia. }
    2 : {
     Search Nat.log2. eapply Nat.log2_le_lin. lia.
    }
    Search (2 ^ (Nat.log2 _)).
    specialize (Nat.log2_spec n) as H. destruct n.
    simpl. lia.
    specialize (H ltac:(lia)). destruct H as (H1 & H2).
    
  Admitted. *)

  Definition shift (f : nat -> nat) := fun x => f (x + 1).

  Fixpoint sum_over (f : nat -> nat) (n : nat) := match n with 
  | 0 => 0
  | S m => (f 0) + (sum_over (shift f) m)
  end.

  Lemma sum_row_sum_col : forall (n m : nat) (f : nat -> nat -> nat),
    sum_over (fun i => sum_over (f i) m) n = sum_over (fun j => sum_over (fun x => f x j) n) m.
  Proof.
    induction n.
      - intros.
        simpl. induction m.
          -- simpl. lia.
          -- simpl. assumption.
      - induction m.
          * simpl.
          clear IHn. induction n.
            + simpl. lia.
            + simpl. assumption.
          * simpl. Search (_ = _ -> _ + _ = _ + _).

          assert (sum_add : forall k (g1 g2 : nat -> nat), 
            sum_over (fun i => g1 i + g2 i) k = sum_over g1 k + sum_over g2 k). {
            induction k. intros g1 g2.
            - simpl. lia.
            - simpl. unfold shift. simpl. intros. rewrite IHk. lia.
          }
          
          repeat rewrite sum_add in *.
          unfold shift.
          intros.
          repeat rewrite sum_add.
          rewrite (IHn m (fun x y => f (x + 1) (y + 1))).
          lia.
  Qed.

  Lemma sum_over_fg : forall m g1 g2,
    (forall x, (g1 x) = (g2 x)) -> sum_over g1 m = sum_over g2 m.
  Proof.
    induction m.
      - intros. simpl. reflexivity.
      - intros. simpl. rewrite H. erewrite IHm. reflexivity.
        intros. unfold shift. erewrite H. reflexivity.
  Qed.

  Lemma sum_over_f_leq_g : forall m g1 g2,
    (forall x, (g1 x) <= (g2 x)) -> sum_over g1 m <= sum_over g2 m.
  Proof.
    induction m.
      - intros. simpl. reflexivity.
      - intros. simpl. specialize (H 0) as H0. specialize (IHm (shift g1) (shift g2)).
        assert ((forall x : nat, shift g1 x <= shift g2 x)).
        intros. unfold shift. specialize (H (x + 1)) as H1. assumption. specialize (IHm H1). lia.
  Qed.

  Lemma sum_over_indicator : forall m k l,
    sum_over (fun j : nat => if j + 1 + l <=? k then 1 else 0) m = (min (k - l) m).
  Proof.
    induction m.
      - intros. simpl. lia.
      - intros. simpl. unfold shift. erewrite sum_over_fg. 2 : {
        intros. replace (x + 1 + 1 + l) with (x + 1 + (S l)) by lia. reflexivity.  
      }
      erewrite IHm. destruct k. lia. destruct (l <=? k) eqn:Hd.
        + Search (_ <=? _). rewrite Nat.leb_le in Hd. lia.
        + Search (_ <=? _). rewrite Nat.leb_gt in Hd. lia.
  Qed.

  Lemma sum_over_list_sum : forall n l m f,
  length l = n ->
    f =
    (fun i j : nat =>
    match nth_error l i with
    | Some x => if j + 1 <=? length x then 1 else 0
    | None => 0
    end) ->
    sum_over (fun i : nat => sum_over (f i) (m)) (length l) <= list_sum (map (@length bool) l).
  Proof.
    induction n.
      - intros. destruct l. simpl. lia.
        simpl in H. lia.
      - intros. destruct l.
        + simpl in H. lia.
        + simpl in H. Search (S _ = S _). specialize (Nat.succ_inj _ _ H) as Hlen.
          specialize (IHn l0 m _ Hlen eq_refl). simpl in IHn. simpl. clear H.
          assert (sum_over (f 0) m <= length l). {
            rewrite H0. simpl. erewrite  sum_over_fg.
            2: {
              intros. replace (x + 1) with (x + 1 + 0) by lia. reflexivity.
            }
            erewrite sum_over_indicator. lia.
          }
          unfold shift. rewrite H0. simpl. 
          assert ((sum_over
(fun i : nat =>
sum_over
(fun j : nat =>
match nth_error l0 i with
| Some x => if j + 1 <=? length x then 1 else 0
| None => 0
end) m) (length l0)) = sum_over
(fun x : nat =>
sum_over
(fun j : nat =>
match nth_error (l :: l0) (x + 1) with
| Some x0 => if j + 1 <=? length x0 then 1 else 0
| None => 0
end) m) (length l0)).
          {
            eapply sum_over_fg.
            intros.
            eapply sum_over_fg.
            intros.
            replace (x + 1) with (S x) by lia.
            simpl. reflexivity. 
          }
          rewrite <- H1.
          rewrite H0 in H. simpl in H.
          lia.
  Qed.

  Lemma len_filt_sum_over : forall l x f,
    f = (fun i j : nat =>
      match nth_error l i with
      | Some x => if j + 1 <=? length x then 1 else 0
      | None => 0
      end) -> length (filter (equal_or_greater_len_n (x + 1)) l) = sum_over (fun x0 : nat => f x0 x) (length l).
  Proof.
    induction l.
      - intros. simpl. reflexivity.
      - intros. simpl. rewrite H. simpl. unfold equal_or_greater_len_n. destruct (x + 1 <=? length a).
         + simpl. f_equal. unfold equal_or_greater_len_n in IHl. 
           specialize (IHl x _ (eq_refl ((fun i j : nat =>
                        match nth_error (l) i with
                        | Some x => if j + 1 <=? length x then 1 else 0
                        | None => 0
                        end)))).
                        
          unfold shift.
          erewrite sum_over_fg. 2 : {
              intros. replace (x0 + 1) with (S x0) by lia. simpl. reflexivity.
            }
          simpl in IHl. assumption.
        +  simpl. f_equal. unfold equal_or_greater_len_n in IHl. 
           specialize (IHl x _ (eq_refl ((fun i j : nat =>
                        match nth_error (l) i with
                        | Some x => if j + 1 <=? length x then 1 else 0
                        | None => 0
                        end)))).
                        
          unfold shift.
          erewrite sum_over_fg. 2 : {
              intros. replace (x0 + 1) with (S x0) by lia. simpl. reflexivity.
            }
          simpl in IHl. assumption.
  Qed.
(* 
  Lemma easy_uneq : forall k n l,
    l <= k ->
    sum_over (fun x : nat => n + 1 - 2^(x + 1 + l)) k >= (n + 1) * (k) - (2^(k + 1) - 2^(l)).
  Proof.
    induction k.
      - intros. lia.
      - intros. simpl. unfold shift.
        specialize (IHk n (l + 1)). erewrite sum_over_fg. 2 : {
          intros. replace (x + 1 + 1 + l) with (x + 1 + (l + 1)) by lia. reflexivity.
        }
        assert ((n + 1 - 2 ^ S l) + (n + 1) * k - (2 ^ (k + 1) - 2 ^ (l + 1)) >= (n + 1) * S k - (2 ^ S (k + 1) - 2 ^ l)). 2: { lia. }
        Search (_ ^ (S _)). rewrite Nat.pow_succ_r'. rewrite Nat.pow_succ_r'.
        replace (k + 1) with (S k) by lia. replace (l + 1) with (S l) by lia. rewrite Nat.pow_succ_r'. rewrite Nat.pow_succ_r'.
         *)


  Lemma sum_const : forall k c, sum_over (fun _ => c) k = k * c.
  Proof.
    induction k. intros c.
    - simpl. lia.
    - simpl. unfold shift. intros. rewrite IHk. lia.
  Qed.

  Lemma sum_sub : forall k f g, 
    (forall x, x < k -> g x <= f x) ->
    sum_over (fun x => f x - g x) k + sum_over g k = sum_over f k.
  Proof.
    induction k. intros f g H.
    - simpl. reflexivity.
    - intros. simpl. 
      assert (H0: g 0 <= f 0). { apply H. lia. }
      assert (Hrest: forall x, x < k -> shift g x <= shift f x).
      { intros x Hx. unfold shift. apply H. lia. }
      specialize (IHk (shift f) (shift g) Hrest).
      unfold shift. unfold shift in IHk.
      lia.
  Qed.

  Lemma sum_mult_2 : forall k f, sum_over (fun x => 2 * f x) k = 2 * sum_over f k.
  Proof.
    induction k. intros f.
    - simpl. reflexivity.
    - simpl. unfold shift. intros. rewrite IHk. lia.
  Qed.

  Lemma sum_pow2 : forall k, sum_over (fun x => 2 ^ (x + 1)) k + 2 = 2 ^ (k + 1).
  Proof.
    induction k.
    - simpl. reflexivity.
    - simpl. unfold shift. 
      assert (H: forall x, 2 ^ (x + 1 + 1) = 2 * 2 ^ (x + 1)).
      { intro x. 
        replace (x + 1 + 1) with (S (x + 1)) by lia.
        reflexivity. }
      rewrite (sum_over_fg k _ _ H).
      rewrite sum_mult_2.
      change (2 ^ S (k + 1)) with (2 * 2 ^ (k + 1)).
      lia.
  Qed.


  Lemma pow2_bound_all : forall n x, x < Nat.log2 n -> 2 ^ (x + 1) <= n + 1.
  Proof.
    intros n x Hx.
    destruct n.
    - simpl in Hx. change (Nat.log2 0) with 0 in Hx. lia.
    - assert (H_lt: x + 1 <= Nat.log2 (S n)) by lia.
      assert (H_pow: 2 ^ (x + 1) <= 2 ^ Nat.log2 (S n)).
      { apply Nat.pow_le_mono_r; lia. }
      pose proof (Nat.log2_spec (S n)) as Hlog.
      assert (0 < S n) by lia.
      specialize (Hlog H).
      lia.
  Qed.

  Theorem main_sum : forall n : nat,
    sum_over (fun x : nat => n + 1 - 2 ^ (x + 1)) (Nat.log2 n) >= n * (Nat.log2 n - 2).
  Proof.
    intro n.
    remember (Nat.log2 n) as k.
    
    assert (Hbound: forall x, x < k -> 2 ^ (x + 1) <= n + 1). {
      intros x Hx. subst k. apply pow2_bound_all. exact Hx.
    }
    
    pose proof (sum_sub k (fun _ => n + 1) (fun x => 2 ^ (x + 1)) Hbound) as Hsub.
    rewrite sum_const in Hsub.
    pose proof (sum_pow2 k) as Hpow2.
    
    assert (H2n: 2 ^ (k + 1) <= 2 * n + 2). {
      subst k.
      destruct n.
      - simpl. change (2 ^ 1) with 2. lia.
      - pose proof (Nat.log2_spec (S n)) as Hlog.
        assert (0 < S n) by lia.
        specialize (Hlog H).
        replace (Nat.log2 (S n) + 1) with (S (Nat.log2 (S n))) by lia.
        simpl. Search (_ ^ (S _)). rewrite Nat.pow_succ_r'. lia.
    }
    lia. 
  Qed.

  Lemma corr_lb : forall l,
    different l -> list_sum (map (@length (bool)) l) >= (length l) * (Nat.log2(length l) - 2).
  Proof.
    intros.
    remember (fun i j => match (nth_error l i) with
      | None => 0
      | Some x => if (j + 1 <=? length x) then 1 else 0
    end) as f.
    (* specialize (sum_row_sum_col (length l) (Nat.log2(length l)) f) as Hsum. *)
    specialize (sum_over_list_sum (length l) l (Nat.log2 (length l)) f eq_refl Heqf) as Hsum.
    assert ((sum_over (fun i : nat => sum_over (f i) (Nat.log2 (length l))) (length l)) >= length l * (Nat.log2 (length l) - 2)). 2: { lia. }
    erewrite sum_row_sum_col. remember (length l) as n. specialize (sum_over_f_leq_g (Nat.log2 n) (fun x => n + 1 - 2^(x + 1)) (fun j : nat => sum_over (fun x : nat => f x j) n)) as Hflg. 
    assert ((forall x : nat,
(fun x0 : nat => n + 1 - 2 ^ (x0 + 1)) x <=
(fun j : nat => sum_over (fun x0 : nat => f x0 j) n) x)). {
      intros. specialize (diff_lb (x + 1) l H) as Hdifflb. assert (length (filter (equal_or_greater_len_n (x + 1)) l) = sum_over (fun x0 : nat => f x0 x) n). 2: { lia. }
      erewrite len_filt_sum_over. rewrite Heqn. reflexivity. exact Heqf.
    }
    specialize (Hflg H0). assert (sum_over (fun x : nat => n + 1 - 2 ^ (x + 1)) (Nat.log2 n) >= n * (Nat.log2 n - 2)). 2: { lia. }
    clear.

    eapply main_sum.
  Qed.

  Lemma ind_bound {A : Type} : forall (l : list A) i x,
    nth_error l i = Some x -> i < length l.
  Proof.
    induction l.
      - intros. simpl. destruct i. simpl in H. inversion H. simpl in H. inversion H.
      - intros. destruct i. simpl. lia.
        simpl. simpl in H. specialize (IHl i x H). lia.
  Qed.      

  Lemma comb (tokens: list Token) :
    (forall ind phr, In (Last ind phr) tokens -> False) ->
    (phrases_differ_one tokens) ->
    length (concat (map get_phrase tokens)) >= (length tokens) * (Nat.log2 (length tokens) - 2).
  Proof.
    intros. remember (map (get_phrase) tokens) as l.
    assert (different l). {
      unfold different. intros. unfold phrases_differ_one in H0. 

      specialize (ind_bound _ _ _ H2) as Hi.
      specialize (ind_bound _ _ _ H3) as Hj.

      Search (length (map _ _ ) = length (_)).
      specialize (length_map (get_phrase) tokens) as Hmapl.
      rewrite <- Heql in Hmapl.
      assert (i < length tokens) by lia.
      assert (j < length tokens) by lia.

      Search (nth_error). specialize (@nth_error_nth' Token tokens i (Last 0 []) H4) as Hit. 
      specialize (@nth_error_nth' Token tokens j (Last 0 []) H5) as Hjt.

      specialize (H0 i j _ _ H1 Hit Hjt).
      assert (not_last (nth i tokens (Last 0 []))). {
        unfold not_last.
        destruct (nth i tokens (Last 0 [])) eqn:hd.
        auto.
        specialize (nth_error_In _ _ Hit) as Hin.
        specialize (H _ _ Hin).
        assumption.
      }

      assert (not_last (nth j tokens (Last 0 []))). {
        unfold not_last.
        destruct (nth j tokens (Last 0 [])) eqn:hd.
        auto.
        specialize (nth_error_In _ _ Hjt) as Hjn.
        specialize (H _ _ Hjn).
        assumption.
      }

      specialize (H0 H6 H7).
    
      (* Search (nth_error). specialize (@nth_error_nth Token tokens i (nth i tokens (Last 0 [])) (Last 0 []) Hit) as Hnth. *)
      Search map.

      specialize (map_nth_error get_phrase i tokens Hit) as Hmap.
      rewrite Heql in H2.
      rewrite H2 in Hmap.
      inversion Hmap. clear Hmap.

      specialize (map_nth_error get_phrase j tokens Hjt) as Hmap2.
      rewrite Heql in H3.
      rewrite H3 in Hmap2.
      inversion Hmap2. clear Hmap2.
      assumption.
    }
    specialize (corr_lb l H1) as Hcor.
    Search (length (concat _)). rewrite length_concat. erewrite <- length_map. rewrite <- Heql. assumption. 
  Qed.

  Lemma all_but_last' : forall fuel dict s tokens,
    compress' fuel dict s = tokens ->
    (forall ind phr, In (Last ind phr) (removelast tokens) -> False).
  Proof.
    induction fuel. 
      - intros. simpl in H. subst. simpl in H0. assumption.
      - intros. simpl in H. destruct s.
          + subst. simpl in H0. assumption.
          + destruct (find_largest_prefix dict (b :: s)).
            destruct (skipn n0 (b :: s)).
              * subst. simpl in H0. assumption.
              * subst. simpl in H0. destruct (compress' fuel (dict ++ [firstn n0 (b :: s) ++ [b0]]) l) eqn:Hd.
                -- simpl in H0. assumption.
                -- simpl in H0. destruct H0 as [Ha | Hb].
                  ++ inversion Ha. 
                  ++ destruct l0. simpl in Hb. assumption.
                     eapply IHfuel. exact Hd. simpl. simpl in Hb.
                     exact Hb.
  Qed.

  Lemma all_but_last : forall s tokens,
    compress s = tokens ->
      (forall ind phr, In (Last ind phr) (removelast tokens) -> False).
  Proof.
    intros.
    unfold compress in H.
    eapply all_but_last'.
    exact H.
    exact H0.
  Qed.

  Lemma removelast_len {A : Type} : forall (l : list A),
    length (removelast l) = length l - 1.
  Proof.
    intros.
    induction l.
      - simpl. lia.
      - simpl. destruct l.
        + simpl. lia.
        + simpl. simpl in IHl. lia.
  Qed.    

  Lemma phrases_diff_her : forall l,
    phrases_differ_one l -> phrases_differ_one (removelast l).
  Proof.
    intros.
    unfold phrases_differ_one in *.
    intros.
    specialize (H i j t1 t2 H0).
    Search removelast.
    specialize (ind_bound _ _ _ H1) as Hi.
    specialize (ind_bound _ _ _ H2) as Hj.
    specialize (removelast_len l) as He. 
    specialize (removelast_firstn_len l) as Hlast. Search firstn.
    rewrite Hlast in H1.
    specialize (nth_error_firstn (Init.Nat.pred (length l)) l i) as Hnth.
    rewrite H1 in Hnth. assert (i <? Init.Nat.pred (length l) = true). {
      Search ((_ <? _) = true). eapply Nat.ltb_lt.
      lia.
    }
    rewrite H5 in Hnth.
    symmetry in Hnth. 
    specialize (H Hnth).

    rewrite Hlast in H2.
    specialize (nth_error_firstn (Init.Nat.pred (length l)) l j) as Hnth2.
    rewrite H2 in Hnth2. assert (j <? Init.Nat.pred (length l) = true). {
      Search ((_ <? _) = true). eapply Nat.ltb_lt.
      lia.
    }
    rewrite H6 in Hnth2.
    symmetry in Hnth2. 
    specialize (H Hnth2 H3 H4).
    assumption.
  Qed.
                             
  Lemma compress_bound: forall s tokens,
    compress s = tokens ->
    length s >= (length tokens - 1) * (Nat.log2 (length tokens - 1) - 2).
  Proof.
    unfold compress.
    intros * Hc.
    rewrite (compress'_eq_concat_phrases (length s) s empty_dict tokens
               ltac:(lia) ltac:(unfold empty_dict; now simpl) Hc).
    specialize (all_but_last _ _ Hc) as H.
    assert (length (concat (map get_phrase tokens)) >= length (concat (map get_phrase (removelast tokens)))). 2 : {
      specialize (comb (removelast tokens) H) as Hcomb.
      pose proof (compress'_phrases_differ (length s) empty_dict s tokens [] ltac:(lia) Hc) as Hpd.
      assert (agreement empty_dict []). { unfold agreement. intros. inversion H1. } specialize (Hpd H1).
      assert (nth_error empty_dict 0 = Some []). { simpl. reflexivity. } specialize (Hpd H2).
      destruct Hpd as (Hpd1 & Hpd2).
      specialize (phrases_diff_her _ Hpd2) as Hpdp.
      specialize (Hcomb Hpdp).
      specialize (removelast_len tokens) as Hlen.
      Search Nat.log2.
      assert (Nat.log2 (length (removelast tokens)) = Nat.log2 (length tokens - 1)). {
        rewrite Hlen. lia.
      }
      lia.
    }
    clear.
    induction tokens.
      - simpl. lia.
      - simpl. destruct tokens.
        + simpl. lia.
        + rewrite length_app.
          change (length (concat (map get_phrase (a :: removelast (t :: tokens))))) with  
            (length (get_phrase a ++ concat (map get_phrase (removelast (t :: tokens))))).
          rewrite length_app. lia.
  Qed.

End Impl.
