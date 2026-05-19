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

  Definition equal_or_less_len_n (n : nat) (l : list bool) := if (length l <=? n) then 1 else 0.

  Definition amount_geq_n (l : list nat) (n : nat) := list_sum (map (fun x => if (x <? n) then 0 else 1) l).

  Fixpoint gen_array (n : nat) := match n with
    | 0 => []
    | S x => S x :: (gen_array x)
    end.

  Lemma comb1 : forall l n,
    (different l) -> list_sum (map (equal_len_n n) l) <= 2^n.

  Lemma comb2 : forall l n,
    (different l) -> list_sum (map (equal_or_less_len_n n) l) <= 2^(n + 1) - 1.

  Lemma comb3 : forall l n, list_sum (map (amount_geq_n l) (gen_array n)) <= list_sum l.

  Print filter.

  Print partition.

  Search partition.

  Search filter.

  Compute (Nat.log2 3).


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


  Lemma comb (tokens: list Token) :
    (phrases_differ_one tokens) ->
    length (concat (map get_phrase tokens)) >= (length tokens) * (Nat.log2 (length tokens) - 10 * (Nat.log2 (Nat.log2 (length tokens))) - 10).
  Proof. 

  Admitted.

  Lemma compress_bound: forall s tokens,
    compress s = tokens ->
    length s >= length tokens * (Nat.log2 (length tokens) - 3).
  Proof.
    unfold compress.
    intros * Hc.
    rewrite (compress'_eq_concat_phrases (length s) s empty_dict tokens
               ltac:(lia) ltac:(unfold empty_dict; now simpl) Hc).
    apply comb.
    pose proof (compress'_phrases_differ (length s) empty_dict s tokens []) as Hpd.
    unfold empty_dict, agreement in *.
    assert ((forall index phr next,
               In (Tok index phr next) [] -> In (phr ++ [next]) [[]])). {
     intros. now simpl in Hpd.
   }
    specialize (Hpd ltac:(lia) Hc ltac:(assumption) ltac:(now simpl)).
    tauto.
  Qed.

End Impl.
