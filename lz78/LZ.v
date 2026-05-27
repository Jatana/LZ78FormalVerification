From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Dict LZ_Tokens.
Import ListNotations.

Module Impl.

  Fixpoint compress_aux (fuel: nat) (dict: dict_type) (s: list bool) :=
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
                Tok index (firstn len s) next :: compress_aux fuel (dict ++ [firstn len s ++ [next]]) rest
            end
        end
    end.

  Definition compress (s: list bool) :=
    compress_aux (length s) empty_dict s.

  Definition compress_to_bits (s: list bool) :=
    tokens_to_bits (compress s).

  Fixpoint decompress_aux (dict: dict_type) (tokens: list Token) :=
    match tokens with
    | [] => []
    | Tok index _ next :: rest =>
        match nth_error dict index with
        | Some s => s ++ [next] ++ decompress_aux (dict ++ [s ++ [next]]) rest
        | None => [] (* Should not happen *)
        end
    | Last index _ :: rest =>
        match nth_error dict index with
        | Some s => s
        | None => [] (* Should not happen *)
        end
    end.

  Definition decompress (tokens: list Token) :=
    decompress_aux empty_dict tokens.

  Definition decompress_from_bits (s: list bool) :=
    decompress (bits_to_tokens s).


  Lemma compress_aux_valid_tokens: forall fuel s dict n,
    length s <= fuel ->
    nth_error dict 0 = Some [] ->
    length dict <= n ->
    valid_tokens (compress_aux fuel dict s) n.
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

  Lemma decompress_aux_indep : forall tokens tokens' dict,
      list_eqiv token_equiv tokens tokens' ->
      decompress_aux dict tokens = decompress_aux dict tokens'.
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
    list_eqiv token_equiv tokens tokens' ->
    decompress tokens = decompress tokens'.
  Proof.
    intros. unfold decompress.
    eapply decompress_aux_indep. assumption.
  Qed.

  Lemma compress_correctness_aux: forall fuel dict s,
    length s <= fuel ->
    nth_error dict 0 = Some [] ->
    decompress_aux dict (compress_aux fuel dict s) = s.
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
      eapply compress_aux_valid_tokens.
        - lia.
        - reflexivity.
        - simpl. lia.
    }
    - eapply compress_correctness_aux.
      + lia.
      + unfold empty_dict.
        reflexivity.
  Qed.

  Lemma compress_aux_length_le_fuel: forall fuel dict s,
      length (compress_aux fuel dict s) <= fuel.
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
    apply compress_aux_length_le_fuel.
  Qed.

  Lemma tokens_to_bits_aux_length_bound: forall tokens dict_size max_dict_size,
      dict_size + length tokens <= max_dict_size ->
      length (tokens_to_bits_aux dict_size tokens)
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
    apply tokens_to_bits_aux_length_bound.
    pose proof (compress_length_upperbound s).
    simpl in *.
    now apply Nat.succ_le_mono in H.
  Qed.

  Lemma compress_aux_eq_concat_phrases: forall fuel s dict tokens,
    length s <= fuel ->
    nth_error dict 0 = Some [] ->
    compress_aux fuel dict s = tokens ->
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

  Lemma compress_aux_phrases_differ: forall fuel dict s tokens prev_tokens,
    length s <= fuel ->
    compress_aux fuel dict s = tokens ->
    dict_tokens_agreement dict prev_tokens ->
    nth_error dict 0 = Some [] ->
    phrases_differ prev_tokens tokens /\ phrases_differ_one tokens.
  Proof.
    unfold phrases_differ, phrases_differ_one, dict_tokens_agreement, not_last.
    induction fuel; intros; destruct s; simpl in *; subst.
    1, 3: split; intros; rewrite nth_error_nil in *; discriminate.
    - lia.
    - destruct (find_largest_prefix dict (b :: s)) eqn:Hd, (skipn n0 (b :: s)) eqn:Hd2.
      + split; intros; destruct j, t1, i; simpl in *; inversion H3; subst; try contradiction;
        rewrite nth_error_nil in *; discriminate.
      + destruct ((Tok n (firstn n0 (b :: s)) b0
                         :: compress_aux fuel (dict ++ [firstn n0 (b :: s) ++ [b0]]) l)) eqn:?.
        * discriminate.
        * specialize (IHfuel (dict ++ [firstn n0 (b :: s) ++ [b0]])
                             l l0 (prev_tokens ++ [Tok n (firstn n0 (b :: s)) b0])).
          assert (Hlf: length l <= fuel). {
            pose proof (length_skipn n0 (b :: s)) as Hlen.
            rewrite Hd2 in Hlen.
            simpl in *.
            destruct n0; lia.
          }
          assert (Hagr: dict_tokens_agreement (dict ++ [firstn n0 (b :: s) ++ [b0]])
                                        (prev_tokens ++ [Tok n (firstn n0 (b :: s)) b0])) by 
            now eapply dict_tokens_agreement_app.
          assert (Hns: nth_error (dict ++ [firstn n0 (b :: s) ++ [b0]]) 0 = Some []) by
            now eapply nth_error_some.
          specialize (IHfuel Hlf ltac:(congruence) Hagr Hns).
          destruct IHfuel as (IHfuel1 & IHfuel2).
          split; intros; rewrite <- Heql0 in H3; inversion Heql0; simpl in *.
          -- destruct j.
             ++ inversion H3.
                intro Hf.
                destruct t1.
                ** simpl in Hf.
                   pose proof (nth_error_In _ _ H0) as Hin.
                   specialize (H1 _ _ _ Hin).
                   pose proof (find_largest_prefix_optimal
                                 dict ((firstn n0 (b :: s)) ++ [b0]) l n n0) as Hopt.
                   assert (Hl: (firstn n0 (b :: s) ++ [b0]) ++ l = b :: s). {
                     rewrite <- app_assoc.
                     change ([b0] ++ l) with (b0 :: l).
                     now rewrite <- Hd2, firstn_skipn.
                   }
                   rewrite Hl in Hopt.
                   rewrite Hf in H1.
                   specialize (Hopt Hd H1).
                   pose proof (skipn_length _ _ _ _ Hd2) as Hlen.
                   pose proof (firstn_length_le (b :: s)) as Hbound.
                   assert (Hn0: n0 <= length (b :: s)) by lia.
                   specialize (Hbound n0 Hn0).
                   rewrite length_app, Hbound in Hopt.
                   simpl in Hopt.
                   lia.
                ** contradiction.
             ++ rewrite nth_error_cons_succ in H3.
                rewrite H8 in H3.
                eapply IHfuel1 with (i := i) (j := j); try assumption.
                now apply nth_error_some.
          -- pose proof (nth_error_app2 prev_tokens [Tok n (firstn n0 (b :: s)) b0]) as Hlem.
             specialize (Hlem (length prev_tokens) ltac:(lia)).
             replace ((length prev_tokens - length prev_tokens)) with 0 in Hlem by lia.
             destruct i, j; subst; try rewrite nth_error_cons_succ in *; simpl in *.
             ++ auto.
             ++ specialize (IHfuel1 (length prev_tokens) j t1 t2).
                rewrite Hlem, H3 in IHfuel1.
                eapply IHfuel1; auto.
             ++ specialize (IHfuel1 (length prev_tokens) i t2 t1).
                rewrite Hlem, H3 in IHfuel1.
                symmetry.
                eapply IHfuel1; auto.
             ++ apply (IHfuel2 i j); auto.
  Qed.

  Definition list_elements_distinct (l : list (list bool)) :=
    forall i j a b,
      i <> j ->
      nth_error l i = Some a ->
      nth_error l j = Some b ->
      a <> b.

  Definition length_le_n (n : nat) (l : list bool) :=
    length l <=? n.

  Definition count_geq_n (l : list nat) (n : nat) :=
    list_sum (map (fun x => if (x <? n) then 0 else 1) l).

  Fixpoint gen_seq_desc (n : nat) :=
    match n with
    | 0 => []
    | S x => S x :: (gen_seq_desc x)
    end.

  Lemma distinct_cons_inv : forall a l,
    list_elements_distinct (a :: l) ->
    list_elements_distinct l.
  Proof.
    unfold list_elements_distinct.
    intros.
    apply (H (S i) (S j) a0 b); auto.
  Qed.

  Lemma distinct_cons_in_neq : forall a b l,
    list_elements_distinct (a :: l) ->
    In b l ->
    a <> b.
  Proof.
    unfold list_elements_distinct.
    intros.
    specialize (In_nth_error _ _ H0) as Hin.
    destruct Hin as (n & Hin).
    apply (H 0 (S n) a b); auto.
  Qed.

  Lemma partition_preserves_distinct : forall l f l1 l2,
    partition f l = (l1, l2) ->
    list_elements_distinct l ->
    list_elements_distinct l1 /\ list_elements_distinct l2.
  Proof.
    unfold list_elements_distinct.
    induction l; intros; inversion H; subst; clear H; simpl in *.
    - split; intros; rewrite nth_error_nil in *; discriminate.
    - assert (Hld: list_elements_distinct l) by (eapply distinct_cons_inv; eassumption).
      destruct (f a) eqn:Hfa, (partition f l) eqn:Hp; inversion H2; subst; clear H2; simpl in *;
      match goal with
      | [ H: partition ?f _ = (?l, ?l') |- _ ] =>
          specialize (IHl f l l' ltac:(congruence) Hld); split; intros
      end.
      + destruct i, j; simpl in *; auto.
        * pose proof (nth_error_In _ _ H2) as Hin.
          assert (In b l). {
            eapply elements_in_partition.
            - eassumption.
            - now left.
          }
          injection H1 as H1; subst.
          apply distinct_cons_in_neq with (l := l).
          -- now unfold list_elements_distinct.
          -- assumption.
        * pose proof (nth_error_In _ _ H1) as Hin.
          assert (In a0 l). {
            eapply elements_in_partition.
            - eassumption.
            - now left.
          }
          injection H2 as H2; subst.
          symmetry.
          apply distinct_cons_in_neq with (l := l).
          -- now unfold list_elements_distinct.
          -- assumption.
        * destruct IHl as [IHl _].
          apply (IHl i j); lia || assumption.
      + destruct IHl as [_ IHl].
        apply (IHl i j); assumption.
      + destruct IHl as [IHl _].
        apply (IHl i j); assumption.
      + destruct i, j; simpl in *; auto.
        pose proof (nth_error_In _ _ H2) as Hin.
        assert (In b l). {
          eapply elements_in_partition.
          - eassumption.
          - now right.
        }
        injection H1 as H1; subst.
        apply distinct_cons_in_neq with (l := l).
        * now unfold list_elements_distinct.
        * assumption.
        * pose proof (nth_error_In _ _ H1) as Hin.
          assert (In a0 l). {
            eapply elements_in_partition.
            - eassumption.
            - now right.
          }
          injection H2 as H2; subst.
          symmetry.
          apply distinct_cons_in_neq with (l := l).
          -- now unfold list_elements_distinct.
          -- assumption.
        * destruct IHl as [_ IHl].
          apply (IHl i j); lia || assumption.
  Qed.

  Lemma filter_preserves_distinct : forall l f,
    list_elements_distinct l ->
    list_elements_distinct (filter f l).
  Proof.
    intros.
    destruct (partition f l) eqn:Hp.
    specialize (partition_preserves_distinct _ _ _ _ Hp H) as Hpart.
    specialize (partition_as_filter f l) as Hpf.
    rewrite Hpf in Hp.
    inversion Hp.
    rewrite H1.
    now destruct Hpart as (Hpart & _).
  Qed.

  Definition split_func (l : list bool) :=
    match l with
    | true :: lst => true
    | false :: lst => false
    | _ => true
    end.

  Definition drop_first (l : list bool) :=
    match l with
    | _ :: y => y
    | _ => []
    end.

  Lemma partition_preserves_forall: forall (l : list (list bool)) f p l1 l2,
    partition f l = (l1, l2) ->
    Forall p l ->
    Forall p l1 /\ Forall p l2.
  Proof.
    intros.
    split; eapply Forall_forall; intros;
    eapply Forall_forall; try eassumption; eapply elements_in_partition; try eassumption;
    (now apply or_introl) || (now apply or_intror).
  Qed.

  Lemma drop_first_length_pred : forall l k l1,
    Forall (fun x : list bool => length x = S k) l ->
    l1 = map drop_first l ->
    Forall (fun x : list bool => length x = k) l1.
  Proof.
    induction l; intros; subst; constructor; inversion H; subst.
    - destruct a; simpl in *; lia.
    - eapply IHl; auto.
  Qed.

  Lemma drop_first_preserves_distinct : forall l (b : bool) l1,
    list_elements_distinct l ->
    Forall (fun x => match x with
                     | s :: _ => b = s
                     | _ => False
                     end) l ->
    l1 = map drop_first l ->
    list_elements_distinct l1.
  Proof.
    unfold list_elements_distinct.
    intros.
    specialize (H i j (b :: a) (b :: b0) H2).
    remember (nth_error l i) as x.
    specialize (nth_error_map (drop_first) i l) as Hnth1.
    destruct (nth_error l i) eqn:Hd1; subst; simpl in *; rewrite H3 in Hnth1;
    inversion Hnth1.
    specialize (nth_error_In _ _ Hd1) as Hin.
    specialize (Forall_forall (fun x : list bool => match x with
                                                    | [] => False
                                                    | s :: _ => b = s
                                                    end) l) as Hfor.
    destruct Hfor as (Hfor & _).
    specialize (Hfor H0 l0 Hin).
    destruct l0; subst; simpl in *.
    - auto.
    - specialize (H eq_refl).
      remember (nth_error l j) as y.
      specialize (nth_error_map (drop_first) j l) as Hnth2.
      subst.
      destruct (nth_error l j) eqn:Hd2; simpl in Hnth2; rewrite H4 in Hnth2; inversion Hnth2.
      subst.
      specialize (nth_error_In _ _ Hd2) as Hin2.
      specialize (Forall_forall (fun x : list bool => match x with
                                                      | [] => False
                                                      | s :: _ => b1 = s
                                                      end) l) as Hfor.
      destruct Hfor as (Hfor & _).
      specialize (Hfor H0 l1 Hin2).
      destruct l1; subst; simpl in *.
      + auto.
      + specialize (H eq_refl).
        unfold "<>".
        intros.
        subst.
        auto.
  Qed.


  Lemma distinct_length_n_bound : forall k (l : list (list bool)),
    Forall (fun x => length x = k) l ->
    list_elements_distinct l ->
    length l <= 2^k.
  Proof.
    unfold list_elements_distinct.
    induction k; intros.
    - change (2^0) with 1.
      destruct l; simpl.
      + lia.
      + inversion H. subst.
        destruct l0; simpl.
        * lia.
        * inversion H4. subst.
          destruct l, l0; simpl in *; try lia.
          specialize (H0 0 1 [] [] ltac:(lia) ltac:(constructor) ltac:(constructor)).
          exfalso.
          now eapply H0.
    - destruct (partition split_func l) as [l1 l2] eqn:Hspl.
      pose proof (partition_as_filter split_func l) as Hfilt.
      assert ((Forall (fun x : list bool => length x = S k) l1) /\
              (Forall (fun x : list bool => length x = S k) l2)) as Hlen. {
        eapply partition_preserves_forall; eassumption.
      }
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
      assert (Hl1: Forall (fun x : list bool => length x = k) l1'). {
        eapply drop_first_length_pred.
        - exact Hlen1.
        - exact Hr1.
      }
      specialize (IHk1 Hl1).
      assert (Hl2: Forall (fun x : list bool => length x = k) l2'). {
        eapply drop_first_length_pred.
        - exact Hlen2.
        - exact Hr2.
      }
      specialize (IHk2 Hl2).
      pose proof (filter_In split_func) as Hfin1.
      specialize (Hfin1) with (l := l).
      rewrite Hspl in Hfilt.
      inversion Hfilt.
      pose proof (partition_preserves_distinct _ _ _ _ Hspl H0) as [Hdiff1 Hdiff2].
      assert (list_elements_distinct l1'). {
        eapply drop_first_preserves_distinct with (b := true).
        - exact Hdiff1.
        - apply Forall_forall.
          intros.
          rewrite <- H2 in Hfin1.
          specialize (Hfin1 x).
          destruct Hfin1 as (Hfin11 & _).
          specialize (Hfin11 H1).
          destruct Hfin11 as (Hin3 & Hspltrue).
          unfold split_func in Hspltrue.
          destruct x.
          + specialize (Forall_forall (fun x : list bool => length x = S k) l1) as Hfor3.
            destruct Hfor3 as (Hfor3 & _).
            specialize (Hfor3 Hlen1 [] H1).
            simpl in Hfor3. lia.
          + destruct b; [trivial | symmetry]; auto.
        - exact Hr1.
      }
      specialize (IHk1 H1).
      pose proof (filter_In (fun x : list bool => negb (split_func x))) as Hfin2.
      specialize (Hfin2) with (l := l).
      assert (list_elements_distinct l2'). {
        eapply drop_first_preserves_distinct with (b := false).
        - exact Hdiff2.
        - apply Forall_forall.
          intros.
          rewrite <- H3 in Hfin2.
          specialize (Hfin2 x).
          destruct (Hfin2) as (Hfin11 & _).
          specialize (Hfin11 H4).
          destruct Hfin11 as (Hin3 & Hspltrue).
          unfold split_func in Hspltrue.
          destruct x; simpl in *.
          + inversion Hspltrue.
          + destruct b.
            * inversion Hspltrue.
            * reflexivity.
        - exact Hr2.
      }
      specialize (IHk2 H4).
      pose proof (partition_length split_func l Hspl) as Hpartlen.
      assert (length l1' = length l1) by (rewrite Hr1; apply length_map).
      assert (length l2' = length l2) by (rewrite Hr2; apply length_map).
      rewrite Nat.pow_succ_r'. lia.
  Qed.

  Lemma filter_filter_length {A : Type} : forall (f : A -> bool) l,
   length (filter f (filter f l)) = length (filter f l).
  Proof.
    intros.
    specialize (filter_length f (filter f l)) as H.
    assert (length (filter (fun x : A => negb (f x)) (filter f l)) = 0). {
      destruct (filter (fun x : A => negb (f x)) (filter f l)) eqn:Hd; simpl.
      - lia.
      - specialize (filter_In (fun x : A => negb (f x)) a (filter f l)) as (Hfin1 & _).
        rewrite Hd in Hfin1.
        simpl in Hfin1.
        specialize (Hfin1 ltac:(apply or_introl; reflexivity)).
        specialize (filter_In f a l) as (Hfin2 & _).
        destruct Hfin1 as (Ha & Hb).
        specialize (Hfin2 Ha).
        destruct Hfin2 as (_ & Hc).
        rewrite Hc in Hb.
        simpl in Hb.
        discriminate.
    }
    lia.
  Qed.

  Lemma distinct_length_le_n_bound : forall n l,
    list_elements_distinct l ->
    length (filter (length_le_n n) l) <= 2^(n + 1) - 1.
  Proof.
    induction n; intros.
    - change (2 ^ (0 + 1) - 1) with (2^0).
      eapply distinct_length_n_bound.
      + eapply Forall_forall. intros.
        specialize (filter_In (length_le_n 0) x l) as Hin.
        destruct Hin as (Hin1 & _).
        specialize (Hin1 H0).
        destruct Hin1 as (_ & Hin1).
        unfold length_le_n in Hin1.
        destruct x; simpl in *.
        * reflexivity.
        * discriminate.
      + now apply filter_preserves_distinct.
    - destruct (partition (length_le_n n) (filter (length_le_n (S n)) l)) eqn:Hp.
      specialize (IHn l0).
      assert (list_elements_distinct (filter (length_le_n (S n)) l)) by now apply filter_preserves_distinct.
      specialize (partition_preserves_distinct _ _ _ _ Hp H0) as Hpart.
      destruct Hpart as (Hpart1 & Hpart2).
      specialize (IHn Hpart1).
      specialize (distinct_length_n_bound (S n) l1 ) as Hexact.
      assert (Forall (fun x : list bool => length x = S n) l1). {
        eapply Forall_forall.
        intros.
        assert (Forall (fun x => length x <= S n) (filter (length_le_n (S n)) l) ). {
          apply Forall_forall.
          intros.
          specialize (filter_In (length_le_n (S n)) x0 l) as Hfin.
          destruct Hfin as (Hfin1 & _).
          specialize (Hfin1 H2).
              destruct Hfin1 as (_ & Hfin1).
              unfold length_le_n in *.
              now apply leb_complete.
        }
        specialize (partition_preserves_forall (filter (length_le_n (S n)) l) (length_le_n n)
                      (fun x : list bool => length x <= S n)) as Hpart_prop.
        specialize (Hpart_prop l0 l1 Hp H2).
        specialize (partition_as_filter (length_le_n n)
                      (filter (length_le_n (S n)) l)) as Hfilt.
        rewrite Hfilt in Hp.
        inversion Hp.
        specialize (filter_In (fun x : list bool => negb (length_le_n n x)) x
                      (filter (length_le_n (S n)) l)) as Hin.
        destruct Hin as (Hin1 & _).
        rewrite H5 in Hin1.
        specialize (Hin1 H1).
        destruct Hin1 as (_ & Hin1).
        rewrite Bool.negb_true_iff in Hin1.
        unfold length_le_n in *.
        specialize (leb_complete_conv _ _ Hin1) as Hless.
        destruct Hpart_prop as (Hpart_prop1 & Hpart_prop2).
        rewrite Forall_forall in Hpart_prop2.
        specialize (Hpart_prop2 x H1).
        lia.
      }
      specialize (Hexact H1 Hpart2).
      specialize (partition_length _ _ Hp) as Hlen.
      replace (S n + 1) with (S (S n)) by lia.
      rewrite Hlen, Nat.pow_succ_r'.
      specialize (partition_as_filter (length_le_n n)
                   (filter (length_le_n (S n)) l)) as Hfilt.
      rewrite Hp in Hfilt.
      inversion Hfilt.
      rewrite <- H4, <- H3.
      rewrite H3, filter_filter_length, <- H3 in IHn.
      rewrite Nat.pow_succ_r'.
      replace (n + 1) with (S n) in IHn by lia.
      rewrite Nat.pow_succ_r' in *.
      lia.
  Qed.

  Definition length_ge_n (n : nat) (l : list bool) :=
    n <=? length l.

  Lemma distinct_length_ge_n_lower_bound : forall n l,
    list_elements_distinct l ->
    length (filter (length_ge_n n) l) >= length l + 1 - 2^(n).
  Proof.
    intros.
    destruct n.
    - replace (2^0) with 1.
      2: { rewrite Nat.pow_0_r. reflexivity. }
      replace (length l + 1 - 1) with (length l) by lia.
      specialize (filter_length (length_ge_n 0) l) as Hflt.
      destruct (filter (fun x : list bool => negb (length_ge_n 0 x))) eqn:Hd.
      simpl in Hd. simpl in Hflt. lia.
      specialize (filter_In (fun x : list bool => negb (length_ge_n 0 x)) l0 l) as Hin.
      destruct Hin as (Hin1 & _).
      rewrite Hd in Hin1.
      simpl in Hin1. specialize (Hin1 ltac:(apply or_introl;reflexivity)).
      destruct Hin1 as (_ & Hin1).
      discriminate.
    - destruct (partition (length_ge_n (S n)) l) eqn:Hd.
      specialize (partition_as_filter (length_ge_n (S n)) l) as Hfilt.
      specialize (filter_ext (fun x : list bool => negb (length_ge_n (S n) x))
                             (length_le_n n)) as Hext.
      assert ((forall a : list bool, (fun x : list bool =>
                  negb (length_ge_n (S n) x)) a = length_le_n n a)). {
        intros. unfold length_ge_n, length_le_n.
        rewrite <- Nat.ltb_antisym.
        destruct ((length a <? S n)) eqn:Hdd;
        [(rewrite Nat.ltb_lt in Hdd) | (rewrite Nat.ltb_ge in Hdd)]; symmetry;
        [(rewrite Nat.leb_le) | (rewrite leb_iff_conv)]; lia.
      }
      specialize (Hext H0).
      specialize (Hext l).
      specialize (distinct_length_le_n_bound n l H) as Hdiff.
      specialize (partition_length (length_ge_n (S n)) l Hfilt) as Hlen.
      rewrite Hext in Hlen.
      rewrite Hlen.
      replace (S n) with (n + 1). 2: { lia. }
      assert (2^(n + 1) >= 2). {
        replace (n + 1) with (S n).
        2: { lia. }
        rewrite Nat.pow_succ_r'.
        specialize (Nat.pow_lt_mono_r 2 0 n (ltac:(lia))) as HH.
        destruct n.
        - replace (2^0) with 1.
          + lia.
          + now rewrite Nat.pow_0_r.
        - specialize (HH ltac:(lia)).
          rewrite Nat.pow_0_r in HH.
          lia.
      }
      lia.
  Qed.

  Lemma list_sum_filter_le : forall f (g : list bool -> nat) l,
    list_sum (map g (filter f l)) <= list_sum (map g l).
  Proof.
    induction l; simpl.
    - lia.
    - destruct (f a); simpl; lia.
  Qed.

  Lemma mul_le_mono_l_nat : forall a b c,
    a >= b ->
    c * a >= c * b.
  Proof.
    intros.
    induction c; lia.
  Qed.

  Lemma sum_length_ge_k_bound : forall l k,
    (forall x, In x l -> (length_ge_n k x) = true) ->
    list_sum (map (@length (bool)) l) >= k * (length l).
  Proof.
    intros.
    induction l; simpl in *.
    - lia.
    - assert ((forall x : list bool, In x l -> length_ge_n k x = true)). {
        intros.
        specialize (H x).
        now specialize (H ltac:(apply or_intror; assumption)).
      }
      specialize (IHl H0).
      specialize (H a).
      specialize (H ltac:(apply or_introl;reflexivity)).
      unfold length_ge_n in H.
      rewrite Nat.leb_le in H.
      lia.
  Qed.

  Definition shift (f : nat -> nat) := fun x => f (x + 1).

  Fixpoint sum_over (f : nat -> nat) (n : nat) :=
    match n with
    | 0 => 0
    | S m => (f 0) + (sum_over (shift f) m)
    end.

  Lemma sum_row_sum_col : forall (n m : nat) (f : nat -> nat -> nat),
    sum_over (fun i => sum_over (f i) m) n = sum_over (fun j => sum_over (fun x => f x j) n) m.
  Proof.
    induction n; simpl; induction m; intros; simpl.
    - lia.
    - now eapply IHm.
    - clear IHn. induction n; simpl; auto.
    - assert (sum_add: forall k (g1 g2 : nat -> nat),
                         sum_over (fun i => g1 i + g2 i) k = sum_over g1 k + sum_over g2 k). {
        induction k; intros; simpl.
        - lia.
        - unfold shift.
          rewrite IHk. lia.
      }
      unfold shift.
      repeat rewrite sum_add in *.
      rewrite (IHn m (fun x y => f (x + 1) (y + 1))).
      lia.
  Qed.

  Lemma sum_over_fg : forall m g1 g2,
    (forall x, (g1 x) = (g2 x)) ->
    sum_over g1 m = sum_over g2 m.
  Proof.
    induction m; intros; simpl.
    - reflexivity.
    - erewrite H, IHm.
      + reflexivity.
      + intros.
        unfold shift.
        now rewrite H.
  Qed.

  Lemma sum_over_f_leq_g : forall m g1 g2,
    (forall x, (g1 x) <= (g2 x)) ->
    sum_over g1 m <= sum_over g2 m.
  Proof.
    induction m; intros; simpl.
    - reflexivity.
    - specialize (H 0) as H0.
      specialize (IHm (shift g1) (shift g2)).
      assert ((forall x : nat, shift g1 x <= shift g2 x)). {
        intros.
        unfold shift.
        now specialize (H (x + 1)) as H1.
      }
      specialize (IHm H1).
      lia.
  Qed.

  Lemma sum_over_indicator : forall m k l,
    sum_over (fun j : nat => if j + 1 + l <=? k then 1 else 0) m = (min (k - l) m).
  Proof.
    induction m; intros; simpl.
    - lia.
    - unfold shift.
      erewrite sum_over_fg.
      2: {
        intros.
        replace (x + 1 + 1 + l) with (x + 1 + (S l)) by lia.
        reflexivity.
      }
      rewrite IHm.
      destruct k.
      + lia.
      + destruct (l <=? k) eqn:Hd.
        * rewrite Nat.leb_le in Hd. lia.
        * rewrite Nat.leb_gt in Hd. lia.
  Qed.

  Lemma sum_over_list_sum : forall n l m f,
    length l = n ->
    f = (fun i j : nat =>
            match nth_error l i with
            | Some x => if j + 1 <=? length x then 1 else 0
            | None => 0
            end) ->
    sum_over (fun i : nat => sum_over (f i) (m)) (length l) <= list_sum (map (@length bool) l).
  Proof.
    induction n; intros; destruct l; simpl in *; try lia.
    specialize (Nat.succ_inj _ _ H) as Hlen.
    specialize (IHn l0 m _ Hlen eq_refl).
    simpl in *.
    assert (sum_over (f 0) m <= length l). {
      rewrite H0.
      simpl.
      erewrite sum_over_fg.
      2: {
        intros.
        replace (x + 1) with (x + 1 + 0) by lia.
        reflexivity.
      }
      rewrite sum_over_indicator.
      lia.
    }
    unfold shift.
    rewrite H0.
    simpl.
    assert ((sum_over (fun i : nat =>
                        sum_over (fun j : nat =>
                              match nth_error l0 i with
                              | Some x => if j + 1 <=? length x then 1 else 0
                              | None => 0
                              end) m)
                      (length l0)) =
             sum_over (fun i : nat =>
                        sum_over (fun j : nat =>
                              match nth_error (l :: l0) (i + 1) with
                              | Some x => if j + 1 <=? length x then 1 else 0
                              | None => 0
                              end) m)
                        (length l0)). {
      do 2 (eapply sum_over_fg; intros).
      replace (x + 1) with (S x) by lia.
      reflexivity.
    }
    rewrite <- H2.
    rewrite H0 in H1.
    simpl in *.
    lia.
  Qed.

  Lemma length_filter_eq_sum_over : forall l x f,
    f = (fun i j : nat =>
            match nth_error l i with
            | Some x => if j + 1 <=? length x then 1 else 0
            | None => 0
            end) ->
    length (filter (length_ge_n (x + 1)) l) = sum_over (fun x0 : nat => f x0 x) (length l).
  Proof.
    induction l; intros; simpl.
    - reflexivity.
    - rewrite H.
      simpl.
      unfold length_ge_n in *.
      specialize (IHl x _ (eq_refl ((fun i j : nat =>
                                      match nth_error (l) i with
                                      | Some x => if j + 1 <=? length x then 1 else 0
                                      | None => 0
                                      end)))).
      destruct (x + 1 <=? length a); simpl in *; f_equal; unfold shift; erewrite sum_over_fg.
      2, 4: intros; replace (x0 + 1) with (S x0) by lia; reflexivity.
      all: assumption.
  Qed.

  Lemma sum_over_const : forall k c,
    sum_over (fun _ => c) k = k * c.
  Proof.
    induction k; simpl; unfold shift; intros.
    - lia.
    - rewrite IHk.
      lia.
  Qed.

  Lemma sum_over_sub : forall k f g,
    (forall x, x < k -> g x <= f x) ->
    sum_over (fun x => f x - g x) k + sum_over g k = sum_over f k.
  Proof.
    induction k; intros * H; simpl.
    - reflexivity.
    - assert (H0: g 0 <= f 0) by (apply H; lia).
      assert (Hrest: forall x, x < k -> shift g x <= shift f x). {
        intros x Hx.
        unfold shift.
        apply H.
        lia.
      }
      specialize (IHk (shift f) (shift g) Hrest).
      unfold shift in *.
      lia.
  Qed.

  Lemma sum_over_mult_2 : forall k f,
    sum_over (fun x => 2 * f x) k = 2 * sum_over f k.
  Proof.
    induction k; simpl; unfold shift; intros.
    - reflexivity.
    - rewrite IHk.
      lia.
  Qed.

  Lemma sum_over_pow2 : forall k,
    sum_over (fun x => 2 ^ (x + 1)) k + 2 = 2 ^ (k + 1).
  Proof.
    induction k; simpl; unfold shift.
    - reflexivity.
    - assert (H: forall x, 2 ^ (x + 1 + 1) = 2 * 2 ^ (x + 1)). {
        intro x.
        replace (x + 1 + 1) with (S (x + 1)) by lia.
        reflexivity.
      }
      rewrite (sum_over_fg k _ _ H).
      rewrite sum_over_mult_2.
      change (2 ^ S (k + 1)) with (2 * 2 ^ (k + 1)).
      lia.
  Qed.

  Lemma pow2_log2_bound : forall n x,
    x < Nat.log2 n ->
    2 ^ (x + 1) <= n + 1.
  Proof.
    intros n x Hx.
    destruct n; simpl in *.
    - change (Nat.log2 0) with 0 in Hx.
      lia.
    - assert (H_lt: x + 1 <= Nat.log2 (S n)) by lia.
      assert (H_pow: 2 ^ (x + 1) <= 2 ^ Nat.log2 (S n)) by (apply Nat.pow_le_mono_r; lia).
      pose proof (Nat.log2_spec (S n)) as Hlog.
      assert (0 < S n) by lia.
      specialize (Hlog H).
      lia.
  Qed.

  Theorem sum_over_log2_lower_bound : forall n : nat,
    sum_over (fun x : nat => n + 1 - 2 ^ (x + 1)) (Nat.log2 n) >= n * (Nat.log2 n - 2).
  Proof.
    intro n.
    remember (Nat.log2 n) as k.

    assert (Hbound: forall x, x < k -> 2 ^ (x + 1) <= n + 1). {
      intros x Hx.
      subst k.
      now apply pow2_log2_bound.
    }

    pose proof (sum_over_sub k (fun _ => n + 1) (fun x => 2 ^ (x + 1)) Hbound) as Hsub.
    rewrite sum_over_const in Hsub.
    pose proof (sum_over_pow2 k) as Hpow2.

    assert (H2n: 2 ^ (k + 1) <= 2 * n + 2). {
      subst k.
      destruct n; simpl in *.
      - change (2 ^ 1) with 2.
        lia.
      - pose proof (Nat.log2_spec (S n)) as Hlog.
        assert (0 < S n) by lia.
        specialize (Hlog H).
        replace (Nat.log2 (S n) + 1) with (S (Nat.log2 (S n))) by lia.
        rewrite Nat.pow_succ_r'.
        lia.
    }
    lia.
  Qed.

  Lemma distinct_phrases_length_lower_bound : forall l,
    list_elements_distinct l ->
    list_sum (map (@length (bool)) l) >= (length l) * (Nat.log2(length l) - 2).
  Proof.
    intros.
    remember (fun i j => match (nth_error l i) with
                         | None => 0
                         | Some x => if (j + 1 <=? length x) then 1 else 0
                         end) as f.
    specialize (sum_over_list_sum (length l) l (Nat.log2 (length l)) f eq_refl Heqf) as Hsum.
    assert ((sum_over (fun i : nat => sum_over (f i) (Nat.log2 (length l))) (length l))
              >= length l * (Nat.log2 (length l) - 2)). {
      erewrite sum_row_sum_col.
      remember (length l) as n.
      specialize (sum_over_f_leq_g (Nat.log2 n) (fun x => n + 1 - 2^(x + 1))
                    (fun j : nat => sum_over (fun x : nat => f x j) n)) as Hflg.
      assert ((forall x : nat, (fun x0 : nat => n + 1 - 2 ^ (x0 + 1)) x
                  <= (fun j : nat => sum_over (fun x0 : nat => f x0 j) n) x)). {
        intros.
        specialize (distinct_length_ge_n_lower_bound (x + 1) l H) as Hdifflb.
        assert (length (filter (length_ge_n (x + 1)) l)
                  = sum_over (fun x0 : nat => f x0 x) n). {
          erewrite length_filter_eq_sum_over.
          - now rewrite Heqn.
          - assumption.
        }
        lia.
      }
      specialize (Hflg H0).
      assert (sum_over (fun x : nat => n + 1 - 2 ^ (x + 1)) (Nat.log2 n)
                >= n * (Nat.log2 n - 2)) by apply sum_over_log2_lower_bound.
      lia.
    }
    lia.
  Qed.

  Lemma nth_error_implies_lt_length {A : Type} : forall (l : list A) i x,
    nth_error l i = Some x -> i < length l.
  Proof.
    induction l; intros; destruct i; simpl in *.
    - discriminate.
    - discriminate.
    - lia.
    - specialize (IHl i x H).
      lia.
  Qed.

  Lemma tokens_concat_length_lower_bound (tokens: list Token) :
    (forall ind phr, In (Last ind phr) tokens -> False) ->
    phrases_differ_one tokens ->
    length (concat (map get_phrase tokens)) >= length tokens * (Nat.log2 (length tokens) - 2).
  Proof.
    intros. remember (map (get_phrase) tokens) as l.
    assert (list_elements_distinct l). {
      unfold list_elements_distinct. intros. unfold phrases_differ_one in H0.

      specialize (nth_error_implies_lt_length _ _ _ H2) as Hi.
      specialize (nth_error_implies_lt_length _ _ _ H3) as Hj.

      specialize (length_map (get_phrase) tokens) as Hmapl.
      rewrite <- Heql in Hmapl.
      assert (i < length tokens) by lia.
      assert (j < length tokens) by lia.

      specialize (@nth_error_nth' Token tokens i (Last 0 []) H4) as Hit.
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
    specialize (distinct_phrases_length_lower_bound l H1) as Hcor.
    rewrite length_concat. erewrite <- length_map. rewrite <- Heql. assumption.
  Qed.

  Lemma compress_aux_no_last_in_removelast : forall fuel dict s tokens,
    compress_aux fuel dict s = tokens ->
    (forall ind phr, In (Last ind phr) (removelast tokens) -> False).
  Proof.
    induction fuel; intros; simpl in *; subst.
    - now simpl in *.
    - destruct s; simpl in *; trivial.
      destruct (find_largest_prefix dict (b :: s)).
      destruct (skipn n0 (b :: s)); subst; simpl in *; trivial.
      destruct (compress_aux fuel (dict ++ [firstn n0 (b :: s) ++ [b0]]) l) eqn:Hd; simpl in *; trivial.
      destruct H0 as [Ha | Hb].
      + inversion Ha.
      + destruct l0; simpl in *; trivial.
        eapply IHfuel; simpl in *.
        * eassumption.
        * exact Hb.
  Qed.

  Lemma compress_no_last_in_removelast : forall s tokens,
    compress s = tokens ->
    (forall ind phr, In (Last ind phr) (removelast tokens) -> False).
  Proof.
    intros.
    unfold compress in *.
    eapply compress_aux_no_last_in_removelast; eassumption.
  Qed.

  Lemma removelast_len {A : Type} : forall (l : list A),
    length (removelast l) = length l - 1.
  Proof.
    induction l; simpl.
    - lia.
    - destruct l; simpl in *; lia.
  Qed.

  Lemma phrases_differ_one_removelast : forall l,
    phrases_differ_one l ->
    phrases_differ_one (removelast l).
  Proof.
    unfold phrases_differ_one in *.
    intros.
    specialize (H i j t1 t2 H0).
    specialize (nth_error_implies_lt_length _ _ _ H1) as Hi.
    specialize (nth_error_implies_lt_length _ _ _ H2) as Hj.
    specialize (removelast_len l) as He.
    specialize (removelast_firstn_len l) as Hlast.
    rewrite Hlast in H1.
    specialize (nth_error_firstn (Init.Nat.pred (length l)) l i) as Hnth.
    rewrite H1 in Hnth.
    assert (i <? Init.Nat.pred (length l) = true). {
      eapply Nat.ltb_lt.
      lia.
    }
    rewrite H5 in Hnth.
    symmetry in Hnth.
    specialize (H Hnth).

    rewrite Hlast in H2.
    specialize (nth_error_firstn (Init.Nat.pred (length l)) l j) as Hnth2.
    rewrite H2 in Hnth2.
    assert (j <? Init.Nat.pred (length l) = true). {
      eapply Nat.ltb_lt.
      lia.
    }
    rewrite H6 in Hnth2.
    symmetry in Hnth2.
    specialize (H Hnth2 H3 H4).
    assumption.
  Qed.

  Lemma compress_length_lower_bound: forall s tokens,
    compress s = tokens ->
    length s >= (length tokens - 1) * (Nat.log2 (length tokens - 1) - 2).
  Proof.
    unfold compress.
    intros * Hc.
    rewrite (compress_aux_eq_concat_phrases (length s) s empty_dict tokens
               ltac:(lia) ltac:(unfold empty_dict; now simpl) Hc).
    specialize (compress_no_last_in_removelast _ _ Hc) as H.
    assert (length (concat (map get_phrase tokens))
              >= length (concat (map get_phrase (removelast tokens)))). {
      clear.
      induction tokens.
        - simpl. lia.
        - simpl. destruct tokens.
          + simpl. lia.
          + rewrite length_app.
            change (length (concat (map get_phrase (a :: removelast (t :: tokens))))) with
              (length (get_phrase a ++ concat (map get_phrase (removelast (t :: tokens))))).
            rewrite length_app. lia.
    }
    specialize (tokens_concat_length_lower_bound (removelast tokens) H) as Hcomb.
    pose proof (compress_aux_phrases_differ (length s) empty_dict s tokens [] ltac:(lia) Hc) as Hpd.
    assert (dict_tokens_agreement empty_dict []). { unfold dict_tokens_agreement. intros. inversion H1. } specialize (Hpd H1).
    assert (nth_error empty_dict 0 = Some []). { simpl. reflexivity. } specialize (Hpd H2).
    destruct Hpd as (Hpd1 & Hpd2).
    specialize (phrases_differ_one_removelast _ Hpd2) as Hpdp.
    specialize (Hcomb Hpdp).
    specialize (removelast_len tokens) as Hlen.
    assert (Nat.log2 (length (removelast tokens)) = Nat.log2 (length tokens - 1)). {
      rewrite Hlen. lia.
    }
    lia.
  Qed.


  Lemma log2_10_n: forall x,
    10 <= Nat.log2 x ->
    1024 <= x.
  Proof.
    intros * H.
    destruct (Nat.ltb x 1024) eqn:E.
    - apply Nat.ltb_lt in E.
      assert (Nat.log2 x <= Nat.log2 1023) by (apply Nat.log2_le_mono; lia).
      assert (Nat.log2 1023 = 9) by now compute.
      rewrite H1 in H0.
      lia.
    - now apply Nat.ltb_ge in E.
  Qed.

  Lemma log2_lt_pow2: forall a b,
    0 < a ->
    a < 2 ^ b ->
    Nat.log2 a < b.
  Proof.
    intros * Ha Hab.
    destruct (Nat.ltb (Nat.log2 a) b) eqn:E.
    - now apply Nat.ltb_lt in E.
    - apply Nat.ltb_ge in E.
      pose proof (Nat.log2_spec a Ha) as [Hpow _].
      pose proof (Nat.pow_le_mono_r 2 b (Nat.log2 a) ltac:(lia) E).
      lia.
  Qed.

  Lemma log2_square_upper_bound: forall x,
    0 < x ->
    Nat.log2 (x * x) <= 2 * Nat.log2 x + 1.
  Proof.
    intros * Hx.
    pose proof (Nat.log2_spec x Hx) as [_ H2].
    assert (x * x < 2 ^ (Nat.log2 x + 1) * 2 ^ (Nat.log2 x + 1)). {
      apply Nat.square_lt_mono_nonneg.
      - lia.
      - assert (S (Nat.log2 x) = Nat.log2 x + 1) by lia.
        now rewrite <- H.
    }
    assert (Nat.log2 x + 1 + (Nat.log2 x + 1) = 2 * Nat.log2 x + 2) by lia.
    rewrite <- Nat.pow_add_r, H0 in H.
    assert (Nat.log2 (x * x) < 2 * Nat.log2 x + 2) by (apply log2_lt_pow2; lia).
    lia.
  Qed.

  Lemma square_le_pow2: forall m,
    4 <= m ->
    m * m <= 2 ^ m.
  Proof.
    induction m; intros.
    - lia.
    - destruct (Nat.eq_dec m 3) as [Eq | Neq].
      + subst. cbv. lia.
      + assert (4 <= m) by lia.
        specialize (IHm H0).
        replace (2 ^ S m) with (2 * 2 ^ m) by reflexivity.
        nia.
  Qed.

  Lemma log2_4_16: forall x,
    16 <= x ->
    4 <= Nat.log2 x.
  Proof.
    intros * H.
    assert (H1: Nat.log2 16 <= Nat.log2 x) by (apply Nat.log2_le_mono; lia).
    now simpl in H1.
  Qed.

  Lemma log2_square_le: forall x,
    16 <= x ->
    Nat.log2 x * Nat.log2 x <= x.
  Proof.
    intros * H.
    assert (4 <= Nat.log2 x) by (apply log2_4_16; lia).
    pose proof (square_le_pow2 (Nat.log2 x) H0).
    assert (0 < x) by lia.
    pose proof (Nat.log2_spec x H2) as [H3 _].
    lia.
  Qed.

  Lemma log2_le : forall x,
    16 <= x ->
    Nat.log2 x <= x.
  Proof.
    intros x H.
    pose proof (log2_square_le x H).
    assert (4 <= Nat.log2 x) by (apply log2_4_16; lia).
    nia.
  Qed.

  Lemma square_le_mono: forall n m k,
    n <= k ->
    m <= k ->
    n * m <= k * k.
  Proof. intros. nia. Qed.

  Section AsymptoticBound.

    Variables n m k : nat.

    Hypothesis Hn : 1 <= n.
    Hypothesis Hlog : 10 <= Nat.log2 n.
    Hypothesis Hmn : m <= n * (Nat.log2 n + 2).
    Hypothesis Hnk : (n - 1) * (Nat.log2 n - 3) <= k.
    Hypothesis Hk_large : 12 <= Nat.log2 k.

    Lemma algebraic_bound: m <= k + 5 * n + Nat.log2 n.
    Proof.
      remember (Nat.log2 n) as L.
      assert (n * L <= (n - 1) * (L - 3) + 3 * n + L) by nia.
      lia.
    Qed.

    Lemma bound_log: Nat.log2 n * Nat.log2 k <= k.
    Proof.
      assert (1024 <= n) by (apply log2_10_n; lia).
      assert (n <= k) by nia.
      assert (Nat.log2 n <= Nat.log2 k) by (apply Nat.log2_le_mono; lia).
      assert (16 <= k) by lia.
      pose proof (log2_square_le k ltac:(assumption)).
      nia.
    Qed.

    Lemma bound_n: n * Nat.log2 k <= 4 * k.
    Proof.
      assert (1024 <= n) by (apply log2_10_n; lia).
      assert (n <= k) by nia.
      assert (H_k_16: 16 <= k) by lia.
      destruct (Nat.ltb k (n * n)) eqn:E_k.
      - apply Nat.ltb_lt in E_k.
        assert (Nat.log2 k <= 2 * Nat.log2 n + 1). {
          apply Nat.le_trans with (m := Nat.log2 (n * n)).
          - apply Nat.log2_le_mono; lia.
          - apply log2_square_upper_bound; lia.
        }
        assert (n * Nat.log2 k <= 2 * n * Nat.log2 n + n) by nia.
        assert (n * Nat.log2 n <= k + 3 * n + Nat.log2 n). {
          assert (7 <= Nat.log2 n - 3) by lia.
          remember (Nat.log2 n) as L.
          lia.
        }
        assert (Nat.log2 n <= n) by (apply log2_le; lia).
        assert (7 * n <= k + 7). {
          assert (7 <= Nat.log2 n - 3) by lia.
          assert (7 * (n - 1) <= (n - 1) * (Nat.log2 n - 3)). {
            rewrite Nat.mul_comm.
            now apply Nat.mul_le_mono_l.
          }
          lia.
        }
        lia.
      - apply Nat.ltb_ge in E_k.
        pose proof (log2_square_le k H_k_16).
        assert (Hsquare: (n * Nat.log2 k) ^ 2 <= (4 * k) ^ 2). {
          pose proof (square_le_mono (n * n) (Nat.log2 k * Nat.log2 k) (4 * k) ltac:(lia) ltac:(lia)).
          do 2 rewrite Nat.pow_2_r in *.
          lia.
        }
        apply Nat.pow_le_mono_l_iff in Hsquare.
        + assumption.
        + lia.
    Qed.

    Theorem final_bound: m * Nat.log2 k <= k * Nat.log2 k + 21 * k.
    Proof.
      pose proof algebraic_bound.
      pose proof bound_n.
      pose proof bound_log.
      nia.
    Qed.

    Theorem final_division_bound: m <= k + 21 * k / Nat.log2 k.
    Proof.
      pose proof final_bound.
      assert (Hlk: Nat.log2 k <> 0) by lia.
      pose proof (Nat.div_mod (21 * k) (Nat.log2 k) Hlk).
      pose proof (Nat.mod_upper_bound (21 * k) (Nat.log2 k) Hlk).
      nia.
    Qed.

  End AsymptoticBound.

  Theorem compress_to_bits_bound: forall s n k,
    n = length (compress s) ->
    10 <= Nat.log2 n ->
    k = length s ->
    12 <= Nat.log2 k ->
    length (compress_to_bits s) <= k + 21 * k / Nat.log2 k.
  Proof.
    intros * Hn Hngt Hk Hkgt.
    pose proof (compress_length_lower_bound s (compress s) ltac:(reflexivity)) as Hkn.
    unfold ">=" in Hkn.
    pose proof (tokens_to_bits_aux_length_bound (compress_aux (length s) empty_dict s) 1
                 (1 + length (compress_aux (length s) empty_dict s)) ltac:(lia)) as Hmn.
    unfold compress_to_bits, compress, tokens_to_bits, num_bits_for_dict in *.
    rewrite <- Hk in *.
    rewrite <- Hn in *.
    set (m := length (tokens_to_bits_aux 1 (compress_aux k empty_dict s))) in *.
    destruct (1 + n <=? 1) eqn:?.
    - apply leb_complete in Heqb.
      lia.
    - apply leb_complete_conv in Heqb.
      assert (Hn1: 1 <= n) by lia.
      assert (Hnk: (n - 1) * (Nat.log2 n - 3) <= k). {
        etransitivity.
        2: exact Hkn.
        apply Nat.mul_le_mono_l.
        pose proof (Nat.log2_succ_le (n - 1)) as Hlog.
        assert (Nat.log2 n <= Nat.log2 (n - 1) + 1). {
          assert (Hsm1: S (n - 1) = n) by lia.
          rewrite Hsm1 in Hlog.
          lia.
        }
        lia.
      }
      simpl in Hmn.
      rewrite Nat.sub_0_r in *.
      apply final_division_bound with (n := n); lia.
  Qed.

End Impl.

Export Impl.
