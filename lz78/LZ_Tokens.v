From Stdlib Require Import Arith Strings.Byte List Lia BinPos.
Require Import Utils.
Require Import LZ_Dict.
Import ListNotations.

Module Tokens.

  Inductive Token :=
    | Tok (index: nat) (phr : list bool) (next: bool)
    | Last (index: nat) (phr : list bool).

  Fixpoint valid_tokens (tokens: list Token) (dict_size: nat) :=
    match tokens with
    | Tok index _ _ :: rest => index < 2 ^ (num_bits_for_dict dict_size)
                               /\ valid_tokens rest (S dict_size)
    | Last _ _ :: _ :: _  => False
    | [Last index _] => index < 2 ^ (num_bits_for_dict dict_size)
    | [] => True
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

  Fixpoint nat_to_k_bits (k n : nat) : list bool :=
    match k with
      | 0 => []
      | S t => (if (n mod 2) =? 0 then false else true) :: nat_to_k_bits t (n / 2)
    end.

  Definition to_nat (b : bool) : nat :=
    match b with
      | true => 1
      | false => 0
    end.

  Fixpoint k_bits_to_nat (bits: list bool) :=
    match bits with
    | [] => 0
    | b :: rest => to_nat b + 2 * k_bits_to_nat rest
    end.

  Fixpoint tokens_to_bits' (dict_size: nat) (tokens: list Token) :=
    match tokens with
    | [] => []
    | Tok index phr next :: rest =>
        nat_to_k_bits (num_bits_for_dict dict_size) index ++ [next] ++
        tokens_to_bits' (S dict_size) rest
    | Last index _ :: _ =>
        nat_to_k_bits (num_bits_for_dict dict_size) index
    end.

  Definition tokens_to_bits (tokens: list Token) :=
    tokens_to_bits' 1 tokens.

  Fixpoint bits_to_tokens' (fuel dict_size: nat) (bits: list bool) : list Token :=
    match fuel, bits with
    | 0, _ => []
    | _, [] => []
    | S fuel, _ =>
        let k := num_bits_for_dict dict_size in
        if length bits <? k then []
        else if length bits =? k then [Last (k_bits_to_nat bits) []]
        else
          let index_bits := firstn k bits in
          match skipn k bits with
          | [] => [Last (k_bits_to_nat index_bits) []]
          | next :: rest =>
              Tok (k_bits_to_nat index_bits) [] next :: (bits_to_tokens' fuel (S dict_size) rest)
          end
    end.

  Definition bits_to_tokens (bits: list bool) :=
    bits_to_tokens' (length bits) 1 bits.


  Lemma agreement_app : forall dict tokens phr next n,
    agreement dict tokens ->
    agreement (dict ++ [phr ++ [next]]) (tokens ++ [Tok n phr next]).
  Proof.
    unfold agreement.
    intros.
    apply in_or_app.
    specialize (in_app_or _ _ _ H0) as Hcase.
    destruct Hcase as [H1 | H2]; [left | right].
    - eauto.
    - inversion H2; inversion H1.
      subst.
      do 2 constructor.
  Qed.

  Lemma nat_to_bit_correctness: forall n,
    n < 2 ->
    to_nat (if n =? 0 then false else true) = n.
  Proof.
    intros.
    do 2 (destruct n; try reflexivity).
    lia.
  Qed.

  Arguments Nat.modulo : simpl never.
  Arguments Nat.divmod : simpl never.
  Arguments Nat.pow : simpl never.
  Arguments Nat.div : simpl never.
  Arguments Nat.mul : simpl never.

  Lemma nat_to_k_bits_correctness: forall k n,
    n < 2 ^ k ->
    k_bits_to_nat (nat_to_k_bits k n) = n.
  Proof.
    induction k; simpl; intros n Hnlt.
    - rewrite Nat.pow_0_r in Hnlt.
      lia.
    - rewrite IHk.
      + rewrite nat_to_bit_correctness with (n := n mod 2).
        * pose proof (Nat.div_mod_eq n 2).
          lia.
        * apply Nat.mod_upper_bound.
          lia.
      + rewrite Nat.pow_succ_r in Hnlt by lia.
        apply Nat.Div0.div_lt_upper_bound.
        lia.
  Qed.

  Lemma nat_to_k_bits_length: forall k n,
    length (nat_to_k_bits k n) = k.
  Proof.
    induction k; simpl; intros.
    - reflexivity.
    - now rewrite IHk.
  Qed.

  Definition token_equiv (t1 t2 : Token) :=
    match (t1, t2) with
      | (Tok _ _ _, Last _ _) => False
      | (Last _ _, Tok _ _ _) => False
      | (Tok ind1 _ next1, Tok ind2 _ next2) => ind1 = ind2 /\ next1 = next2
      | (Last ind1 _, Last ind2 _) => ind1 = ind2
    end.

  Fixpoint list_eq {A : Type} (eqb : A -> A -> Prop) (s t : list A) : Prop :=
    match (s, t) with
    | (cons s1 s2, cons t1 t2) => (eqb s1 t1) /\ (list_eq eqb s2 t2)
    | (nil, nil) => True
    | _ => False
    end.

  Lemma tokens_to_bits_correctness': forall fuel tokens dict_size bits,
    length bits <= fuel ->
    valid_tokens tokens dict_size ->
    tokens_to_bits' dict_size tokens = bits ->
    list_eq token_equiv (bits_to_tokens' fuel dict_size bits) (tokens).
  Proof.
    induction fuel; simpl; intros * Hlen Hvt Htb.
    - destruct tokens. reflexivity.
      inversion Hlen.
      apply length_zero_iff_nil in H0.
      subst.
      destruct t; simpl in H0.
      + apply app_eq_nil in H0.
        destruct H0.
        discriminate.
      + pose proof (num_bits_for_dict_gt_one dict_size).
        destruct (num_bits_for_dict dict_size).
        * lia.
        * simpl in H0.
          discriminate.
    - repeat match goal with
             | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
             | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
             end; subst.
      + destruct tokens. reflexivity.
        destruct t; simpl in Htb.
        * apply app_eq_nil in Htb.
          destruct Htb.
          discriminate.
        * pose proof (num_bits_for_dict_gt_one dict_size).
          destruct (num_bits_for_dict dict_size).
          -- lia.
          -- simpl in Htb.
             discriminate.
      + destruct tokens. reflexivity.
        simpl in Htb.
        apply Nat.ltb_lt in Heqb0.
        destruct t.
        * pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index).
          assert (length (nat_to_k_bits (num_bits_for_dict dict_size) index)
                   <= length (b :: l)). {
               rewrite <- Htb, length_app.
               lia.
             }
             lia.
        * pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index) as Hdlen.
          rewrite Htb in Hdlen.
          lia.
      + destruct tokens; simpl in Htb.
        * discriminate.
        * destruct t.
          -- apply Nat.eqb_eq in Heqb1.
             rewrite <- Htb, length_app, nat_to_k_bits_length in Heqb1.
             simpl in Heqb1. lia.
          -- unfold token_equiv.
             destruct tokens.
             ++ rewrite <- Htb, nat_to_k_bits_correctness; simpl in *; auto.
             ++ now exfalso.
      + apply Nat.ltb_ge in Heqb0.
        apply Nat.eqb_neq in Heqb1.
        apply skipn_all_iff in Heql0.
        lia.
      + destruct tokens; simpl in Htb.
        * discriminate.
        * destruct t.
          -- f_equal.
             ++ pose proof (firstn_skipn (num_bits_for_dict dict_size) (b :: l)) as Hfsn.
                rewrite Heql0 in Hfsn.
                rewrite <- Hfsn in Htb.
                assert (Hf: firstn (num_bits_for_dict dict_size) (b :: l)
                            = nat_to_k_bits (num_bits_for_dict dict_size) index). {
                  pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index) as Hdlen.
                  eapply app_l_eq_length in Htb.
                  - congruence.
                  - rewrite Hdlen.
                    reflexivity.
                  - rewrite length_firstn.
                    apply Nat.ltb_ge in Heqb0.
                    apply Nat.eqb_neq in Heqb1.
                    assert (Hmin: Nat.min (num_bits_for_dict dict_size) (length (b :: l))
                                   = num_bits_for_dict dict_size) by lia.
                    now rewrite Hmin.
                }
                rewrite Hf in Htb |- *.
                rewrite nat_to_k_bits_correctness.
                ** f_equal.
                   apply app_inv_head in Htb.
                   split.
                   --- unfold token_equiv.
                       split; [reflexivity | congruence].
                   --- apply IHfuel.
                       +++ pose proof (length_skipn (num_bits_for_dict dict_size) (b :: l)) as Hls.
                           rewrite Heql0 in Hls.
                           simpl in *.
                           destruct (num_bits_for_dict dict_size); lia.
                       +++ simpl in Hvt.
                           now destruct Hvt.
                       +++ congruence.
                ** simpl in Hvt.
                   now destruct Hvt.
          -- pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index) as Hdlen.
             rewrite Htb in Hdlen.
             apply Nat.eqb_neq in Heqb1.
             lia.
  Qed.

  Lemma tokens_to_bits_correctness: forall tokens,
    valid_tokens tokens 1 ->
    list_eq token_equiv (bits_to_tokens (tokens_to_bits tokens)) tokens.
  Proof.
    intros.
    eapply tokens_to_bits_correctness'.
    - lia.
    - assumption.
    - reflexivity.
  Qed.

  Lemma length_nat_to_k_bits :
    forall k n,
      length (nat_to_k_bits k n) = k.
  Proof.
    induction k; simpl; intros; auto.
  Qed.

End Tokens.

Export Tokens.
