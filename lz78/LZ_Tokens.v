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
    induction fuel; simpl; intros.
    - destruct tokens. reflexivity.
      inversion H.
      apply length_zero_iff_nil in H3.
      subst.
      destruct t; simpl in H3.
      + apply app_eq_nil in H3.
        destruct H3.
        discriminate.
      + pose proof (num_bits_for_dict_gt_one dict_size).
        destruct (num_bits_for_dict dict_size).
        * lia.
        * simpl in H3.
          discriminate.
    - destruct bits.
      + destruct tokens. reflexivity.
        destruct t; simpl in H1.
        * apply app_eq_nil in H1.
          destruct H1.
          discriminate.
        * pose proof (num_bits_for_dict_gt_one dict_size).
          destruct (num_bits_for_dict dict_size).
          -- lia.
          -- simpl in H1.
             discriminate.
      + destruct (length (b :: bits) <? num_bits_for_dict dict_size) eqn:?.
        * destruct tokens. reflexivity.
          simpl in H1.
          apply Nat.ltb_lt in Heqb0.
          destruct t.
          -- pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index).
             assert (length (nat_to_k_bits (num_bits_for_dict dict_size) index)
                      <= length (b :: bits)). {
               rewrite <- H1, length_app.
               lia.
             }
             lia.
          -- pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index).
             rewrite H1 in H2.
             lia.
        * destruct (length (b :: bits) =? num_bits_for_dict dict_size) eqn:?.
          -- destruct tokens; simpl in H1.
             ++ discriminate.
             ++ destruct t.
                ** apply Nat.eqb_eq in Heqb1.
                   rewrite <- H1, length_app, nat_to_k_bits_length in Heqb1.
                   simpl in Heqb1. lia.
                ** destruct tokens.
                   --- rewrite <- H1, nat_to_k_bits_correctness.
                       +++ simpl. unfold token_equiv. auto.
                       +++ now simpl in H0.
                   --- simpl in H0. now exfalso.
          -- destruct (skipn (num_bits_for_dict dict_size) (b :: bits)) eqn:?.
             ++ apply Nat.ltb_ge in Heqb0.
                apply Nat.eqb_neq in Heqb1.
                apply skipn_all_iff in Heql.
                lia.
             ++ destruct tokens; simpl in H1.
                ** discriminate.
                ** destruct t.
                   --- f_equal.
                       +++ pose proof (firstn_skipn (num_bits_for_dict dict_size) (b :: bits)).
                           rewrite Heql in H2.
                           rewrite <- H2 in H1.
                           assert (firstn (num_bits_for_dict dict_size) (b :: bits)
                                   = nat_to_k_bits (num_bits_for_dict dict_size) index). {
                             pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index).
                             eapply app_l_eq_length in H1.
                             - congruence.
                             - rewrite H3.
                               reflexivity.
                             - rewrite length_firstn.
                               apply Nat.ltb_ge in Heqb0.
                               apply Nat.eqb_neq in Heqb1.
                               assert (Nat.min (num_bits_for_dict dict_size) (length (b :: bits))
                                       = num_bits_for_dict dict_size) by lia.
                               now rewrite H4.
                           }
                           rewrite H3 in H1 |- *.
                           rewrite nat_to_k_bits_correctness.
                           *** f_equal. 
                               apply app_inv_head in H1.
                               simpl. split. 
                                ---- unfold token_equiv. split.
                                  **** reflexivity.
                                  **** congruence.
                                ---- simpl.
                                     apply IHfuel.
                                     ++++ pose proof (length_skipn (num_bits_for_dict dict_size) (b :: bits)).
                                          rewrite Heql in H4.
                                          simpl in H4, H.
                                          destruct (num_bits_for_dict dict_size); lia.
                                     ++++ simpl in H0.
                                          now destruct H0.
                                     ++++ congruence.
                           *** simpl in H0.
                               now destruct H0.
                   --- pose proof (nat_to_k_bits_length (num_bits_for_dict dict_size) index).
                       rewrite H1 in H2.
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
