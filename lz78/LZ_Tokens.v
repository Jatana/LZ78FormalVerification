From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Dict.
Import ListNotations.

Module Tokens.

  Inductive Token :=
    | Tok (index: nat) (next: byte)
    | Last (index: nat).

  Fixpoint valid_tokens (tokens: list Token) (dict_size: nat) :=
    match tokens with
    | Tok index _ :: rest => index < 256 ^ (num_bytes_for_dict dict_size)
                               /\ valid_tokens rest (S dict_size)
    | Last _ :: _ :: _ => False
    | [Last index] => index < 256 ^ (num_bytes_for_dict dict_size) 
    | [] => True
    end.

  Definition nat_to_byte (n: nat): byte :=
    match of_nat (n mod 256) with
    | Some b => b
    | None => x00 (* Never happens *)
    end.

  Fixpoint nat_to_k_bytes (k n: nat) :=
    match k with
    | 0 => []
    | S k => nat_to_byte (n mod 256) :: nat_to_k_bytes k (n / 256)
    end.

  Fixpoint k_bytes_to_nat (bytes: list byte) :=
    match bytes with
    | [] => 0
    | b :: rest => to_nat b + 256 * k_bytes_to_nat rest
    end.

  Fixpoint tokens_to_bytes' (dict_size: nat) (tokens: list Token) :=
    match tokens with
    | [] => []
    | Tok index next :: rest =>
        nat_to_k_bytes (num_bytes_for_dict dict_size) index ++ [next] ++
        tokens_to_bytes' (S dict_size) rest
    | Last index :: _ =>
        nat_to_k_bytes (num_bytes_for_dict dict_size) index
    end.

  Definition tokens_to_bytes (tokens: list Token) :=
    tokens_to_bytes' 1 tokens.

  Fixpoint bytes_to_tokens' (fuel dict_size: nat) (bytes: list byte) :=
    match fuel, bytes with
    | 0, _ => []
    | _, [] => []
    | S fuel, _ =>
        let k := num_bytes_for_dict dict_size in
        if length bytes <? k then []
        else if length bytes =? k then [Last (k_bytes_to_nat bytes)]
        else
          let index_bytes := firstn k bytes in
          match skipn k bytes with
          | [] => [Last (k_bytes_to_nat index_bytes)]
          | next :: rest =>
              Tok (k_bytes_to_nat index_bytes) next :: bytes_to_tokens' fuel (S dict_size) rest
          end
    end.

  Definition bytes_to_tokens (bytes: list byte) :=
    bytes_to_tokens' (length bytes) 1 bytes.


  Lemma nat_to_byte_correctness: forall n,
    n < 256 ->
    to_nat (nat_to_byte n) = n.
  Proof.
    unfold nat_to_byte.
    intros.
    destruct (of_nat (_ mod 256)) eqn:Heqo.
    - apply to_of_nat_iff.
      rewrite (Nat.mod_small n 256 ltac:(lia)) in Heqo.
      assumption.
    - exfalso.
      apply of_nat_None_iff in Heqo.
      pose proof (Nat.mod_upper_bound n 256 ltac:(lia)).
      lia.
  Qed.

  Arguments Nat.modulo : simpl never.
  Arguments Nat.divmod : simpl never.
  Arguments Nat.pow : simpl never.
  Arguments Nat.div : simpl never.
  Arguments Nat.mul : simpl never.

  Lemma nat_to_k_bytes_correctness: forall k n,
    n < 256 ^ k ->
    k_bytes_to_nat (nat_to_k_bytes k n) = n.
  Proof.
    induction k; simpl; intros n Hnlt.
    - rewrite Nat.pow_0_r in Hnlt.
      lia.
    - rewrite IHk.
      + rewrite nat_to_byte_correctness.
        * pose proof (Nat.div_mod_eq n 256).
          lia.
        * apply Nat.mod_upper_bound.
          lia.
      + rewrite Nat.pow_succ_r in Hnlt by lia.
        apply Nat.Div0.div_lt_upper_bound.
        lia.
  Qed.

  Lemma nat_to_k_bytes_length: forall k n,
    length (nat_to_k_bytes k n) = k.
  Proof.
    induction k; simpl; intros.
    - reflexivity.
    - now rewrite IHk.
  Qed.

  Lemma tokens_to_bytes_correctness': forall fuel tokens dict_size bytes,
    length bytes <= fuel ->
    valid_tokens tokens dict_size ->
    tokens_to_bytes' dict_size tokens = bytes ->
    bytes_to_tokens' fuel dict_size bytes = tokens.
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
      + pose proof (num_bytes_for_dict_gt_one dict_size).
        destruct (num_bytes_for_dict dict_size).
        * lia.
        * simpl in Hlen.
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
        * pose proof (num_bytes_for_dict_gt_one dict_size).
          destruct (num_bytes_for_dict dict_size).
          -- lia.
          -- simpl in Htb.
             discriminate.
      + destruct tokens. reflexivity.
        simpl in Htb.
        apply Nat.ltb_lt in Heqb0.
        destruct t.
        * pose proof (nat_to_k_bytes_length (num_bytes_for_dict dict_size) index).
          assert (length (nat_to_k_bytes (num_bytes_for_dict dict_size) index)
                   <= length (b :: l)). {
            rewrite <- Htb, length_app.
            lia.
          }
          lia.
        * pose proof (nat_to_k_bytes_length (num_bytes_for_dict dict_size) index) as Hdlen.
          rewrite Htb in Hdlen.
          lia.
      + destruct tokens; simpl in Htb.
        * discriminate.
        * destruct t.
          -- apply Nat.eqb_eq in Heqb1.
             rewrite <- Htb, length_app, nat_to_k_bytes_length in Heqb1.
             simpl in Heqb1. lia.
          -- destruct tokens.
             ++ rewrite <- Htb, nat_to_k_bytes_correctness.
                ** reflexivity.
                ** now simpl in Hlen.
             ++ simpl in Hlen. now exfalso.
      + apply Nat.ltb_ge in Heqb0.
        apply Nat.eqb_neq in Heqb1.
        apply skipn_all_iff in Heql0.
        lia.
      + destruct tokens; simpl in Htb.
        * discriminate.
        * destruct t.
          -- f_equal.
             ++ pose proof (firstn_skipn (num_bytes_for_dict dict_size) (b :: l)) as Hfsn.
                rewrite Heql0 in Hfsn.
                rewrite <- Hfsn in Htb.
                assert (Hf: firstn (num_bytes_for_dict dict_size) (b :: l)
                             = nat_to_k_bytes (num_bytes_for_dict dict_size) index). {
                  pose proof (nat_to_k_bytes_length (num_bytes_for_dict dict_size) index) as Hdlen.
                  eapply app_l_eq_length in Htb.
                  - congruence.
                  - rewrite Hdlen.
                    reflexivity.
                  - rewrite length_firstn.
                    apply Nat.ltb_ge in Heqb0.
                    apply Nat.eqb_neq in Heqb1.
                    assert (Hmin: Nat.min (num_bytes_for_dict dict_size) (length (b :: l))
                                   = num_bytes_for_dict dict_size) by lia.
                    now rewrite Hmin.
                }
                rewrite Hf in Htb |- *.
                rewrite nat_to_k_bytes_correctness.
                ** f_equal.
                   apply app_inv_head in Htb.
                   congruence.
                ** simpl in Hvt.
                   now destruct Hvt.
             ++ erewrite IHfuel.
                ** reflexivity.
                ** pose proof (length_skipn (num_bytes_for_dict dict_size) (b :: l)) as Hls.
                   rewrite Heql0 in Hls.
                   simpl in *.
                   destruct (num_bytes_for_dict dict_size); lia.
                ** simpl in Hvt.
                   now destruct Hvt.
                ** rewrite <- Htb in Heql0.
                   pose proof (nat_to_k_bytes_length (num_bytes_for_dict dict_size) index) as Hdlen.
                   rewrite <- Hdlen in Heql0 at 1.
                   rewrite skipn_app, Nat.sub_diag, skipn_all, skipn_0 in Heql0.
                   simpl in Heql0.
                   congruence.
          -- pose proof (nat_to_k_bytes_length (num_bytes_for_dict dict_size) index) as Hdlen.
             rewrite Htb in Hdlen.
             apply Nat.eqb_neq in Heqb1.
             lia.
  Qed.

  Lemma tokens_to_bytes_correctness: forall tokens,
    valid_tokens tokens 1 ->
    bytes_to_tokens (tokens_to_bytes tokens) = tokens.
  Proof.
    intros.
    eapply tokens_to_bytes_correctness'.
    - lia.
    - assumption.
    - reflexivity.
  Qed.
  
  Lemma length_nat_to_k_bytes :
    forall k n,
      length (nat_to_k_bytes k n) = k.
  Proof.
    induction k; simpl; intros; auto.
  Qed.

End Tokens.

Export Tokens.
