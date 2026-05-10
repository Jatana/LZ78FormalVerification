From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import LZ_Dict.
Import ListNotations.

Module Tokens.

  Inductive Token :=
    | Tok (index: nat) (next: byte)
    | Last (index: nat).

  Fixpoint valid_tokens (tokens: list Token) :=
    match tokens with
    | Tok _ _ :: rest => valid_tokens rest
    | Last _ :: _ :: _ => False
    | _ => True
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
    destruct (of_nat (_ mod 256)) eqn:?.
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

  (* The Hypothesis are not strong enough! *)
  Lemma tokens_to_bytes_correctness': forall fuel tokens dict_size bytes,
    length bytes <= fuel ->
    valid_tokens tokens ->
    tokens_to_bytes' dict_size tokens = bytes ->
    bytes_to_tokens' fuel dict_size bytes = tokens.
  Proof.
  Admitted.

  Lemma tokens_to_bytes_correctness: forall tokens,
    valid_tokens tokens ->
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
