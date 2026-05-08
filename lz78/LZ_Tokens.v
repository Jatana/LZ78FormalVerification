From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import LZ_Dict.
Import ListNotations.

Module Tokens.

  Inductive Token :=
    | Tok (index: nat) (next: byte)
    | Last (index: nat).

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

  Lemma nat_to_k_bytes_correctness: forall k n,
    n < 256 ^ k ->
    k_bytes_to_nat (nat_to_k_bytes k n) = n.
  Proof. Admitted.

  Lemma tokens_to_bytes_correctness': forall fuel dict_size tokens bytes,
    length bytes <= fuel ->
    tokens_to_bytes' dict_size tokens = bytes ->
    bytes_to_tokens' fuel dict_size bytes = tokens.
  Proof. Admitted.

  Lemma tokens_to_bytes_correctness: forall tokens,
    bytes_to_tokens (tokens_to_bytes tokens) = tokens.
  Proof.
    intros.
    eapply tokens_to_bytes_correctness'.
    - lia.
    - reflexivity.
  Qed.

End Tokens.

Export Tokens.
