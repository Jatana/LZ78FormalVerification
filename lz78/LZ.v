From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import LZ_Dict LZ_Tokens.
Import ListNotations.

Module Impl.

  Fixpoint compress' (fuel: nat) (dict: dict_type) (s: list byte) :=
    match fuel with
    | 0 => []
    | S fuel =>
        match s with
        | [] => []
        | _ =>
            let (index, len) := find_largest_prefix dict s in
            match skipn len s with
            | [] => [Last index]
            | next :: rest =>
                Tok index next :: compress' fuel (dict ++ [firstn len s ++ [next]]) rest
            end
        end
    end.

  Definition compress (s: list byte) :=
    compress' (length s) empty_dict s.

  Definition compress_to_bytes (s: list byte) :=
    tokens_to_bytes (compress s).

  Fixpoint decompress' (dict: dict_type) (tokens: list Token) :=
    match tokens with
    | [] => []
    | Tok index next :: rest =>
        match nth_error dict index with
        | Some s => s ++ [next] ++ decompress' (dict ++ [s ++ [next]]) rest
        | None => [] (* Should not happen *)
        end
    | Last index :: rest =>
        match nth_error dict index with
        | Some s => s
        | None => [] (* Should not happen *)
        end
    end.

  Definition decompress (tokens: list Token) :=
    decompress' empty_dict tokens.

  Definition decompress_from_bytes (s: list byte) :=
    decompress (bytes_to_tokens s).


  Lemma compress_correctness': forall fuel dict s,
    length s <= fuel ->
    decompress' dict (compress' fuel dict s) = s.
  Proof. Admitted.

  Theorem compress_correctness: forall s,
    decompress_from_bytes (compress_to_bytes s) = s.
  Proof.
    intros.
    unfold compress_to_bytes, decompress_from_bytes.
    rewrite (tokens_to_bytes_correctness (compress s)).
    eapply compress_correctness'.
    lia.
  Qed.

End Impl.
