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


  Lemma compress'_valid_tokens: forall fuel s dict,
    length s <= fuel ->
    valid_tokens (compress' fuel dict s).
  Proof.
    induction fuel, s; simpl; intros; try constructor.
    destruct (find_largest_prefix dict (b :: s)) as [index len].
    destruct (skipn len (b :: s)) eqn:?; simpl; try constructor.
    apply IHfuel.
    pose proof (length_skipn len (b :: s)) as Hls.
    rewrite Heql in Hls.
    simpl in Hls.
    destruct len; lia.
  Qed.

  Lemma compress_correctness': forall fuel dict s,
    length s <= fuel ->
    In [] dict ->
    decompress' dict (compress' fuel dict s) = s.
  Proof.
    induction fuel; simpl; intros dict s Hlen Hin.
    - inversion Hlen.
      now apply length_zero_iff_nil in H0.
    - destruct s; try reflexivity.
      destruct (find_largest_prefix dict (b :: s)) as [index len] eqn:?.
      pose proof (find_largest_prefix_correctness dict (b :: s) index len Heqp Hin) as [_ Hs].
      pose proof (firstn_skipn len (b :: s)) as Hfs.
      destruct (skipn len (b :: s)) eqn:?; simpl.
      + rewrite app_nil_r in Hfs.
        rewrite Hfs in Hs.
        now rewrite Hs.
      + rewrite <- Hfs, Hs, app_inv_head_iff.
        f_equal.
        assert (Hlf: length l <= fuel). {
          rewrite <- Hfs, length_app, length_cons in Hlen.
          lia.
        }
        assert (Hinapp: In [] (dict ++ [firstn len (b :: s) ++ [b0]])). {
          apply in_or_app.
          now left.
        }
        specialize (IHfuel (dict ++ [firstn len (b :: s) ++ [b0]]) l Hlf Hinapp).
        assert (Hd: dict ++ [firstn len (firstn len (b :: s) ++ b0 :: l) ++ [b0]] = 
                dict ++ [firstn len (b :: s) ++ [b0]]). {
         rewrite app_inv_head_iff.
         f_equal.
         now rewrite app_inv_tail_iff, Hfs.
        }
        now rewrite Hd.
  Qed.

  Theorem compress_correctness: forall s,
    decompress_from_bytes (compress_to_bytes s) = s.
  Proof.
    intros.
    unfold compress_to_bytes, decompress_from_bytes.
    rewrite (tokens_to_bytes_correctness (compress s)).
    - eapply compress_correctness'.
      + lia.
      + unfold empty_dict.
        simpl.
        now left.
    - apply compress'_valid_tokens.
      lia.
  Qed.

End Impl.
