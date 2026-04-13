From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Matching LZ_Tokens LZ_Expand.
Import ListNotations.

Module Impl.

  Fixpoint compress' (before after: list byte) (l: nat): list Token :=
    match after, l with
    | [], _ => []
    | hd :: tl, 0 => 
        match (find_largest_match before after) with 
        | None => Lit hd :: compress' (before ++ [hd]) tl 0
        | Some (length, offset) => Ref length offset :: compress' (before ++ [hd]) tl (length - 1)
        end
    | hd :: tl, S x => compress' (before ++ [hd]) tl x
    end.

  (* We need to add the length of s as a prefix here. *)
  Definition compress (s: list byte): list Token :=
    compress' [] s 0.

  Fixpoint decompress' (acc : list byte) (l : list Token) : list byte :=
    match l with
    | [] => acc
    | Lit b :: tl => decompress' (acc ++ [b]) tl
    | Ref len off :: tl => decompress' (expand_ref acc len off) tl
    end.

  Definition decompress (l : list Token) : list byte :=
    decompress' [] l.
  
  Theorem correctness: forall s,
    decompress (compress s) = s.
  Proof.
  Admitted.

  Theorem upperbound: forall s,
    length (compress s) <= 9 * length s / 8 + 8 * Nat.log2 (length s) / 7.
  Proof.
  Admitted.

End Impl.

Section Tests.
  Import Impl.

  Definition empty : list byte := [].
  Definition literals : list byte := ["010"%byte; "011"%byte].
  Definition compressed_literals : list Token := [Lit "010"%byte; Lit "011"%byte].
  Definition repeating : list byte := [zero; one; one; zero; one; zero; one; one; zero].
  Definition overlapping : list byte := [zero; one; zero; one; zero; one].
  Definition compressed_repeating : list Token := [Lit zero; Lit one; Lit one; Lit zero; Lit one; Ref 4 5].
  Definition compressed_overlapping : list Token := [Lit zero; Lit one; Ref 4 2].
  
  Example compress_empty_test :
    compress empty = [].
  Proof. reflexivity. Qed.
  
  Example decompress_empty_test :
    decompress [] = empty.
  Proof. reflexivity. Qed.
  
  Example compress_literals_test :
    compress literals = compressed_literals.
  Proof. reflexivity. Qed.
  
  Example decompress_literals_test :
    decompress compressed_literals = literals.
  Proof. reflexivity. Qed.
  
  Example compress_repetition_test :
    compress repeating = compressed_repeating.
  Proof. reflexivity. Qed.
  
  Example decompress_overlap_test :
    decompress compressed_overlapping = overlapping.
  Proof. reflexivity. Qed.
  
  Example correctness_empty :
    decompress (compress empty) = empty.
  Proof. reflexivity. Qed.
  
  Example correctness_simple :
    decompress (compress [zero]) = [zero].
  Proof. reflexivity. Qed.
  
  Example correctness_repeating :
    decompress (compress repeating) = repeating.
  Proof. reflexivity. Qed.
  
  Example correctness_overlapping :
    decompress (compress overlapping) = overlapping.
  Proof. reflexivity. Qed.

End Tests.
