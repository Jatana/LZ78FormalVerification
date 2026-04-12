From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Matching LZ_Tokens.
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

  Fixpoint decompress (l : list Token) : list byte := nil. 

  Theorem correctness: forall s,
    decompress (compress s) = s.
  Proof.
  Admitted.

  Theorem upperbound: forall s,
    length (compress s) <= 9 * length s / 8 + 8 * Nat.log2 (length s) / 7.
  Proof.
  Admitted.

End Impl.
