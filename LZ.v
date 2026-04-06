(* Require Import LZ78Signature. *)
From Stdlib Require Import Arith String Ascii List.
Import ListNotations.

Module Impl.
  Definition char_to_string (c : ascii) : string :=
    String c EmptyString.

  Inductive Token :=
  | Literal (c : ascii)
  | BackRef (start : nat) (length : nat)
  .

  Fixpoint tokens_to_bytes (l : list Token) : list ascii := nil.

  Fixpoint bytes_to_tokens (l : list ascii) : list Token := nil.

  Fixpoint find_largest_match (bef : string) (aft : string) : option (nat * nat) := None.
  (* returns 18 >= c >= 3, l where we need to go back c symbols back and l is the length  *)


(* abcdeabcdeffg *)
  Fixpoint compress (bef aft : string) (l : nat) : list Token :=
    match l with
    | 0 => 
        match (find_largest_match bef aft) with 
        | None => match aft with
                | String hd tl => (Literal hd) :: compress (bef ++ char_to_string hd)%string tl 0
                | EmptyString => nil
            end
        | Some (st, len) => match aft with
                | String hd tl => (BackRef st len) :: (compress (bef ++ char_to_string hd)%string tl (len - 1))
                | EmptyString => nil
            end
        end
    | S x =>
        match aft with 
            | EmptyString => nil
            | String hd tl => compress ((bef ++ char_to_string hd)%string) tl (x)
        end
    end.

  Fixpoint decompress (l : list Token) : string := EmptyString. 

  Theorem correctness (s : string) : decompress (compress EmptyString s 0) = s.
  Proof.  Admitted.

  Definition compress (s : string) : compressed :=
    compress_with_dictionary s EmptyString None nil nil 1.

  Example compress_ok :
  compress "aab"%string = [(None, "a"%char) ; (Some 1, "b"%char)].
  Proof.
    reflexivity.
  Qed.

End Impl.