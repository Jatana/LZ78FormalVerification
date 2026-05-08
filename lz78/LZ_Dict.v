From Stdlib Require Import Arith Strings.Byte List Lia.
Import ListNotations.

Module Dict.

  Definition dict_type := list (list byte).
  Definition empty_dict: dict_type := [[]].

  Definition num_bytes_for_dict (dict_size: nat) :=
    if dict_size <=? 1 then 1
    else (Nat.log2 (dict_size - 1) / 8) + 1.

  Fixpoint prefix_eq (p s: list byte) :=
    match p, s with
    | [], _ => true
    | _, [] => false
    | ph :: pt, sh :: st => if Byte.eqb ph sh then prefix_eq pt st else false
    end.

  Fixpoint find_largest_prefix' (dict: dict_type) (s: list byte) (index best_index best_len: nat) :=
    match dict with
    | [] => (best_index, best_len)
    | d :: ds =>
        let l := length d in
        if andb (prefix_eq d s) (best_len <? l) then
          find_largest_prefix' ds s (S index) index l
        else find_largest_prefix' ds s (S index) best_index best_len
    end.

  Definition find_largest_prefix (dict: dict_type) (s: list byte) :=
    find_largest_prefix' dict s 0 0 0.


  Lemma prefix_eq_correctness: forall p s,
    prefix_eq p s = true <-> firstn (length p) s = p.
  Proof. Admitted.

  Lemma find_largest_prefix_correctness: forall dict s index len,
    find_largest_prefix dict s = (index, len) ->
    len <= length s /\ nth_error dict index = Some (firstn len s).
  Proof. Admitted.

End Dict.

Export Dict.
