From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import Utils LZ_Tokens LZ_Matching.
Import ListNotations.

Module Expand.

  Definition nth_byte (l : list byte) (n : nat) : byte :=
    nth n l x00.

  Fixpoint expand_ref (acc : list byte) (len off : nat) : list byte :=
    match len with
    | 0 => acc
    | S len' =>
        let b := nth_byte acc (length acc - off) in
        expand_ref (acc ++ [b]) len' off
    end.

  Lemma expand_ref_length :
    forall acc len off,
      length (expand_ref acc len off) = length acc + len.
  Proof.
    intros acc len. revert acc.
    induction len; intros.
    - simpl. lia.
    - simpl. rewrite IHlen.
      rewrite length_app.
      simpl. lia.
  Qed.

  Lemma expand_ref_preserves_prefix_length :
    forall acc len off,
      off <= length acc ->
      length acc <= length (expand_ref acc len off).
  Proof.
    intros.
    rewrite expand_ref_length.
    lia.
  Qed.

End Expand.
Export Expand.

Section Tests.
  Definition zero := "0"%byte.
  Definition one := "1"%byte.
    
  Example nth_byte_test0 :
    nth_byte [zero; one] 0 = zero.
  Proof. reflexivity. Qed.

  Example nth_byte_test1 :
    nth_byte [zero; one] 1 = one.
  Proof. reflexivity. Qed.

  Example nth_byte_default_test :
    nth_byte [zero; one] 5 = x00.
  Proof. reflexivity. Qed.

  Example expand_ref_len0_test :
    expand_ref [zero; one] 0 1 = [zero; one].
  Proof. reflexivity. Qed.

  Example expand_ref_one_byte_test :
    expand_ref [zero; one] 1 1 = [zero; one; one].
  Proof. reflexivity. Qed.

  Example expand_ref_nonoverlap_test :
    expand_ref [zero; one; one; zero; one] 4 5 =
      [zero; one; one; zero; one; zero; one; one; zero].
  Proof. reflexivity. Qed.

  Example expand_ref_overlap_test :
    expand_ref [zero; one] 4 2 =
      [zero; one; zero; one; zero; one].
  Proof. reflexivity. Qed.

End Tests.
