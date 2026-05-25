From Stdlib Require Import Arith String Strings.Byte List Lia.
Require Import Utils LZ_Dict LZ_Tokens LZ.
Import ListNotations.

Module Example.

  Definition byte_to_bits (b: byte): list bool :=
    let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := to_bits b in
    [b0; b1; b2; b3; b4; b5; b6; b7].

  Definition bits_to_byte (bits : list bool) : byte :=
    match bits with
    | [b0; b1; b2; b3; b4; b5; b6; b7] =>
        of_bits (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7)))))))
    | _ => x00
    end.

  Fixpoint bits_to_bytes (bits : list bool) : list byte :=
    match bits with
    | [] => []
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
        bits_to_byte [b0; b1; b2; b3; b4; b5; b6; b7] :: bits_to_bytes rest
    | _ => [bits_to_byte (bits ++ repeat false (8 - length bits))]
    end.

  Definition green_eggs_and_ham: string :=
    "I am Sam\" ++
    "\" ++
    "Sam I am\" ++
    "\" ++
    "That Sam-I-am!\" ++
    "That Sam-I-am!\" ++
    "I do not like\" ++
    "that Sam-I-am!\" ++
    "\" ++
    "Do you like green eggs and ham?\" ++
    "\" ++
    "I do not like them, Sam-I-am.\" ++
    "I do not like green eggs and ham.\".

  Definition geah_bits :=
    concat (map byte_to_bits (list_byte_of_string green_eggs_and_ham)).

  Definition geah_tokens := compress geah_bits.
  Compute geah_tokens.

  Definition geah_compressed := compress_to_bits geah_bits.
  Compute geah_compressed.

  Definition geah_decompressed := decompress_from_bits geah_compressed.
  Compute string_of_list_byte (bits_to_bytes geah_decompressed).

  Goal geah_bits = geah_decompressed.
  Proof. reflexivity. Qed.

  Compute length geah_bits. (* 177 * 8 = 1416 *)
  Compute length geah_compressed. (* = 1752 *)

  Definition green_eggs_and_ham_repeated :=
    String.concat "" (repeat green_eggs_and_ham 16).

  Definition geahr_bits :=
    concat (map byte_to_bits (list_byte_of_string green_eggs_and_ham_repeated)).
  Compute length geahr_bits. (* 1416 * 16 = 22'656 *)

  Definition geahr_compressed := compress_to_bits geahr_bits.
  Compute length geahr_compressed. (* = 22'253 *)

End Example.
