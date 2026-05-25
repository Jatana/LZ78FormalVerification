From Stdlib Require Import Arith String Strings.Byte List Lia.
Require Import Utils LZ_Matching LZ_Tokens LZ.
Import ListNotations.

Module Example.

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

  Definition geah_bytes := list_byte_of_string green_eggs_and_ham.

  Definition geah_tokens := compress geah_bytes.
  Compute geah_tokens.

  Definition geah_compressed := compress_to_bytes geah_bytes.
  Compute geah_compressed.

  Definition geah_decompressed := decompress_from_bytes geah_compressed.
  Compute string_of_list_byte geah_decompressed.

  Compute list_eqb eqb geah_bytes geah_decompressed.

  Compute length geah_bytes.
  Compute length geah_compressed. (* 2 + 11 + 96 (Wikipedia says 95 which is wrong!) *)

End Example.
