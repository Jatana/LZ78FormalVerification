Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import LZC.
Require Import LZ LZ_Matching LZ_Tokens Utils.
Require Import Stdlib.Strings.Byte.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* Adapted from: https://github.com/PrincetonUniversity/VST/blob/master/progs/verif_queue.v *)
Definition surely_malloc_spec :=
  DECLARE _surely_malloc
    WITH t:type, gv: globals
    PRE [ tulong ]
      PROP (0 <= sizeof t <= Int64.max_unsigned;
            complete_legal_cosu_type t = true;
            natural_aligned natural_alignment t = true)
      PARAMS (Vlong (Int64.repr (sizeof t))) GLOBALS (gv)
      SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
      PROP ()
      RETURN (p)
      SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).


Definition bytes_to_vals (bs : list byte) : list val :=
  map Vbyte (map Byte.repr (map Z.of_nat (map to_nat bs))).

Definition encode_length_spec :=
  DECLARE _encode_length
    WITH sh: share, len: Z, out_: val, out: list val, out_len: Z, gv: globals
    PRE [ tulong, tptr tuchar ]
      PROP (writable_share sh; 0 <= len <= Int64.max_unsigned; isptr out_;
            Zlength (nat_to_bytes (Z.to_nat len)) <= out_len; 0 <= out_len)
      PARAMS (Vlong (Int64.repr len); out_) GLOBALS (gv)
      SEP (mem_mgr gv)
    POST [ tulong ] EX idx: Z,
      PROP (idx = Zlength (nat_to_bytes (Z.to_nat len)))
      RETURN (Vlong (Int64.repr idx))
      SEP (mem_mgr gv;
           data_at sh (tarray tuchar idx) (bytes_to_vals (nat_to_bytes (Z.to_nat len))) out_).

Definition decode_length_spec :=
  DECLARE _decode_length
    WITH sh_in: share, in_: val, in_bytes: list byte, in_len: Z,
         sh_out: share, out_: val, gv: globals
    PRE [ tptr tuchar, tulong, tptr tulong ]
      PROP (readable_share sh_in; writable_share sh_out;
            0 <= in_len <= 9; (* HERE IS THE ASSUMPTION. *)
            in_len = Zlength in_bytes)
      PARAMS (in_; Vlong (Int64.repr in_len); out_) GLOBALS (gv)
      SEP (mem_mgr gv;
           data_at sh_in (tarray tuchar in_len) (bytes_to_vals in_bytes) in_;
           data_at sh_out tulong (Vlong Int64.zero) out_)
    POST [ tulong ] EX idx: Z,
      PROP (idx = Zlength (nat_to_bytes (fst (bytes_to_nat in_bytes))); 0 <= idx <= in_len)
      RETURN (Vlong (Int64.repr idx))
      SEP (mem_mgr gv;
           data_at sh_out tulong (Vlong (Int64.repr (Z.of_nat (fst (bytes_to_nat in_bytes))))) out_).


Definition find_largest_match_spec :=
  DECLARE _find_largest_match
    WITH sh: share, in_: val, in_bytes: list byte, in_len: Z,
         p: Z, len_: val, off_: val, gv: globals
    PRE [ tptr tuchar, tulong, tulong, tptr tulong, tptr tulong ]
      PROP (readable_share sh;
            0 <= p <= in_len;
            in_len = Zlength in_bytes;
            in_len <= Int64.max_unsigned)
      PARAMS (in_; Vlong (Int64.repr in_len); Vlong (Int64.repr p); len_; off_) GLOBALS (gv)
      SEP (mem_mgr gv; data_at sh (tarray tuchar in_len) (bytes_to_vals in_bytes) in_)
    POST [ tvoid ]
      let result := find_largest_match (slice 0 (Z.to_nat p) in_bytes)
                                       (slice (Z.to_nat p) (length in_bytes) in_bytes) in
      PROP () RETURN ()
      SEP (mem_mgr gv;
           data_at Ews tulong
             (Vlong (Int64.repr (Z.of_nat
               (match result with
                | Some (len, _) => len
                | None => 0
                end)))) len_;
           data_at Ews tulong
             (Vlong (Int64.repr (Z.of_nat
               (match result with
                | Some (_, off) => off
                | None => 0
                end)))) off_).


Definition compress_out_size (in_len : Z) : Z :=
  (9 * in_len + 7) / 8 + 65.

Definition compress_spec :=
  DECLARE _compress
    WITH sh: share, in_: val, in_bytes: list byte, in_len: Z, gv: globals
    PRE [ tptr tuchar, tulong ]
      PROP (readable_share sh;
            0 <= in_len <= Int64.max_unsigned;
            in_len = Zlength in_bytes)
      PARAMS (in_; Vlong (Int64.repr in_len)) GLOBALS (gv)
      SEP (mem_mgr gv; data_at sh (tarray tuchar in_len) (bytes_to_vals in_bytes) in_)
    POST [ tptr tuchar ] EX p: val,
      let out_bytes := compress_to_bytes in_bytes in
      PROP (Zlength out_bytes <= compress_out_size in_len)
      RETURN (p)
      SEP (mem_mgr gv;
           malloc_token Ews (tarray tuchar (compress_out_size in_len)) p *
           data_at Ews (tarray tuchar (Zlength out_bytes)) (bytes_to_vals out_bytes) p).

Definition decompress_spec :=
  DECLARE _decompress
    WITH sh: share, in_: val, in_bytes: list byte, in_len: Z, gv: globals
    PRE [ tptr tuchar, tulong ]
      PROP (readable_share sh;
            0 <= in_len <= Int64.max_unsigned;
            in_len = Z.of_nat (length in_bytes);
            exists src : list byte,
              in_bytes = compress_to_bytes src /\ Zlength src <= Int64.max_unsigned)
      PARAMS (in_; Vlong (Int64.repr in_len)) GLOBALS (gv)
      SEP (mem_mgr gv; data_at sh (tarray tuchar in_len) (bytes_to_vals in_bytes) in_)
    POST [ tptr tuchar ] EX p: val,
      let out_bytes := decompress_from_bytes in_bytes in
      PROP ()
      RETURN (p)
      SEP (mem_mgr gv;
           data_at sh (tarray tuchar in_len) (bytes_to_vals in_bytes) in_;
           malloc_token Ews (tarray tuchar (Zlength out_bytes)) p *
           data_at Ews (tarray tuchar (Zlength out_bytes)) (bytes_to_vals out_bytes) p).


Definition Gprog: funspecs :=
        ltac:(with_library prog [surely_malloc_spec;
                                 encode_length_spec;
                                 decode_length_spec;
                                 find_largest_match_spec;
                                 compress_spec;
                                 decompress_spec]).


(* Adapted from: https://github.com/PrincetonUniversity/VST/blob/master/progs/verif_queue.v *)
Lemma body_surely_malloc:
  semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     (t, gv).
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p)).
   - if_tac.
     + subst p. entailer!.
     + entailer!.
   - forward_call 1.
     contradiction.
   - if_tac.
     + contradiction.
     + Intros. forward. entailer!.
   - forward. Exists p. entailer!.
Qed.


Lemma encode_length_body:
  semax_body Vprog Gprog f_encode_length encode_length_spec.
Proof.
  start_function.
  forward_if.
  - forward.
    assert (len = 0). {
      assert (Int64.unsigned (Int64.repr len) = len). {
        rewrite Int64.unsigned_repr_eq.
        rewrite Z.mod_small; [reflexivity | rep_lia].
      }
      rewrite H3 in H4.
      auto.
    }
    Exists 0.
    entailer!!.
    rewrite data_at_tuchar_zero_array_eq; auto.
  - forward.
    (* forward_loop ??? *)
Admitted.

Lemma decode_length_body:
  semax_body Vprog Gprog f_decode_length decode_length_spec.
Proof.
  start_function.
  forward_if.
  - forward.
    forward.
    assert (Zlength in_bytes = 0). {
      assert (Int64.unsigned (Int64.repr (Zlength in_bytes)) = (Zlength in_bytes)). {
        rewrite Int64.unsigned_repr_eq.
        rewrite Z.mod_small; [reflexivity | rep_lia].
      }
      rewrite H1 in H6.
      auto.
    }
    assert (in_bytes = []) by now apply Zlength_nil_inv.
    unfold nat_to_bytes.
    subst. simpl.
    Exists 0.
    entailer!!.
    rewrite H6. 
    unfold bytes_to_vals. simpl.
    rewrite data_at_tuchar_zero_array_eq; auto.
  - forward.
    (* forward_while ??? *)
Admitted.


Lemma find_largest_match_body: 
  semax_body Vprog Gprog f_find_largest_match find_largest_match_spec.
Proof.
  start_function.
  forward. forward. forward.
  (* forward_if ??? *)
Admitted.


Lemma compress_body:
  semax_body Vprog Gprog f_compress compress_spec.
Proof.
  start_function.
  forward.
  (* forward_call ??? *)
Admitted.

Lemma decompress_body:
  semax_body Vprog Gprog f_decompress decompress_spec.
Proof.
  start_function.
  forward.
  (* forward_call ??? *)
Admitted.

