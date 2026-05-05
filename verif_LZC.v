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

  Print Z.

Definition get_nth_spec :=
  DECLARE _encode_length
    WITH sh: share, x : Z, n : Z, gv: globals
    PRE [ tulong, tulong ]
      PROP (writable_share sh; 0 <= x <= Int64.max_unsigned - 128; 0 <= n <= 20)
      PARAMS (Vlong (Int64.repr x); Vlong (Int64.repr n)) GLOBALS (gv)
      SEP (mem_mgr gv)
    POST [ tuchar ] EX val: Z,
      PROP (val = Z.of_nat (get_nth (Z.to_nat x) (Z.to_nat n)))
      RETURN (Vint (Int.repr val))
      SEP (mem_mgr gv).

Definition encode_length_spec :=
  DECLARE _encode_length
    WITH sh: share, len: Z, out_: val, out: list val, out_len: Z, initial: list val, gv: globals
    PRE [ tulong, tptr tuchar ]
      PROP (writable_share sh; 0 <= len <= Int64.max_unsigned; isptr out_;
            Zlength (nat_to_bytes (Z.to_nat len)) <= out_len; 0 <= out_len; Zlength initial = 20)
      PARAMS (Vlong (Int64.repr len); out_) GLOBALS (gv)
      SEP (mem_mgr gv; data_at sh (tarray tuchar 20) initial out_)
    POST [ tulong ] EX idx: Z,
      PROP (idx = Zlength (nat_to_bytes (Z.to_nat len)))
      RETURN (Vlong (Int64.repr idx))
      SEP (mem_mgr gv;
           data_at sh (tarray tuchar 20) ((bytes_to_vals (nat_to_bytes (Z.to_nat len))) ++ (sublist idx 20 initial)) out_).

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
  hint.
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

Lemma easy_ineq1 (x i : Z) :
  0 <= x <= Int64.max_unsigned -> 0 <= i -> x / 128 ^ i <= Int64.max_unsigned.
Proof.
  intros.
  assert (1 <= 128 ^ i).
  replace 1 with (128 ^ 0) by reflexivity.
  apply Z.pow_le_mono_r; lia.
  assert (H_div_le_x : x / 128 ^ i <= x). {
    apply Z.div_le_upper_bound.
    * apply Z.pow_pos_nonneg; lia.
    * replace x with (x * 1) at 1 by lia.
      Search (_ * _ <= _ * _).
      Search (_ * _ = _ * _).
      rewrite (Z.mul_comm (128^i) x).
      apply Z.mul_le_mono_nonneg_l. lia. lia.
  }
  etransitivity.
  exact H_div_le_x.
  lia.
Qed.

Lemma easy_eq2 :
  128^0 = 1.
Proof.
  Search (_ ^ _).
  apply Z.pow_0_r.
Qed.

Arguments Nat.modulo : simpl never.
Arguments Nat.divmod : simpl never.
Arguments Nat.div : simpl never.

Lemma get_nth_Z : forall (x n : Z),
  0 <= x -> 
  0 <= n ->
  Z.of_nat (get_nth (Z.to_nat x) (Z.to_nat n)) = (x / 128 ^ n) mod 128 + 128.
Proof.
  intros x n Hx Hn.
  rewrite <- (Z2Nat.id n) by lia.
  generalize (Z.to_nat n); intro n_nat. clear n Hn. generalize Hx. clear Hx. generalize x. 
  induction n_nat.
    - intros. change (Z.of_nat 0) with 0. rewrite easy_eq2. Search (_ / _). rewrite Zdiv_1_r.
      change (Z.to_nat 0) with 0%nat.
      simpl get_nth.
      Search (Z.of_nat _).


      rewrite Nat2Z.inj_add.
      
      change (Z.of_nat 128) with 128.

      Search (Z.of_nat _).

      rewrite Nat2Z.inj_mod.
      change (Z.of_nat 128) with 128.
      rewrite Z2Nat.id by lia.
      reflexivity.
    - intros. 
      rewrite Nat2Z.id.
      simpl get_nth.
      rewrite Nat2Z.id in IHn_nat.
      assert ((Nat.div (Z.to_nat x0) 128) = Z.to_nat (Z.of_nat ((Z.to_nat x0) / 128))).
      {
       rewrite Nat2Z.id. reflexivity. 
      }
      rewrite H. rewrite IHn_nat.
        -- Search (_ + _ = _ + _). eapply Zplus_eq_compat. 2 : { reflexivity. }
           f_equal.
          rewrite Nat2Z.inj_div.
          
          change (Z.of_nat 128) with 128.
          
          rewrite Z2Nat.id by lia.

          replace (Z.of_nat (S n_nat)) with (Z.of_nat n_nat + 1) by lia.
          rewrite Z.pow_add_r by lia.
          change (128 ^ 1) with 128.

          rewrite (Z.mul_comm (128 ^ Z.of_nat n_nat) 128).

          rewrite <- Z.div_div.
          * reflexivity.
          *
            lia.
          *
            apply Z.pow_pos_nonneg; lia.
        -- Search (0 <= Z.of_nat _). apply Zle_0_nat.
Qed.

Lemma get_nth_body:
  semax_body Vprog Gprog f_get_nth get_nth_spec.
Proof.
  start_function.
  hint.
  forward_for_simple_bound n (EX i:Z,
    PROP()
    LOCAL(gvars gv; temp _x (Vlong (Int64.repr (x / 128^i))); temp _n (Vlong (Int64.repr n)))
    SEP(mem_mgr gv)).
    - entailer!.
      f_equal.
      f_equal.
      Search (_ ^ 0). 
      rewrite Z.pow_0_r.
      Search (_ / _).
      rewrite Z.div_1_r.
      auto.
    - forward.
      entailer!.
      apply f_equal.
      rewrite Z.pow_add_r by lia.
      change (128 ^ 1) with 128.

      rewrite <- Z.div_div.
      2: { lia. }
      2: { lia. }

      unfold Int64.divu.

      apply f_equal.
      rewrite Int64.unsigned_repr.
      reflexivity.

      split. apply Z.div_pos; lia.
      eapply easy_ineq1; lia.

    - hint.
      forward.
      entailer!.
      Exists (Z.of_nat (get_nth (Z.to_nat x) (Z.to_nat n))).
      hint.
      entailer!.

      remember (Int64.unsigned (Int64.repr (x / 128 ^ n)) mod 128) as my_mod.

      rewrite !Int64.Z_mod_modulus_eq.
      
      assert (H_my_mod_bounds : 0 <= my_mod < 128). {
        subst my_mod.
        apply Z.mod_pos_bound.
        lia.
      }

      rewrite !Z.mod_small.
      2: { 
        change Int64.modulus with 18446744073709551616.
        lia.
      }
      2: {
        change Int64.modulus with 18446744073709551616.
        rewrite !Z.mod_small. lia. lia.
      }

      subst my_mod.

      rewrite Int64.unsigned_repr.
      2: { 
        split.
        - apply Z.div_pos; lia.
        - apply easy_ineq1. lia. lia.
      }
      f_equal.
      rewrite get_nth_Z.
      2 : { lia. }
      2 : { lia. }
  remember ((x / 128 ^ n) mod 128 + 128) as Y.

  assert (H_Y_bounds : 0 <= Y < 256). {
    subst Y.
    pose proof (Z.mod_pos_bound (x / 128 ^ n) 128).
    lia.
  }

  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr Y))).
  rewrite <- (Int.repr_unsigned (Int.repr Y)).
  f_equal.

  Search (Int.zero_ext).
  rewrite Int.zero_ext_mod.
  2: {
    split. lia. unfold Int.zwordsize. unfold Int.wordsize. unfold Wordsize_32.wordsize. simpl. lia.
  }


  rewrite !Int.unsigned_repr.
  2: { 
    change Int.max_unsigned with 4294967295.
    lia. 
  }
  2: { 
    change Int.max_unsigned with 4294967295.
    apply Int.unsigned_range_2.
  }

  change (two_p 8) with 256. rewrite Z.mod_small. reflexivity.
  assumption.
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
      rewrite H4 in H8.
      auto.
    }
    Exists 0.
    entailer!!.
    autorewrite with sublist.
    entailer!.
  - forward.
    forward.
    forward_while (EX (i t: Z),
    PROP  (0 <= i < 20 /\ t = len / (128^i))
    LOCAL (
            temp _t (Vlong (Int64.repr t));
            temp _idx (Vlong (Int64.repr i));
            temp _len (Vlong (Int64.repr len));
            temp _out out_)
    SEP   (mem_mgr gv; data_at sh (tarray tuchar 20) ((sublist 0 i (bytes_to_vals (nat_to_bytes (Z.to_nat len)))) ++ (sublist i 20 initial)) out_)).
      + 
        Exists 0 len.
        entailer!.
        rewrite Z.pow_0_r, Z.div_1_r.
        reflexivity.
        autorewrite with sublist.
        auto.
      + entailer!.
      + repeat forward.
        entailer!.
        Exists ((i + 1), t / 128).
        entailer!.
          * split. 
            -- split. lia.
               admit.
            -- split. destruct H5 as (H5a & H5b). rewrite H5b.
               rewrite Z.pow_add_r, Z.pow_1_r, Zdiv.Zdiv_Zdiv.
               reflexivity. rep_lia. rep_lia. rep_lia. rep_lia.
               rewrite divu_repr64. reflexivity.
               admit. rep_lia.
               * assert (sublist i (i + 1) (bytes_to_vals (nat_to_bytes (Z.to_nat len))) = [Vint (Int.repr ((t mod 128) + 128))]). {
              admit.
            }
            assert ((sublist 0 (i + 1)
(bytes_to_vals (nat_to_bytes (Z.to_nat len))) ++
sublist (i + 1) 20 initial) = (sublist 0 i
(bytes_to_vals (nat_to_bytes (Z.to_nat len))) ++ [Vint (Int.repr (t mod 128 + 128))]++
 sublist (i + 1) 20 initial)). {
              rewrite <- H9.
              autorewrite with sublist.
              rewrite (sublist_split 0 i (i + 1) (bytes_to_vals (nat_to_bytes (Z.to_nat len)))).
              rewrite app_assoc.
              reflexivity.
              rep_lia.
              split. lia.
              admit.
            }
            rewrite H10. 
            rewrite upd_Znth_app2.
            assert (Zlength (sublist 0 i (bytes_to_vals (nat_to_bytes (Z.to_nat len)))) = i) by admit.
            rewrite H11, Z.sub_diag.
            assert ((sublist i 20 initial) = (Znth i initial) :: (sublist (i + 1) 20 initial)) by admit.
            rewrite H12, upd_Znth0.
            assert (Int.repr (t mod 128 + 128) = Int.zero_ext 8
        (Int.zero_ext 8
           (Int.repr
              (Int64.Z_mod_modulus
                 (Int64.Z_mod_modulus (Int64.Z_mod_modulus t mod 128) + 128))))) by admit.
            rewrite H13.
            entailer.
            admit.
      + forward_if (EX (i t: Z),
    PROP  ()
    LOCAL (
            temp _t (Vlong (Int64.repr t));
            temp _idx (Vlong (Int64.repr i));
            temp _len (Vlong (Int64.repr len));
            temp _out out_)
    SEP   (mem_mgr gv; data_at sh (tarray tuchar 20) ((sublist 0 (i) (bytes_to_vals (nat_to_bytes (Z.to_nat len)))) ++ (sublist i 20 initial)) out_)).
        * repeat forward.
          Exists (i + 1) t.
          entailer!!.
          admit. (* very similar to above! *)
        * forward. entailer!. Exists i t. autorewrite with sublist in *|-. entailer!.
        * Intros idx t0. forward.
          try autorewrite with sublist in *|-.
          assert (idx = Zlength (nat_to_bytes (Z.to_nat len))) by admit.
          Exists idx. entailer!.
          autorewrite with sublist in *|-.
          entailer!.
          assert (Zlength (nat_to_bytes (Z.to_nat len)) = Zlength (bytes_to_vals (nat_to_bytes (Z.to_nat len)))). {
            unfold bytes_to_vals.
            now repeat rewrite Zlength_map.
          }
          rewrite H11, sublist_firstn, ZtoNat_Zlength, firstn_exact_length.
          entailer.
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

