Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import LZ LZ_Matching LZ_Tokens Utils LZC.
Require Import Stdlib.Strings.Byte.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Fixpoint get_nth (x n : nat) : nat :=
  match n with
    | 0%nat => (x mod 128) + 128
    | S m => get_nth (x / 128) m
    end.

Fixpoint nat_to_bytes_fixed (i l x : nat) : list nat :=
  match l with
    | 0%nat => []
    | S p => get_nth x i :: (nat_to_bytes_fixed (i + 1) (p) x)
  end.

Lemma nat_to_bytes_fixed_len : forall l i x,
  length (nat_to_bytes_fixed i l x) = l.
Proof.
  induction l.
    - intros. simpl. reflexivity.
    - intros. simpl. rewrite IHl. reflexivity.
Qed.

Lemma nat_to_bytes_fixed_sn : forall l i x,
  nat_to_bytes_fixed i (S l) x = nat_to_bytes_fixed i l x ++ [get_nth x (i + l)].
Proof.
  induction l.
    - intros. simpl. assert (i + 0 = i)%nat by lia. rewrite H. reflexivity.
    - intros. assert ((nat_to_bytes_fixed i (S (S l)) x) = ((get_nth x (i)) :: (nat_to_bytes_fixed (i+1) (S (l)) x))).
      simpl. reflexivity.
      rewrite H. rewrite IHl. simpl. assert (i + 1 + l = i + S l)%nat by lia. rewrite H0. reflexivity.
Qed.



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


Definition bytes_to_vals (bs : list nat) : list val :=
  map Vint (map Int.repr (map Z.of_nat (bs))).

  Definition bytes_to_nat (bs : list byte) : list nat :=
    (map Byte.to_nat (bs)).

Definition get_nth_spec :=
  DECLARE _get_nth
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
      PROP (writable_share sh; 0 <= len <= Int64.max_unsigned - 128; isptr out_;
            Zlength (nat_to_bytes (Z.to_nat len)) <= out_len; 0 <= out_len; Zlength initial = 20)
      PARAMS (Vlong (Int64.repr len); out_) GLOBALS (gv)
      SEP (mem_mgr gv; data_at sh (tarray tuchar 20) initial out_)
    POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (mem_mgr gv;
           data_at sh (tarray tuchar 20) ((bytes_to_vals (nat_to_bytes_fixed 0 20 (Z.to_nat len)))) out_).

Definition is_equal_spec :=
  DECLARE _is_equal
    WITH sh1: share, sh2: share, s_ptr: val, t_ptr: val, len: Z, s_vals: list Z, t_vals: list Z
    PRE [ tptr tuchar, tptr tuchar, tulong ]
      PROP (
        readable_share sh1;
        readable_share sh2;
        0 <= len <= Int64.max_unsigned;
        Zlength s_vals = len;
        Zlength t_vals = len;
        Forall (fun x => 0 <= x <= 255) s_vals;
        Forall (fun x => 0 <= x <= 255) t_vals
      )
      PARAMS (s_ptr; t_ptr; Vlong (Int64.repr len))
      SEP (
        data_at sh1 (tarray tuchar len) (map Vint (map Int.repr s_vals)) s_ptr;
        data_at sh2 (tarray tuchar len) (map Vint (map Int.repr t_vals)) t_ptr
      )
    POST [ tint ]
      PROP ()
      RETURN (Vint (Int.repr (if list_eqb Z.eqb s_vals t_vals then 1 else 0)))
      SEP (
        data_at sh1 (tarray tuchar len) (map Vint (map Int.repr s_vals)) s_ptr;
        data_at sh2 (tarray tuchar len) (map Vint (map Int.repr t_vals)) t_ptr
      ).

Definition Gprog: funspecs :=
        ltac:(with_library prog [surely_malloc_spec;
                                 get_nth_spec;
                                 encode_length_spec;
                                 is_equal_spec]).


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
  forward_for_simple_bound 20 (EX i:Z,
    PROP()
    LOCAL(gvars gv; temp _len (Vlong (Int64.repr (len))); temp _out out_)
    SEP(mem_mgr gv; data_at sh (tarray tuchar 20) ((bytes_to_vals (nat_to_bytes_fixed 0 (Z.to_nat i) (Z.to_nat len))) ++ (sublist i 20 initial)) out_)).
    - entailer!. hint. autorewrite with sublist. auto.
    - hint.
      Opaque Z.div Z.modulo Z.pow.
      Opaque Z.to_nat Z.of_nat.
      hint.
      forward_call (sh, len, i, gv).
        -- hint. entailer!. hint. autorewrite with sublist in *|-.
           simpl. f_equal. Search (Int.signed (Int.repr _)).
           rewrite Int.signed_repr.
            * reflexivity.
            * unfold Int.min_signed. unfold Int.max_signed.
              unfold Int.half_modulus. unfold Int.modulus.
              unfold Int.wordsize. unfold Wordsize_32.wordsize.
              Search (two_power_nat _).
              change (two_power_nat 32) with 4294967296.
              change (4294967296 / 2) with (2147483648).
              lia.
        -- hint. Intros ret_val. hint. assert (Int.min_signed <= i <= Int.max_signed).
           unfold Int.min_signed. unfold Int.max_signed.
              unfold Int.half_modulus. unfold Int.modulus.
              unfold Int.wordsize. unfold Wordsize_32.wordsize.
              Search (two_power_nat _).
              change (two_power_nat 32) with 4294967296.
              change (4294967296 / 2) with (2147483648).
              lia.
            forward. entailer!. hint.
  replace (upd_Znth i (bytes_to_vals (nat_to_bytes_fixed 0 (Z.to_nat i) (Z.to_nat len)) ++ sublist i 20 initial) _)
     with (bytes_to_vals (nat_to_bytes_fixed 0 (Z.to_nat (i + 1)) (Z.to_nat len)) ++ sublist (i + 1) 20 initial).
  2: {
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.

    rewrite nat_to_bytes_fixed_sn. Print bytes_to_vals. unfold bytes_to_vals.


    rewrite map_app.
    simpl.

    rewrite upd_Znth_app2.
    2: {

      rewrite Zlength_map.

      rewrite Zlength_map. rewrite Zlength_map.
      rewrite Zlength_correct. rewrite nat_to_bytes_fixed_len.
      split.
        - Search (Z.of_nat (Z.to_nat _)). rewrite Z2Nat.id. lia.
          lia.
        - rewrite Z2Nat.id. Search (Zlength _). specialize (Zlength_nonneg (sublist i 20 initial)) as Hnon.
          lia. lia.
    }

    assert ((i -
Zlength
(map Vint
(map Int.repr (map Z.of_nat (nat_to_bytes_fixed 0 (Z.to_nat i) (Z.to_nat len)))))) = 0).
    Search (Zlength (map _ _)).
    rewrite Zlength_map. rewrite Zlength_map. rewrite Zlength_map.
    Search (Zlength _). rewrite Zlength_correct. rewrite nat_to_bytes_fixed_len. Search (Z.of_nat (Z.to_nat _)). rewrite Z2Nat.id. lia. lia.

    rewrite H5.
    rewrite (sublist_split i (i + 1) 20 initial) by lia.

    Search (upd_Znth 0).
    specialize (Zlength_sublist i (i + 1) initial ltac:(lia) ltac:(lia)) as Hl.
    assert (i + 1 - i = 1). lia. rewrite H11 in Hl.
    destruct (sublist i (i + 1) initial) eqn:Hd. inversion Hl.
    rewrite Zlength_cons in Hl.
    Search (Z.succ _).
    rewrite <- Z.add_1_r in Hl. assert (Zlength l = 0) by lia.
    clear H11 Hl. destruct l. 2: { rewrite Zlength_cons in H12. specialize (Zlength_nonneg l) as H13. rewrite <- Z.add_1_r in H12. lia. }
    Search (_ ++ _). simpl. rewrite upd_Znth0.

    rewrite !map_app.
    simpl map.

    rewrite <- app_assoc.
    simpl app.
    f_equal.
  }

  entailer!.

  - entailer!. hint. list_solve.
Qed.

Lemma pos_eqb_refl : forall p : positive, (p =? p)%positive = true.
Proof.
  induction p.

  - simpl.
    exact IHp.

  - simpl.
    exact IHp.

  - simpl.
    reflexivity.
Qed.

Lemma is_equal_body:
  semax_body Vprog Gprog f_is_equal is_equal_spec.
Proof.
  start_function.
  forward_if.
    - forward. entailer!. f_equal. f_equal.
  assert (H_len_s : Zlength s_vals = 0).
  inversion H4.
  Search (Int64.Z_mod_modulus _ = _).
  rewrite Int64.Z_mod_modulus_eq.
  symmetry.
  apply Z.mod_small.
  rep_lia.

  destruct s_vals as [| s s_vals'].
  2: {
    list_solve.
  }

  assert (H_len_t : Zlength t_vals = 0) by lia.

  destruct t_vals as [| t t_vals'].
  2: {
    list_solve.
  }

  simpl.
  reflexivity.

  - assert (Int.min_signed <= 0 <= Int.max_signed).
    unfold Int.min_signed. unfold Int.max_signed. unfold Int.half_modulus. unfold Int.modulus.
    change (two_power_nat Int.wordsize) with (4294967296).
    change (4294967296 / 2) with (2147483648).
    lia.
    assert (0 <= 0 < Zlength (map Int.repr s_vals)).
    split. lia.
    rewrite Zlength_map.

    rewrite H0.

    assert (H_len_not_zero : len <> 0).
    {
      intro H_zero.
      subst len.
      apply H4.
      rewrite H_zero.
      reflexivity.
    }

    lia.
    assert (0 <= 0 < Zlength s_vals).
    split. lia.

    rewrite H0.

    assert (H_len_not_zero : len <> 0).
    {
      intro H_zero.
      subst len.
      apply H4.
      rewrite H_zero.
      reflexivity.
    }

    lia.

    forward.
      -- entailer!.
        rewrite Forall_Znth in H2.
        pose proof (H2 0 H7) as H_s0_bounds.
        rewrite Int.unsigned_repr.
        2: {
          rep_lia.
        }
        change Byte.max_unsigned with 255.
        rep_lia.
      -- forward.
          --- entailer!.
              assert (H_t_len : 0 <= 0 < Zlength t_vals) by lia.
              rewrite Forall_Znth in H3.
              pose proof (H3 0 H_t_len) as H_t0_bounds.

              rewrite Int.unsigned_repr.
              2: {
                rep_lia.
              }

              change Byte.max_unsigned with 255.
              rep_lia.

          --- forward_if.
            ---- forward. entailer!.
                 f_equal. f_equal.
                destruct s_vals as [| s s_vals'].
                { list_solve. }
                destruct t_vals as [| t t_vals'].
                { list_solve. }

                change (Znth 0 (s :: s_vals')) with s in H8.
                change (Znth 0 (t :: t_vals')) with t in H8.

                assert (H_neq : s <> t).
                {
                  intro H_eq.
                  subst t.
                  apply H8.
                  reflexivity.
                }

                simpl list_eqb.

                destruct (Zeq_bool s t) eqn:H_bool.
                ----- apply Zeq_bool_eq in H_bool.
                  contradiction.
                ----- simpl.
                      reflexivity.
            ---- assert (H_len_pos : 1 <= len) by lia.

                rewrite (split2_data_at_Tarray_tuchar sh1 len 1 (map Vint (map Int.repr s_vals)) s_ptr).
                2: lia.
                2: { rewrite !Zlength_map; lia. }

                rewrite (split2_data_at_Tarray_tuchar sh2 len 1 (map Vint (map Int.repr t_vals)) t_ptr).
                2: lia.
                2: { rewrite !Zlength_map; lia. }

                rewrite !sublist_map.

                forward_call (sh1, sh2, offset_val 1 s_ptr, offset_val 1 t_ptr, len - 1, sublist 1 len s_vals, sublist 1 len t_vals).
                  * entailer!.
                  * entailer!. hint. autorewrite with sublist in *|-.
                    assert_PROP (field_address0 (Tarray tuchar (Zlength s_vals) noattr) (SUB 1) s_ptr = offset_val 1 s_ptr) as Hs_ptr.
                    { entailer!.
                      unfold field_address0.

                      if_tac.

                      - simpl.
                        reflexivity.

                      - auto with field_compatible. hint.
                        exfalso.

                        unfold field_address0 in H12.

                        destruct (field_compatible0_dec (Tarray tuchar (Zlength s_vals) noattr) (SUB 1) s_ptr).

                        + contradiction.

                        + destruct H12 as [H_isptr _].
                          inversion H_isptr.
                    }

                    assert_PROP (field_address0 (Tarray tuchar (Zlength s_vals) noattr) (SUB 1) t_ptr = offset_val 1 t_ptr) as Ht_ptr.
                    { entailer!. auto with field_compatible.
                      unfold field_address0.

                      if_tac.

                      - simpl.
                        reflexivity.

                      - exfalso.

                        unfold field_address0 in H18.

                        destruct (field_compatible0_dec (Tarray tuchar (Zlength s_vals) noattr) (SUB 1) t_ptr).

                        + contradiction.

                        + destruct H18 as [H_isptr _].
                          inversion H_isptr.
                    }

                    rewrite Hs_ptr, Ht_ptr.


                    cancel.

                  * repeat split.

                + rewrite Zlength_sublist; lia.

                + rewrite Zlength_sublist; lia.

                + apply Forall_sublist.
                  apply H2.

                + apply Forall_sublist.
                  apply H3.
                *  forward. entailer!.
                  ++ f_equal. f_equal.

  destruct s_vals as [| s s_vals']; [list_solve|].
  destruct t_vals as [| t t_vals']; [list_solve|].

  change (Znth 0 (s :: s_vals')) with s in H8.
  change (Znth 0 (t :: t_vals')) with t in H8.

  assert (H_s_eq_t : s = t).
  {
    inversion H2; subst.
    inversion H3; subst.

    apply (f_equal Int.unsigned) in H8.
    rewrite !Int.unsigned_repr in H8 by rep_lia.
    exact H8.
  }

  subst t.

  autorewrite with sublist.

  simpl list_eqb.

  assert (H_true : Zeq_bool s s = true).
  {
    unfold Zeq_bool.
    destruct (Z.eq_dec s s).
    - destruct s. reflexivity. Search (_ =? _). rewrite pos_eqb_refl. reflexivity. apply pos_eqb_refl.
    - contradiction.
  }
  rewrite H_true.

  simpl.
  autorewrite with sublist.
  Search (sublist 1 _ _ = _). rewrite sublist_1_cons.
  simpl.
  assert (Z.succ (Zlength s_vals') - 1 = (Zlength s_vals')).
  lia. rewrite H0. rewrite sublist_1_cons.
  rewrite H0.
  autorewrite with sublist.
  autorewrite with sublist.
  assert (Zlength s_vals' = Zlength t_vals').
  rewrite !Zlength_cons in H1.

  lia.
  rewrite H23.
  autorewrite with sublist.
  reflexivity.

  ++ entailer!.

  rewrite <- !sublist_map.

  assert_PROP (offset_val 1 s_ptr = field_address0 (Tarray tuchar (Zlength s_vals) noattr) (SUB 1) s_ptr) as Hs_ptr.
  { entailer!.
  unfold field_address0.

  if_tac.

  - simpl.
    reflexivity.

  - auto with field_compatible.
    exfalso.

  apply H30.


  auto with field_compatible.

  unfold field_compatible0.
  unfold field_compatible in H11, H17.


  destruct H17 as [H_isptr [H_cosu [H_size1 [H_align _]]]].
  destruct H11 as [_ [_ [H_size2 _]]].

  split. { exact H_isptr. }
  split. { exact H_cosu. }
  split.
  {
    destruct s_ptr; try contradiction.
    unfold size_compatible in *. simpl in *.
    unfold Ptrofs.add in H_size2.

    rewrite Ptrofs.unsigned_repr in H_size2 by admit.

    admit.
  }
  split.
  {
    unfold align_compatible in *. auto.

    destruct s_ptr as [| | | | | b i_ofs]; try contradiction.


  simpl in H_align |- *.

  simpl.

  simpl in H_align.
  Search align_compatible_rec.
Admitted.

