From Stdlib Require Import Arith Strings.Byte List Lia.
Import ListNotations.

Module Tokens.

  Inductive Token :=
    | Lit (b: byte)
    | Ref (length offset: nat). (* 4bit length, 12bit offset *)
    (*| Ref : forall length offset, 3 <= length <= 18 /\ 3 <= offset <= 4098 -> Token.*)

  Definition valid_token (t: Token) :=
    match t with
    | Lit _ => True
    | Ref length offset => (3 <= length <= 18) /\ (3 <= offset <= 4098)
    end.

  Definition nat_to_byte (n: nat): byte :=
    match of_nat (n mod 256) with
    | Some b => b
    | None => x00 (* Never happens *)
    end.

  Lemma nat_to_byte_correctness : forall n,
    n < 256 ->
    to_nat (nat_to_byte n) = n.
  Proof.
    unfold nat_to_byte.
    intros.
    destruct (of_nat (_ mod 256)) eqn:?.
    - apply to_of_nat_iff.
      rewrite (Nat.mod_small n 256 ltac:(lia)) in Heqo.
      assumption.
    - exfalso.
      apply of_nat_None_iff in Heqo.
      pose proof (Nat.mod_upper_bound n 256 ltac:(lia)).
      lia.
  Qed.

  Fixpoint nat_to_bytes_fueled (fuel n: nat): list byte :=
    match fuel with
    | 0 => []
    | S fuel =>
        if n <? 128 then [nat_to_byte n]
        else let byte := nat_to_byte ((n mod 128) + 128) in
             byte :: nat_to_bytes_fueled fuel (n / 128)
    end.

  Definition nat_to_bytes (n: nat): list byte :=
    nat_to_bytes_fueled n n.

  Fixpoint bytes_to_nat (l: list byte): nat * list byte :=
    match l with
    | [] => (0, [])
    | byte :: tl =>
        let n := to_nat byte in
        if n <? 128 then (n, tl)
        else let (n', tail) := bytes_to_nat tl in
             ((n mod 128) + 128 * n', tail)
    end.

  Lemma nat_to_bytes_correctness': forall n fuel,
    n <= fuel ->
    bytes_to_nat (nat_to_bytes_fueled fuel n) = (n, []).
  Proof.
    induction n as [n IHn] using lt_wf_rec; intros.
    destruct fuel.
    - assert (n = 0) by lia. subst.
      reflexivity.
    - simpl.
      destruct (n <? 128) eqn:?; subst; simpl.
      + apply Nat.ltb_lt in Heqb as Hnl.
        rewrite nat_to_byte_correctness by lia.
        rewrite Heqb. reflexivity.
      + apply Nat.ltb_ge in Heqb as Hng.
        set (b := nat_to_byte (n mod 128 + 128)).
        assert (to_nat b = n mod 128 + 128). {
          apply nat_to_byte_correctness.
          pose proof (Nat.mod_upper_bound n 128 ltac:(lia)).
          lia.
        }
        match goal with
        | [ |- context[if to_nat (nat_to_byte ?m) <? _ then _ else _] ] =>
            assert (Hm: m = n mod 128 + 128) by reflexivity; rewrite Hm; clear Hm
        end.
        assert (Heqby: n mod 128 + 128 < 256). {
          pose proof (Nat.mod_upper_bound n 128 ltac:(lia)). lia.
        }
        rewrite nat_to_byte_correctness by lia.
        assert (Hf: n mod 128 + 128 <? 128 = false). {
          apply Nat.ltb_ge. lia.
        }
        rewrite Hf.
        replace (fst (Nat.divmod n 127 0 127)) with (n / 128) by reflexivity.
        assert (Hdiv : n / 128 < n) by (apply Nat.div_lt; lia).
        rewrite (IHn (n / 128) Hdiv fuel ltac:(lia)).
        f_equal.
        pose proof (Nat.divmod_spec (n mod 128 + 128) 127 0 127 ltac:(lia)).
        destruct (Nat.divmod (n mod 128 + 128) 127 0 127) as [q u].
        simpl.
        match goal with
        | [ |- ?l + ?r = _ ] =>
            assert (Hl: l = 127 - u) by reflexivity;
            assert (Hr: r = 128 * (n / 128)) by reflexivity;
            rewrite Hl, Hr; clear Hl Hr
        end.
        pose proof (Nat.div_mod n 128 ltac:(lia)).
        lia.
  Qed.

  Lemma nat_to_bytes_correctness: forall n rest,
    n <> 0 ->
    bytes_to_nat (nat_to_bytes n ++ rest) = (n, rest).
  Proof.
  Admitted.

  Lemma nat_to_bytes_length': forall n fuel,
    length (nat_to_bytes_fueled fuel n) <= Nat.log2 n / 7 + 1.
  Proof.
    induction n as [n IHn] using lt_wf_rec; intros.
    destruct n, fuel; simpl; try lia.
    destruct (S n <? 128) eqn:?; simpl; try lia.
    apply Nat.ltb_ge in Heqb.
    set (lhs := S (length (nat_to_bytes_fueled fuel (S n / 128)))).
    set (rhs := Nat.log2 (S n) / 7 + 1).
    match goal with
    | [ |- ?l <= ?r ] =>
        assert (Heq: l = lhs) by reflexivity; rewrite Heq; clear Heq;
        assert (Heq: r = rhs) by reflexivity; rewrite Heq; clear Heq
    end.
    assert (Hdiv: S n / 128 < S n) by (apply Nat.div_lt; lia).
    assert (Hlog: Nat.log2 (S n / 128) = Nat.log2 (S n) - 7). {
      destruct n.
      - simpl. lia.
      - assert (128 = 2 ^ 7) by reflexivity.
        rewrite H, <- Nat.shiftr_div_pow2, Nat.log2_shiftr.
        reflexivity.
    }
    specialize (IHn (S n / 128) Hdiv fuel).
    assert (Hm: lhs <= Nat.log2 (S n / 128) / 7 + 1 + 1) by lia.
    rewrite Hlog in *.

    etransitivity.
    - exact Hm.
    - apply Nat.add_le_mono_r.
      set (m := Nat.log2 (S n)).
      assert (7 <= m). {
        assert (Nat.log2 128 <= m) by now apply Nat.log2_le_mono.
        unfold Nat.log2 in H.
        now simpl in H.
      }
      simpl.
      pose proof (Nat.divmod_spec (m - 7) 6 0 6 ltac:(lia)).
      destruct (Nat.divmod (m - 7) 6 0 6) as [q u].
      pose proof (Nat.divmod_spec m 6 0 6 ltac:(lia)).
      destruct (Nat.divmod m 6 0 6) as [q' u'].
      simpl. lia.
  Qed.

  Lemma nat_to_bytes_length: forall n,
    length (nat_to_bytes n) <= Nat.log2 n / 7 + 1.
  Proof. intro n. exact (nat_to_bytes_length' n n). Qed.

  Definition nibbles_to_byte (h l: nat): byte :=
    nat_to_byte ((h mod 16) * 16 + (l mod 16)).

  Lemma to_nat_nibbles_correct : forall h l,
    h < 16 ->
    l < 16 ->
    to_nat (nibbles_to_byte h l) = h * 16 + l.
  Proof.
    unfold nibbles_to_byte, nat_to_byte.
    intros.
    destruct (of_nat (_ mod 256)) eqn:?.
    - apply to_of_nat_iff in Heqo.
      rewrite Heqo.
      rewrite (Nat.mod_small h 16 ltac:(lia)).
      rewrite (Nat.mod_small l 16 ltac:(lia)).
      exact (Nat.mod_small (h * 16 + l) 256 ltac:(lia)).
    - exfalso.
      apply of_nat_None_iff in Heqo.
      pose proof (Nat.mod_upper_bound (h mod 16 * 16 + l mod 16) 256).
      lia.
  Qed.

  Definition token_to_bytes (t: Token): list byte :=
    match t with
    | Lit b => [b]
    | Ref length offset =>
        let len_opt := length - 3 in
        let off_opt := offset - 3 in
        let b0 := nibbles_to_byte len_opt (off_opt / 256) in
        let b1 := nat_to_byte (off_opt mod 256) in
        [b0; b1]
    end.

  Fixpoint tokens_to_bytes_chunk_len (n: nat) (ts: list Token) :=
    match n, ts with
    | 0, _ => 0
    | S pn, [] => 0
    | S pn, t :: tl => (tokens_to_bytes_chunk_len pn tl) + (length (token_to_bytes t))
    end.

  Fixpoint tokens_to_bytes_chunk (n: nat) (ts: list Token) :=
    match n, ts with
    | 0, _ => ([], ts, [])
    | S pn, [] => ([], [], [])
    | S pn, t :: tl =>
        let flag' := match t with
                     | Lit _ => true
                     | Ref _ _ => false end
        in let '(flag, ts'', acc) :=  tokens_to_bytes_chunk pn tl
        in (flag' :: flag, ts'', token_to_bytes t ++ acc)
    end.

  Lemma tokens_to_bytes_chunk_len_correctness: forall n ts flag_byte tail acc,
    tokens_to_bytes_chunk n ts = (flag_byte, tail, acc) ->
    tokens_to_bytes_chunk_len n ts = length acc.
  Proof.
    induction n; simpl; intros.
    - inversion H. now simpl.
    - destruct ts.
      + inversion H. now simpl.
      + destruct (tokens_to_bytes_chunk n ts) as [[flag tail'] acc'] eqn:?.
        rewrite (IHn ts flag tail' acc' Heqp).
        assert (token_to_bytes t ++ acc' = acc) by congruence.
        rewrite <- H0, length_app.
        lia.
  Qed.

  Fixpoint list_bool_to_byte (l: list bool) (x: nat) (n: nat) : byte :=
    match l, n with
    | b :: tl, S n => list_bool_to_byte tl (x * 2 + (if b then 1 else 0)) n
    | _, n => nat_to_byte (x * 2 ^ n)
    end.

  Fixpoint tokens_to_bytes_fueled (tokens: list Token) (fuel: nat): list byte :=
    match fuel, tokens with
    | 0, _ => [] (* Never happens if fuel = length tokens *)
    | _, [] => []
    | S fuel, _ =>
        let '(flag, tail, acc) := tokens_to_bytes_chunk 8 tokens in
        list_bool_to_byte flag 0 8 :: acc ++ tokens_to_bytes_fueled tail fuel
    end.

  Definition tokens_to_bytes tokens := tokens_to_bytes_fueled tokens (length tokens).

  Example tokens_to_bytes_test1 :
    tokens_to_bytes [Lit "000"; Lit "001"; Lit "002"; Lit "003"; Lit "004"; Ref 5 1000] =
    (* 0b1111_1000 = 248, (2 << 12) + 997 = 9189 = <35, 229> *)
    ["248"%byte; "000"%byte; "001"%byte; "002"%byte; "003"%byte; "004"%byte; "035"%byte; "229"%byte ].
  Proof. reflexivity. Qed.

  Example tokens_to_bytes_test2 :
    tokens_to_bytes [Lit "000"; Lit "001"; Lit "002"; Lit "003"; Lit "004";
    Lit "005"; Lit "006"; Lit "007"; Lit "008"; Lit "009"; Ref 5 1000] =
    (* 0b1111_1111 = 255 *)
    ["255"%byte; "000"%byte; "001"%byte; "002"%byte; "003"%byte; "004"%byte; "005"%byte; "006"%byte; "007"%byte;
    (* 0b1100_0000 = 192, (2 << 12) + 997 = 9189 = <35, 229> *)
    "192"%byte; "008"%byte; "009"%byte; "035"%byte; "229"%byte ].
  Proof. reflexivity. Qed.

  Definition bytes_to_token (l: list byte) (flag: bool): option Token * list byte :=
    match flag, l with
    | true, b :: tl => (Some (Lit b), tl)
    | false, b0 :: b1 :: tl =>
        let n0 := to_nat b0 in
        let n1 := to_nat b1 in
        let len_opt := n0 / 16 in
        let off_hi := n0 mod 16 in
        let off_lo := n1 in
        (Some (Ref (len_opt + 3) (off_hi * 256 + off_lo + 3)), tl)
    | _, _ => (None, []) (* This may happen if we consumed all bytes but flag had extra bits *)
    end.

  Fixpoint bytes_to_tokens_chunk (n flag: nat) (after: list byte) : (list Token * list byte) :=
    match n with
    | 0 => ([], after)
    | S pn =>
        let (otoken, tail) := bytes_to_token after (Nat.testbit flag pn) in
        match otoken with
        | Some token =>
            let (tokens, rest) := bytes_to_tokens_chunk pn flag tail in
            (token :: tokens, rest)
        | None => ([], [])
        end
    end.

  Fixpoint bytes_to_tokens_fueled (l: list byte) (fuel: nat) : list Token :=
    match fuel, l with
    | 0, _ => [] (* Never happens if fuel = length l *)
    | _, [] => []
    | S fuel, flag_byte :: tl =>
        let flag := to_nat flag_byte in
        let (tokens, tail) := bytes_to_tokens_chunk 8 flag tl
        in tokens ++ bytes_to_tokens_fueled tail fuel
    end.

  Definition bytes_to_tokens (l: list byte) : list Token :=
    bytes_to_tokens_fueled l (length l).

  Example bytes_to_tokens_test1 :
    bytes_to_tokens ["248"%byte; "000"%byte; "001"%byte; "002"%byte; "003"%byte; "004"%byte; "035"%byte; "229"%byte ] =
    [Lit "000"; Lit "001"; Lit "002"; Lit "003"; Lit "004"; Ref 5 1000].
  Proof. reflexivity. Qed.

  Example bytes_to_tokens_test2 :
    bytes_to_tokens ["255"%byte; "000"%byte; "001"%byte; "002"%byte; "003"%byte; "004"%byte; "005"%byte; "006"%byte; "007"%byte;
    "192"%byte; "008"%byte; "009"%byte; "035"%byte; "229"%byte ] =
    [Lit "000"; Lit "001"; Lit "002"; Lit "003"; Lit "004";
    Lit "005"; Lit "006"; Lit "007"; Lit "008"; Lit "009"; Ref 5 1000].
  Proof. reflexivity. Qed.

  Lemma to_token_correctness: forall t rest,
    valid_token t ->
    bytes_to_token (token_to_bytes t ++ rest)
                   (match t with Lit _ => true | Ref _ _ => false end) = (Some t, rest).
  Proof.
    intros.
    destruct t.
    - reflexivity.
    - apply pair_equal_spec.
      split; [f_equal | reflexivity].
      f_equal.
      + simpl in *.
        pose proof (Nat.divmod_spec (offset - 3) 255 0 255 ltac:(lia)).
        destruct (Nat.divmod (offset - 3) 255 0 255) as [q'1 u'1]. simpl.
        rewrite (to_nat_nibbles_correct (length - 3) q'1 ltac:(lia) ltac:(lia)).
        pose proof (Nat.divmod_spec ((length - 3) * 16 + q'1) 15 0 15 ltac:(lia)).
        destruct (Nat.divmod ((length - 3) * 16 + q'1) 15 0 15) as [q'2 u'2]. simpl.
        lia.
      + unfold nibbles_to_byte.
        pose proof (Nat.mod_upper_bound (offset - 3) 256 ltac:(lia)).
        rewrite (nat_to_byte_correctness ((offset - 3) mod 256) ltac:(lia)).
        assert ((length - 3) mod 16 * 16 + ((offset - 3) / 256) mod 16 < 256). {
          pose proof (Nat.mod_upper_bound (length - 3) 16 ltac:(lia)).
          pose proof (Nat.mod_upper_bound ((offset - 3) / 256) 16 ltac:(lia)).
          lia.
        }
        rewrite (nat_to_byte_correctness ((length - 3) mod 16 * 16 + ((offset - 3) / 256) mod 16) H1).
        unfold Nat.modulo, Nat.div.
        pose proof (Nat.divmod_spec (length - 3) 15 0 15 ltac:(lia)).
        destruct (Nat.divmod (length - 3) 15 0 15) as [q1 u1].
        pose proof (Nat.divmod_spec (offset - 3) 255 0 255 ltac:(lia)).
        destruct (Nat.divmod (offset - 3) 255 0 255) as [q2 u2].
        assert (snd (q1, u1) = u1) by reflexivity.
        rewrite H4. clear H4.
        assert (snd (q2, u2) = u2) by reflexivity.
        rewrite H4. clear H4.
        assert (fst (q2, u2) = q2) by reflexivity.
        rewrite H4. clear H4.
        pose proof (Nat.divmod_spec q2 15 0 15 ltac:(lia)).
        destruct (Nat.divmod q2 15 0 15) as [q3 u3].
        assert (snd (q3, u3) = u3) by reflexivity.
        rewrite H5. clear H5.
        pose proof (Nat.divmod_spec ((15 - u1) * 16 + (15 - u3)) 15 0 15 ltac:(lia)).
        destruct (Nat.divmod ((15 - u1) * 16 + (15 - u3)) 15 0 15) as [q4 u4].
        assert (snd (q4, u4) = u4) by reflexivity.
        rewrite H6. clear H6.
        destruct H. lia.
  Qed.

  Lemma chunk_remove: forall n tokens acc flag_byte tail,
    n <= 8 ->
    Forall valid_token tokens ->
    tokens_to_bytes_chunk n tokens = (flag_byte, tail, acc) ->
    exists prev,
      tokens = prev ++ tail /\
      Forall valid_token prev /\
      length prev = Nat.min n (length tokens) /\
      tokens_to_bytes_chunk n prev = (flag_byte, [], acc).
  Proof.
    induction n; intros; simpl in H1.
    - exists [].
      repeat split; simpl.
      + congruence.
      + constructor.
      + congruence.
    - destruct tokens.
      + exists [].
        repeat split.
        * inversion H1; subst. reflexivity.
        * constructor.
        * simpl. congruence.
      + destruct (tokens_to_bytes_chunk n tokens) as [[b tail'] acc'] eqn:?.
        destruct t.
        * assert (true :: b = flag_byte) by congruence. subst.
          assert (tail = tail') by congruence. subst.
          assert (token_to_bytes (Lit b0) ++ acc' = acc) by congruence. subst.
          inversion H0; subst.
          specialize (IHn tokens acc' b tail' ltac:(lia) H5 Heqp).
          destruct IHn as [prev [Heq [Hfa [Hlen Hp]]]].
          exists (Lit b0 :: prev).
          repeat split.
          -- rewrite Heq. reflexivity.
          -- constructor; assumption.
          -- simpl. f_equal. assumption.
          -- simpl. rewrite Hp. reflexivity.
        * assert (false :: b = flag_byte) by congruence. subst.
          assert (tail = tail') by congruence. subst.
          assert (token_to_bytes (Ref length offset) ++ acc' = acc) by congruence. subst.
          inversion H0; subst.
          specialize (IHn tokens acc' b tail' ltac:(lia) H5 Heqp).
          destruct IHn as [prev [Heq [Hfa [Hlen Hp]]]].
          exists (Ref length offset :: prev).
          repeat split.
          -- rewrite Heq. reflexivity.
          -- constructor; assumption.
          -- simpl. f_equal. assumption.
          -- simpl. rewrite Hp. reflexivity.
  Qed.

  Lemma bytes_to_token_app: forall flag acc rest token tail,
    bytes_to_token acc flag = (Some token, tail) ->
    bytes_to_token (acc ++ rest) flag = (Some token, tail ++ rest).
  Proof.
    intros. destruct flag, acc as [| b [| b0 tailB]];
    simpl in H; try discriminate; injection H as <- <-; reflexivity.
  Qed.

  Lemma chunk_app: forall n flag acc rest tokens tail,
    bytes_to_tokens_chunk n flag acc = (tokens, tail) ->
    length tokens = n \/ rest = [] ->
    bytes_to_tokens_chunk n flag (acc ++ rest) = (tokens, tail ++ rest).
  Proof.
    induction n; intros.
    - simpl in *. congruence.
    - simpl in H.
      destruct (bytes_to_token acc (Nat.testbit flag n)) as [otoken tailB] eqn:?, otoken.
      + destruct (bytes_to_tokens_chunk n flag tailB) as [tokensB restB] eqn:?.
        injection H as <- <-.
        simpl in H0 |- *. destruct H0.
        * injection H as H.
          rewrite (bytes_to_token_app (Nat.testbit flag n) acc rest t tailB Heqp).
          rewrite (IHn flag tailB rest tokensB restB Heqp0); auto.
        * subst.
          repeat rewrite app_nil_r.
          rewrite Heqp, Heqp0. reflexivity.
      + injection H as <- <-.
        simpl in H0. destruct H0.
        * discriminate.
        * subst. simpl.
          repeat rewrite app_nil_r.
          rewrite Heqp. reflexivity.
  Qed.

  Lemma tokens_to_bytes_chunk_flag_length: forall n tokens ts acc flag,
    tokens_to_bytes_chunk n tokens = (flag, ts, acc) ->
    length flag <= n.
  Proof.
    induction n; simpl; intros.
    - inversion H; subst. now simpl.
    - destruct tokens.
      + inversion H; subst. simpl. lia.
      + destruct (tokens_to_bytes_chunk n tokens) as [[flag' ts'] acc'] eqn:?.
        inversion H. subst. simpl.
        specialize (IHn tokens ts acc' flag' Heqp).
        lia.
  Qed.

  Lemma zero_lt_2_pow: forall n,
    0 < 2 ^ n.
  Proof. intros. assert (2 ^ n <> 0) by (apply Nat.pow_nonzero; lia). lia. Qed.

  Lemma list_bool_to_byte_correctness: forall l n x,
    length l <= n ->
    n <= 8 ->
    x < 2 ^ (8 - n) ->
    exists rest,
      rest < 2 ^ n /\
      to_nat (list_bool_to_byte l x n) = x * 2 ^ n + rest.
  Proof.
    induction l; intros; simpl.
    - rewrite nat_to_byte_correctness.
      + exists 0.
        split.
        * apply zero_lt_2_pow.
        * lia.
      + assert (x * 2 ^ n < 2 ^ (8 - n) * 2 ^ n). {
          apply Nat.mul_lt_mono_pos_r.
          - apply zero_lt_2_pow.
          - assumption.
        }
        assert (8 - n + n = 8) by lia.
        assert (1 * 2 ^ 8 = 256) by reflexivity.
        rewrite <- 2 Nat.shiftl_mul_pow2, <- Nat.shiftl_1_l, Nat.shiftl_shiftl, H3,
                2 Nat.shiftl_mul_pow2 in H2.
        now rewrite H4 in H2.
    - destruct n.
      + exists 0; simpl.
        split.
        * lia.
        * rewrite nat_to_byte_correctness.
          -- lia.
          -- assert (2 ^ (8 - 0) = 256) by reflexivity. lia.
      + assert (x * 2 + (if a then 1 else 0) < 2 ^ (8 - n)). {
          replace (8 - S n) with (7 - n) in * by reflexivity.
          rewrite Nat.mul_comm.
          destruct a.
          - clear l IHl H.
            replace (8 - n) with (S (7 - n)) by lia.
            change (2 ^ S (7 - n)) with (2 * (2 ^ (7 - n))).
            lia.
          - replace (2 ^ (8 - n)) with (2 * 2 ^ (7 - n)).
            + lia.
            + rewrite <- Nat.pow_succ_r'.
              f_equal. lia.
        }
        destruct a.
        * destruct (IHl n (x * 2 + 1) ltac:(simpl in H; lia) ltac:(lia) H2) as [rest [Hb Heq]].
          exists (2 ^ n + rest).
          split.
          -- simpl. lia.
          -- rewrite Heq. simpl. lia.
        * destruct (IHl n (x * 2 + 0) ltac:(simpl in H; lia) ltac:(lia) H2) as [rest [Hb Heq]].
          exists rest.
          split.
          -- simpl. lia.
          -- rewrite Heq. simpl. lia.
  Qed.

  Lemma div_double_plus_r: forall n r,
    Nat.div2 (2 * n + r) = n + Nat.div2 r.
  Proof.
    intros.
    rewrite 2 Nat.div2_div. simpl.
    pose proof (Nat.divmod_spec (n + (n + 0) + r) 1 0 1 ltac:(lia)).
    destruct (Nat.divmod (n + (n + 0) + r) 1 0 1) as [q u].
    pose proof (Nat.divmod_spec r 1 0 1 ltac:(lia)).
    destruct (Nat.divmod r 1 0 1) as [q' u'].
    simpl. lia.
  Qed.

  Lemma testbit_flag: forall b: bool, forall x rest n,
    rest < 2 ^ n ->
    Nat.testbit ((x * 2 + (if b then 1 else 0)) * 2 ^ n + rest) n = b.
  Proof.
    intros.
    revert b x rest H.
    induction n; simpl in *; intros.
    - replace rest with 0 by lia.
      rewrite Nat.add_0_r, Nat.mul_1_r, Nat.mul_comm.
      destruct b.
      + apply Nat.odd_odd.
      + rewrite Nat.add_0_r. apply Nat.odd_even.
    - assert (Nat.div2 rest < 2 ^ n). {
        rewrite Nat.div2_div.
        now apply Nat.Div0.div_lt_upper_bound.
      }
      replace (2 ^ n + (2 ^ n + 0)) with (2 * 2 ^ n) in * by reflexivity.
      specialize (IHn b x (Nat.div2 rest) H0). simpl in IHn.
      now rewrite Nat.mul_comm, <- Nat.mul_assoc, div_double_plus_r, Nat.mul_comm.
  Qed.

  Lemma to_tokens_chunk_correctness: forall n tokens acc flag_byte x,
    n <= 8 ->
    x < 2 ^ (8 - n) ->
    Forall valid_token tokens ->
    length tokens <= n ->
    tokens_to_bytes_chunk n tokens = (flag_byte, [], acc) ->
    bytes_to_tokens_chunk n (to_nat (list_bool_to_byte flag_byte x n)) acc = (tokens, []).
  Proof.
    induction n; intros; simpl in H3 |- *.
    - congruence.
    - destruct tokens.
      + inversion H3; subst.
        simpl bytes_to_tokens_chunk.
        destruct (Nat.testbit (to_nat (list_bool_to_byte [] x (S n))) n); reflexivity.
      + destruct (tokens_to_bytes_chunk n tokens) as [[flag ts'] acc'] eqn:?.
        inversion H3. subst. clear H3.
        set (b := match t with Lit _ => true | Ref _ _ => false end).
        assert (to_nat (list_bool_to_byte flag (x * 2 + (if b then 1 else 0)) n) =
                to_nat (list_bool_to_byte (b :: flag) x (S n))) by reflexivity.
        rewrite <- H3. clear H3.

        assert (Hb: x * 2 + (if b then 1 else 0) < 2 ^ (8 - n)). {
          assert (2 ^ (8 - n) = 2 ^ (8 - S n) * 2). {
            replace (8 - n) with (S (8 - S n)) by lia.
            rewrite Nat.pow_succ_r'. lia.
          }
          destruct b; lia.
        }
        pose proof (tokens_to_bytes_chunk_flag_length n tokens [] acc' flag Heqp).
        pose proof (list_bool_to_byte_correctness flag n (x * 2 + (if b then 1 else 0)) H3
                    ltac:(lia) Hb) as [rest [Hrb Heq]].
        rewrite Heq.
        rewrite testbit_flag by assumption.
        inversion H1; subst.
        rewrite to_token_correctness by assumption.
        specialize (IHn tokens acc' flag (x * 2 + (if b then 1 else 0)) ltac:(lia) Hb H7
                    ltac:(simpl in H2; lia) Heqp).
        rewrite Heq in IHn.
        now rewrite IHn.
  Qed.

  Lemma to_tokens_fueled_correctness: forall fuel1 fuel2 t l,
    Forall valid_token t ->
    length t <= fuel1 ->
    tokens_to_bytes_fueled t fuel1 = l ->
    length l <= fuel2 ->
    bytes_to_tokens_fueled l fuel2 = t.
  Proof.
    induction fuel1; intros.
    - inversion H0. apply length_zero_iff_nil in H4. subst.
      destruct fuel2; reflexivity.
    - destruct t.
      + simpl in H1; subst. destruct fuel2; reflexivity.
      + unfold tokens_to_bytes_fueled in H1.
        destruct (tokens_to_bytes_chunk _ _) as [[flag restT] bytes] eqn:?.
        match goal with
        | [ H: _ :: _ ++ ?f _ _ = _ |- _ ] =>
            assert (Hfun: f = tokens_to_bytes_fueled) by reflexivity; rewrite Hfun in H; clear Hfun
        end.

        unfold bytes_to_tokens_fueled.
        destruct fuel2.
        * inversion H2. apply length_zero_iff_nil in H4. subst. discriminate.
        * destruct l. discriminate.
          destruct (bytes_to_tokens_chunk 8 (to_nat b) l) as [tokens tail] eqn:?.
          match goal with
          | [ |- _ ++ ?f _ _ = _] =>
              assert (Hfun: f = bytes_to_tokens_fueled) by reflexivity; rewrite Hfun; clear Hfun
          end.

          assert (list_bool_to_byte flag 0 8 = b) by congruence. subst.
          injection H1 as H1.
          pose proof (chunk_remove 8 (t :: t0) bytes flag restT ltac:(lia) H Heqp)
                      as [prev [Heqpv [Hf [Hl Ht]]]].
          pose proof (to_tokens_chunk_correctness 8 prev bytes flag 0 ltac:(lia)
                      ltac:(apply zero_lt_2_pow) Hf ltac:(lia) Ht).
          assert (Hor: length prev = 8 \/ tokens_to_bytes_fueled restT fuel1 = []). {
            destruct (Nat.min_dec 8 (length (t :: t0))).
            - left. lia.
            - right.
              assert (restT = []). {
                rewrite Heqpv, length_app, Hl in H0.
                destruct restT.
                - reflexivity.
                - rewrite e, Heqpv, length_app in Hl. simpl in Hl. lia.
              }
              subst. destruct fuel1; reflexivity.
          }
          pose proof (chunk_app 8 (to_nat (list_bool_to_byte flag 0 8)) bytes
                      (tokens_to_bytes_fueled restT fuel1) prev [] H3 Hor).
          rewrite app_nil_l in H4.
          assert (prev = tokens) by congruence. subst.
          rewrite Heqpv, app_inv_head_iff.
          assert (Forall valid_token restT). {
            rewrite Heqpv in H.
            apply Forall_app in H. tauto.
          }
          assert (length restT <= fuel1). {
            rewrite Heqpv in H0. simpl in H0.
            rewrite length_app, Hl in H0.
            simpl in H0. lia.
          }
          assert (length tail <= fuel2). {
            assert (tail = tokens_to_bytes_fueled restT fuel1) by congruence. subst.
            simpl in H2. rewrite length_app in H2.
            lia.
          }
          exact (IHfuel1 fuel2 restT tail H1 H5 ltac:(congruence) H6).
  Qed.

  Theorem to_tokens_correctness: forall t,
    Forall valid_token t ->
    bytes_to_tokens (tokens_to_bytes t) = t.
  Proof.
    intros.
    unfold bytes_to_tokens, tokens_to_bytes.
    eapply to_tokens_fueled_correctness; trivial.
  Qed.

End Tokens.

Export Tokens.
