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

  Lemma nat_to_bytes_correctness: forall n,
    bytes_to_nat (nat_to_bytes n) = (n, []).
  Proof.
    intro. unfold nat_to_bytes.
    apply nat_to_bytes_correctness'.
    lia.
  Qed.

  Lemma nat_to_bytes_length: forall n,
    length (nat_to_bytes n) <= 8 * (Nat.log2 n) / 7.
  Proof.
  Admitted.

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

  Fixpoint tokens_to_bytes_chunk_len (ts: list Token) (n: nat) :=
    match n, ts with
    | 0, _ => 0
    | S pn, [] => 0
    | S pn, t :: tl => (tokens_to_bytes_chunk_len tl pn) + (length (token_to_bytes t))
    end.

  Fixpoint tokens_to_bytes_chunk (ts: list Token) (n: nat) :=
    match n, ts with
    | 0, _ => ([], ts, [])
    | S pn, [] => ([], [], [])
    | S pn, t :: tl =>
        let flag' := match t with
                     | Lit _ => true
                     | Ref _ _ => false end
        in match tokens_to_bytes_chunk tl pn with
           | (flag, ts'', acc) => (flag' :: flag, ts'', token_to_bytes t ++ acc)
           end
    end.

  Lemma flag_correctness: forall ts n flag i acc tail,
    n <= 8 -> i < Nat.min n (length ts) ->
    tokens_to_bytes_chunk ts n = (flag, tail, acc) ->
    exists b len off,
    match nth i flag false with
    | true => nth i ts (Lit x00) = Lit b
    | false => nth i ts (Lit x00) = Ref len off
    end.
  Proof.
    induction ts; intros.
    - simpl in H0. lia.
    - destruct a eqn:?.
      + simpl in H1.
        destruct n eqn:?.
        * lia.
        * destruct (tokens_to_bytes_chunk ts n0) as [[b' tail'] acc'] eqn:?.
          inversion H1; subst.
          simpl in H0.
          destruct i eqn:?.
          -- simpl. eexists _, _, _. reflexivity.
          -- specialize (IHts n0 b' n acc' tail ltac:(lia) ltac:(lia) Heqp).
             destruct IHts as [b'' [len [off ?]]].
             exists b'', len, off.
             simpl.
             assumption.
      + simpl in H1.
        destruct n eqn:?.
        * lia.
        * destruct (tokens_to_bytes_chunk ts n0) as [[b' tail'] acc'] eqn:?.
          inversion H1; subst.
          simpl in H0.
          destruct i eqn:?.
          -- simpl. eexists _, _, _. reflexivity.
          -- specialize (IHts n0 b' n acc' tail ltac:(lia) ltac:(lia) Heqp).
             destruct IHts as [b'' [len [off ?]]].
             exists b'', len, off.
             simpl.
             assumption.
    Unshelve. exact 0. exact 0. exact "000"%byte.
  Qed.

  Lemma tokens_to_bytes_chunk_len_correctness: forall ts n flag_byte tail acc,
    tokens_to_bytes_chunk ts n = (flag_byte, tail, acc) ->
    tokens_to_bytes_chunk_len ts n = length acc.
  Proof.
    induction ts; simpl; intros.
    - destruct n; injection H as <- <-; subst; simpl; lia.
    - destruct n.
      + injection H as <- <-. subst. simpl. lia.
      + destruct a;
        destruct (tokens_to_bytes_chunk ts n) as [[l toks] acc'] eqn:?;
        specialize (IHts n l toks acc' Heqp);
        simpl in H; unfold nibbles_to_byte in H;
        inversion H; subst; simpl; lia.
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
        let '(flag, tail, acc) := tokens_to_bytes_chunk tokens 8 in
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

  Lemma chunk_remove: forall tokens n acc flag_byte tail,
    n <= 8 ->
    Forall valid_token tokens ->
    tokens_to_bytes_chunk tokens n = (flag_byte, tail, acc) ->
    exists prev,
      tokens = prev ++ tail /\
      Forall valid_token prev /\
      length prev = Nat.min n (length tokens) /\
      tokens_to_bytes_chunk prev n = (flag_byte, [], acc).
  Proof.
    induction tokens; intros.
    - exists []. simpl in H1. destruct n;
      assert (tail = []) by congruence; rewrite H2;
        repeat split; try assumption; simpl; rewrite H2 in H1; congruence.
    - inversion H0; subst.
      simpl in H1. destruct n.
      + exists []. assert (tail = a :: tokens) by congruence.
        rewrite H2.
        repeat split.
        * constructor.
        * simpl. congruence.
      + destruct (tokens_to_bytes_chunk tokens) as [[b tail'] acc'] eqn:?.
        destruct a.
        * assert (true :: b = flag_byte) by congruence. subst.
          assert (tail = tail') by congruence. subst.
          assert (token_to_bytes (Lit b0) ++ acc' = acc) by congruence. subst.
          specialize (IHtokens n acc' b tail' ltac:(lia) H5 Heqp).
          destruct IHtokens as [prev [Heq [Hfa [Hlen Hp]]]].
          exists (Lit b0 :: prev).
          repeat split.
          -- rewrite Heq. reflexivity.
          -- constructor; assumption.
          -- simpl. f_equal. assumption.
          -- simpl. rewrite Hp. reflexivity.
        * assert (false :: b = flag_byte) by congruence. subst.
          assert (tail = tail') by congruence. subst.
          assert (token_to_bytes (Ref length offset) ++ acc' = acc) by congruence. subst.
          specialize (IHtokens n acc' b tail' ltac:(lia) H5 Heqp).
          destruct IHtokens as [prev [Heq [Hfa [Hlen Hp]]]].
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

  Lemma to_tokens_chunk_correctness: forall n tokens acc flag_byte,
    n <= 8 ->
    Forall valid_token tokens ->
    length tokens <= n ->
    tokens_to_bytes_chunk tokens n = (flag_byte, [], acc) ->
    bytes_to_tokens_chunk n (to_nat (list_bool_to_byte flag_byte 0 8)) acc = (tokens, []).
  Proof.
    induction n; intros.
    - destruct tokens; simpl in *.
      + congruence.
      + discriminate.
    - destruct tokens; simpl in *.
      + injection H2 as <- <-.

  Admitted.

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
          pose proof (chunk_remove (t :: t0) 8 bytes flag restT ltac:(lia) H Heqp) as [prev [Heqpv [Hf [Hl Ht]]]].
          pose proof (to_tokens_chunk_correctness 8 prev bytes flag ltac:(lia) Hf ltac:(lia) Ht).
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
          pose proof (chunk_app 8 (to_nat (list_bool_to_byte flag 0 8)) bytes (tokens_to_bytes_fueled restT fuel1) prev [] H3 Hor).
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
