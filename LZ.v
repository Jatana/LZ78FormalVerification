From Stdlib Require Import Arith Strings.Byte List Lia.
Require Import StringsModule.
Import ListNotations.


Module Impl.
  Inductive Token :=
    | Lit (b: byte)
    | Ref (length offset: nat). (* 4bit length, 12bit offset *)

  Definition nat_to_byte' (n: nat): byte :=
    match of_nat (n mod 256) with
    | Some b => b
    | None => x00 (* Never happens *)
    end.

  (* This does not have the Never happens case! *)
  Definition nat_to_byte (n: nat): byte.
  Proof.
    destruct (of_nat (n mod 256)) eqn:?.
    - exact b.
    - exfalso.
      assert (H_range : n mod 256 < 256).
      + apply Nat.mod_upper_bound. lia.
      + rewrite of_nat_None_iff in Heqo.
        lia.
  Defined.

  Definition nibbles_to_byte (h l: nat): byte :=
    nat_to_byte ((h mod 16) * 16 + (l mod 16)).

  Definition token_to_bytes (t: Token): list byte :=
    match t with
    | Lit b => [b]
    | Ref length offset =>
        let len_opt := length - 3 in
        let off_opt := offset - 3 in
        let b0 := nibbles_to_byte len_opt (off_opt / 256) in
        let b1 := nat_to_byte off_opt in
        [b0; b1]
    end.

  Fixpoint tokens_to_bytes_fueled (tokens: list Token) (fuel: nat): list byte :=
    match fuel, tokens with
    | _, [] => []
    | 0, _ => [] (* Never happens if fuel = length tokens *)
    | S fuel, _ =>
        let fix take_eight (ts: list Token) (n: nat) (flag: nat) (acc: list byte) :=
          match n, ts with
          | 0, _ => (nat_to_byte flag, ts, acc)
          | S pn, [] => (nat_to_byte (flag * (2 ^ n)), [], acc)
          | S pn, t :: tl =>
              let flag' := match t with
                           | Lit _ => flag * 2 + 1
                           | Ref _ _ => flag * 2 end
              in take_eight tl pn flag' (acc ++ token_to_bytes t)
          end
        in 
        let '(flag, tail, acc) := take_eight tokens 8 0 [] in
        flag :: acc ++ tokens_to_bytes_fueled tail fuel
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

  Fixpoint bytes_to_tokens_fueled (l: list byte) (fuel: nat) : list Token :=
    match fuel, l with
    | 0, _ => []
    | _, [] => [] (* Never happens if fuel = length l *)
    | S fuel, flag_byte :: tl =>
        let flag := to_nat flag_byte in
        let fix process_flag (n: nat) (after: list byte) : (list Token * list byte) :=
          match n with
          | 0 => ([], after)
          | S pn =>
              let (otoken, tail) := bytes_to_token after (Nat.testbit flag pn) in
              match otoken with
              | Some token => 
                  let (tokens, rest) := process_flag pn tail in
                  (token :: tokens, rest)
              | None => ([], [])
              end
          end
        in
        let (tokens, tail) := process_flag 8 tl
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

  Fixpoint find_largest_match' (before after: list byte) (l : nat) : option (nat * nat) :=
    match l with
      | 2 => None
      | 1 => None
      | 0 => None
      | S k => 
        let suff := (slice ((length before) - 4098) 4098 before) in
        let m := find_match Byte.eqb suff (slice 0 l after) in
        match m with
          | None => find_largest_match' before after k
          | Some p => Some (l, (length suff) - p)
        end
    end.

  (* returns 3 <= length <= 18, 3 <= offset <= 4098 *)
  Definition find_largest_match (before after: list byte): option (nat * nat) := 
    find_largest_match' before after (min (length after) 18).

  Definition one : byte := "1"%byte.
  Definition zero : byte := "0"%byte.
  
  Example find_largest_match_test1 : find_largest_match [zero; one; one; zero; one] [zero; one; one; zero] = Some (4, 5).
  Proof. unfold find_largest_match. simpl. reflexivity. Qed.
  
  Example find_largest_match_test2 : find_largest_match [zero; one] [zero] = None.
  Proof. unfold find_largest_match. simpl. reflexivity. Qed.

  Lemma find_largest_match_corr1' : forall s t l len off, l <= 18 -> find_largest_match' s t l = Some (len, off) -> 3 <= len <= 18.
  Proof.
    intros s t l. generalize s t. clear s t. induction l.
    intros. simpl in H0. inversion H0.
    intros. simpl in H0. destruct l. inversion H0. destruct l. inversion H0.
    destruct (find_match eqb
(slice (length s - 4098) 4098 s)
(slice 0 (S (S (S l))) t)). 
    inversion H0. clear H0. split. lia. lia.
    eapply IHl. lia. exact H0.
  Qed.

  Lemma find_largest_match_corr1 : forall s t len off, find_largest_match s t = Some (len, off) -> 3 <= len <= 18.
  Proof.
    intros. unfold find_largest_match in H. eapply find_largest_match_corr1'.
    assert (Init.Nat.min (length t) 18 <= 18). lia. exact H0. exact H.
  Qed.

  Lemma find_largest_match_corr2' : forall s t l len off, (length t) >= 3 -> (length s) <= 4098 -> find_largest_match' s t l = Some (len, off) -> 3 <= off <= 4098.
  Proof.
    intros s t l. generalize s t. clear s t. induction l.
    intros. simpl in H1. inversion H1.
    intros. simpl in H1. destruct l. inversion H1. destruct l. inversion H1.
    remember (slice (length s - 4098) 4098 s) as suff.
    remember (slice 0 (S (S (S l))) t) as pref.
    destruct (find_match eqb suff pref) eqn:Hd.
    inversion H1. clear H1. split.
    assert (list_eqb Byte.eqb (slice n (length pref) suff) pref = true).
    eapply find_match_corr. assumption.
    specialize (equality_implies_length_eq eqb (slice n (length pref) suff) pref H1) as Heq.
    assert (length pref = length (slice 0 (S (S (S l))) t)).
    eapply f_equal. assumption.
    specialize (slice_size t 0 (S (S (S l)))) as Hsize.
    rewrite <- H2 in Hsize.

    assert ((length pref) >= 3).

    destruct pref. simpl in Hsize. destruct t. inversion H. simpl in Hsize.
    simpl in H. destruct t. simpl in H. lia. simpl in Hsize. destruct t.
    simpl in H. lia. simpl in Hsize. lia.

    destruct pref. simpl in Hsize. destruct t. inversion H. simpl in Hsize.
    simpl in H. destruct t. simpl in H. lia. simpl in Hsize. destruct t.
    simpl in H. lia. simpl in Hsize. lia. 

    destruct pref. simpl in Hsize. destruct t. inversion H. simpl in Hsize.
    simpl in H. destruct t. simpl in H. lia. simpl in Hsize. destruct t.
    simpl in H. lia. simpl in Hsize. lia. simpl. lia.

    assert (length (slice n (length pref) suff) >= 3). lia.

    specialize (slice_size suff n (length pref)) as Hslice.
    rewrite Hslice in H6. lia.

    specialize (slice_size s (length s - 4098) 4098) as HH.
    assert (length suff = length (slice (length s - 4098) 4098 s)).
    apply f_equal. assumption. rewrite <- H1 in HH. lia.

    eapply IHl. apply H. apply H0. exact H1.
  Qed.

  Lemma find_largest_match_corr2 : forall s t len off, (length s) <= 4098 -> find_largest_match s t = Some (len, off) -> 3 <= off <= 4098.
  Proof.
    intros. unfold find_largest_match in H0.
    destruct t. simpl in H0. inversion H0.
    destruct t. simpl in H0. inversion H0.
    destruct t. simpl in H0. inversion H0.
    eapply find_largest_match_corr2'.
    assert (length (b :: b0 :: b1 :: t) >= 3). simpl. lia.
    exact H1. exact H. exact H0.
  Qed.

  Lemma find_largest_match_corr3' (s t : list byte) (n l len off : nat) :
        find_largest_match' s t l = Some (len, off) -> (l <= length t) ->
        list_eqb Byte.eqb (slice ((length s) - off) len s) (slice 0 len t) = true /\ len <= length t.
  Proof.
    generalize s t n len off. clear s t n len off. induction l.
    intros. simpl in H. inversion H.

    intros. simpl in H.
    destruct l. inversion H.
    destruct l. inversion H.

    destruct (find_match eqb (slice (length s - 4098) 4098 s)
              (slice 0 (S (S (S l))) t)) eqn:Hd.

    inversion H. clear H.
    remember (slice (length s - 4098) 4098 s) as suff.
    remember (slice 0 (S (S (S l))) t) as pref.

    specialize (find_match_corr Byte.eqb suff pref n0 Hd) as Hslice.
    clear IHl.
    specialize (slice_slice s (length s - 4098) 4098 n0 (length pref)) as Hdouble.
    rewrite Heqsuff in Hslice. rewrite Hdouble in Hslice.
    destruct Hslice as (Hslice1 & Hslice2).

    assert (length pref >= 1). assert (length t >= 3). lia.
    specialize (slice_size t 0 (S (S (S l)))) as Hpref_size. rewrite <- Heqpref in Hpref_size.
    lia.

    specialize (Hslice2 H). rewrite <- Heqsuff in Hslice2.
    assert ((length s - (length suff - n0)) = (length s - 4098 + n0)).
    specialize (slice_size s (length s - 4098) 4098) as Hsuff_size.
    rewrite <- Heqsuff in Hsuff_size.
    lia.

    rewrite H1.
    assert (length pref = (S (S (S l))) ).
    specialize (slice_size t 0 (S (S (S l)))) as Hpref_size. rewrite <- Heqpref in Hpref_size.
    lia.

    rewrite H4 in Hslice1. 
    assert ((4098 - n0) >= length pref).
    specialize (equality_implies_length_eq Byte.eqb  (slice (length s - 4098 + n0) (Init.Nat.min (S (S (S l)))
(4098 - n0)) s) pref Hslice1) as Hlength_eq.
    specialize (slice_size s (length s - 4098 + n0) (Init.Nat.min (S (S (S l))) (4098 - n0))) as Hlen.
    rewrite Hlen in Hlength_eq. clear Hlen.
    lia.

    rewrite H4 in H5.
    assert (Init.Nat.min (S (S (S l))) (4098 - n0) = (S (S (S l)))).
    lia.

    rewrite H6 in Hslice1.


    split.
    assumption.
    assumption.
    
    eapply IHl.     
    exact l.
    exact H.
    lia.
  Qed.

  Lemma find_largest_match_corr3 (s t : list byte) (n l len off : nat) :
        find_largest_match s t = Some (len, off) ->
        list_eqb Byte.eqb (slice ((length s) - off) len s) (slice 0 len t) = true /\ len <= length t.
  Proof.
    intros. unfold find_largest_match in H. eapply find_largest_match_corr3'.
    exact n.
    exact H.
    lia.
  Qed.


  Fixpoint compress' (before after: list byte) (l: nat): list Token :=
    match after, l with
    | [], _ => []
    | hd :: tl, 0 => 
        match (find_largest_match before after) with 
        | None => Lit hd :: compress' (before ++ [hd]) tl 0
        | Some (length, offset) => Ref length offset :: compress' (before ++ [hd]) tl (length - 1)
        end
    | hd :: tl, S x => compress' (before ++ [hd]) tl x
    end.

  (* We need to add the length of s as a prefix here. *)
  Definition compress (s: list byte): list Token :=
    compress' [] s 0.

  Fixpoint decompress (l : list Token) : list byte := nil. 

  Theorem to_token_correctness: forall t, bytes_to_tokens (tokens_to_bytes t) = t.
  Proof.
  Admitted.

  Theorem correctness: forall s,
    decompress (compress s) = s.
  Proof.
  Admitted.

  Theorem upperbound: forall s,
    length (compress s) <= 9 * length s / 8 + 8 * Nat.log2 (length s) / 7.
  Proof.
  Admitted.

End Impl.

