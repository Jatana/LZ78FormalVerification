From Stdlib Require Import Arith Strings.Byte List Lia.
Import ListNotations.

Module Tokens.

  Inductive Token :=
    | Lit (b: byte)
    | Ref (length offset: nat). (* 4bit length, 12bit offset *)

  Definition nat_to_byte (n: nat): byte :=
    match of_nat (n mod 256) with
    | Some b => b
    | None => x00 (* Never happens *)
    end.

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

  Theorem to_token_correctness: forall t, bytes_to_tokens (tokens_to_bytes t) = t.
  Proof.
  Admitted.

End Tokens.

Export Tokens.
