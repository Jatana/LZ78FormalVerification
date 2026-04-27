From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.17".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "LZC.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _b0 : ident := $"b0".
Definition _b1 : ident := $"b1".
Definition _best_len : ident := $"best_len".
Definition _best_off : ident := $"best_off".
Definition _compress : ident := $"compress".
Definition _decode_length : ident := $"decode_length".
Definition _decompress : ident := $"decompress".
Definition _encode_length : ident := $"encode_length".
Definition _exit : ident := $"exit".
Definition _find_largest_match : ident := $"find_largest_match".
Definition _flag : ident := $"flag".
Definition _flag_i : ident := $"flag_i".
Definition _i : ident := $"i".
Definition _idx : ident := $"idx".
Definition _in : ident := $"in".
Definition _in_i : ident := $"in_i".
Definition _in_len : ident := $"in_len".
Definition _k : ident := $"k".
Definition _len : ident := $"len".
Definition _len_opt : ident := $"len_opt".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _match_len : ident := $"match_len".
Definition _max_match_len : ident := $"max_match_len".
Definition _n : ident := $"n".
Definition _off : ident := $"off".
Definition _off_hi : ident := $"off_hi".
Definition _off_lo : ident := $"off_lo".
Definition _off_opt : ident := $"off_opt".
Definition _out : ident := $"out".
Definition _out_i : ident := $"out_i".
Definition _out_len : ident := $"out_len".
Definition _p : ident := $"p".
Definition _start : ident := $"start".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _token_count : ident := $"token_count".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
      ((Etempvar _n tulong) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition f_encode_length := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_len, tulong) :: (_out, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _len tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sset _idx (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Sifthenelse (Ebinop Olt (Etempvar _len tulong)
                         (Econst_int (Int.repr 128) tint) tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'1 (Etempvar _idx tulong))
                  (Sset _idx
                    (Ebinop Oadd (Etempvar _t'1 tulong)
                      (Econst_int (Int.repr 1) tint) tulong)))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _out (tptr tuchar))
                      (Etempvar _t'1 tulong) (tptr tuchar)) tuchar)
                  (Ecast (Etempvar _len tulong) tuchar)))
              Sbreak)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'2 (Etempvar _idx tulong))
                  (Sset _idx
                    (Ebinop Oadd (Etempvar _t'2 tulong)
                      (Econst_int (Int.repr 1) tint) tulong)))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _out (tptr tuchar))
                      (Etempvar _t'2 tulong) (tptr tuchar)) tuchar)
                  (Ecast
                    (Ebinop Oadd
                      (Ebinop Omod (Etempvar _len tulong)
                        (Econst_int (Int.repr 128) tint) tulong)
                      (Econst_int (Int.repr 128) tint) tulong) tuchar)))
              (Sset _len
                (Ebinop Odiv (Etempvar _len tulong)
                  (Econst_int (Int.repr 128) tint) tulong)))))
        Sskip)
      (Sreturn (Some (Etempvar _idx tulong))))))
|}.

Definition f_decode_length := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_in, (tptr tuchar)) :: (_in_len, tulong) ::
                (_out, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tulong) :: (_n, tuchar) :: (_t'1, tulong) ::
               (_t'4, tuchar) :: (_t'3, tulong) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _in_len tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Sassign (Ederef (Etempvar _out (tptr tulong)) tulong)
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))
    Sskip)
  (Ssequence
    (Sset _idx (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _idx tulong) (Etempvar _in_len tulong) tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'1 (Etempvar _idx tulong))
              (Sset _idx
                (Ebinop Oadd (Etempvar _t'1 tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _in (tptr tuchar))
                    (Etempvar _t'1 tulong) (tptr tuchar)) tuchar))
              (Sset _n (Ecast (Etempvar _t'4 tuchar) tuchar))))
          (Sifthenelse (Ebinop Olt (Etempvar _n tuchar)
                         (Econst_int (Int.repr 128) tint) tint)
            (Ssequence
              (Ssequence
                (Sset _t'3 (Ederef (Etempvar _out (tptr tulong)) tulong))
                (Sassign (Ederef (Etempvar _out (tptr tulong)) tulong)
                  (Ebinop Oadd (Etempvar _t'3 tulong)
                    (Ebinop Oshl (Ecast (Etempvar _n tuchar) tulong)
                      (Ebinop Omul (Econst_int (Int.repr 7) tint)
                        (Ebinop Osub (Etempvar _idx tulong)
                          (Econst_int (Int.repr 1) tint) tulong) tulong)
                      tulong) tulong)))
              (Sreturn (Some (Etempvar _idx tulong))))
            (Ssequence
              (Sset _t'2 (Ederef (Etempvar _out (tptr tulong)) tulong))
              (Sassign (Ederef (Etempvar _out (tptr tulong)) tulong)
                (Ebinop Oadd (Etempvar _t'2 tulong)
                  (Ebinop Oshl
                    (Ecast
                      (Ebinop Omod (Etempvar _n tuchar)
                        (Econst_int (Int.repr 128) tint) tint) tulong)
                    (Ebinop Omul (Econst_int (Int.repr 7) tint)
                      (Ebinop Osub (Etempvar _idx tulong)
                        (Econst_int (Int.repr 1) tint) tulong) tulong)
                    tulong) tulong))))))
      (Sreturn (Some (Etempvar _idx tulong))))))
|}.

Definition f_find_largest_match := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_in, (tptr tuchar)) :: (_in_len, tulong) :: (_p, tulong) ::
                (_len, (tptr tulong)) :: (_off, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_best_len, tuchar) :: (_best_off, tushort) ::
               (_max_match_len, tulong) :: (_start, tulong) ::
               (_i, tulong) :: (_match_len, tulong) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'4, tuchar) :: (_t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _best_len (Ecast (Econst_int (Int.repr 0) tint) tuchar))
  (Ssequence
    (Sset _best_off (Ecast (Econst_int (Int.repr 0) tint) tushort))
    (Ssequence
      (Sset _max_match_len
        (Ebinop Osub (Etempvar _in_len tulong) (Etempvar _p tulong) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Ogt (Etempvar _max_match_len tulong)
                       (Econst_int (Int.repr 18) tint) tint)
          (Sset _max_match_len
            (Ecast (Econst_int (Int.repr 18) tint) tulong))
          Sskip)
        (Ssequence
          (Sset _start (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Ssequence
            (Sifthenelse (Ebinop Oge (Etempvar _p tulong)
                           (Econst_int (Int.repr 4098) tint) tint)
              (Sset _start
                (Ebinop Osub (Etempvar _p tulong)
                  (Econst_int (Int.repr 4098) tint) tulong))
              Sskip)
            (Ssequence
              (Ssequence
                (Sset _i (Etempvar _start tulong))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                   (Etempvar _p tulong) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _match_len
                        (Ecast (Econst_int (Int.repr 0) tint) tulong))
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Olt
                                             (Etempvar _match_len tulong)
                                             (Etempvar _max_match_len tulong)
                                             tint)
                                (Ssequence
                                  (Sset _t'3
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _in (tptr tuchar))
                                        (Ebinop Oadd (Etempvar _i tulong)
                                          (Etempvar _match_len tulong)
                                          tulong) (tptr tuchar)) tuchar))
                                  (Ssequence
                                    (Sset _t'4
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _in (tptr tuchar))
                                          (Ebinop Oadd (Etempvar _p tulong)
                                            (Etempvar _match_len tulong)
                                            tulong) (tptr tuchar)) tuchar))
                                    (Sset _t'1
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _t'3 tuchar)
                                          (Etempvar _t'4 tuchar) tint) tbool))))
                                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                              (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
                            (Sset _match_len
                              (Ebinop Oadd (Etempvar _match_len tulong)
                                (Econst_int (Int.repr 1) tint) tulong)))
                          Sskip)
                        (Ssequence
                          (Sifthenelse (Ebinop Ole
                                         (Econst_int (Int.repr 3) tint)
                                         (Etempvar _match_len tulong) tint)
                            (Sset _t'2
                              (Ecast
                                (Ebinop Olt (Etempvar _best_len tuchar)
                                  (Etempvar _match_len tulong) tint) tbool))
                            (Sset _t'2 (Econst_int (Int.repr 0) tint)))
                          (Sifthenelse (Etempvar _t'2 tint)
                            (Ssequence
                              (Sset _best_len
                                (Ecast (Etempvar _match_len tulong) tuchar))
                              (Sset _best_off
                                (Ecast
                                  (Ebinop Osub (Etempvar _p tulong)
                                    (Etempvar _i tulong) tulong) tushort)))
                            Sskip)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tulong)
                      (Econst_int (Int.repr 1) tint) tulong))))
              (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 3) tint)
                             (Etempvar _best_len tuchar) tint)
                (Ssequence
                  (Sassign (Ederef (Etempvar _len (tptr tulong)) tulong)
                    (Etempvar _best_len tuchar))
                  (Sassign (Ederef (Etempvar _off (tptr tulong)) tulong)
                    (Etempvar _best_off tushort)))
                (Ssequence
                  (Sassign (Ederef (Etempvar _len (tptr tulong)) tulong)
                    (Econst_int (Int.repr 0) tint))
                  (Sassign (Ederef (Etempvar _off (tptr tulong)) tulong)
                    (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_compress := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_in, (tptr tuchar)) :: (_in_len, tulong) :: nil);
  fn_vars := ((_len, tulong) :: (_off, tulong) :: nil);
  fn_temps := ((_out_len, tulong) :: (_out, (tptr tuchar)) ::
               (_out_i, tulong) :: (_in_i, tulong) :: (_flag, tuchar) ::
               (_token_count, tuchar) :: (_flag_i, tulong) ::
               (_len_opt, tulong) :: (_off_opt, tulong) :: (_t'7, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, (tptr tvoid)) ::
               (_t'12, tulong) :: (_t'11, tulong) :: (_t'10, tulong) ::
               (_t'9, tuchar) :: (_t'8, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _out_len
    (Ebinop Oadd
      (Ebinop Odiv
        (Ebinop Oadd
          (Ebinop Omul (Econst_int (Int.repr 9) tint)
            (Etempvar _in_len tulong) tulong) (Econst_int (Int.repr 7) tint)
          tulong) (Econst_int (Int.repr 8) tint) tulong)
      (Econst_int (Int.repr 65) tint) tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                               cc_default))
        ((Etempvar _out_len tulong) :: nil))
      (Sset _out (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tuchar))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _encode_length (Tfunction (tulong :: (tptr tuchar) :: nil)
                                 tulong cc_default))
          ((Etempvar _in_len tulong) :: (Etempvar _out (tptr tuchar)) :: nil))
        (Sset _out_i (Etempvar _t'2 tulong)))
      (Ssequence
        (Sset _in_i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Ssequence
          (Sset _flag (Ecast (Econst_int (Int.repr 0) tint) tuchar))
          (Ssequence
            (Sset _token_count (Ecast (Econst_int (Int.repr 0) tint) tuchar))
            (Ssequence
              (Sset _flag_i (Etempvar _out_i tulong))
              (Ssequence
                (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                               (Etempvar _in_len tulong) tint)
                  (Sset _out_i
                    (Ebinop Oadd (Etempvar _out_i tulong)
                      (Econst_int (Int.repr 1) tint) tulong))
                  Sskip)
                (Ssequence
                  (Swhile
                    (Ebinop Olt (Etempvar _in_i tulong)
                      (Etempvar _in_len tulong) tint)
                    (Ssequence
                      (Sassign (Evar _len tulong)
                        (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign (Evar _off tulong)
                          (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Scall None
                            (Evar _find_largest_match (Tfunction
                                                        ((tptr tuchar) ::
                                                         tulong :: tulong ::
                                                         (tptr tulong) ::
                                                         (tptr tulong) ::
                                                         nil) tvoid
                                                        cc_default))
                            ((Etempvar _in (tptr tuchar)) ::
                             (Etempvar _in_len tulong) ::
                             (Etempvar _in_i tulong) ::
                             (Eaddrof (Evar _len tulong) (tptr tulong)) ::
                             (Eaddrof (Evar _off tulong) (tptr tulong)) ::
                             nil))
                          (Ssequence
                            (Ssequence
                              (Sset _t'8 (Evar _len tulong))
                              (Sifthenelse (Ebinop Ole
                                             (Econst_int (Int.repr 3) tint)
                                             (Etempvar _t'8 tulong) tint)
                                (Ssequence
                                  (Sset _flag
                                    (Ecast
                                      (Ebinop Oshl (Etempvar _flag tuchar)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tuchar))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'12 (Evar _len tulong))
                                      (Sset _len_opt
                                        (Ebinop Osub (Etempvar _t'12 tulong)
                                          (Econst_int (Int.repr 3) tint)
                                          tulong)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'11 (Evar _off tulong))
                                        (Sset _off_opt
                                          (Ebinop Osub
                                            (Etempvar _t'11 tulong)
                                            (Econst_int (Int.repr 3) tint)
                                            tulong)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'3
                                              (Etempvar _out_i tulong))
                                            (Sset _out_i
                                              (Ebinop Oadd
                                                (Etempvar _t'3 tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong)))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _out (tptr tuchar))
                                                (Etempvar _t'3 tulong)
                                                (tptr tuchar)) tuchar)
                                            (Ebinop Oor
                                              (Ebinop Oshl
                                                (Etempvar _len_opt tulong)
                                                (Econst_int (Int.repr 4) tint)
                                                tulong)
                                              (Ecast
                                                (Ebinop Oshr
                                                  (Etempvar _off_opt tulong)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tulong) tuchar) tulong)))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'4
                                                (Etempvar _out_i tulong))
                                              (Sset _out_i
                                                (Ebinop Oadd
                                                  (Etempvar _t'4 tulong)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tulong)))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _out (tptr tuchar))
                                                  (Etempvar _t'4 tulong)
                                                  (tptr tuchar)) tuchar)
                                              (Ecast
                                                (Etempvar _off_opt tulong)
                                                tuchar)))
                                          (Ssequence
                                            (Sset _t'10 (Evar _len tulong))
                                            (Sset _in_i
                                              (Ebinop Oadd
                                                (Etempvar _in_i tulong)
                                                (Etempvar _t'10 tulong)
                                                tulong))))))))
                                (Ssequence
                                  (Sset _flag
                                    (Ecast
                                      (Ebinop Oor
                                        (Ebinop Oshl (Etempvar _flag tuchar)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tuchar))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'5
                                            (Etempvar _out_i tulong))
                                          (Sset _out_i
                                            (Ebinop Oadd
                                              (Etempvar _t'5 tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong)))
                                        (Sset _t'6 (Etempvar _in_i tulong)))
                                      (Sset _in_i
                                        (Ebinop Oadd (Etempvar _t'6 tulong)
                                          (Econst_int (Int.repr 1) tint)
                                          tulong)))
                                    (Ssequence
                                      (Sset _t'9
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _in (tptr tuchar))
                                            (Etempvar _t'6 tulong)
                                            (tptr tuchar)) tuchar))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _out (tptr tuchar))
                                            (Etempvar _t'5 tulong)
                                            (tptr tuchar)) tuchar)
                                        (Etempvar _t'9 tuchar)))))))
                            (Ssequence
                              (Sset _token_count
                                (Ecast
                                  (Ebinop Oadd (Etempvar _token_count tuchar)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tuchar))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _token_count tuchar)
                                             (Econst_int (Int.repr 8) tint)
                                             tint)
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _out (tptr tuchar))
                                        (Etempvar _flag_i tulong)
                                        (tptr tuchar)) tuchar)
                                    (Etempvar _flag tuchar))
                                  (Ssequence
                                    (Sset _flag
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tuchar))
                                    (Ssequence
                                      (Sset _token_count
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          tuchar))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Etempvar _out_i tulong))
                                          (Sset _out_i
                                            (Ebinop Oadd
                                              (Etempvar _t'7 tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong)))
                                        (Sset _flag_i (Etempvar _t'7 tulong))))))
                                Sskip)))))))
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                                   (Etempvar _token_count tuchar) tint)
                      (Ssequence
                        (Sset _flag
                          (Ecast
                            (Ebinop Oshl (Etempvar _flag tuchar)
                              (Ebinop Osub (Econst_int (Int.repr 8) tint)
                                (Etempvar _token_count tuchar) tint) tint)
                            tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _out (tptr tuchar))
                              (Etempvar _flag_i tulong) (tptr tuchar))
                            tuchar) (Etempvar _flag tuchar)))
                      Sskip)
                    (Sreturn (Some (Etempvar _out (tptr tuchar))))))))))))))
|}.

Definition f_decompress := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_in, (tptr tuchar)) :: (_in_len, tulong) :: nil);
  fn_vars := ((_out_len, tulong) :: nil);
  fn_temps := ((_in_i, tulong) :: (_out_i, tulong) ::
               (_out, (tptr tuchar)) :: (_flag, tuchar) ::
               (_token_count, tuchar) :: (_flag_i, tulong) ::
               (_b0, tuchar) :: (_b1, tuchar) :: (_len_opt, tuchar) ::
               (_off_hi, tuchar) :: (_off_lo, tuchar) :: (_len, tulong) ::
               (_off, tulong) :: (_k, tulong) :: (_t'8, tulong) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tint) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tulong) :: (_t'15, tulong) :: (_t'14, tulong) ::
               (_t'13, tuchar) :: (_t'12, tuchar) :: (_t'11, tuchar) ::
               (_t'10, tuchar) :: (_t'9, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _out_len tulong) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _decode_length (Tfunction
                               ((tptr tuchar) :: tulong :: (tptr tulong) ::
                                nil) tulong cc_default))
        ((Etempvar _in (tptr tuchar)) :: (Etempvar _in_len tulong) ::
         (Eaddrof (Evar _out_len tulong) (tptr tulong)) :: nil))
      (Sset _in_i (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _out_i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'15 (Evar _out_len tulong))
            (Scall (Some _t'2)
              (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                     cc_default))
              ((Etempvar _t'15 tulong) :: nil)))
          (Sset _out (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tuchar))))
        (Ssequence
          (Sset _flag (Ecast (Econst_int (Int.repr 0) tint) tuchar))
          (Ssequence
            (Sset _token_count (Ecast (Econst_int (Int.repr 0) tint) tuchar))
            (Ssequence
              (Sset _flag_i (Etempvar _out_i tulong))
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'14 (Evar _out_len tulong))
                        (Sifthenelse (Ebinop Olt (Etempvar _out_i tulong)
                                       (Etempvar _t'14 tulong) tint)
                          (Sset _t'3
                            (Ecast
                              (Ebinop Olt (Etempvar _in_i tulong)
                                (Etempvar _in_len tulong) tint) tbool))
                          (Sset _t'3 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'3 tint) Sskip Sbreak))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _token_count tuchar)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'4 (Etempvar _in_i tulong))
                              (Sset _in_i
                                (Ebinop Oadd (Etempvar _t'4 tulong)
                                  (Econst_int (Int.repr 1) tint) tulong)))
                            (Ssequence
                              (Sset _t'13
                                (Ederef
                                  (Ebinop Oadd (Etempvar _in (tptr tuchar))
                                    (Etempvar _t'4 tulong) (tptr tuchar))
                                  tuchar))
                              (Sset _flag
                                (Ecast (Etempvar _t'13 tuchar) tuchar))))
                          (Sset _token_count
                            (Ecast (Econst_int (Int.repr 8) tint) tuchar)))
                        Sskip)
                      (Ssequence
                        (Sifthenelse (Ebinop Oshr (Etempvar _flag tuchar)
                                       (Econst_int (Int.repr 7) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'5 (Etempvar _out_i tulong))
                                  (Sset _out_i
                                    (Ebinop Oadd (Etempvar _t'5 tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)))
                                (Sset _t'6 (Etempvar _in_i tulong)))
                              (Sset _in_i
                                (Ebinop Oadd (Etempvar _t'6 tulong)
                                  (Econst_int (Int.repr 1) tint) tulong)))
                            (Ssequence
                              (Sset _t'12
                                (Ederef
                                  (Ebinop Oadd (Etempvar _in (tptr tuchar))
                                    (Etempvar _t'6 tulong) (tptr tuchar))
                                  tuchar))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Etempvar _out (tptr tuchar))
                                    (Etempvar _t'5 tulong) (tptr tuchar))
                                  tuchar) (Etempvar _t'12 tuchar))))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'7 (Etempvar _in_i tulong))
                                (Sset _in_i
                                  (Ebinop Oadd (Etempvar _t'7 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))
                              (Ssequence
                                (Sset _t'11
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _in (tptr tuchar))
                                      (Etempvar _t'7 tulong) (tptr tuchar))
                                    tuchar))
                                (Sset _b0
                                  (Ecast (Etempvar _t'11 tuchar) tuchar))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'8 (Etempvar _in_i tulong))
                                  (Sset _in_i
                                    (Ebinop Oadd (Etempvar _t'8 tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)))
                                (Ssequence
                                  (Sset _t'10
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _in (tptr tuchar))
                                        (Etempvar _t'8 tulong) (tptr tuchar))
                                      tuchar))
                                  (Sset _b1
                                    (Ecast (Etempvar _t'10 tuchar) tuchar))))
                              (Ssequence
                                (Sset _len_opt
                                  (Ecast
                                    (Ebinop Oshr (Etempvar _b0 tuchar)
                                      (Econst_int (Int.repr 4) tint) tint)
                                    tuchar))
                                (Ssequence
                                  (Sset _off_hi
                                    (Ecast
                                      (Ebinop Oand (Etempvar _b0 tuchar)
                                        (Econst_int (Int.repr 15) tint) tint)
                                      tuchar))
                                  (Ssequence
                                    (Sset _off_lo
                                      (Ecast (Etempvar _b1 tuchar) tuchar))
                                    (Ssequence
                                      (Sset _len
                                        (Ecast
                                          (Ebinop Oadd
                                            (Etempvar _len_opt tuchar)
                                            (Econst_int (Int.repr 3) tint)
                                            tint) tulong))
                                      (Ssequence
                                        (Sset _off
                                          (Ecast
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Ebinop Oshl
                                                  (Etempvar _off_hi tuchar)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tint)
                                                (Etempvar _off_lo tuchar)
                                                tint)
                                              (Econst_int (Int.repr 3) tint)
                                              tint) tulong))
                                        (Ssequence
                                          (Sset _k
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              tulong))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _k tulong)
                                                             (Etempvar _len tulong)
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'9
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _out (tptr tuchar))
                                                        (Ebinop Osub
                                                          (Etempvar _out_i tulong)
                                                          (Etempvar _off tulong)
                                                          tulong)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _out (tptr tuchar))
                                                        (Etempvar _out_i tulong)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Etempvar _t'9 tuchar)))
                                                (Sset _out_i
                                                  (Ebinop Oadd
                                                    (Etempvar _out_i tulong)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tulong))))
                                            (Sset _k
                                              (Ebinop Oadd
                                                (Etempvar _k tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong))))))))))))
                        (Ssequence
                          (Sset _flag
                            (Ecast
                              (Ebinop Oshl (Etempvar _flag tuchar)
                                (Econst_int (Int.repr 1) tint) tint) tuchar))
                          (Sset _token_count
                            (Ecast
                              (Ebinop Osub (Etempvar _token_count tuchar)
                                (Econst_int (Int.repr 1) tint) tint) tuchar))))))
                  Sskip)
                (Sreturn (Some (Etempvar _out (tptr tuchar))))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc, Gfun(External EF_malloc (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_encode_length, Gfun(Internal f_encode_length)) ::
 (_decode_length, Gfun(Internal f_decode_length)) ::
 (_find_largest_match, Gfun(Internal f_find_largest_match)) ::
 (_compress, Gfun(Internal f_compress)) ::
 (_decompress, Gfun(Internal f_decompress)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _decompress :: _compress :: _find_largest_match ::
 _decode_length :: _encode_length :: _surely_malloc :: _exit :: _malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


