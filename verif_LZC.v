Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import LZC.
Require Import LZ LZ_Matching LZ_Tokens Utils.
Require Import Stdlib.Strings.Byte.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
    WITH t:type, gv: globals
    PRE [ tuint ]
      PROP (0 <= sizeof t <= Int64.max_unsigned;
            complete_legal_cosu_type t = true;
            natural_aligned natural_alignment t = true)
      PARAMS (Vlong (Int64.repr (sizeof t))) GLOBALS (gv)
      SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
      PROP ()
      RETURN (p)
      SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

