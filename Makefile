.PHONY: rocq clean

ROCQC=rocq compile
CC=clightgen -normalize

rocq:
	$(ROCQC) Utils.v
	$(ROCQC) LZ_Matching.v
	$(ROCQC) LZ_Tokens.v
	$(ROCQC) LZ.v
	$(CC) LZC.c
	$(ROCQC) LZC.v
	$(ROCQC) verif_LZC.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache

