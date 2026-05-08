.PHONY: rocq clean

ROCQC=rocq compile
CC=clightgen -normalize

rocq:
	$(ROCQC) LZ_Dict.v
	$(ROCQC) LZ_Tokens.v
	$(ROCQC) LZ.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache

