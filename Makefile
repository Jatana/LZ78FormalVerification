.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) Utils.v
	$(ROCQC) LZ_Matching.v
	$(ROCQC) LZ_Expand.v
	$(ROCQC) LZ_Tokens.v
	$(ROCQC) LZ.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache

