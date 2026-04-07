.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) StringsModule.v
	$(ROCQC) LZ.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache


