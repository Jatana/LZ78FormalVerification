.PHONY: rocq clean

ROCQC=rocq compile

rocq:
	$(ROCQC) LZ.v

clean:
	rm -f *.vo* *.glob *.aux .*.aux .*.cache
