report:
	# pandoc 'Formal Verification of the LZ77 and LZ78 Compression Algorithms.md' --pdf-engine=lualatex -o report.pdf
	pandoc 'Formal Verification of the LZ77 and LZ78 Compression Algorithms.md' -o report.pdf

clean:
	rm -f *.pdf


