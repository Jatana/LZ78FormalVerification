---
title: |
  Formal Verification of the LZ77 and LZ78 Compression Algorithms
subtitle: |
  CS-428 project report
author:
  - "Alexander Shekhovtsov"
  - "Ozair Faizan"
  - "Clément Tsedri"
date: "2026-05-31"

documentclass: scrartcl
classoption: a4paper, twocolumn, DIV=calc
mainfont: "Libertinus Serif"
sansfont: "Libertinus Sans"
mathfont: "Libertinus Math"
monofont: "Fira Code"
---

<!--
# How to use this template

1. Rename this template to `<Your group id> - <Your project title>.md`.

2. Make sure that this document compiles without errors with `pandoc <your document>.txt --pdf-engine=lualatex -o template.pdf`.

3. Replace all `{}` blocks in this template with your own content.  Use `[@citation_id]` syntax for citations (for example~[@rocq91]), and `[^footnote]` syntax for footnotes (for example[^foo]).

4. Delete this section.

[^foo]: Here's a footnote!

--->

# Abstract

Lempel-Ziv compression algorithms (LZ77 and LZ78) are the backbone of many widely used compression
algorithms, including DEFLATE, gzip, and zip.
In this project, we modeled and formally proved the functional correctness of both algorithms in
Rcoq, alongside upper bounds on their worst-case compressed output lengths.
Originally we proposed verification of low-level C implementation using
[VST](https://github.com/PrincetonUniversity/VST), however, verifying low-level memory operations
and pointer arithmetic in VST is excessively time-consuming even for simple array manipulations,
leading us to focus only on the high-level functional correctness.

**Keywords:** Formal verification, Lempel-Ziv, LZ77, LZ78, functional correctness, data compression.


# Introduction

Data compression is widely-used in day-to-day and security-sensitive applications, yet its
correctness often relies on manual testing rather than formal verification. 

## LZ77
The LZ77 (Lempel-Ziv'77) algorithm operates over a sliding window of previously seen bytes. During
compression, the algorithm scans the input and, at each position, searches the window for the
longest match to the upcoming bytes. If a match of length at least 3 is found, it emits a reference
token `(length, offset)`, where offset is the distance to the start of the match in the window.
Otherwise, it emits a literal token containing the current byte.
These references are encoded into two bytes using 4 bits for the length and 12 bits for the offset,
therefore, they are limited to the range $[3, 18]$ and $[3, 4098]$ respectively.

## LZ78
LZ78 takes a dictionary-based approach. It maintains an explicit dictionary of previously seen byte
sequences, starting with a single empty entry. At each step, the algorithm finds the longest prefix
of the remaining input that already appears in the dictionary, then emits a token `(index,
next_byte)` pointing to that dictionary entry and the following byte. The concatenation of the
matched prefix and the new byte is then added to the dictionary.

## Problem Statement
The goal of this project is to prove an end-to-end correctness theorem: for all byte sequences `s`,
`decompress (compress s) = s` and an upper bound on the compressed output size.


# Approach (2 pages)

Both implementations share a common architecture. Compression proceeds in two passes, in the first
pass, the input byte sequence is converted to a list of abstract tokens and in the second pass, the
token list is serialized to bytes. Decompression reverses these steps. This two-level design cleanly
separates the compression logic from the byte encoding and simplifies the reasoning.

## LZ77 Implementation Details

- Token definition and reasoning.
- Compression to tokens.
- Tokens to bytes (mainly the chunk ones).
- Upper bound strategy (with token weights)

## LZ78 Implementation Details

- Token and Dict definitions and reasoning.
- Upper bound reasoning.

## Design Choices and Challenges

- Fueled structural recursion for termination.
- Tokens as intermediate step (two passes).


# Results (3/4 page)

## LZ77 Correctness

## LZ77 Upper Bound

## LZ78 Correctness

## LZ78 Upper Bounds

## Limitations
### VST Verification

- Give all the reasons and stuff we tried.

### Admitted Lemmas

- If any admitted lemmas remain, we state them here with maybe where they are used and why we believe they are correct.


# Timeline
The project started out strong, with the proofs of LZ77 correctness and upper bound done a week
earlier than planned. Then, we had 3 weeks (originally 2) to prove the correctness of our C
implementation, however, after dedicating two weeks to VST without viable progress, we made the
decision to pivot our scope. We reallocated our remaining schedule to formally model and prove the
correctness of the LZ78 algorithm instead.

- Short summary of contribution.


# Related work

Our project closely aligns with existing verification efforts in the data compression, most notably
[lean-zip](https://github.com/kim-em/lean-zip) which is an implementation and verification of the
LZ77 algorithm and DEFLATE standard written in Lean 4.
Our work differs in targeting both LZ77 and LZ78 in Rocq, and providing concrete upper bounds on
compressed size.

There is a [catalog of
examples](https://github.com/PrincetonUniversity/VST/blob/master/doc/catalog-of-examples.md) of
VST-based verifications, most notably, [@VSTSHA]. These projects confirm the significant cost of
VST-based verification, consistent with our experience.


#  Future work

This formalization provides a foundation for serveral directions.

## VST
Define an LZ77 implementation in a more VST-friendly style and prove equivalence with the functional
Rocq model. The equivalence proof would then transfer our correctness and bound results to the C
implementation.

## Intermediate State Invariants
Our proofs establish end-to-end correctness but say nothing about intermediate states during
compression or decompression. Proving invariants at each step would provide stronger guarantees
about correctness.

## Asymptotic Optimality
The Lempel-Ziv Optimality proof shows that LZ78 is asymptotically optimal and achieves the entropy
rate of stationary ergodic sources. Formalizing this proof would be a significant theoretical
contribution.


# Conclusion

We have presented machine-checked proofs for the correctness of our implementations of LZ77 and LZ78
compression algorithms. We additionally prove concrete upper bounds on compressed sizes.

The formalization demonstrates that a two-pass architecture (compression to tokens, then token
serialization to bytes) is well-suited to formal verification as it cleanly separates concerns and
allows independent proofs at each level.

Our experience with VST suggests that verifying a low-level C implementation of LZ77 is feasible but
requires substantially more effort than the functional formalization.

This work provides a solid, foundation for Lempel-Ziv compression that can serve as a basis for
further verification of compression-related software, including C implementations, streaming
variants, and higher-level algorithms built on the LZ family.


# AI use disclosure

- Alexander Shekhovtsov
    - ...
- Ozair Faizan
    - The LLMs are capable of proving some simple lemmas, however, for more challenging proofs it
    fails.
    - Nevertheless, they were quite helpful for pen and paper proofs and brainstorming ideas.
    - Help with (re)writing of this report.
- Clément Tsedri
    - ...


# References

---
references:
  - id: rocq91
    DOI: 10.5281/zenodo.17473943
    title: "The Rocq Prover"
    author:
      - literal: "The Rocq Development Team"
    issued:
      date-parts: [[2025, 09, 15]]
    publisher: Zenodo
    type: software
    version: 9.1.0
  - id: VSTSHA
    DOI: 10.1145/2701415
    title: "Verification of a Cryptographic Primitive: SHA-256"
    author: "Appel, Andrew"
    issued:
      data-parts: [2015, 04]
    journal: "ACM Transactions on Programming Languages and Systems"
---

