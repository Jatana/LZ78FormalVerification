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

{ABSTRACT}
- LZ77 and LZ78 are the backbones of many widely used compressions algorithms.
- We modeled and proved the correctness of both along with upper bounds on the compressed length.
- Originally we proposed verification of low-level C implementation using VST which ended
  up being too time-consuming even for simple properties.


**Keywords:** Formal verification, Lempel-Ziv, LZ77, LZ78, functional correctness, data compression.

# Introduction

{INTRODUCTION}
- Brief repetition of motivation.
- Basics of LZ77
- Basics of LZ78
- Problem statement and Goal.

# Approach

{APPROACH}
- Some LZ77 implementation details:
    - Token definition and reasoning.
    - Compression to tokens.
    - Tokens to bytes (mainly the chunk ones).
    - Upper bound strategy (with token weights)
- Some LZ78 implementation details:
    - Token and Dict definitions and reasoning.
    - Upper bound reasoning.
- Design choices and challenges:
    - Fueled structural recursion for termination.
    - Tokens as intermediate step (two passes).

# Results

{RESULTS}
- LZ77:
    - Main correctness lemmas.
    - Upper bound lemma.
- LZ78:
    - Main correctness lemmas.
    - Upper bound lemmas.
- Limitations:
    - VST Verification:
        - Give all the reasons and stuff we tried.
    - If any admitted lemmas remain, we state them here with maybe where they are used and why we believe they are correct.

# Timeline

{TIMELINE}
- Copy the main ideas from [EdStem](https://edstem.org/eu/courses/3024/discussion/229004)
- Short summary of contribution.

# Related work

{RELATED WORK}
- Mainly [lean-zip](https://github.com/kim-em/lean-zip)

#  Future work

{FUTURE WORK}
- Define LZ77 in a more VST friendly way, and prove equivalence.
- Rewrite of easy extraction, currently the extraction is very bad.
- We showed end-to-end correctness, and nothing about the intermediate states...

# Conclusion

{CONCLUSION}
- Repeat first point of abstract again.
- Strong foundation for future work.
- Successfully proved correctness and upper bound.

# AI use disclosure

{AI USE DISCLOSURE}
- Alexander Shekhovtsov
    - ...
- Ozair Faizan
    - ...
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
---

