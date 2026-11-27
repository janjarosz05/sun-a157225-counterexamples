# Kernel-checked counterexamples to a conjecture of Zhi-Wei Sun (OEIS A157225)

**Jan Jarosz, 26 November 2026 (revised 27 November 2026)**

[OEIS A157225](https://oeis.org/A157225) counts the ways to write the odd number `2n-1` as

    p + 2^x + 7*2^y,    p prime, p ≡ 5 (mod 6),    x, y ≥ 1.

Zhi-Wei Sun conjectured in 2009 that every odd `m > 20` other than 25, 31 and 1983 has such a
representation. The conjecture was disproved in August 2026 by one counterexample,
`m = 1433987797` (T. Adamczewski, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941)).

This repository contains Lean 4 proofs that seven numbers are counterexamples:

| m | n = (m+1)/2 | found by |
|---|---|---|
| 1 433 987 797 | 716 993 899 | Adamczewski (Aug 2026) |
| 45 483 661 477 | 22 741 830 739 | Yotam Moshe (26 Nov 2026); independently here |
| 85 305 551 767 | 42 652 775 884 | Yotam Moshe (26 Nov 2026); independently here |
| 367 084 269 651 | 183 542 134 826 | Yotam Moshe (26 Nov 2026) |
| 1 572 650 032 347 | 786 325 016 174 | Yotam Moshe (26 Nov 2026) |
| **15 429 013 109 983** | 7 714 506 554 992 | this repository (27 Nov 2026) |
| **16 170 736 674 691** | 8 085 368 337 346 | this repository (27 Nov 2026) |

The last two lie beyond Moshe's stated search bound of 10^13. They were found on 27 November 2026
by the segmented sieve [`search/seg2k.c`](search/seg2k.c), which has so far covered
10^13 ≤ m < 2.7·10^13 exhaustively (search in progress). I know of no earlier source for them,
but I could not read pending OEIS drafts automatically, so treat "first found here" as provisional.
The PDF note still describes the first five only.

## Priority (correction, 27 November 2026)

The first version of this repository called the second and third numbers "new". That was wrong.
Yotam Moshe had proposed them (together with the last two, from a search below 10^13) as an edit
to the OEIS entry on 26 November 2026 at 07:25 UTC, a few hours before I found them with a sieve
up to 10^11. Pending OEIS edits are not shown on the published page, which is why I missed it.
Priority for all four belongs to Moshe. What this repository adds is the formal verification.

## What is proved and what is not

- **Proved (Lean 4 kernel):** none of the seven numbers has a representation, hence the conjecture
  is false. No `sorry`, no `native_decide`; axioms used: `propext`, `Quot.sound`.
- **Computed, not proved:** my exhaustive bit-sieve finds no other counterexample below 10^11
  (hypothesis `SieveComplete` in the Lean file). Moshe reports none other below 10^13
  (hypothesis `SearchComplete13`; I have not re-run that search). Theorems such as
  "1433987797 is the least counterexample" are conditional on these hypotheses.
- **Open:** whether there are infinitely many counterexamples.

## Files

- [`Sun_A157225_counterexamples.pdf`](Sun_A157225_counterexamples.pdf): the note
  (statement, proof, method, full certificates in the appendix).
- [`SunA157225.lean`](SunA157225.lean): the formal proof (Lean 4.35.0 + Mathlib).
- [`certificates/`](certificates): one CSV per number with a line `x,y,r,d` for every cell
  `(x, y)` that survives the mod 6 filter; `d` is the least prime factor of
  `r = m - 2^x - 7*2^y`.
- [`search/sieve2k.c`](search/sieve2k.c): the sieve below 10^11. [`search/seg2k.c`](search/seg2k.c): segmented sieve for larger ranges
  (`./seg2k A B`; every survivor of the bit-sieve is re-checked exactly with a deterministic Miller-Rabin test). [`search/verify.py`](search/verify.py): an
  independent check with SymPy.
- [`paper/`](paper): LaTeX source of the note.

## Check it yourself

Lean (the first build downloads the Mathlib cache; the file itself takes a few minutes at most):

    lake exe cache get
    lake build

Python (checks every cell of the seven numbers, then all odd m < 200000):

    pip install sympy
    python3 search/verify.py

Sieve up to 10^11 (about 75 s on 4 cores, needs about 2 GB of RAM):

    gcc -O3 -march=native -fopenmp search/sieve2k.c -o sieve2k -lm
    ./sieve2k 5 100000000000 7

Expected sieve output: the small exceptions 1, 3, ..., 19, 25, 31, 1983 and the first three numbers above.

## Why the proofs are short

The first three numbers are ≡ 1 (mod 6); then `r ≡ 5 (mod 6)` forces `x` and `y` to be both even.
The last two are ≡ 3 (mod 6), which forces both to be odd. Either way three quarters of the cells
disappear. Each remaining `r` (between 194 and 380 of them per number) has a prime factor below
1.2 million, listed in the certificates.
