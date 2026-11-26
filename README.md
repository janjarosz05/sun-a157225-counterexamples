# Two new counterexamples to a conjecture of Zhi-Wei Sun (OEIS A157225)

**Jan Jarosz, 26 November 2026**

[OEIS A157225](https://oeis.org/A157225) counts the ways to write the odd number `2n-1` as

    p + 2^x + 7*2^y,    p prime, p ≡ 5 (mod 6),    x, y ≥ 1.

Zhi-Wei Sun conjectured in 2009 that every odd `m > 20` other than 25, 31 and 1983 has such a
representation. The conjecture was disproved in August 2026 by one counterexample,
`m = 1433987797` (T. Adamczewski, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941)).

This repository gives two more:

| m | n = (m+1)/2 | status |
|---|---|---|
| 1 433 987 797 | 716 993 899 | known, re-proved here |
| **45 483 661 477** | 22 741 830 739 | new |
| **85 305 551 767** | 42 652 775 884 | new |

"New" means: not on the OEIS page as of 26 November 2026 and not known to me from any other source.

## What is proved and what is not

- **Proved (Lean 4 kernel):** none of the three numbers has a representation, hence the conjecture
  is false. No `sorry`, no `native_decide`; axioms used: `propext`, `Quot.sound`.
- **Computed, not proved:** an exhaustive bit-sieve finds no other counterexample below 10^11.
  In the Lean file this is only a named hypothesis (`SieveComplete`), and the theorems
  "1433987797 is the least counterexample" and "these are exactly the three below 10^11" are
  conditional on it.
- **Open:** whether there are infinitely many counterexamples.

## Files

- [`Sun_A157225_two_new_counterexamples.pdf`](Sun_A157225_two_new_counterexamples.pdf): the note
  (statement, proof, method, full certificates in the appendix).
- [`SunA157225.lean`](SunA157225.lean): the formal proof (Lean 4.35.0 + Mathlib).
- [`certificates/`](certificates): one CSV per number with a line `x,y,r,d` for every cell
  `(x, y)` that survives the mod 6 filter; `d` is the least prime factor of
  `r = m - 2^x - 7*2^y`.
- [`search/sieve2k.c`](search/sieve2k.c): the sieve. [`search/verify.py`](search/verify.py): an
  independent check with SymPy.
- [`paper/`](paper): LaTeX source of the note.

## Check it yourself

Lean (the first build downloads the Mathlib cache; the file itself takes well under a minute):

    lake exe cache get
    lake build

Python (checks every cell of the three numbers, then all odd m < 200000):

    pip install sympy
    python3 search/verify.py

Sieve up to 10^11 (about 75 s on 4 cores, needs about 2 GB of RAM):

    gcc -O3 -march=native -fopenmp search/sieve2k.c -o sieve2k -lm
    ./sieve2k 5 100000000000 7

Expected sieve output: the small exceptions 1, 3, ..., 19, 25, 31, 1983 and the three numbers above.

## Why the proof is short

All three numbers are ≡ 1 (mod 6). Then `r ≡ 5 (mod 6)` forces `x` and `y` to be both even, which
removes three quarters of the cells. Each remaining `r` (271 and 287 of them for the new numbers)
has a prime factor below 300000, listed in the certificates.
