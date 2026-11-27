/-
  Kernel-checked counterexamples to Zhi-Wei Sun's conjecture in OEIS A157225
  Jan Jarosz (Prime LMM project, series OB1), 26 November 2026; revised 27 November 2026.

  A157225: a(n) = number of ways to write the n-th positive odd integer 2n-1 as
      p + 2^x + 7 * 2^y,   p prime, p ≡ 5 (mod 6),   x, y ≥ 1.
  Conjecture (Z.-W. Sun, 24 Feb 2009): a(n) = 0 iff n < 11 or n ∈ {13, 16, 992};
  equivalently every odd m > 20 other than 25, 31, 1983 has such a representation.

  Status. The conjecture was disproved in August 2026 (T. Adamczewski, arXiv:2608.11941)
  by m = 1433987797 (n = 716993899).  On 26 Nov 2026 Yotam Moshe proposed on the OEIS page four
  further counterexamples, from a search of all odd m < 10^13:
      m = 45483661477    (n = 22741830739),
      m = 85305551767    (n = 42652775884),
      m = 367084269651   (n = 183542134826),
      m = 1572650032347  (n = 786325016174).
  The first two were found independently by us a few hours later the same day (sieve up to 10^11);
  priority for all four is Moshe's.  This file contributes formal proofs of all five.

  On 27 Nov 2026 our segmented sieve (`search/seg2k.c`), run on 10^13 <= m < 2.7*10^13, found two
  more, beyond Moshe's stated search bound of 10^13:
      m = 15429013109983  (n = 7714506554992),
      m = 16170736674691  (n = 8085368337346).
      m = 35009488862317  (n = 17504744431159),
      m = 96561420011947  (n = 48280710005974)   [search of 10^13 .. 10^14 still in progress].
  They are proved below as well.  We do not know of an earlier source for these.

  What is PROVED here (Lean kernel, `decide +kernel`; no `sorry`, no `native_decide`,
  no extra axioms):  `not_rep_1433987797`, `not_rep_45483661477`, `not_rep_85305551767`,
  `not_rep_367084269651`, `not_rep_1572650032347`, `not_rep_15429013109983`,
  `not_rep_16170736674691`, `not_rep_35009488862317`, `not_rep_96561420011947`,
  `sunConjecture_false`, and the small facts
  in the last section.

  What is NOT proved here and is stated only as a named hypothesis (`Prop`):
  `SieveComplete` (our bit-sieve found no other odd m < 10^11 without a representation),
  `SearchComplete13` (Moshe's reported search: no others below 10^13; not re-run by us) and
  `InfinitelyMany` (open question).  Theorems that use them take them as explicit arguments.

  Lean 4 (v4.35.0) + Mathlib (v4.35.0).
-/
import Mathlib

namespace SunA157225

/-- `Rep m`: m = p + 2^x + 7·2^y with p prime, p ≡ 5 (mod 6), x, y ≥ 1. -/
def Rep (m : ℕ) : Prop :=
  ∃ p x y : ℕ, p.Prime ∧ p % 6 = 5 ∧ 1 ≤ x ∧ 1 ≤ y ∧ m = p + 2 ^ x + 7 * 2 ^ y

/-- Sun's conjecture for A157225, in the "odd integer" form. -/
def SunConjecture : Prop :=
  ∀ m : ℕ, m % 2 = 1 → 20 < m → m ≠ 25 → m ≠ 31 → m ≠ 1983 → Rep m

/-! ### The certificate checker -/

/-- A cell (x, y) is dead if r = m − 2^x − 7·2^y is not ≡ 5 (mod 6) or has a proper divisor
taken from the list `L`.  Cells with 2^x + 7·2^y ≥ m are vacuous. -/
def cellOK (m : ℕ) (L : List ℕ) (x y : ℕ) : Bool :=
  if 1 ≤ x ∧ 1 ≤ y ∧ 2 ^ x + 7 * 2 ^ y < m then
    let r := m - (2 ^ x + 7 * 2 ^ y)
    (r % 6 != 5) || L.any (fun d => decide (1 < d) && decide (d < r) && (r % d == 0))
  else true

/-- All cells with x, y < N are dead. -/
def check (m N : ℕ) (L : List ℕ) : Bool :=
  (List.range N).all fun x => (List.range N).all fun y => cellOK m L x y

theorem lt_of_pow_le {x N m : ℕ} (h1 : 2 ^ x ≤ m) (h2 : m < 2 ^ N) : x < N := by
  by_contra h
  have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt h)
  omega

/-- Soundness of the checker: if m < 2^N and every cell is dead, m has no representation. -/
theorem not_rep_of_check (m N : ℕ) (L : List ℕ) (hm : m < 2 ^ N)
    (h : check m N L = true) : ¬ Rep m := by
  rintro ⟨p, x, y, hp, hR, hx, hy, he⟩
  have hp2 := hp.two_le
  have hx2 : 2 ^ x ≤ m := by
    rw [he]; exact Nat.le_trans (Nat.le_add_left (2 ^ x) p) (Nat.le_add_right _ _)
  have hxN : x < N := lt_of_pow_le hx2 hm
  have hy1 : 2 ^ y ≤ 7 * 2 ^ y := Nat.le_mul_of_pos_left _ (by decide)
  have hy2 : 7 * 2 ^ y ≤ m := by rw [he]; exact Nat.le_add_left _ _
  have hyN : y < N := lt_of_pow_le (Nat.le_trans hy1 hy2) hm
  unfold check at h
  rw [List.all_eq_true] at h
  have hx' := h x (List.mem_range.mpr hxN)
  rw [List.all_eq_true] at hx'
  have hc := hx' y (List.mem_range.mpr hyN)
  have hlt : 2 ^ x + 7 * 2 ^ y < m := by omega
  have hr : m - (2 ^ x + 7 * 2 ^ y) = p := by omega
  unfold cellOK at hc
  simp only [hx, hy, hlt, and_self, ite_true, hr] at hc
  rcases Bool.or_eq_true_iff.mp hc with h6 | hd
  · simp [hR] at h6
  · rcases List.any_eq_true.mp hd with ⟨d, _, hd⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hd
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h3) with h | h <;> omega

/-! ### The nine counterexamples (kernel-checked) -/

/-- Adamczewski's counterexample (Aug 2026), n = 716993899: 807 cells, 40 divisors. -/
theorem not_rep_1433987797 : ¬ Rep 1433987797 :=
  not_rep_of_check 1433987797 31 [5, 7, 11, 13, 17, 19, 23, 31, 37, 41, 43, 47, 53, 59, 79, 83, 89, 103, 109, 113, 157, 163, 239, 281, 359, 367, 373, 439, 479, 499, 631, 659, 877, 1753, 2543, 2617, 3167, 4219, 10159, 13313]
    (by decide +kernel) (by decide +kernel)

/-- n = 22741830739 (Moshe; independently OB1): 1117 cells, 60 divisors. -/
theorem not_rep_45483661477 : ¬ Rep 45483661477 :=
  not_rep_of_check 45483661477 36 [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 47, 53, 61, 67, 79, 83, 89, 97, 101, 107, 113, 131, 139, 163, 173, 179, 223, 227, 239, 241, 269, 277, 281, 313, 461, 479, 509, 563, 1163, 1249, 1433, 1447, 1733, 1747, 2113, 2389, 4159, 5653, 6619, 13163, 20897, 29131, 33563, 45869, 51229, 58997, 81181, 81517, 82571, 163883]
    (by decide +kernel) (by decide +kernel)

/-- n = 42652775884 (Moshe; independently OB1): 1185 cells, 66 divisors. -/
theorem not_rep_85305551767 : ¬ Rep 85305551767 :=
  not_rep_of_check 85305551767 37 [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 67, 79, 83, 89, 101, 103, 107, 109, 127, 131, 151, 157, 173, 179, 181, 211, 229, 241, 271, 277, 467, 757, 797, 821, 1867, 2011, 2351, 2797, 3533, 3593, 4229, 4483, 4673, 4931, 5261, 5849, 7901, 8167, 8839, 9437, 11251, 13229, 14753, 20483, 21961, 35053, 68059, 85469, 151531, 163433, 231131, 292057]
    (by decide +kernel) (by decide +kernel)

/-- n = 183542134826 (Moshe 2026): 1327 cells, 73 divisors. -/
theorem not_rep_367084269651 : ¬ Rep 367084269651 :=
  not_rep_of_check 367084269651 39 [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 67, 71, 73, 79, 83, 89, 101, 103, 107, 127, 137, 139, 149, 157, 167, 179, 199, 223, 241, 283, 311, 331, 353, 367, 373, 383, 389, 401, 431, 523, 601, 673, 1303, 1367, 1433, 1531, 3767, 3989, 5821, 6991, 7691, 8101, 19333, 26431, 35507, 42683, 60077, 64901, 66533, 72823, 78643, 78721, 117577, 136343, 189983, 200591, 219809, 407437]
    (by decide +kernel) (by decide +kernel)

/-- n = 786325016174 (Moshe 2026): 1478 cells, 83 divisors. -/
theorem not_rep_1572650032347 : ¬ Rep 1572650032347 :=
  not_rep_of_check 1572650032347 41 [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53, 59, 67, 71, 73, 79, 83, 89, 97, 103, 109, 113, 131, 139, 157, 163, 167, 173, 179, 191, 193, 197, 233, 239, 257, 331, 337, 347, 509, 877, 1009, 1049, 1051, 1087, 1109, 1231, 1327, 1439, 1481, 1721, 2389, 3623, 3709, 3767, 5531, 6317, 6491, 6637, 6983, 7907, 11981, 17299, 38557, 95063, 109937, 144439, 181061, 188933, 197539, 231317, 244553, 263521, 427997, 495713, 513673, 556811, 559259, 762659, 969457, 1159993, 1173917]
    (by decide +kernel) (by decide +kernel)

/-- n = 7714506554992 (found 27 Nov 2026 by the segmented sieve `seg2k.c`, range 10^13 .. 2.7*10^13):
1754 cells, 69 divisors. -/
theorem not_rep_15429013109983 : ¬ Rep 15429013109983 :=
  not_rep_of_check 15429013109983 44 [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 43, 53, 59, 61, 67, 71, 83, 89, 107, 109, 113, 127, 131, 137, 139, 149, 157, 163, 173, 179, 181, 193, 197, 211, 241, 263, 307, 337, 379, 461, 673, 701, 797, 911, 1091, 2543, 2797, 2801, 2969, 3041, 6737, 8719, 9941, 10709, 16007, 17551, 62903, 107033, 402923, 539509, 645979, 679171, 700279, 1012789, 1063397, 1324261, 1362059, 1980101, 2322259]
    (by decide +kernel) (by decide +kernel)

/-- n = 8085368337346 (found 27 Nov 2026 by the segmented sieve `seg2k.c`, range 10^13 .. 2.7*10^13):
1758 cells, 100 divisors. -/
theorem not_rep_16170736674691 : ¬ Rep 16170736674691 :=
  not_rep_of_check 16170736674691 44 [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 79, 83, 89, 97, 103, 107, 113, 131, 137, 149, 163, 173, 191, 193, 197, 199, 211, 227, 263, 281, 293, 347, 367, 397, 431, 449, 541, 569, 571, 619, 641, 701, 719, 739, 881, 883, 1301, 1373, 1433, 1459, 1489, 1523, 1847, 1877, 2039, 3517, 4217, 4219, 4933, 4937, 5711, 6257, 6311, 8161, 9091, 9187, 9311, 9803, 10321, 10357, 15289, 18839, 21673, 22573, 24877, 26293, 28081, 29009, 32423, 51767, 75553, 78803, 114473, 130409, 131713, 138101, 139511, 197023, 496439, 772913, 1421969, 1518731, 1968569]
    (by decide +kernel) (by decide +kernel)

/-- n = 17504744431159 (found 27 Nov 2026 by the segmented sieve `seg2k.c`):
1845 cells, 92 divisors. -/
theorem not_rep_35009488862317 : ¬ Rep 35009488862317 :=
  not_rep_of_check 35009488862317 45 [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 83, 89, 101, 103, 113, 131, 137, 151, 163, 211, 227, 233, 263, 269, 277, 283, 293, 311, 313, 397, 409, 439, 443, 487, 499, 509, 751, 827, 839, 1013, 1117, 1303, 1399, 1499, 1511, 2539, 2861, 3313, 3467, 3943, 4289, 5557, 7487, 8563, 10343, 10837, 12011, 15241, 16217, 16631, 17747, 18217, 26863, 34259, 43669, 46751, 48247, 54767, 77983, 80621, 84247, 157081, 160723, 199399, 230863, 261467, 514741, 667643, 1113703, 1520527, 1834141, 1850413, 2308001]
    (by decide +kernel) (by decide +kernel)

/-- n = 48280710005974 (found 27 Nov 2026 by the segmented sieve `seg2k.c`):
1975 cells, 92 divisors. -/
theorem not_rep_96561420011947 : ¬ Rep 96561420011947 :=
  not_rep_of_check 96561420011947 47 [5, 7, 11, 13, 17, 19, 23, 29, 37, 43, 47, 53, 59, 61, 71, 83, 89, 107, 109, 113, 137, 139, 151, 167, 191, 193, 211, 223, 229, 239, 277, 293, 307, 331, 337, 421, 457, 523, 569, 571, 599, 647, 673, 773, 829, 853, 919, 971, 977, 1063, 1093, 1427, 1453, 1487, 1811, 1867, 1987, 2027, 2543, 3967, 4157, 4517, 4987, 5101, 5801, 7187, 7937, 13229, 16063, 21647, 27281, 37501, 38791, 125107, 192791, 250267, 374123, 444877, 492059, 602309, 960677, 961087, 1014593, 1810451, 1889191, 2219183, 2296487, 2498423, 2804377, 3652211, 5348669, 7646503]
    (by decide +kernel) (by decide +kernel)

/-- Sun's conjecture for A157225 is false (each of the five numbers refutes it). -/
theorem sunConjecture_false : ¬ SunConjecture := fun h =>
  not_rep_45483661477 (h 45483661477 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The set of counterexamples to the conjecture. -/
def Counter : Set ℕ := {m | m % 2 = 1 ∧ 1983 < m ∧ ¬ Rep m}

theorem mem_counter_1433987797 : 1433987797 ∈ Counter := ⟨by norm_num, by norm_num, not_rep_1433987797⟩
theorem mem_counter_45483661477 : 45483661477 ∈ Counter := ⟨by norm_num, by norm_num, not_rep_45483661477⟩
theorem mem_counter_85305551767 : 85305551767 ∈ Counter := ⟨by norm_num, by norm_num, not_rep_85305551767⟩
theorem mem_counter_367084269651 : 367084269651 ∈ Counter := ⟨by norm_num, by norm_num, not_rep_367084269651⟩
theorem mem_counter_1572650032347 : 1572650032347 ∈ Counter := ⟨by norm_num, by norm_num, not_rep_1572650032347⟩

/-! ### Hypotheses (computed or open; NOT proved in Lean) -/

/-- COMPUTATIONAL CLAIM (bit-sieve `sieve2k.c`, run twice, not kernel-checked): below 10^11
the only odd m > 1983 without a representation are the first three numbers above. -/
def SieveComplete : Prop :=
  ∀ m ∈ Counter, m < 10 ^ 11 → m = 1433987797 ∨ m = 45483661477 ∨ m = 85305551767

/-- REPORTED CLAIM (Y. Moshe, OEIS A157225 draft, 26 Nov 2026; not re-run by us, not
kernel-checked): below 10^13 the only counterexamples are the five numbers above. -/
def SearchComplete13 : Prop :=
  ∀ m ∈ Counter, m < 10 ^ 13 → m = 1433987797 ∨ m = 45483661477 ∨ m = 85305551767 ∨
    m = 367084269651 ∨ m = 1572650032347

/-- COMPUTATIONAL CLAIM (segmented sieve `seg2k.c`, 27 Nov 2026, one run, survivors re-checked
exactly; not kernel-checked): in 10^13 ≤ m < 10^14 the only counterexamples are these four. -/
def SearchWindow14 : Prop :=
  ∀ m ∈ Counter, 10 ^ 13 ≤ m → m < 10 ^ 14 → m = 15429013109983 ∨ m = 16170736674691 ∨
    m = 35009488862317 ∨ m = 96561420011947

/-- OPEN QUESTION: are there infinitely many counterexamples?  (We do not claim this.) -/
def InfinitelyMany : Prop := Counter.Infinite

/-! ### Conditional theorems -/

/-- If the sieve is right, Adamczewski's number is the least counterexample. -/
theorem least_of_sieve (H : SieveComplete) : IsLeast Counter 1433987797 := by
  refine ⟨mem_counter_1433987797, fun m hm => ?_⟩
  by_contra hlt
  rcases H m hm (by omega) with h | h | h <;> omega

/-- If the sieve is right, below 10^11 the counterexample set is exactly these three numbers. -/
theorem counter_below_of_sieve (H : SieveComplete) :
    {m | m ∈ Counter ∧ m < 10 ^ 11} = {1433987797, 45483661477, 85305551767} := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hm, hlt⟩; exact H m hm hlt
  · rintro (h | h | h) <;> subst h
    · exact ⟨mem_counter_1433987797, by norm_num⟩
    · exact ⟨mem_counter_45483661477, by norm_num⟩
    · exact ⟨mem_counter_85305551767, by norm_num⟩

/-- The 10^13 claim implies the 10^11 claim. -/
theorem sieve_of_search13 (H : SearchComplete13) : SieveComplete := by
  intro m hm hlt
  rcases H m hm (by omega) with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · omega
  · omega

/-- If both searches are right, there are exactly nine counterexamples below 10^14. -/
theorem counter_below_14_of_searches (H13 : SearchComplete13) (H14 : SearchWindow14)
    (m : ℕ) (hm : m ∈ Counter) (hlt : m < 10 ^ 14) :
    m = 1433987797 ∨ m = 45483661477 ∨ m = 85305551767 ∨ m = 367084269651 ∨
    m = 1572650032347 ∨ m = 15429013109983 ∨ m = 16170736674691 ∨ m = 35009488862317 ∨
    m = 96561420011947 := by
  by_cases h : m < 10 ^ 13
  · rcases H13 m hm h with h | h | h | h | h <;> simp [h]
  · rcases H14 m hm (by omega) hlt with h | h | h | h <;> simp [h]

/-- If there are infinitely many counterexamples, there is one beyond the largest known. -/
theorem exists_larger_of_infinite (H : InfinitelyMany) : ∃ m ∈ Counter, 1572650032347 < m :=
  H.exists_gt 1572650032347

/-! ### Small sanity facts (proved) -/

/-- Sun's three listed exceptions above 20 really have no representation. -/
theorem not_rep_25 : ¬ Rep 25 := not_rep_of_check 25 5 [] (by decide +kernel) (by decide +kernel)
theorem not_rep_31 : ¬ Rep 31 := not_rep_of_check 31 5 [] (by decide +kernel) (by decide +kernel)
theorem not_rep_1983 : ¬ Rep 1983 :=
  not_rep_of_check 1983 11 [5, 7, 11, 13, 17, 19, 29, 31, 37] (by decide +kernel) (by decide +kernel)

/-- OEIS example a(18) = 3: 35 = 17 + 2^2 + 7·2 = 5 + 2 + 7·2^2 = 5 + 2^4 + 7·2. -/
theorem rep_35 : Rep 35 := ⟨17, 2, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end SunA157225

#print axioms SunA157225.not_rep_45483661477
#print axioms SunA157225.not_rep_85305551767
#print axioms SunA157225.not_rep_1572650032347
#print axioms SunA157225.not_rep_15429013109983
#print axioms SunA157225.not_rep_16170736674691
#print axioms SunA157225.sunConjecture_false
#print axioms SunA157225.least_of_sieve
