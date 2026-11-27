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

  What is PROVED here (Lean kernel, `decide +kernel`; no `sorry`, no `native_decide`,
  no extra axioms):  `not_rep_1433987797`, `not_rep_45483661477`, `not_rep_85305551767`,
  `not_rep_367084269651`, `not_rep_1572650032347`, `sunConjecture_false`, and the small facts
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

/-! ### The five counterexamples (kernel-checked) -/

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
#print axioms SunA157225.sunConjecture_false
#print axioms SunA157225.least_of_sieve
