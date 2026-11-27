import BuchstabSwitchingK2.Sieve.ChenSwitching
import Mathlib.Tactic

/-!
# Weighted Quadratic & Cubic Combinatorial Switching (`-w₁ + w₂ - w₃ + w₄ - w_B - w_sq`)

Generalizes `WeightedSmoothedSwitching` to full quadratic + cubic strip-indexed switching
weights `(w₁z, w₁q, w₂, w₃, w₄, w_B, w_sq)` over shifted primes `p ∈ sievedShifted N z`:
1. `divisiblePairCofactorSieved`, `divisibleTripleCofactorSieved`, `divisibleSquareSieved`:
   exact cofactor-sieved prime-pair, triple, and square-divisor filtered sets;
2. `weightedQuadSwitchingBalance1p2`: full rational `-w₁ + w₂ - w₃ + w₄ - w_B - w_sq` balance;
3. `weightedQuadSwitchingBalance_abstract_le_sum_good` and
   `exists_prime_add_omegaMult_le_two_of_weighted_quad_switching_pos`:
   deterministic `Ω(N - p) ≤ 2` lower bound from pointwise combinatorial dominance on
   `sievedShifted N z` (`0 ≤ mult(p)` for `Ω(N - p) ≤ 2` and `1 ≤ mult(p)` for `3 ≤ Ω(N - p)`).
-/

namespace BuchstabSwitchingK2

open scoped BigOperators

section WeightedQuadraticSwitching

/-- Cofactor-sieved prime-shift set at `(q₁, q₂)` up to cutoff `z₂`:
primes `p < N` coprime to `N` with `q₁ * q₂ ∣ N - p` whose cofactor `(N - p) / (q₁ * q₂)`
has no `P_N(z₂)` prime divisors. -/
def divisiblePairCofactorSieved (N z₂ q₁ q₂ : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p =>
    q₁ * q₂ ∣ N - p ∧
      ∀ r ∈ Finset.range z₂, r.Prime → ¬ r ∣ N → ¬ r ∣ ((N - p) / (q₁ * q₂)))

/-- Cofactor-sieved prime-shift set at triple `(q₁, q₂, q₃)` up to cutoff `z₃`. -/
def divisibleTripleCofactorSieved (N z₃ q₁ q₂ q₃ : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p =>
    q₁ * q₂ * q₃ ∣ N - p ∧
      ∀ r ∈ Finset.range z₃, r.Prime → ¬ r ∣ N → ¬ r ∣ ((N - p) / (q₁ * q₂ * q₃)))

/-- Square-divisor sieved prime-shift set `(sievedShifted N zSq).filter (q^2 ∣ N - p)`. -/
def divisibleSquareSieved (N zSq q : ℕ) : Finset ℕ :=
  (sievedShifted N zSq).filter (fun p => q ^ 2 ∣ N - p)

/-- Primes `q ∈ [q₀, q₁)` not dividing `N`. -/
def stripCoprimePrimes (N q₀ q₁ : ℕ) : Finset ℕ :=
  (Finset.Ico q₀ q₁).filter (fun q => q.Prime ∧ ¬ q ∣ N)

/-- Ordered coprime prime pairs `(q₁, q₂)` with `q₁ ∈ I_i`, `q₂ ∈ I_j`, `q₁ < q₂`. -/
def stripOrderedPairs (N : ℕ) (q₀ q₁ : ℕ → ℕ) (i j : ℕ) : Finset (ℕ × ℕ) :=
  ((stripCoprimePrimes N (q₀ i) (q₁ i)) ×ˢ (stripCoprimePrimes N (q₀ j) (q₁ j))).filter
    (fun pr => pr.1 < pr.2)

/-- Ordered coprime prime triples `(q₁, q₂, q₃)` with `q₁ < q₂ < q₃` across strips `a, b, c`. -/
def stripOrderedTriples (N : ℕ) (q₀ q₁ : ℕ → ℕ) (a b c : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((stripCoprimePrimes N (q₀ a) (q₁ a)) ×ˢ
    ((stripCoprimePrimes N (q₀ b) (q₁ b)) ×ˢ (stripCoprimePrimes N (q₀ c) (q₁ c)))).filter
    (fun tr => tr.1 < tr.2.1 ∧ tr.2.1 < tr.2.2)

/-- Concrete weighted quadratic/cubic switching balance combining `+S(A_N, z)`,
`-S₁` (with cutoffs `z` and `z₁`), `+S₂` (lower-bound cofactor sieved at `z₂`),
`-S₃` (upper-bound cofactor sieved at `z₃`), `+S₄` (lower-bound triple cofactor sieved at `z₄`),
`-B` (on `bTriples N z y`), and `-S_sq`. -/
def weightedQuadSwitchingBalance1p2
    (w : ℕ → ℚ) (N z y : ℕ) (k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (z1q : ℕ → ℕ)
    (w2 : ℕ → ℕ → ℚ) (z2 : ℕ → ℕ → ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (z3 : ℕ → ℕ → ℕ → ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (z4 : ℕ → ℕ → ℕ → ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ)
    (wSq : ℕ → ℚ) (zSq : ℕ → ℕ) : ℚ :=
  (∑ p ∈ sievedShifted N z, w p)
    - ∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
        ∑ p ∈ divisibleSievedShifted N z q, w p
    - ∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
        ∑ p ∈ divisibleSievedShifted N (z1q i) q, w p
    + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
        w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
          ∑ p ∈ divisiblePairCofactorSieved N (z2 i j) pr.1 pr.2, w p
    - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
          ∑ p ∈ divisibleTripleCofactorSieved N (z3 a b c) tr.1 tr.2.1 tr.2.2, w p
    + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
          ∑ p ∈ divisibleTripleCofactorSieved N (z4 a b c) tr.1 tr.2.1 tr.2.2, w p
    - ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
        wB a b c * ∑ t ∈ (bTriples N z y).filter (fun t =>
          q₀ a ≤ t.1 ∧ t.1 < q₁ a ∧ q₀ b ≤ t.2.1 ∧ t.2.1 < q₁ b ∧ q₀ c ≤ t.2.2 ∧ t.2.2 < q₁ c),
            w (N - t.1 * t.2.1 * t.2.2)
    - ∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
        ∑ p ∈ divisibleSquareSieved N (zSq i) q, w p

/-- Pointwise multiplicity count induced by any nested family of rational
divisibility/triple penalties attached to `p ∈ sievedShifted N z`. -/
def pointwisePenaltySum
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ)
    (N k : ℕ) (q₀ q₁ : ℕ → ℕ) (p : ℕ) : ℚ :=
  (∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
      if p ∈ S1z i q then (1 : ℚ) else 0)
    + (∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
        if p ∈ S1q i q then (1 : ℚ) else 0)
    - (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
        w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
          if p ∈ S2 i j pr.1 pr.2 then (1 : ℚ) else 0)
    + (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
          if p ∈ S3 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0)
    - (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
        w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
          if p ∈ S4 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0)
    + (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
        wB a b c * if p ∈ SB a b c then (1 : ℚ) else 0)
    + (∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
        if p ∈ SSq i q then (1 : ℚ) else 0)

private lemma sum_filter_le_sum_of_nonneg {A : Finset ℕ} (T : Finset ℕ) (w : ℕ → ℚ)
    (hw : ∀ n, 0 ≤ w n) :
    ∑ p ∈ A, (if p ∈ T then w p else 0) ≤ ∑ p ∈ T, w p := by
  rw [← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p _ _ => hw p)

private lemma sum_filter_eq_sum_of_subset {A : Finset ℕ} (T : Finset ℕ) (w : ℕ → ℚ)
    (hTA : T ⊆ A) :
    ∑ p ∈ A, (if p ∈ T then w p else 0) = ∑ p ∈ T, w p := by
  rw [← Finset.sum_filter]
  have hEq : A.filter (· ∈ T) = T := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hTA h, h⟩⟩
  rw [hEq]

private lemma sum_Fubini_strip1 {A : Finset ℕ} (w : ℕ → ℚ) (hw : ∀ n, 0 ≤ w n)
    (N k : ℕ) (q₀ q₁ : ℕ → ℕ) (c : ℕ → ℚ) (hc : ∀ i, 0 ≤ c i) (S : ℕ → ℕ → Finset ℕ) :
    (∑ p ∈ A, (∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
        if p ∈ S i q then (1 : ℚ) else 0) * w p) ≤
      ∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
        ∑ p ∈ S i q, w p := by
  have hswap1 :
      (∑ p ∈ A, (∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
          if p ∈ S i q then (1 : ℚ) else 0) * w p) =
        ∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
          ∑ p ∈ A, if p ∈ S i q then w p else 0 := by
    have hpt : ∀ p ∈ A,
        (∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S i q then (1 : ℚ) else 0) * w p =
          ∑ i ∈ Finset.range k, c i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S i q then w p else 0 := by
      intro p _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  rw [hswap1]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hc i)
  exact Finset.sum_le_sum fun q _ => sum_filter_le_sum_of_nonneg (S i q) w hw

/-- General deterministic quadratic switching pinch: if every non-negative shifted prime
`p ∈ sievedShifted N z` with `0 < w p` satisfies `0 ≤ mult(p)` (non-overcounting on
`Ω(N - p) ≤ 2`, which allows `r = 2` semiprime subtraction) and `1 ≤ mult(p)` whenever
`3 ≤ omegaMult (N - p)`, and every added `+w₂` set lies inside `sievedShifted N z`, then the
weighted quadratic switching balance lower-bounds `∑_{p ∈ goodRepresentations2 N} w p`. -/
theorem weightedQuadSwitchingBalance_abstract_le_sum_good
    (w : ℕ → ℚ) (N z : ℕ) (hw : ∀ n : ℕ, 0 ≤ w n)
    (k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ)
    (hw1z : ∀ i, 0 ≤ w1z i) (hw1q : ∀ i, 0 ≤ w1q i)
    (_hw2 : ∀ i j, 0 ≤ w2 i j)
    (hw3 : ∀ a b c, 0 ≤ w3 a b c)
    (_hw4 : ∀ a b c, 0 ≤ w4 a b c)
    (hwB : ∀ a b c, 0 ≤ wB a b c)
    (hwSq : ∀ i, 0 ≤ wSq i)
    (hS2_sub : ∀ i j q₁' q₂', S2 i j q₁' q₂' ⊆ sievedShifted N z)
    (hS4_sub : ∀ a b c q₁' q₂' q₃', S4 a b c q₁' q₂' q₃' ⊆ sievedShifted N z)
    (hgood_nonneg : ∀ p ∈ sievedShifted N z, omegaMult (N - p) ≤ 2 → 0 < w p →
      (0 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p)
    (hbad_dom : ∀ p ∈ sievedShifted N z, ¬ omegaMult (N - p) ≤ 2 → 0 < w p →
      (1 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p) :
    (∑ p ∈ sievedShifted N z, w p)
      - ∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1z i q, w p
      - ∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1q i q, w p
      + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
          w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, w p
      - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, w p
      + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, w p
      - ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
          wB a b c * ∑ p ∈ SB a b c, w p
      - ∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ SSq i q, w p
    ≤ ∑ p ∈ goodRepresentations2 N, w p := by
  set A := sievedShifted N z
  set Agood := A.filter (fun p => omegaMult (N - p) ≤ 2)
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  set M := pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁
  have hsplit : (∑ p ∈ Agood, w p) + (∑ p ∈ Abad, w p) = ∑ p ∈ A, w p :=
    Finset.sum_filter_add_sum_filter_not A (fun p => omegaMult (N - p) ≤ 2) w
  have hAgood_sub : Agood ⊆ goodRepresentations2 N := by
    intro p hp
    have hpA := (Finset.mem_filter.mp hp).1
    have hp_le := (Finset.mem_filter.mp hp).2
    have hp_cop := (Finset.mem_filter.mp hpA).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp_cop).1, (Finset.mem_filter.mp hp_cop).2.1, hp_le⟩
  have hgood_le : ∑ p ∈ Agood, w p ≤ ∑ p ∈ goodRepresentations2 N, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hAgood_sub (fun p _ _ => hw p)
  have hbad_pt : ∀ p ∈ Abad, w p ≤ M p * w p := by
    intro p hp
    rcases eq_or_lt_of_le (hw p) with h0 | hpos
    · rw [← h0, mul_zero]
    · have hp' := Finset.mem_filter.mp hp
      exact le_mul_of_one_le_left hpos.le (hbad_dom p hp'.1 hp'.2 hpos)
  have hA_nn : ∀ p ∈ A, 0 ≤ M p * w p := by
    intro p hpA
    rcases eq_or_lt_of_le (hw p) with h0 | hpos
    · rw [← h0, mul_zero]
    · by_cases hle2 : omegaMult (N - p) ≤ 2
      · exact mul_nonneg (hgood_nonneg p hpA hle2 hpos) hpos.le
      · exact mul_nonneg (le_trans zero_le_one (hbad_dom p hpA hle2 hpos)) hpos.le
  have hbad_sum : ∑ p ∈ Abad, w p ≤ ∑ p ∈ A, M p * w p := by
    calc
      ∑ p ∈ Abad, w p ≤ ∑ p ∈ Abad, M p * w p := Finset.sum_le_sum hbad_pt
      _ ≤ ∑ p ∈ A, M p * w p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp _ => hA_nn p hp)
  have hM_expand :
      (∑ p ∈ A, M p * w p) =
        (∑ p ∈ A, (∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
            if p ∈ S1z i q then (1 : ℚ) else 0) * w p)
          + (∑ p ∈ A, (∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
              if p ∈ S1q i q then (1 : ℚ) else 0) * w p)
          - (∑ p ∈ A, (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
              w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
                if p ∈ S2 i j pr.1 pr.2 then (1 : ℚ) else 0) * w p)
          + (∑ p ∈ A, (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
              w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
                if p ∈ S3 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0) * w p)
          - (∑ p ∈ A, (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
              w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
                if p ∈ S4 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0) * w p)
          + (∑ p ∈ A, (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
              wB a b c * if p ∈ SB a b c then (1 : ℚ) else 0) * w p)
          + (∑ p ∈ A, (∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i),
              if p ∈ SSq i q then (1 : ℚ) else 0) * w p) := by
    simp only [M, pointwisePenaltySum, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1z := sum_Fubini_strip1 (A := A) w hw N k q₀ q₁ w1z hw1z S1z
  have h1q := sum_Fubini_strip1 (A := A) w hw N k q₀ q₁ w1q hw1q S1q
  have hsq := sum_Fubini_strip1 (A := A) w hw N k q₀ q₁ wSq hwSq SSq
  have h2eq :
      (∑ p ∈ A, (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
          w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
            if p ∈ S2 i j pr.1 pr.2 then (1 : ℚ) else 0) * w p) =
        ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
          w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, w p := by
    have hpt : ∀ p ∈ A,
        (∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
              if p ∈ S2 i j pr.1 pr.2 then (1 : ℚ) else 0) * w p =
          ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j,
              if p ∈ S2 i j pr.1 pr.2 then w p else 0 := by
      intro p _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun pr _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun pr _ => ?_
    exact sum_filter_eq_sum_of_subset (S2 i j pr.1 pr.2) w (hS2_sub i j pr.1 pr.2)
  have h3le :
      (∑ p ∈ A, (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
            if p ∈ S3 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0) * w p) ≤
        ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, w p := by
    have hpt : ∀ p ∈ A,
        (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ S3 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0) * w p =
          ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ S3 a b c tr.1 tr.2.1 tr.2.2 then w p else 0 := by
      intro p _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun tr _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_le_mul_of_nonneg_left ?_ (hw3 a b c)
    exact Finset.sum_le_sum fun tr _ => sum_filter_le_sum_of_nonneg (S3 a b c tr.1 tr.2.1 tr.2.2) w hw
  have h4eq :
      (∑ p ∈ A, (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
            if p ∈ S4 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0) * w p) =
        ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
          w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, w p := by
    have hpt : ∀ p ∈ A,
        (∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ S4 a b c tr.1 tr.2.1 tr.2.2 then (1 : ℚ) else 0) * w p =
          ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c,
              if p ∈ S4 a b c tr.1 tr.2.1 tr.2.2 then w p else 0 := by
      intro p _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun tr _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun tr _ => ?_
    exact sum_filter_eq_sum_of_subset (S4 a b c tr.1 tr.2.1 tr.2.2) w
      (hS4_sub a b c tr.1 tr.2.1 tr.2.2)
  have hBle :
      (∑ p ∈ A, (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
          wB a b c * if p ∈ SB a b c then (1 : ℚ) else 0) * w p) ≤
        ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
          wB a b c * ∑ p ∈ SB a b c, w p := by
    have hpt : ∀ p ∈ A,
        (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            wB a b c * if p ∈ SB a b c then (1 : ℚ) else 0) * w p =
          ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            wB a b c * if p ∈ SB a b c then w p else 0 := by
      intro p _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_filter_le_sum_of_nonneg (SB a b c) w hw) (hwB a b c)
  rw [hM_expand] at hbad_sum
  linarith

/-- Strictly positive abstract quadratic switching balance yields a representation
`p + m = N` with `p` prime and `omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_weighted_quad_switching_pos
    (w : ℕ → ℚ) (N z : ℕ) (hw : ∀ n : ℕ, 0 ≤ w n)
    (k : ℕ) (q₀ q₁ : ℕ → ℕ)
    (w1z w1q : ℕ → ℚ) (S1z S1q : ℕ → ℕ → Finset ℕ)
    (w2 : ℕ → ℕ → ℚ) (S2 : ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w3 : ℕ → ℕ → ℕ → ℚ) (S3 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (w4 : ℕ → ℕ → ℕ → ℚ) (S4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ)
    (wB : ℕ → ℕ → ℕ → ℚ) (SB : ℕ → ℕ → ℕ → Finset ℕ)
    (wSq : ℕ → ℚ) (SSq : ℕ → ℕ → Finset ℕ)
    (hw1z : ∀ i, 0 ≤ w1z i) (hw1q : ∀ i, 0 ≤ w1q i)
    (_hw2 : ∀ i j, 0 ≤ w2 i j)
    (hw3 : ∀ a b c, 0 ≤ w3 a b c)
    (_hw4 : ∀ a b c, 0 ≤ w4 a b c)
    (hwB : ∀ a b c, 0 ≤ wB a b c)
    (hwSq : ∀ i, 0 ≤ wSq i)
    (hS2_sub : ∀ i j q₁' q₂', S2 i j q₁' q₂' ⊆ sievedShifted N z)
    (hS4_sub : ∀ a b c q₁' q₂' q₃', S4 a b c q₁' q₂' q₃' ⊆ sievedShifted N z)
    (hgood_nonneg : ∀ p ∈ sievedShifted N z, omegaMult (N - p) ≤ 2 → 0 < w p →
      (0 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p)
    (hbad_dom : ∀ p ∈ sievedShifted N z, ¬ omegaMult (N - p) ≤ 2 → 0 < w p →
      (1 : ℚ) ≤ pointwisePenaltySum w1z w1q S1z S1q w2 S2 w3 S3 w4 S4 wB SB wSq SSq N k q₀ q₁ p)
    (hpos : 0 <
      (∑ p ∈ sievedShifted N z, w p)
        - ∑ i ∈ Finset.range k, w1z i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1z i q, w p
        - ∑ i ∈ Finset.range k, w1q i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ S1q i q, w p
        + ∑ i ∈ Finset.range k, ∑ j ∈ Finset.Ico i k,
            w2 i j * ∑ pr ∈ stripOrderedPairs N q₀ q₁ i j, ∑ p ∈ S2 i j pr.1 pr.2, w p
        - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w3 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S3 a b c tr.1 tr.2.1 tr.2.2, w p
        + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.Ico a k, ∑ c ∈ Finset.Ico b k,
            w4 a b c * ∑ tr ∈ stripOrderedTriples N q₀ q₁ a b c, ∑ p ∈ S4 a b c tr.1 tr.2.1 tr.2.2, w p
        - ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.Ico a (k + 1), ∑ c ∈ Finset.Ico b (k + 1),
            wB a b c * ∑ p ∈ SB a b c, w p
        - ∑ i ∈ Finset.range k, wSq i * ∑ q ∈ stripCoprimePrimes N (q₀ i) (q₁ i), ∑ p ∈ SSq i q, w p) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hle := weightedQuadSwitchingBalance_abstract_le_sum_good w N z hw k q₀ q₁ w1z w1q S1z S1q
    w2 S2 w3 S3 w4 S4 wB SB wSq SSq hw1z hw1q _hw2 hw3 _hw4 hwB hwSq hS2_sub hS4_sub hgood_nonneg hbad_dom
  have hsum_pos : (0 : ℚ) < ∑ p ∈ goodRepresentations2 N, w p := lt_of_lt_of_le hpos hle
  have hex : ∃ p ∈ goodRepresentations2 N, 0 < w p := by
    by_contra hall
    push Not at hall
    have hsum_nonpos : ∑ p ∈ goodRepresentations2 N, w p ≤ 0 := Finset.sum_nonpos hall
    linarith
  rcases hex with ⟨p, hp, _⟩
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact ⟨p, N - p, hp'.2.1, hp'.2.2, Nat.add_sub_cancel' (le_of_lt hpN)⟩

end WeightedQuadraticSwitching

end BuchstabSwitchingK2
