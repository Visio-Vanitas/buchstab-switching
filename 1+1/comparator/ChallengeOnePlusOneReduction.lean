import ChallengeOnePlusOneDefs
import ChallengeOnePlusOnePremises
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Comparator Challenge Spec for `OnePlusOne`

Declares the exact theorem signatures exported by `OnePlusOne` (`theorem_1A_all_even_exceptional_set`,
`theorem_1B_all_even_short_interval`, unconditional arithmetic & dyadic/short-interval reductions)
with `:= sorry` so `lake comparator` can verify that the compiled `OnePlusOne` binary exports
identical theorem types using strictly `[propext, Quot.sound, Classical.choice]`, and reject
the self-challenge containing `sorryAx`.
-/

namespace OnePlusOne

namespace Arithmetic

open scoped BigOperators

theorem major_arcs_disjoint {Y : ℝ} (hY : 4 ≤ Y)
    {q q' : ℕ} {a a' : ℤ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hqY : (q : ℝ) ≤ Real.sqrt Y / 2)
    (hq'Y : (q' : ℝ) ≤ Real.sqrt Y / 2)
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / (2 * (q : ℝ) * Real.sqrt Y) + 1 / (2 * (q' : ℝ) * Real.sqrt Y) ≤
      |(a : ℝ) / q - (a' : ℝ) / q'| := by
  sorry

theorem ratio_2p_sub_1_le_pow_eighth {p : ℝ} (hp : 271 ≤ p) :
    ((2 * p - 1) / (p - 1)) ^ 8 ≤ p := by
  sorry

theorem twin_prime_partial_product_ge (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ 2 < p) :
    (0.65928 : ℝ) < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  sorry

theorem totient_sq_ge_half {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) / 2 ≤ (q.totient : ℝ) ^ 2 := by
  sorry

theorem dyadic_geom_sum_lt (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 / Real.sqrt 2) ^ k < 2 + Real.sqrt 2 := by
  sorry

theorem fouradic_geom_sum_lt (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ k < 2 := by
  sorry

end Arithmetic

namespace Exceptional

theorem exceptional_all_range_of_dyadic
    (hbase : EmpiricalGoldbachBase)
    {C_dyad : ℝ} (hC : 0 ≤ C_dyad)
    (hdyad : ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 2) : ℝ) ≤
        C_dyad * Real.sqrt Y * (Real.log Y) ^ 3) :
    ExceptionalSetProp ((2 + Real.sqrt 2) * C_dyad) 3 := by
  sorry

theorem exceptional_all_range_of_fouradic
    (hbase : EmpiricalGoldbachBase)
    {C_4adic : ℝ} (hC : 0 ≤ C_4adic)
    (hfour : ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ) ≤
        C_4adic * Real.sqrt Y * (Real.log Y) ^ 3) :
    ExceptionalSetProp (2 * C_4adic) 3 := by
  sorry

end Exceptional

namespace ShortInterval

theorem short_interval_all_range
    (hbase : EmpiricalGoldbachBase)
    (hlarge : ∀ X : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X →
      ∃ N : ℕ, X ≤ (N : ℝ) ∧ (N : ℝ) ≤ X + 8 * (Real.log X) ^ 2 ∧ IsGoldbachEven N) :
    ShortIntervalProp 8 2 := by
  sorry

end ShortInterval

namespace Linnik

def linnikBridge18 : ℕ := (2 ^ 19 - 2) * 2 ^ 61 + 4 * 10 ^ 18

theorem binary_goldbach_bridge_18
    (hbase : EmpiricalGoldbachBase)
    {N : ℕ} (hEven : Even N) (hLo : 40 ≤ N) (hHi : N ≤ linnikBridge18) :
    HasExactPosLinnikRep 18 N := by
  sorry

theorem all_even_exact_linnik_18
    (hbase : EmpiricalGoldbachBase)
    (hlarge : ∀ N : ℕ, linnikBridge18 < N → Even N → HasExactPosLinnikRep 18 N) :
    AllEvenExactLinnikAbove 18 := by
  sorry

theorem all_even_linnik_18
    (hbase : EmpiricalGoldbachBase)
    (hlarge : ∀ N : ℕ, linnikBridge18 < N → Even N → HasExactPosLinnikRep 18 N) :
    AllEvenLinnikProp 18 := by
  sorry

end Linnik

theorem theorem_1A_all_even_exceptional_set
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    ExceptionalSetProp 16 3 := by
  sorry

theorem theorem_1B_all_even_short_interval
    (hRH : RiemannHypothesis)
    (hPrem : External.OnePlusOnePremises) :
    ShortIntervalProp 8 2 := by
  sorry

theorem theorem_3A_all_even_exact_linnik_18
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    AllEvenExactLinnikAbove 18 := by
  sorry

theorem theorem_3_all_even_linnik_goldbach
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPrem : External.OnePlusOnePremises) :
    AllEvenLinnikProp 18 := by
  sorry

end OnePlusOne
