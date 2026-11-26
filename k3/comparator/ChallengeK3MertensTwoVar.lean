import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Verbatim challenge copy of `MertensSumBounds` (`Sieve/MertensTwoVar.lean`). -/

namespace BuchstabSwitching

def MertensSumBounds (M0 : ℝ) (E_lo E_hi : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    Real.log (Real.log x) + M0 - E_lo x ≤
        (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / p) ∧
      (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / p) ≤
        Real.log (Real.log x) + M0 + E_hi x

end BuchstabSwitching
