import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! Verbatim challenge copies of `canonicalLi2` and `meisselMertensConst`
(`External/NumericalConstants/CanonicalDefs.lean`). -/

namespace BuchstabSwitching.External

noncomputable def canonicalLi2 : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log 2) +
    ∑' k : ℕ, (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))

noncomputable def meisselMertensConst : ℝ :=
  Real.eulerMascheroniConstant +
    ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))

end BuchstabSwitching.External
