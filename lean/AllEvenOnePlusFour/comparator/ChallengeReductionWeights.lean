import Mathlib

/-! Challenge for the reduction, part 2: verbatim copies of the definitions in `AllEvenOnePlusFour/Weights.lean` (separate module for the same reason). -/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace AllEvenOnePlusFour

noncomputable def switchPrimes (z y : ℝ) (a : ℕ) : Finset ℕ :=
  {q ∈ a.primeFactors | z ≤ q ∧ (q : ℝ) < y}

noncomputable def squareSwitchPrimes (z y : ℝ) (a : ℕ) : Finset ℕ :=
  {q ∈ switchPrimes z y a | q ^ 2 ∣ a}

noncomputable def weight (z y : ℝ) (a : ℕ) : ℝ :=
  1 - (((switchPrimes z y a).card : ℝ) + ((squareSwitchPrimes z y a).card : ℝ)) / 2

end AllEvenOnePlusFour
