import Mathlib

/-! Challenge for the reduction, part 1: verbatim copies of the definitions in `AllEvenOnePlusFour/Statement.lean`. Kept in a separate module, as in the library, because Lean names the auxiliary proofs inside a definition per module and Comparator compares them by name. -/

open scoped ArithmeticFunction.Omega

namespace AllEvenOnePlusFour

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

end AllEvenOnePlusFour
