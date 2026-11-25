import Mathlib

/-!
# Statement (library copy)

The library's copies of the definitions in `Challenge.lean`, in the namespace
`AllEvenOnePlusFour` so that the library never imports the challenge file (which contains a
`sorry`). `AxiomsCheck.lean` proves by `Iff.rfl` that each copy agrees definitionally with the
challenge file's definition.
-/

open scoped ArithmeticFunction.Omega

namespace AllEvenOnePlusFour

/-- GRH for Dirichlet `L`-functions, copied verbatim from the upstream challenge file:
no `L(s, χ)` vanishes in `Re s > 1/2`. -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Every even `N ≥ 4` is `p + m` with `p` prime, `m ≥ 1` and `Ω m ≤ K`
(copy of `_root_.AllEvenPrimePlusAlmostPrime`). -/
def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

end AllEvenOnePlusFour
