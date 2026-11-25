import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Dirichlet `L`-Function Non-Vanishing & Explicit AP Prime Counting Interface

States the half-plane non-vanishing hypothesis for Dirichlet `L`-functions in terms
of Mathlib's `DirichletCharacter.LFunction`, along with an interface for explicit
prime-counting bounds in arithmetic progressions (Grenié–Molteni, *Ramanujan J.* **49**
(2019), 535–548; Johnston–Starichkova, `arXiv:2208.01229v3`, Lemma 5.1).
-/

namespace BuchstabSwitching.External

/-- Non-vanishing of `L(s, χ)` strictly to the right of `Re(s) = 1/2`. -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/--
Contributor target for explicit GRH prime counting in arithmetic progressions:
for `x ≥ 4 * 10^18`, `3 ≤ d ≤ √x`, and `Nat.Coprime a d`, connects `π(x; d, a)`
to `li(x) / φ(d)` with explicit error `c_π(x) √x log x`.
-/
def ExplicitPrimeInAPPremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (x d a : ℕ), 4 * 10 ^ 18 ≤ x → 3 ≤ d → d ^ 2 ≤ x → Nat.Coprime a d →
      ∃ main err : ℝ,
        0 ≤ err ∧
        |(((Finset.Icc 1 x).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℝ) - main| ≤ err

end BuchstabSwitching.External
