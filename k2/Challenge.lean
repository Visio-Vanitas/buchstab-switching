import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Challenge: every even `N ≥ 4` is a prime plus a `P₂`, under GRH

This file depends on Mathlib only. It follows the convention of the upstream
`https://github.com/lsernau/grh-lean` formalisation (commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, file `grh-compact/src/Statements.lean`): it states
definitions and the theorem to be compared, and the theorem is closed by `sorry`. The `sorry`
is the statement under discussion, **not** a claimed proof. Nothing else in this project imports
this file except `AxiomsCheckK2.lean`, which checks that the library's copies of the definitions
agree with these ones definitionally.

The four GRH-type propositions below are copied verbatim from `lsernau/grh-lean`
(`grh-compact/src/Statements.lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`), where
`LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` is proved.
-/

open scoped ArithmeticFunction.Omega

/-- Upstream (`lsernau/grh-lean`, verbatim): every nontrivial zero of `ζ` other than the pole
lies on `Re s = 1/2`. -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- Upstream (`lsernau/grh-lean`, verbatim): no Dirichlet `L`-function vanishes in `Re s > 1/2`
(GRH for Dirichlet `L`-functions, proved as `LFunction_ne_zero_of_half_lt_re`). -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Upstream (`lsernau/grh-lean`, verbatim): zeros of Dirichlet `L`-functions in the critical strip
lie on the critical line. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Upstream (`lsernau/grh-lean`, verbatim): the same, for primitive characters. -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- `AllEvenPrimePlusAlmostPrime K`: every even `N ≥ 4` can be written as `N = p + m` with `p`
prime, `m ≥ 1`, and `m` having at most `K` prime factors counted with multiplicity. -/
def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

/-- **Challenge statement (`1 + 2`).** Under GRH for Dirichlet `L`-functions, every even `N ≥ 4`
is a prime plus a positive integer with at most two prime factors counted with multiplicity.

This is a *statement*, not a proof: the `sorry` is the challenge-file convention. The
conditional reduction proved in this project is
`BuchstabSwitchingK2.all_even_one_plus_two_of_premises` (verified in `AxiomsCheckK2.lean`). -/
theorem all_even_one_plus_two (hGRH : DirichletLNonvanishingRightOfHalf) :
    AllEvenPrimePlusAlmostPrime 2 := by
  sorry
