import Mathlib

/-!
# Challenge: every even `N ≥ 4` is a prime plus a `P₄`, under GRH

This file depends on Mathlib only. It matches the Mathlib-only GRH statements of
`https://github.com/lsernau/grh-lean` (commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
files `grh-compact/src/Statements.lean` and `grh/src/Statements.lean`, where `src/Main.lean`
proves `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`; compare the
challenge-file convention in `grh-compact/Challenge.lean`): it states definitions and the theorem
to be compared, and the theorem is closed by `sorry`. The `sorry` is the statement under
discussion, **not** a claimed proof. Nothing else in this project imports this file except
`AxiomsCheck.lean`, which checks that the library's copies of the definitions agree with these
ones definitionally.

The four GRH-type propositions below match `grh-compact/src/Statements.lean` verbatim (bodies
unchanged; only docstrings are added). The upstream proofs (`src/Main.lean`) live in `grh-lean`.

`Ω` is `ArithmeticFunction.cardFactors`, the number of prime factors counted with
multiplicity, so `Ω 1 = 0` and `Ω 12 = 3`.
-/

open scoped ArithmeticFunction.Omega

/-- Upstream (verbatim): every nontrivial zero of `ζ` other than the pole lies on `Re s = 1/2`. -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- Upstream (verbatim): no Dirichlet `L`-function vanishes in `Re s > 1/2`
(GRH for Dirichlet `L`-functions, in the form used as the premise below). -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Upstream (verbatim): zeros of Dirichlet `L`-functions in the critical strip lie on the
critical line. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Upstream (verbatim): the same, for primitive characters. -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- `AllEvenPrimePlusAlmostPrime K`: every even `N ≥ 4` can be written as `N = p + m` with `p`
prime, `m ≥ 1`, and `m` having at most `K` prime factors counted with multiplicity.

Note that `m = 1` is allowed and has `Ω 1 = 0`; this matches the source note (`η = 1` needs no
exclusion). -/
def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

/-- **Challenge statement.** Under GRH for Dirichlet `L`-functions, every even `N ≥ 4` is a
prime plus a positive integer with at most four prime factors counted with multiplicity.

This is a *statement*, not a proof: the `sorry` is the challenge-file convention. The
conditional reduction proved in this project is
`AllEvenOnePlusFour.all_even_one_plus_four_of_conditionalInputs`. -/
theorem all_even_one_plus_four (hGRH : DirichletLNonvanishingRightOfHalf) :
    AllEvenPrimePlusAlmostPrime 4 := by
  sorry
