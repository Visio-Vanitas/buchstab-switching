import ChallengeReductionStatement
import ChallengeReductionWeights

/-!
# Challenge for what the library proves: the reduction

`Challenge.lean` states `all_even_one_plus_four` (GRH implies that every even `N ≥ 4` is a prime
plus a `P₄`). The library does **not** prove that theorem: it proves it from explicit analytic
hypotheses (`AnalyticInputs`, `ConditionalInputs`). This file states exactly that reduction, so
that Comparator can check it. It depends on Mathlib only, through the two challenge modules it imports.

Every definition here and in those two modules is a verbatim copy (docstrings dropped) of the
library definition of the same name in `AllEvenOnePlusFour/Statement.lean`, `Weights.lean` and
`Reduction.lean`, split into modules the same way. Comparator
compares the challenge's constants with the solution's by name and rejects any difference, so
nothing here has to be trusted beyond reading the two theorem statements and the definitions they
use. The `sorry`s are the challenge-file convention, not proofs.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace AllEvenOnePlusFour

def IsSifted (N : ℕ) (z : ℝ) (a : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < z → ¬ q ∣ N → ¬ q ∣ a

open Classical in
noncomputable def siftedPrimes (N : ℕ) (z : ℝ) : Finset ℕ :=
  {p ∈ Finset.range N | p.Prime ∧ ¬ p ∣ N ∧ IsSifted N z (N - p)}

noncomputable def weightedSum (N : ℕ) (z y : ℝ) : ℝ :=
  ∑ p ∈ siftedPrimes N z, weight z y (N - p)

def GoldbachUpTo (B : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → N ≤ B → Even N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N = p + q

def WeightedSievePositiveOn (S : Set ℕ) : Prop :=
  ∀ N ∈ S, Even N → ∃ z y : ℝ, (N : ℝ) ≤ z * y ^ 4 ∧ (N : ℝ) < y ^ 5 ∧ 0 < weightedSum N z y

def goldbachBound : ℕ := 4 * 10 ^ 18

def tailStart : ℕ := 10 ^ 500

structure AnalyticInputs : Prop where
  regime1 : GoldbachUpTo goldbachBound
  regime2 : WeightedSievePositiveOn (Set.Ico goldbachBound tailStart)
  regime3 : WeightedSievePositiveOn (Set.Ici tailStart)

structure ConditionalInputs : Prop where
  regime1 : GoldbachUpTo goldbachBound
  regime2 : DirichletLNonvanishingRightOfHalf →
    WeightedSievePositiveOn (Set.Ico goldbachBound tailStart)
  regime3 : DirichletLNonvanishingRightOfHalf → WeightedSievePositiveOn (Set.Ici tailStart)

theorem all_even_one_plus_four_of_inputs (h : AnalyticInputs) :
    AllEvenPrimePlusAlmostPrime 4 := by
  sorry

theorem all_even_one_plus_four_of_conditionalInputs (h : ConditionalInputs)
    (hGRH : DirichletLNonvanishingRightOfHalf) : AllEvenPrimePlusAlmostPrime 4 := by
  sorry


end AllEvenOnePlusFour
