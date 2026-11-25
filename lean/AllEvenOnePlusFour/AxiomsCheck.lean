import AllEvenOnePlusFour
import Challenge

/-!
# Axioms check

1. The library's copies of the definitions agree definitionally with `Challenge.lean`.
2. `#print axioms` for every main theorem. Expected: only `propext`, `Classical.choice`,
   `Quot.sound` for the library theorems, and `sorryAx` for the challenge statement
   `all_even_one_plus_four` only.
-/

/-- The library's `AllEvenPrimePlusAlmostPrime` is the challenge file's, definitionally. -/
theorem allEvenPrimePlusAlmostPrime_agrees (K : ℕ) :
    AllEvenOnePlusFour.AllEvenPrimePlusAlmostPrime K ↔ _root_.AllEvenPrimePlusAlmostPrime K :=
  Iff.rfl

/-- The library's GRH premise is the challenge file's, definitionally. -/
theorem dirichletLNonvanishingRightOfHalf_agrees :
    AllEvenOnePlusFour.DirichletLNonvanishingRightOfHalf ↔
      _root_.DirichletLNonvanishingRightOfHalf :=
  Iff.rfl

/-- The main reduction, stated with the challenge file's own definitions. -/
theorem all_even_one_plus_four_of_conditionalInputs' (h : AllEvenOnePlusFour.ConditionalInputs)
    (hGRH : _root_.DirichletLNonvanishingRightOfHalf) : _root_.AllEvenPrimePlusAlmostPrime 4 :=
  AllEvenOnePlusFour.all_even_one_plus_four_of_conditionalInputs h hGRH

-- Agreement of the statements.
#print axioms allEvenPrimePlusAlmostPrime_agrees
#print axioms dirichletLNonvanishingRightOfHalf_agrees
#print axioms all_even_one_plus_four_of_conditionalInputs'

-- Weights.lean
#print axioms AllEvenOnePlusFour.pow_cardFactors_le
#print axioms AllEvenOnePlusFour.cardFactors_lt_of_lt_pow
#print axioms AllEvenOnePlusFour.cardFactors_le_four_of_weight_pos

-- Bonferroni.lean
#print axioms AllEvenOnePlusFour.truncated_alternating_sum_choose
#print axioms AllEvenOnePlusFour.truncated_alternating_sum_choose_le_of_odd
#print axioms AllEvenOnePlusFour.le_truncated_alternating_sum_choose_of_even

-- Reduction.lean
#print axioms AllEvenOnePlusFour.rough_of_mem_siftedPrimes
#print axioms AllEvenOnePlusFour.exists_prime_add_of_weightedSum_pos
#print axioms AllEvenOnePlusFour.prime_add_of_lt_tailStart
#print axioms AllEvenOnePlusFour.all_even_one_plus_four_of_inputs
#print axioms AllEvenOnePlusFour.all_even_one_plus_four_of_conditionalInputs

-- Sanity.lean
#print axioms AllEvenOnePlusFour.AllEvenPrimePlusAlmostPrime.mono
#print axioms AllEvenOnePlusFour.allEvenPrimePlusAlmostPrime_iff_primeFactorsList
#print axioms AllEvenOnePlusFour.allEvenPrimePlusAlmostPrime_iff_isAtMostAlmostPrime
#print axioms AllEvenOnePlusFour.four_eq_prime_add_one
#print axioms AllEvenOnePlusFour.not_allEvenPrimePlusAlmostPrime_zero
#print axioms AllEvenOnePlusFour.goldbach_of_le_forty
#print axioms AllEvenOnePlusFour.primePlusAlmostPrime_one_of_le_forty

-- Challenge.lean: the statement only. Expected to list `sorryAx`.
#print axioms all_even_one_plus_four
