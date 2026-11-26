import ChallengeK3DirichletGRH
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Verbatim challenge copies from `External/SchoenfeldRH/PrimeCountingRH.lean`. -/

namespace BuchstabSwitching.External

noncomputable def primeCounting (x : ℝ) : ℕ :=
  ((Finset.range (Nat.floor x + 1)).filter Nat.Prime).card

noncomputable def logIntegral (li2 x : ℝ) : ℝ :=
  offsetLogIntegral x + li2

def SchoenfeldRHBound (li2 : ℝ) : Prop :=
  ∀ x : ℝ, 2657 ≤ x →
    |(primeCounting x : ℝ) - logIntegral li2 x| ≤ Real.sqrt x * Real.log x / (8 * Real.pi)

def SchoenfeldPrimePremise (li2 : ℝ) : Prop :=
  DirichletLNonvanishingRightOfHalf → SchoenfeldRHBound li2

end BuchstabSwitching.External
