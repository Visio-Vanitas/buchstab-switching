import ChallengeOnePlusOneDefs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Verbatim challenge copy of `OnePlusOne/External/Premises.lean`. -/

namespace OnePlusOne.External

def DyadicLaplaceCirclePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 2) : ℝ) ≤
        (372872 / 100 : ℝ) * Real.sqrt Y * (Real.log Y) ^ 3

def FejerShortIntervalPositivityPremise : Prop :=
  RiemannHypothesis →
    ∀ X : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X →
      ∃ W : ℕ → ℝ, (∀ N, 0 ≤ W N) ∧
        0 < ∑ N ∈ Finset.Icc (Nat.ceil X) (Nat.floor (X + 6281 * (Real.log X) ^ 2)),
          W N * goldbachIndicator N

def LinnikCircleAboveBridgePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, ((2 ^ 23 - 2) * 2 ^ 61 + 4 * 10 ^ 18) < N → Even N →
      HasExactPosLinnikRep 22 N

structure OnePlusOnePremises : Prop where
  empirical : EmpiricalGoldbachBase
  dyadicLaplace : DyadicLaplaceCirclePremise
  fejerShort : FejerShortIntervalPositivityPremise
  linnikCircle : LinnikCircleAboveBridgePremise

end OnePlusOne.External
