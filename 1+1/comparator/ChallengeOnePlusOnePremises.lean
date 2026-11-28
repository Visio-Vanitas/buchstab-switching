import ChallengeOnePlusOneDefs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Verbatim challenge copy of `OnePlusOne/External/Premises.lean`. -/

namespace OnePlusOne.External

def FouradicLaplaceCirclePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ) ≤
        (777 / 100 : ℝ) * Real.sqrt Y * (Real.log Y) ^ 3

def FejerShortIntervalPositivityPremise : Prop :=
  RiemannHypothesis →
    ∀ X : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X →
      ∃ W : ℕ → ℝ, (∀ N, 0 ≤ W N) ∧
        0 < ∑ N ∈ Finset.Icc (Nat.ceil X) (Nat.floor (X + 8 * (Real.log X) ^ 2)),
          W N * goldbachIndicator N

def LinnikCircleAboveBridgePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, ((2 ^ 23 - 2) * 2 ^ 61 + 4 * 10 ^ 18) < N → Even N →
      HasExactPosLinnikRep 22 N

structure OnePlusOnePremises : Prop where
  empirical : EmpiricalGoldbachBase
  fouradicLaplace : FouradicLaplaceCirclePremise
  fejerShort : FejerShortIntervalPositivityPremise
  linnikCircle : LinnikCircleAboveBridgePremise

end OnePlusOne.External
