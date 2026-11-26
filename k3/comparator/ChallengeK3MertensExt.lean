import ChallengeK3MertensTwoVar
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Verbatim challenge copies from `External/MertensSums/ReciprocalPrimeSums.lean`. -/

namespace BuchstabSwitching.External

noncomputable def jsMertensLoErr (x : ℝ) : ℝ :=
  (2.964e-6 : ℝ) / Real.log x

noncomputable def jsMertensHiErr (x : ℝ) : ℝ :=
  if x > (10 : ℝ) ^ 12 then (6.836e-6 : ℝ) / Real.log x
  else if Real.log x > 10 then 2 / (Real.sqrt x * Real.log x)
  else if Real.log x > 8.9 then (1.614e-3 : ℝ)
  else (1 : ℝ)

def MertensPrimeSumPremise (M0 : ℝ) : Prop :=
  (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧
    BuchstabSwitching.MertensSumBounds M0 jsMertensLoErr jsMertensHiErr

end BuchstabSwitching.External
