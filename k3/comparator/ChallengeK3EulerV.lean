import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Verbatim challenge copies from `External/EulerProductV/ProductAsymptotic.lean`. -/

namespace BuchstabSwitching.External

noncomputable def VN (N z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ ¬ p ∣ N),
    (1 - 1 / ((p : ℝ) - 1))

noncomputable def deltaV_bjs (N : ℕ) (x : ℝ) : ℝ :=
  let f1 := (1.45 : ℝ) * (Real.log N / (x - 1)) * (1 + 10 * Real.log (Real.log N) / Real.log N)
  let f2 := (1.002 : ℝ) / (x - 3)
  let f3 := (1 : ℝ) / (2 * (Real.log x) ^ 2)
  let d_lo := 1 - (1 - f1) * (1 - f2) * (1 - f3)
  let d_hi := (1 + f1) * (1 + f2) * (1 + f3) - 1
  max d_lo d_hi

noncomputable def UN_ratio (U_c : ℝ) (N : ℕ) : ℝ :=
  U_c * ∏ p ∈ N.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)

def EulerProductVPremise (U_c eNegGamma : ℝ) : Prop :=
  ∀ (N : ℕ), Even N → 3 ≤ N → ∀ (x : ℝ), 285 ≤ x →
    (1 - deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x ≤ VN N (Nat.ceil x) ∧
      VN N (Nat.ceil x) ≤ (1 + deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x

end BuchstabSwitching.External
