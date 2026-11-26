import ChallengeK3Data
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Verbatim challenge copy of `CertifiedConstants` (`External/NumericalConstants/ExplicitConstants.lean`). -/

namespace BuchstabSwitching.External

structure CertifiedConstants : Type where
  gamma : ℝ
  eGamma : ℝ
  eNegGamma : ℝ
  M0 : ℝ
  C2_twin : ℝ
  U_c : ℝ
  H0 : ℝ
  li2 : ℝ
  alpha0 : ℝ
  C_f0 : ℝ
  H_sigma : ℝ
  C_J : ℝ
  H_tilde : ℝ
  eGamma_eq : eGamma = Real.exp gamma
  eNegGamma_eq : eNegGamma = Real.exp (-gamma)
  U_c_eq : U_c = 2 * C2_twin
  H0_eq : H0 = 2 / U_c
  alpha0_eq : alpha0 = (gamma + Real.log 2) / 2
  C_f0_eq : C_f0 = (0.78 : ℝ)
  C_J_eq : C_J = (alpha0 + C_f0) * H_sigma
  gamma_bounds : (0.577215664901532 : ℝ) ≤ gamma ∧ gamma ≤ (0.577215664901533 : ℝ)
  eGamma_bounds : (1.781072417990197 : ℝ) ≤ eGamma ∧ eGamma ≤ (1.781072417990198 : ℝ)
  eNegGamma_bounds : (0.561459483566885 : ℝ) ≤ eNegGamma ∧ eNegGamma ≤ (0.561459483566886 : ℝ)
  M0_bounds : (0.261496246734501 : ℝ) ≤ M0 ∧ M0 ≤ (0.261497246735500 : ℝ)
  C2_twin_bounds : (0.660161530508911 : ℝ) ≤ C2_twin ∧ C2_twin ≤ (0.660161860589840 : ℝ)
  U_c_bounds : (1.320323061017821 : ℝ) ≤ U_c ∧ U_c ≤ (1.320323721179681 : ℝ)
  H0_bounds : (1.514780025472119 : ℝ) ≤ H0 ∧ H0 ≤ (1.514780782862509 : ℝ)
  li2_bounds : (1.045163780117492 : ℝ) ≤ li2 ∧ li2 ≤ (1.045163780117493 : ℝ)
  alpha0_bounds : (0.635181422730739 : ℝ) ≤ alpha0 ∧ alpha0 ≤ (0.635181422730740 : ℝ)
  H_sigma_bounds : (5.360998310866784 : ℝ) ≤ H_sigma ∧ H_sigma ≤ (5.360998310866785 : ℝ)
  C_J_bounds : (7.586785216829545 : ℝ) ≤ C_J ∧ C_J ≤ (7.586785216829546 : ℝ)
  H_tilde_bounds : (1.295731517927647 : ℝ) ≤ H_tilde ∧ H_tilde ≤ (1.295731517927648 : ℝ)
  ln2_bounds : (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180559946 : ℝ)
  e2_bounds : (7.389056098930650 : ℝ) ≤ Real.exp 2 ∧ Real.exp 2 ≤ (7.389056098930651 : ℝ)

end BuchstabSwitching.External
