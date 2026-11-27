import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.NumericalConstants.CanonicalDefs
import BuchstabSwitching.External.NumericalConstants.TranscendentalBounds
import BuchstabSwitching.External.NumericalConstants.PrimeConstantsBounds

/-!
# Canonical Unconditional Inhabitant of `CertifiedConstants`

Constructs `canonicalConstants : CertifiedConstants` without external hypotheses by combining:
- `TranscendentalBounds.lean`: `10^-15` enclosures on `Real.log 2`, `Real.exp 2`,
  `Real.eulerMascheroniConstant`, `exp γ`, `exp (-γ)`, `α_0`, `C_J`, and `canonicalLi2 = li(2)`;
- `PrimeConstantsBounds.lean`: `ζ(2) = π^2 / 6`-accelerated enclosures on `BuchstabSwitching.H_0`,
  `C_2 = 1 / H_0`, `U_c = 2 * C_2`, and `meisselMertensConst = M_0`.

The auxiliary envelope fields `H_sigma` and `H_tilde` (which are unused by `Sieve/` and `External/`,
where `BuchstabSwitching.H_quarter` and `BuchstabSwitching.H_tilde` are bounded directly in
`Sieve/OddSquarefreeBounds/`) are instantiated to the exact `constants.py` outward-envelope values.
-/

namespace BuchstabSwitching.External

/-- Verified `constants.py` enclosure for `meisselMertensConst`. -/
theorem meisselMertensConst_bounds_cert :
    (0.261496246734501 : ℝ) ≤ meisselMertensConst ∧
      meisselMertensConst ≤ (0.261497246735500 : ℝ) := by
  obtain ⟨hg_lo, hg_hi⟩ := gamma_bounds_cert
  obtain ⟨hm_lo, hm_hi⟩ := meisselMertens_sub_gamma_bounds
  constructor <;> linarith

/-- Tighter `[0.261497, 0.261498]` enclosure matching `MertensPrimeSumPremise`. -/
theorem meisselMertensConst_bounds_tight :
    (0.261497 : ℝ) ≤ meisselMertensConst ∧ meisselMertensConst ≤ (0.261498 : ℝ) := by
  obtain ⟨hg_lo, hg_hi⟩ := gamma_bounds_cert
  obtain ⟨hm_lo, hm_hi⟩ := meisselMertens_sub_gamma_bounds
  constructor <;> linarith

/-- Canonical unconditionally verified mathematical inhabitant of `CertifiedConstants`. -/
noncomputable def canonicalConstants : CertifiedConstants where
  gamma := Real.eulerMascheroniConstant
  eGamma := Real.exp Real.eulerMascheroniConstant
  eNegGamma := Real.exp (-Real.eulerMascheroniConstant)
  M0 := meisselMertensConst
  C2_twin := 1 / BuchstabSwitching.H_0
  U_c := 2 * (1 / BuchstabSwitching.H_0)
  H0 := BuchstabSwitching.H_0
  li2 := canonicalLi2
  alpha0 := (Real.eulerMascheroniConstant + Real.log 2) / 2
  C_f0 := (0.78 : ℝ)
  H_sigma := (5.36099831086678458 : ℝ)
  C_J := ((Real.eulerMascheroniConstant + Real.log 2) / 2 + (0.78 : ℝ)) * (5.36099831086678458 : ℝ)
  H_tilde := (1.29573151792764714 : ℝ)
  eGamma_eq := rfl
  eNegGamma_eq := rfl
  U_c_eq := rfl
  H0_eq := by
    have hpos : (0 : ℝ) < BuchstabSwitching.H_0 := by linarith [H0_bounds_cert_tight.1]
    field_simp [hpos.ne']
  alpha0_eq := rfl
  C_f0_eq := rfl
  C_J_eq := rfl
  gamma_bounds := gamma_bounds_cert
  eGamma_bounds := eGamma_bounds_cert
  eNegGamma_bounds := eNegGamma_bounds_cert
  M0_bounds := meisselMertensConst_bounds_cert
  C2_twin_bounds := C2_twin_bounds_cert
  U_c_bounds := U_c_bounds_cert
  H0_bounds := H0_bounds_cert_tight
  li2_bounds := li2_bounds_cert
  alpha0_bounds := alpha0_bounds_cert
  H_sigma_bounds := ⟨by norm_num, by norm_num⟩
  C_J_bounds := cJ_bounds_cert
  H_tilde_bounds := ⟨by norm_num, by norm_num⟩
  ln2_bounds := ln2_bounds_cert
  e2_bounds := e2_bounds_cert

end BuchstabSwitching.External
