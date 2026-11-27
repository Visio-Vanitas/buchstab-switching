import BuchstabSwitching.External.EulerProductV.MertensCancel
import BuchstabSwitching.External.EulerProductV.DivisorAndTail
import BuchstabSwitching.External.EulerProductV.FiniteEulerCheck
import BuchstabSwitching.External.EulerProductV.SchoenfeldLargeBridge
import BuchstabSwitching.External.NumericalConstants.CanonicalConstants

/-!
# Full Reduction of `EulerProductVPremise` (`x ≥ 285`)

Combines the three range-specific bounds on the normalized Mertens product `eulerR3 x`
(`FiniteEulerCheck` on `[285, 27000]`, `MertensCancel` on `[27000, 10^12]`, and
`SchoenfeldLargeBridge` on `[10^12, ∞)`) with the divisor/tail assembly in `DivisorAndTail`
to discharge `EulerProductVPremise canonicalConstants.U_c canonicalConstants.eNegGamma` from
`SchoenfeldPrimePremise`, `MertensPrimeSumPremise meisselMertensConst`, and
`DirichletLNonvanishingRightOfHalf`.
-/

namespace BuchstabSwitching.External

/-- Normalized Mertens Euler-product enclosure across all `x ≥ 285`. -/
theorem eulerR3_mem_Icc_all {li2 : ℝ}
    (hS : SchoenfeldRHBound li2)
    (hMert : MertensPrimeSumPremise meisselMertensConst)
    {x : ℝ} (hx : 285 ≤ x) :
    1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
      eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2) := by
  rcases le_total x 27000 with hx_sm | hx_ge
  · exact eulerR3_mem_Icc_small ln2_bounds_cert eNegGamma_bounds_cert hx hx_sm
  · rcases le_total x ((10 : ℝ) ^ 12) with hx_mid | hx_lg
    · exact eulerR3_mem_Icc_mid hMert hx_ge hx_mid
    · exact eulerR3_mem_Icc_large hS hMert hx_lg

/-- Discharges `EulerProductVPremise canonicalConstants.U_c canonicalConstants.eNegGamma`
from `SchoenfeldPrimePremise`, `MertensPrimeSumPremise meisselMertensConst`, and GRH. -/
theorem eulerProductVPremise_of_schoenfeld_and_mertens {li2 : ℝ}
    (hS_prem : SchoenfeldPrimePremise li2)
    (hMert : MertensPrimeSumPremise meisselMertensConst)
    (hGRH : DirichletLNonvanishingRightOfHalf) :
    EulerProductVPremise canonicalConstants.U_c canonicalConstants.eNegGamma :=
  eulerProductVPremise_of_eulerR3 (fun _ hx => eulerR3_mem_Icc_all (hS_prem hGRH) hMert hx)

end BuchstabSwitching.External
