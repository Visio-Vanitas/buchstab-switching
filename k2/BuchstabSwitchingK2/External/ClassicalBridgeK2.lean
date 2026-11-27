import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.SchoenfeldRH.PrimeCountingRH
import BuchstabSwitching.External.RobinOmega.PrimeFactorCount
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitchingK2.Sieve.PreSieveBonferroni
import BuchstabSwitchingK2.Sieve.BSetSieveBridge
import BuchstabSwitchingK2.Sieve.BilinearRBBridge
import BuchstabSwitchingK2.External.LargeSieve.MultiplicativeLargeSieve
import BuchstabSwitchingK2.External.Bridge
import BuchstabSwitchingK2.Main

/-!
# Classical Analytic & Large-Sieve External Bridge for `BuchstabSwitchingK2` (`1 + 2`)

Mirrors `BuchstabSwitching/External/Bridge.lean` for `1 + 2`, bundling the explicit
analytic, sieve, and computational inputs:
- `SmallEvenPremise` (`4 ≤ N < 4 * 10^18`)
- `JSLemma51Premise consts.li2` & `BilinearRBLargeSievePremiseK2 consts`
- `SchoenfeldPrimePremise`, `RobinOmegaBound`, `MertensPrimeSumPremise`,
  `EulerProductVGRHPremise`, `BuchstabSeriesPremise` from `BuchstabSwitching.External`
- `SlabListEnclosurePremiseK2` + `LowRangeGapPremiseK2` + `RaySieveBridgePremiseK2`

Discharges `MultiplicativeLargeSievePremise` unconditionally via `multiplicativeLargeSieve`,
and proves `externalPremisesK2_of_classical`, `even_eq_prime_add_omegaMult_le_two_of_classical`,
and `all_even_one_plus_two_of_classical` with zero `sorry` and zero custom axioms.
-/

namespace BuchstabSwitchingK2.External

/-- Uniform switching enclosure over an explicit slab list `slabs : List SlabCert`. -/
def SlabListEnclosurePremiseK2 (slabs : List BuchstabSwitchingK2.SlabCert) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ c ∈ slabs, ∀ N : ℕ,
      Even N → c.X_lo ≤ N → N < c.X_hi →
      ∃ scale : ℚ, 0 < scale ∧
        (c.main_lb - c.err_ub) * scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N c.z c.y

/-- Low-decade gap enclosure covering `[4 * 10^18, X_split)` before the certified
fixed-`(z, y)` slab chain begins at `X_split`. -/
def LowRangeGapPremiseK2 (X_split : ℕ) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → 4 * 10 ^ 18 ≤ N → N < X_split →
      ∃ (z y : ℕ) (scale margin : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 3 ∧ 0 < margin ∧ 0 < scale ∧
        margin * scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N z y

/-- Discharges `LowDecadeGapPremiseK2` covering `[4 * 10^18, asymptoticCert.X_LS)` from:
1. a low-range gap premise on `[4 * 10^18, X_split)`, and
2. a kernel-verified contiguous slab chain `checkSlabChain X_split asymptoticCert.X_LS slabs = true`
   paired with per-slab switching enclosure `SlabListEnclosurePremiseK2 slabs`. -/
theorem lowDecadeGapPremiseK2_of_splitChain
    {X_split : ℕ} {slabs : List BuchstabSwitchingK2.SlabCert}
    (hLow : LowRangeGapPremiseK2 X_split)
    (hchain :
      BuchstabSwitchingK2.checkSlabChain
        X_split BuchstabSwitchingK2.asymptoticCert.X_LS slabs = true)
    (hSlabs : SlabListEnclosurePremiseK2 slabs) :
    LowDecadeGapPremiseK2 := by
  intro hGRH N hN hlo hhi
  by_cases hlt : N < X_split
  · exact hLow hGRH N hN hlo hlt
  · have hge : X_split ≤ N := le_of_not_gt hlt
    have hmem := BuchstabSwitchingK2.checkSlabChainAux_mem_valid
      slabs X_split BuchstabSwitchingK2.asymptoticCert.X_LS hchain
    rcases hmem.2 N hge hhi with ⟨c, hc_mem, hc_lo, hc_hi⟩
    rcases BuchstabSwitchingK2.SlabCert.valid_sound (hmem.1 c hc_mem) with
      ⟨_, hz2, hzy, hy3, hnet_pos, hnet_le⟩
    rcases hSlabs hGRH c hc_mem N hN hc_lo hc_hi with ⟨scale, hscale_pos, hbal⟩
    refine ⟨c.z, c.y, scale, c.main_lb - c.err_ub, hz2, hzy, ?_, ?_, hscale_pos, hbal⟩
    · exact Nat.le_of_lt (lt_of_lt_of_le hc_hi hy3)
    · exact lt_of_lt_of_le hnet_pos hnet_le

/-- Bridge statement deducing `AsymptoticRayEnclosurePremiseK2` from the full family of
classical GRH prime bounds, Large Sieve, Euler products, and Buchstab series. -/
def RaySieveBridgePremiseK2 (consts : BuchstabSwitching.External.CertifiedConstants) : Prop :=
  MultiplicativeLargeSievePremise →
  JSLemma51Premise consts.li2 →
  BuchstabSwitchingK2.BilinearRBLargeSievePremiseK2 consts →
  BuchstabSwitching.External.SchoenfeldPrimePremise consts.li2 →
  BuchstabSwitching.External.RobinOmegaBound →
  BuchstabSwitching.External.MertensPrimeSumPremise consts.M0 →
  BuchstabSwitching.External.EulerProductVGRHPremise consts.U_c consts.eNegGamma →
  BuchstabSwitching.External.BuchstabSeriesPremise →
    AsymptoticRayEnclosurePremiseK2

/-- Consolidated classical/computational premise bundle for all-even `1 + 2`, connecting
`BuchstabSwitching.External` classical bounds, bilinear `R_B` bounds, verified slab chains,
and the asymptotic ray bridge. `MultiplicativeLargeSievePremise` is discharged unconditionally
by `multiplicativeLargeSieve`. -/
structure ClassicalBasicLemmasK2
    (consts : BuchstabSwitching.External.CertifiedConstants)
    (X_split : ℕ) (slabs : List BuchstabSwitchingK2.SlabCert) : Prop where
  small_even : SmallEvenPremise
  js_ap : JSLemma51Premise consts.li2
  bilinear_rb : BuchstabSwitchingK2.BilinearRBLargeSievePremiseK2 consts
  schoenfeld : BuchstabSwitching.External.SchoenfeldPrimePremise consts.li2
  robin : BuchstabSwitching.External.RobinOmegaBound
  mertens : BuchstabSwitching.External.MertensPrimeSumPremise consts.M0
  euler_v_grh : BuchstabSwitching.External.EulerProductVGRHPremise consts.U_c consts.eNegGamma
  buchstab_series : BuchstabSwitching.External.BuchstabSeriesPremise
  low_gap : LowRangeGapPremiseK2 X_split
  chain_ok :
    BuchstabSwitchingK2.checkSlabChain
      X_split BuchstabSwitchingK2.asymptoticCert.X_LS slabs = true
  high_slabs : SlabListEnclosurePremiseK2 slabs
  ray_bridge : RaySieveBridgePremiseK2 consts

/-- Constructs `ExternalPremisesK2` from `ClassicalBasicLemmasK2`. -/
theorem externalPremisesK2_of_classical
    {consts : BuchstabSwitching.External.CertifiedConstants}
    {X_split : ℕ} {slabs : List BuchstabSwitchingK2.SlabCert}
    (hCls : ClassicalBasicLemmasK2 consts X_split slabs) :
    ExternalPremisesK2 where
  small_even := hCls.small_even
  slab_gap_enclosure :=
    lowDecadeGapPremiseK2_of_splitChain hCls.low_gap hCls.chain_ok hCls.high_slabs
  ray_enclosure :=
    hCls.ray_bridge multiplicativeLargeSieve hCls.js_ap hCls.bilinear_rb hCls.schoenfeld
      hCls.robin hCls.mertens hCls.euler_v_grh hCls.buchstab_series

/-- Full all-even `1 + 2` theorem directly from `DirichletLNonvanishingRightOfHalf` and
`ClassicalBasicLemmasK2`. -/
theorem even_eq_prime_add_omegaMult_le_two_of_classical
    {consts : BuchstabSwitching.External.CertifiedConstants}
    {X_split : ℕ} {slabs : List BuchstabSwitchingK2.SlabCert}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalBasicLemmasK2 consts X_split slabs)
    (N : ℕ) (hEven : Even N) (hN : 4 ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ BuchstabSwitchingK2.omegaMult m ≤ 2 ∧ p + m = N :=
  BuchstabSwitchingK2.even_eq_prime_add_omegaMult_le_two
    hGRH (externalPremisesK2_of_classical hCls) N hEven hN

/-- Challenge-aligned phrasing (`AllEvenPrimePlusAlmostPrime 2`) directly from
`DirichletLNonvanishingRightOfHalf` and `ClassicalBasicLemmasK2`. -/
theorem all_even_one_plus_two_of_classical
    {consts : BuchstabSwitching.External.CertifiedConstants}
    {X_split : ℕ} {slabs : List BuchstabSwitchingK2.SlabCert}
    (hGRH : DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalBasicLemmasK2 consts X_split slabs) :
    BuchstabSwitchingK2.AllEvenPrimePlusAlmostPrime 2 :=
  BuchstabSwitchingK2.all_even_one_plus_two_of_premises
    hGRH (externalPremisesK2_of_classical hCls)

end BuchstabSwitchingK2.External
