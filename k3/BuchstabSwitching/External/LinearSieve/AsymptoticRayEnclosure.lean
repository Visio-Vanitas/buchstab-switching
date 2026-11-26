import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.Regime3RayBridge
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.BuchstabSeries.AdjointEvaluation

/-!
# Linear-Sieve Asymptotic Ray Enclosure Interface (`N ≥ X_LS`)

States `AsymptoticRayEnclosurePremise`: under `DirichletLNonvanishingRightOfHalf`, for all
even `N ≥ asymptoticCert.X_LS`, there exist valid switching cutoffs `2 ≤ z ≤ y` with
`N ≤ y^4`, `N ≤ z * y^3`, and positive normalization `scale` such that
`(asymptoticCert.main_lb - asymptoticCert.err_ub) * scale ≤ switchingBalance N z y`.

Also provides `RayAnalyticPremises` and `asymptoticRayEnclosurePremise_of_sieveBridge`,
discharging `AsymptoticRayEnclosurePremise` from the formalized Regime 3 linear-sieve +
Selberg upper-sieve ray bridge (`Regime3RayBridge.regime3_ray_switchingBalance_lb_of_analytic`)
together with the isolated external classical lemmas.
-/

namespace BuchstabSwitching.External

/-- Under `DirichletLNonvanishingRightOfHalf`, every even `N ≥ asymptoticCert.X_LS` inherits
the certified uniform positive switching coefficient from `asymptoticCert`. -/
def AsymptoticRayEnclosurePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → BuchstabSwitching.asymptoticCert.X_LS ≤ N →
      ∃ (z y : ℕ) (scale : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 4 ∧ N ≤ z * y ^ 3 ∧ 0 < scale ∧
        (BuchstabSwitching.asymptoticCert.main_lb - BuchstabSwitching.asymptoticCert.err_ub) *
          scale ≤ BuchstabSwitching.switchingBalance N z y

/-- Bundled external analytic premises for Regime 3 (`N ≥ asymptoticCert.X_LS = 10^600`),
connecting `ClassicalPrimePremises`, `MertensPrimeSumPremise`, and unconditional
`EulerProductVPremise` via `Regime3RayBridge.regime3_ray_switchingBalance_lb_of_analytic`, while
discharging `BuchstabSeriesPremise` (`buchstabSeriesPremise_proved`), closed-interval `(H*)` over
`Q0_100` (`closedHStarCond_Q0_100`), `H_tilde`/`alpha0` constant bounds (`ConstantBounds`), and
the `L = 120` ray-grid enclosure at `X_LS` (`ray_cert_data_inst`) internally. -/
structure RayAnalyticPremises (consts : CertifiedConstants) : Prop where
  classical : BuchstabSwitching.ClassicalPrimePremises consts.li2
  mertens : MertensPrimeSumPremise consts.M0
  euler_v : EulerProductVPremise consts.U_c consts.eNegGamma

/-- Derives `AsymptoticRayEnclosurePremise` from `RayAnalyticPremises consts` via the
formalized Regime 3 sieve bridge `Regime3RayBridge.regime3_ray_switchingBalance_lb_of_analytic`,
discharging `BuchstabSeriesPremise`, `ClosedHStarCond` over `Q0_100`, and `ray_cert_data_inst`
internally. -/
theorem asymptoticRayEnclosurePremise_of_sieveBridge
    {consts : CertifiedConstants} (hPrem : RayAnalyticPremises consts) :
    AsymptoticRayEnclosurePremise := by
  intro hGRH N hN_even hN
  rcases BuchstabSwitching.ray_cert_data_inst consts with
    ⟨L, hL, strips, hvj_pos, hbr_LS, hCertInt⟩
  have hHStar := BuchstabSwitching.closedHStarCond_Q0_100 hPrem.mertens
  exact BuchstabSwitching.regime3_ray_switchingBalance_lb_of_analytic consts
    BuchstabSwitching.certifiedDecaySeq BuchstabSwitching.validDecaySeq_certified
    hGRH hPrem.classical hPrem.mertens hPrem.euler_v buchstabSeriesPremise_proved hHStar
    BuchstabSwitching.C2_bjs_certified_nonneg
    hL strips hvj_pos hbr_LS hCertInt hN_even hN

end BuchstabSwitching.External
