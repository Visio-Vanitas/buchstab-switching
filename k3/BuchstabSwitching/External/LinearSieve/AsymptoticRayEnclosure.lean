import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.Regime3RayBridge
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity

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

/-- Bundled external analytic and finite ray-grid certificate premises for Regime 3
(`N ≥ asymptoticCert.X_LS = 10^600`), connecting `ClassicalPrimePremises`,
`MertensPrimeSumPremise`, `EulerProductVGRHPremise`, `BuchstabSeriesPremise`,
closed-interval `(H*)` over `Q0_100`, and the verified rational enclosure at `X_LS`
via `Regime3RayBridge.regime3_ray_switchingBalance_lb_of_analytic`. -/
structure RayAnalyticPremises (consts : CertifiedConstants) : Prop where
  classical : BuchstabSwitching.ClassicalPrimePremises consts.li2
  mertens : MertensPrimeSumPremise consts.M0
  euler_v_grh : EulerProductVGRHPremise consts.U_c consts.eNegGamma
  buchstab_series : BuchstabSeriesPremise
  closed_hstar :
    BuchstabSwitching.ClosedHStarCond BuchstabSwitching.gTotRay
      (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ BuchstabSwitching.Q0_100) (1 + (1 : ℝ) / 100)
  h_tilde_le : BuchstabSwitching.H_tilde ≤ consts.H_tilde
  alpha0_le : BuchstabSwitching.alpha0 ≤ consts.alpha0
  ray_cert_data :
    ∃ (L : ℕ), 1 ≤ L ∧
      ∃ (strips : ∀ k : Fin L,
        BuchstabSwitching.RaySelbergStrip
          (BuchstabSwitching.rayStripRExp 16 (11 / 2 : ℝ) (BuchstabSwitching.asymptoticCert.X_LS : ℝ)
            (BuchstabSwitching.rayStripU 16 L (k.1 + 1)))),
        (∀ k : Fin L,
          0 < BuchstabSwitching.j_over_logz_lb
            (BuchstabSwitching.rayLogZLb 16 (BuchstabSwitching.asymptoticCert.X_LS : ℝ))
            (BuchstabSwitching.rayStripRExp 16 (11 / 2 : ℝ) (BuchstabSwitching.asymptoticCert.X_LS : ℝ)
              (BuchstabSwitching.rayStripU 16 L (k.1 + 1)))
            (strips k).t (strips k).grid) ∧
        0 ≤ BuchstabSwitching.rayLbA 16 (5 / 2 : ℝ)
            (Real.log (∏ q ∈ BuchstabSwitching.Q0_100, (q : ℝ))) (1 / 100 : ℝ)
            (BuchstabSwitching.C2_bjs BuchstabSwitching.constDecaySeq (1 / 100 : ℝ))
            (BuchstabSwitching.asymptoticCert.X_LS : ℝ) -
          (1 / 2 : ℝ) * BuchstabSwitching.raySumAqMain consts 16 L (11 / 2 : ℝ)
            (BuchstabSwitching.asymptoticCert.X_LS : ℝ) strips
            (BuchstabSwitching.asymptoticCert.X_LS : ℝ) ∧
        (BuchstabSwitching.asymptoticCert.main_lb : ℝ) -
            (BuchstabSwitching.asymptoticCert.err_ub : ℝ) ≤
          BuchstabSwitching.rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ)
              (Real.log (∏ q ∈ BuchstabSwitching.Q0_100, (q : ℝ))) (1 / 100 : ℝ)
              (BuchstabSwitching.C2_bjs BuchstabSwitching.constDecaySeq (1 / 100 : ℝ))
              (BuchstabSwitching.asymptoticCert.X_LS : ℝ) strips
              (BuchstabSwitching.asymptoticCert.X_LS : ℝ) -
            BuchstabSwitching.rayErrorSumInt consts 16
              (BuchstabSwitching.asymptoticCert.X_LS : ℝ)

/-- Derives `AsymptoticRayEnclosurePremise` from `RayAnalyticPremises consts` via the
formalized Regime 3 sieve bridge `Regime3RayBridge.regime3_ray_switchingBalance_lb_of_analytic`. -/
theorem asymptoticRayEnclosurePremise_of_sieveBridge
    {consts : CertifiedConstants} (hPrem : RayAnalyticPremises consts) :
    AsymptoticRayEnclosurePremise := by
  intro hGRH N hN_even hN
  rcases hPrem.ray_cert_data with ⟨L, hL, strips, hvj_pos, hbr_LS, hCertInt⟩
  have hC2_nn : (0 : ℝ) ≤ BuchstabSwitching.C2_bjs BuchstabSwitching.constDecaySeq (1 / 100 : ℝ) := by
    unfold BuchstabSwitching.C2_bjs
    refine tsum_nonneg fun k => ?_
    exact BuchstabSwitching.tauBJS_nonneg (by norm_num)
      (fun j hj => (BuchstabSwitching.validDecaySeq_const.1 j hj).1.le) _
  exact BuchstabSwitching.regime3_ray_switchingBalance_lb_of_analytic consts
    hPrem.h_tilde_le hPrem.alpha0_le hGRH hPrem.classical hPrem.mertens
    hPrem.euler_v_grh hPrem.buchstab_series hPrem.closed_hstar hC2_nn
    hL strips hvj_pos hbr_LS hCertInt hN_even hN

end BuchstabSwitching.External
