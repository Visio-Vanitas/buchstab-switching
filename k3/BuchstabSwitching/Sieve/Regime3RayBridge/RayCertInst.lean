import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstSound

/-!
# Instantiation of `ray_cert_data` at `X_LS = 10^600`

Combines the verified strip grid bounds (`RayCertInstSound`), analytic envelope bounds
(`RayCertInstEnv`), and certified numerical enclosure of `asymptoticCert`
(`BuchstabSwitching.Certificates.Data`) to produce an unconditional Lean witness
`ray_cert_data_inst` for `Regime3RayBridge.regime3_ray_switchingBalance_lb_of_analytic`.
-/

namespace BuchstabSwitching

noncomputable section

/-- Unconditional Lean witness instantiating the `L = 120` ray-grid and normalized main-minus-error
inequalities at `X_LS = 10^600` for any `CertifiedConstants` realization. -/
theorem ray_cert_data_inst (consts : External.CertifiedConstants) :
    ∃ (L : ℕ), 1 ≤ L ∧
      ∃ (strips : ∀ k : Fin L,
        RaySelbergStrip
          (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ)
            (rayStripU 16 L (k.1 + 1)))),
        (∀ k : Fin L,
          0 < j_over_logz_lb
            (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
            (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ)
              (rayStripU 16 L (k.1 + 1)))
            (strips k).t (strips k).grid) ∧
        0 ≤ rayLbA 16 (5 / 2 : ℝ)
            (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
            (C2_bjs certifiedDecaySeq (1 / 100 : ℝ))
            (asymptoticCert.X_LS : ℝ) -
          (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ)
            (asymptoticCert.X_LS : ℝ) strips (asymptoticCert.X_LS : ℝ) ∧
        (asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ) ≤
          rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ)
              (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
              (C2_bjs certifiedDecaySeq (1 / 100 : ℝ))
              (asymptoticCert.X_LS : ℝ) strips (asymptoticCert.X_LS : ℝ) -
            rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ) := by
  refine ⟨120, by norm_num, instStrip, strip_j_over_logz_lb_pos, ?_, ?_⟩
  · have ha : (969550 : ℝ) / (1000000 : ℝ) ≤
        rayLbA 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
          (C2_bjs certifiedDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) :=
      rayLbA_16_X_LS_ge_cert
    have hsum : raySumAqMain consts 16 120 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) instStrip
        (asymptoticCert.X_LS : ℝ) ≤ (1770383099751 : ℝ) / (scaleS : ℝ) :=
      raySumAqMain_le_cert consts
    unfold scaleS at hsum
    linarith
  · have hdv : rayDeltaV 16 (asymptoticCert.X_LS : ℝ) ≤ (67062 : ℝ) / (10 : ℝ) ^ 9 :=
      rayDeltaV_16_X_LS_le_cert
    have he : (0.561459483566885 : ℝ) ≤ consts.eNegGamma := consts.eNegGamma_bounds.1
    have ha : (969550 : ℝ) / (1000000 : ℝ) ≤
        rayLbA 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
          (C2_bjs certifiedDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) :=
      rayLbA_16_X_LS_ge_cert
    have hsum : raySumAqMain consts 16 120 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) instStrip
        (asymptoticCert.X_LS : ℝ) ≤ (1770383099751 : ℝ) / (scaleS : ℝ) :=
      raySumAqMain_le_cert consts
    unfold scaleS at hsum
    have herr : rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ) ≤ (78 : ℝ) / (1000000 : ℝ) :=
      rayErrorSumInt_16_X_LS_le_cert consts
    have hbracket_lb :
        (969550 : ℝ) / (1000000 : ℝ) - (1 / 2 : ℝ) * ((1770383099751 : ℝ) / (10 ^ 12 : ℝ)) ≤
          rayLbA 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
            (C2_bjs certifiedDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) -
            (1 / 2 : ℝ) * raySumAqMain consts 16 120 (11 / 2 : ℝ)
              (asymptoticCert.X_LS : ℝ) instStrip (asymptoticCert.X_LS : ℝ) := by
      linarith
    have hfactor_lb :
        ((1 : ℝ) - (67062 : ℝ) / (10 : ℝ) ^ 9) * (0.561459483566885 : ℝ) ≤
          (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) * consts.eNegGamma := by
      have h1 : (1 : ℝ) - (67062 : ℝ) / (10 : ℝ) ^ 9 ≤
          1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ) := by linarith
      exact mul_le_mul h1 he (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1 - (67062 : ℝ) / (10 : ℝ) ^ 9).trans h1)
    have hmain_lb :
        (((1 : ℝ) - (67062 : ℝ) / (10 : ℝ) ^ 9) * (0.561459483566885 : ℝ)) *
            ((969550 : ℝ) / (1000000 : ℝ) -
              (1 / 2 : ℝ) * ((1770383099751 : ℝ) / (10 ^ 12 : ℝ))) ≤
          rayMainCoeff consts 16 120 (5 / 2 : ℝ) (11 / 2 : ℝ)
            (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
            (C2_bjs certifiedDecaySeq (1 / 100 : ℝ))
            (asymptoticCert.X_LS : ℝ) instStrip (asymptoticCert.X_LS : ℝ) := by
      unfold rayMainCoeff
      exact mul_le_mul hfactor_lb hbracket_lb (by norm_num)
        ((by norm_num :
          (0 : ℝ) ≤ ((1 : ℝ) - (67062 : ℝ) / (10 : ℝ) ^ 9) * (0.561459483566885 : ℝ)).trans
          hfactor_lb)
    have hcert_le : (asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ) ≤
        (469 / 10000 : ℝ) := by
      norm_num [RayCert.main_lb, RayCert.err_ub, asymptoticCert]
    have hnum_check : (469 / 10000 : ℝ) ≤
        (((1 : ℝ) - (67062 : ℝ) / (10 : ℝ) ^ 9) * (0.561459483566885 : ℝ)) *
            ((969550 : ℝ) / (1000000 : ℝ) -
              (1 / 2 : ℝ) * ((1770383099751 : ℝ) / (10 ^ 12 : ℝ))) -
          (78 : ℝ) / (1000000 : ℝ) := by
      norm_num
    linarith

end

end BuchstabSwitching
