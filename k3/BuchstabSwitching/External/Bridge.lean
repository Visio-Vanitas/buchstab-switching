import BuchstabSwitching.External.FiniteVerification.SmallEven
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.SchoenfeldRH.PrimeCountingRH
import BuchstabSwitching.External.RobinOmega.PrimeFactorCount
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEnclosure
import BuchstabSwitching.External.LinearSieve.AsymptoticRayEnclosure

/-!
# Bundled External Analytic Bridge (`ExternalPremises`)

Combines the three independent external premise interfaces (finite initial check,
finite-slab GRH sieve enclosure, and asymptotic linear-sieve ray enclosure) into a single
`Prop` structure consumed by `BuchstabSwitching/Main.lean`.

Also provides `ClassicalBasicLemmas`, gathering the eight independent classical/computational
premise folders under `BuchstabSwitching/External/`, together with `externalPremises_of_classical`,
which proves `ExternalPremises` through the formalized sieve bridges (`SlabSieveEnclosure` and
`AsymptoticRayEnclosure`). No `axiom` declarations are used anywhere in this project.
-/

namespace BuchstabSwitching.External

/-- Complete bundle of unformalized analytic and computational inputs for the conditional
`Ω(m) ≤ 3` shifted prime theorem. -/
structure ExternalPremises : Prop where
  small_even : SmallEvenPremise
  slab_enclosure : SlabSieveEnclosurePremise
  ray_enclosure : AsymptoticRayEnclosurePremise

/-- Consolidated classical/computational premise bundle across the unformalized external
premise folders (`FiniteVerification`, `CharacterSums`, `SchoenfeldRH`, `RobinOmega`,
`MertensSums`, `EulerProductV`, `NumericalConstants`) plus the per-slab and asymptotic ray
rational-interval bridges (`BuchstabSeries` and closed-interval `(H*)` are discharged internally). -/
structure ClassicalBasicLemmas (consts : CertifiedConstants) : Prop where
  small_even : SmallEvenPremise
  js_ap : JSLemma51Premise consts.li2
  schoenfeld : SchoenfeldPrimePremise consts.li2
  robin : RobinOmegaBound
  mertens : MertensPrimeSumPremise consts.M0
  euler_v_grh : EulerProductVGRHPremise consts.U_c consts.eNegGamma
  finite_mertens : FiniteMertensExcursionPremise
  slab_bridges : ∀ c ∈ BuchstabSwitching.allSlabs, SlabCertBridge consts.li2 consts c
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
            (BuchstabSwitching.C2_bjs BuchstabSwitching.certifiedDecaySeq (1 / 100 : ℝ))
            (BuchstabSwitching.asymptoticCert.X_LS : ℝ) -
          (1 / 2 : ℝ) * BuchstabSwitching.raySumAqMain consts 16 L (11 / 2 : ℝ)
            (BuchstabSwitching.asymptoticCert.X_LS : ℝ) strips
            (BuchstabSwitching.asymptoticCert.X_LS : ℝ) ∧
        (BuchstabSwitching.asymptoticCert.main_lb : ℝ) -
            (BuchstabSwitching.asymptoticCert.err_ub : ℝ) ≤
          BuchstabSwitching.rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ)
              (Real.log (∏ q ∈ BuchstabSwitching.Q0_100, (q : ℝ))) (1 / 100 : ℝ)
              (BuchstabSwitching.C2_bjs BuchstabSwitching.certifiedDecaySeq (1 / 100 : ℝ))
              (BuchstabSwitching.asymptoticCert.X_LS : ℝ) strips
              (BuchstabSwitching.asymptoticCert.X_LS : ℝ) -
            BuchstabSwitching.rayErrorSumInt consts 16
              (BuchstabSwitching.asymptoticCert.X_LS : ℝ)

/-- Discharges `ExternalPremises` from `ClassicalBasicLemmas consts` via the formalized
Regime 2 slab bridge and Regime 3 ray bridge. -/
theorem externalPremises_of_classical
    {consts : CertifiedConstants} (hCls : ClassicalBasicLemmas consts) :
    ExternalPremises :=
  have hli2 : (1 / 3 : ℝ) < consts.li2 ∧ consts.li2 < 3 :=
    ⟨by linarith [consts.li2_bounds.1], by linarith [consts.li2_bounds.2]⟩
  { small_even := hCls.small_even
    slab_enclosure := slabSieveEnclosurePremise_of_sieveBridge
      ⟨⟨hCls.js_ap, hCls.schoenfeld, hCls.robin, hli2⟩, hCls.mertens, hCls.slab_bridges⟩
    ray_enclosure := asymptoticRayEnclosurePremise_of_sieveBridge
      ⟨⟨hCls.js_ap, hCls.schoenfeld, hCls.robin, hli2⟩, hCls.mertens, hCls.euler_v_grh,
        hCls.h_tilde_le, hCls.alpha0_le, hCls.ray_cert_data⟩ }

end BuchstabSwitching.External
