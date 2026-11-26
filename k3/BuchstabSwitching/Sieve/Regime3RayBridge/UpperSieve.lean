import BuchstabSwitching.Sieve.Regime3RayBridge.IntegerCutoffs
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.LowerSieve
import BuchstabSwitching.Sieve.Regime3RayBridge.UpperSieveSetup
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.Certificates.Data
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

section SieveBounds

/-- Upper-sieve sum bound for `(1/2) ∑_{q ∈ midPrimes} S(A_{N,q}, z)` when `N ≥ 10^600` is even
(`regime_asymptotic.py:104-154`). -/
theorem regime3_upper_sieve_sum_ub (consts : External.CertifiedConstants)
    (hH_tilde : H_tilde ≤ consts.H_tilde) (halpha0 : alpha0 ≤ consts.alpha0)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0)
    (hV : External.EulerProductVGRHPremise consts.U_c consts.eNegGamma)
    {L : ℕ} (hL : 1 ≤ L)
    (strips : ∀ k : Fin L, RaySelbergStrip
      (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))))
    (hvj_pos : ∀ k : Fin L,
      0 < j_over_logz_lb (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
        (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
        (strips k).t (strips k).grid)
    {N : ℕ} (hN_even : Even N) (hN : asymptoticCert.X_LS ≤ N) :
    (1 / 2 : ℝ) * ∑ q ∈ midPrimes N (rayZ 16 N) (rayY 16 N),
        ((divisibleSievedShifted N (rayZ 16 N) q).card : ℝ) ≤
      (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
          (asymptoticCert.X_LS : ℝ) *
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N (rayZ 16 N)) +
      (rayErrAq1Int consts 16 (N : ℝ) + rayErrAq2 consts 16 (N : ℝ)) *
        rayScale consts.U_c 16 N := by
  obtain ⟨hXLS_pos, hN_pos, hlogLS_ge, hlogN_ge, hN_4e18, hN_2pow16, hXLS_2pow16⟩ := X_LS_facts hN
  have hN_real_ge : (asymptoticCert.X_LS : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hlogLS_pos : 0 < Real.log (asymptoticCert.X_LS : ℝ) := by linarith
  have hXLS_ge1 : (1 : ℝ) ≤ (asymptoticCert.X_LS : ℝ) :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1200)).trans exp_1200_lt_asymptoticCert_X_LS.le
  have hlogLS_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) := by norm_num; linarith
  have hlogN_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by norm_num; linarith
  set z : ℕ := rayZ 16 N
  set y : ℕ := rayY 16 N
  have hcut := regime3_cutoffs_valid (by norm_num : 4 ≤ 16) hN_2pow16
  have hz2 : 2 ≤ z := hcut.1
  have hzy : z ≤ y := hcut.2.1
  have hy_le_beta : (y : ℝ) ≤ (N : ℝ) ^ rayBeta 16 := by
    have h600 : 10 ^ 600 = (10 ^ 200) ^ 3 := by rw [← pow_mul]
    exact rayY_le_rpow_beta_ray (by rw [h600, ten_pow_600_eq_asymptoticCert_X_LS]; exact hN)
  have hz_ge_lb : rayZIntLb 16 (N : ℝ) ≤ (z : ℝ) := by
    unfold rayZIntLb
    rw [rayZ0_eq_rpow hN_pos]
    unfold z rayZ
    have := Nat.sub_one_lt_floor ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)))
    linarith
  have hz_le_z0 : (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) := by
    unfold z rayZ; exact Nat.floor_le (by positivity)
  have hz_1e12 : (10 : ℝ) ^ 12 + 2 ≤ (z : ℝ) :=
    (rayZIntLb_gt_1e12 hlogN_ge.le).trans hz_ge_lb
  have hz_LS_1e12 : (10 : ℝ) ^ 12 + 2 ≤ (rayZ 16 asymptoticCert.X_LS : ℝ) := by
    have hge : rayZIntLb 16 (asymptoticCert.X_LS : ℝ) ≤ (rayZ 16 asymptoticCert.X_LS : ℝ) := by
      unfold rayZIntLb
      rw [rayZ0_eq_rpow hXLS_pos]
      unfold rayZ
      have := Nat.sub_one_lt_floor ((asymptoticCert.X_LS : ℝ) ^ ((1 : ℝ) / (16 : ℝ)))
      linarith
    exact (rayZIntLb_gt_1e12 hlogLS_ge.le).trans hge
  -- Prove `1 < r_k < 3` for every strip `k : Fin L`
  have hr_bounds : ∀ k : Fin L,
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      1 < r_k ∧ r_k < 3 := by
    intro k
    dsimp only
    unfold rayStripRExp
    refine ⟨lt_min (by norm_num) ?_, lt_of_le_of_lt (min_le_left _ _) (by norm_num)⟩
    have haq : rayAlphaQ (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) < (0.04 : ℝ) := by
      unfold rayAlphaQ
      have hll : Real.log (Real.log (asymptoticCert.X_LS : ℝ)) < 8 := log_log_asymptoticCert_X_LS_lt
      have hdiv : (11 / 2 : ℝ) * Real.log (Real.log (asymptoticCert.X_LS : ℝ)) /
          Real.log (asymptoticCert.X_LS : ℝ) < (11 / 2 : ℝ) * 8 / 1200 := by
        rw [div_lt_div_iff₀ hlogLS_pos (by norm_num)]
        nlinarith [hlogLS_ge]
      linarith
    have hu_le : rayStripU 16 L (k.1 + 1) ≤ rayBeta 16 := by
      unfold rayStripU
      have hk1 : ((k.1 + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast k.2
      have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      have hbeta : 0 ≤ (rayBeta 16 - 1 / (16 : ℝ)) / (L : ℝ) :=
        div_nonneg (sub_nonneg.mpr (one_div_lt_rayBeta (by norm_num)).le) hL_pos.le
      have hmul : ((k.1 + 1 : ℕ) : ℝ) * ((rayBeta 16 - 1 / (16 : ℝ)) / (L : ℝ)) ≤
          (L : ℝ) * ((rayBeta 16 - 1 / (16 : ℝ)) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hk1 hbeta
      rw [mul_div_cancel₀ _ hL_pos.ne'] at hmul
      linarith
    have hbeta_lt : rayBeta 16 < (0.32 : ℝ) := by unfold rayBeta; norm_num
    linarith
  -- Apply `vj_monotone_lb_uniform_even_N` on `z_fn M := (rayZ 16 M : ℝ)`, `delta_v M := rayDeltaV 16 M`
  let z_fn : ℕ → ℝ := fun M => (rayZ 16 M : ℝ)
  let dv_fn : ℕ → ℝ := fun M => rayDeltaV 16 M
  have hz_gt_exp10 : Real.exp 10 < z_fn asymptoticCert.X_LS := by
    have he70 : Real.exp 10 < rayZ0 16 (asymptoticCert.X_LS : ℝ) - 1 := by
      have hz0 : Real.exp 75 ≤ rayZ0 16 (asymptoticCert.X_LS : ℝ) :=
        rayZ0_ge_exp_75 hlogLS_ge.le
      have he11 : Real.exp 10 + 1 < Real.exp 75 := by
        have he10_20k := exp_ten_ge_20001
        have he20 : Real.exp 10 * 2 ≤ Real.exp 75 := by
          have : Real.exp 10 * Real.exp 1 ≤ Real.exp 75 := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by norm_num)
          have : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          nlinarith [Real.exp_pos 10]
        linarith
      linarith
    have hfl : rayZ0 16 (asymptoticCert.X_LS : ℝ) - 1 ≤ z_fn asymptoticCert.X_LS := by
      dsimp only [z_fn, rayZ]; rw [rayZ0_eq_rpow hXLS_pos]
      exact (Nat.sub_one_lt_floor _).le
    linarith
  have hz_mono : ∀ ⦃N₁ N₂ : ℕ⦄, asymptoticCert.X_LS ≤ N₁ → N₁ ≤ N₂ → z_fn N₁ ≤ z_fn N₂ := by
    intro N₁ N₂ _ h12
    dsimp only [z_fn, rayZ]
    exact_mod_cast Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg N₁)
      (by exact_mod_cast h12) (by norm_num))
  have hdv_le1 : ∀ M : ℕ, asymptoticCert.X_LS ≤ M → dv_fn M ≤ 1 := by
    intro M hM_ge
    have hM_real : (asymptoticCert.X_LS : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge
    have hM_pos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hXLS_pos hM_real
    have hlogM : 10 * (16 : ℝ) ≤ Real.log (M : ℝ) := by
      linarith [hlogLS_ge, Real.log_le_log hXLS_pos hM_real]
    exact (rayDeltaV_lt_one (by norm_num) (by norm_num) hM_pos hlogM).le
  have hdv_anti : ∀ ⦃N₁ N₂ : ℕ⦄, asymptoticCert.X_LS ≤ N₁ → N₁ ≤ N₂ → dv_fn N₂ ≤ dv_fn N₁ := by
    intro N₁ N₂ hN1 h12
    have hN1_real : (asymptoticCert.X_LS : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hN1
    have hN1_pos : (0 : ℝ) < (N₁ : ℝ) := lt_of_lt_of_le hXLS_pos hN1_real
    have hlogN1 : 10 * (16 : ℝ) ≤ Real.log (N₁ : ℝ) := by
      linarith [hlogLS_ge, Real.log_le_log hXLS_pos hN1_real]
    exact rayDeltaV_antitone (by norm_num) (by norm_num) hN1_pos hlogN1 (by exact_mod_cast h12)
  have hV_cond : ∀ M : ℕ, asymptoticCert.X_LS ≤ M →
      (1 - dv_fn M) * (consts.eNegGamma * consts.U_c) / Real.log (z_fn M) ≤
        External.VN 2 (Nat.ceil (z_fn M)) := by
    intro M hM_ge
    have hM_real : (asymptoticCert.X_LS : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge
    have hM_pos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hXLS_pos hM_real
    have hlogM : 10 * (16 : ℝ) ≤ Real.log (M : ℝ) := by
      linarith [hlogLS_ge, Real.log_le_log hXLS_pos hM_real]
    have hzM_gt : 8 ≤ z_fn M := by
      have : Real.exp 10 < z_fn M := lt_of_lt_of_le hz_gt_exp10 (hz_mono le_rfl hM_ge)
      linarith [exp_ten_ge_20001]
    have hVN := VN_two_ceil_ge_of_EulerProductVGRHPremise hGRH hV hzM_gt
    have h4_le_M : 4 ≤ M := (by norm_num : 4 ≤ 2 ^ 16).trans (hXLS_2pow16.trans hM_ge)
    have hdv_le := deltaV_bs_le_rayDeltaV (M := 16) (K := 4) (N := M)
      (by norm_num) (by norm_num) (by norm_num) h4_le_M hlogM
    have hlogz_pos : 0 < Real.log (z_fn M) := Real.log_pos (by linarith)
    have hnum_le : (1 - dv_fn M) * (consts.eNegGamma * consts.U_c) ≤
        (1 - External.deltaV_bs 4 (z_fn M)) * (consts.eNegGamma * consts.U_c) := by
      refine mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg consts.eNegGamma_pos.le consts.U_c_pos.le)
    exact (div_le_div_of_nonneg_right hnum_le hlogz_pos.le).trans hVN
  have hvj_strip_lb : ∀ k : Fin L,
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      let s := strips k
      vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV 16 (asymptoticCert.X_LS : ℝ))
          (rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) r_k s.t s.grid ≤
        External.VN N z * J_N N z ((z : ℝ) ^ r_k) := by
    intro k
    dsimp only
    set r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
    set s := strips k
    have hlog_z_LS_bounds : rayLogZLb 16 (asymptoticCert.X_LS : ℝ) ≤
        Real.log (z_fn asymptoticCert.X_LS) := by
      have h316 : 3 ^ 16 ≤ asymptoticCert.X_LS := by
        rw [← ten_pow_600_eq_asymptoticCert_X_LS]
        exact (Nat.pow_le_pow_left (by norm_num : 3 ≤ 10) 16).trans
          ((Nat.pow_le_pow_right (by norm_num : 1 ≤ 10) (by norm_num : 16 ≤ 200)).trans
            (Nat.le_self_pow (by norm_num) _))
      exact (log_rayZ_bounds (by norm_num) h316).1
    have hlog_z_LS_gt10 : 10 < rayLogZLb 16 (asymptoticCert.X_LS : ℝ) := by
      have hzlb_ge := rayZIntLb_gt_1e12 hlogLS_ge.le
      rw [rayLogZLb_eq_sub hlogLS_pos (by norm_num) (by linarith)]
      have hinv : 1 / rayZIntLb 16 (asymptoticCert.X_LS : ℝ) < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      linarith
    have hlog_mono := j_over_logz_lb_mono (by linarith [(hr_bounds k).1]) s.t (by rw [s.ht0])
      s.ht_mono (by rw [s.ht_end]) s.grid hlog_z_LS_gt10 hlog_z_LS_bounds
    have hdv_le_1LS : rayDeltaV 16 (asymptoticCert.X_LS : ℝ) ≤ 1 := hdv_le1 _ le_rfl
    have hvj_step1 : vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV 16 (asymptoticCert.X_LS : ℝ))
          (rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) r_k s.t s.grid ≤
        vj_monotone_lb consts.U_c consts.eNegGamma (dv_fn asymptoticCert.X_LS)
          (Real.log (z_fn asymptoticCert.X_LS)) r_k s.t s.grid := by
      unfold vj_monotone_lb
      refine mul_le_mul_of_nonneg_left hlog_mono ?_
      exact mul_nonneg (mul_nonneg consts.U_c_pos.le consts.eNegGamma_pos.le) (by linarith)
    have hvj_unif := (vj_monotone_lb_uniform_even_N hM consts.U_c_pos.le consts.eNegGamma_pos.le
      (hr_bounds k).1 (hr_bounds k).2 z_fn hz_gt_exp10 hz_mono dv_fn hdv_le1 hdv_anti hV_cond
      s.hk₁ s.t s.ht0 s.ht_end s.ht_mono s.grid
      (Or.inl ((hvj_pos k).le.trans hlog_mono)) hN_even hN).2
    have hfl_z : Nat.floor (z_fn N) = z := Nat.floor_natCast z
    rw [hfl_z] at hvj_unif
    exact hvj_step1.trans hvj_unif
  -- Remainder & main decomposition on each `q ∈ midPrimes N z y`
  have hmid_part := midPrimes_subset_biUnion_rayStripPrimes hL hN
  have hmid_eq : midPrimes N z y = Finset.univ.biUnion (rayStripPrimes N L) := by
    refine Finset.Subset.antisymm hmid_part ?_
    refine Finset.biUnion_subset.mpr fun k _ => Finset.filter_subset _ _
  have hVN_pos : 0 < External.VN N z := by
    rw [← eulerProd_shiftedPrimesBelow_eq_VN]
    unfold eulerProd
    refine Finset.prod_pos fun p hp => ?_
    have hm := Finset.mem_filter.mp hp
    have hp_odd : 3 ≤ p := by
      rcases hm.2.1.two_le.eq_or_lt with rfl | hgt
      · exact absurd (even_iff_two_dvd.mp hN_even) hm.2.2
      · omega
    rw [gTotRay_prime hm.2.1]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_odd
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have : 1 / ((p : ℝ) - 1) < 1 := (div_lt_one hp1).mpr (by linarith)
    linarith
  set P_z : Finset ℕ := shiftedPrimesBelow N z
  have hPz_eq_odd : P_z = (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N) := by
    ext p
    simp only [P_z, shiftedPrimesBelow, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hpz, hpr, hpN⟩
      have hp2 : 2 < p := by
        rcases hpr.two_le.eq_or_lt with rfl | hgt
        · exact absurd (even_iff_two_dvd.mp hN_even) hpN
        · exact hgt
      exact ⟨hpz, hpr, hp2, hpN⟩
    · rintro ⟨hpz, hpr, _, hpN⟩
      exact ⟨hpz, hpr, hpN⟩
  have hPz_prime : ∀ p ∈ P_z, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hPz_odd : ∀ p ∈ P_z, 2 < p := fun p hp => by
    rw [hPz_eq_odd] at hp; exact (Finset.mem_filter.mp hp).2.2.1
  have hg_Pz : ∀ p ∈ P_z, 0 < gTotRay p ∧ gTotRay p < 1 := by
    intro p hp
    rw [gTotRay_prime (hPz_prime p hp)]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hPz_odd p hp
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact ⟨by positivity, (div_lt_one hp1).mpr (by linarith)⟩
  have hj_eq_J_N : ∀ r : ℝ, selbergJ gTotRay P_z (Nat.floor ((z : ℝ) ^ r)) =
      J_N N z ((z : ℝ) ^ r) := by
    intro r
    unfold J_N selbergJ
    rw [hPz_eq_odd]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold selbergH
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [gTotRay_prime (Nat.prime_of_mem_primeFactors hp)]
  have hJ_ge1 : ∀ r : ℝ, 0 ≤ r → 1 ≤ J_N N z ((z : ℝ) ^ r) := by
    intro r hr
    rw [← hj_eq_J_N r]
    refine selbergJ_pos hPz_prime hg_Pz ?_
    exact Nat.le_floor (Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ z)) hr)
  have hmass_eq : sieveMass (shiftedSet N) (fun _ => (1 : ℝ)) = ((shiftedCoprimePrimes N).card : ℝ) := by
    unfold sieveMass shiftedSet
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_image_of_injOn]
    intro p₁ hp₁ p₂ hp₂ heq
    have hlt1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).1
    have hlt2 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).1
    dsimp only at heq
    omega
  have hgProd_sqf : ∀ L0 : ℕ, Squarefree L0 → gProd gTotRay L0 = gTotRay L0 := by
    intro L0 hL0
    unfold gProd gTotRay
    rw [totient_eq_prod_sub_one hL0, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.totient_prime (Nat.prime_of_mem_primeFactors hp), one_div]
  have hD_xi_props : ∀ xi0 : ℕ, ∀ L0 ∈ D_xi P_z xi0,
      1 ≤ L0 ∧ L0 ≤ xi0 ∧ Odd L0 ∧ Squarefree L0 ∧ Nat.Coprime L0 N := by
    intro xi0 L0 hL0
    have hm := Finset.mem_filter.mp hL0
    rcases Finset.mem_image.mp hm.1 with ⟨S, hS, rfl⟩
    have hS_sub : S ⊆ P_z := Finset.mem_powerset.mp hS
    have hpos : 1 ≤ ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hPz_prime p (hS_sub hp)).pos
    have hodd : Odd (∏ p ∈ S, p) := by
      refine Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun p hp => ?_
      have hp_mem := hS_sub hp
      have hmP := Finset.mem_filter.mp hp_mem
      have hne2 : p ≠ 2 := fun h => hmP.2.2 (h ▸ even_iff_two_dvd.mp hN_even)
      exact hmP.2.1.odd_of_ne_two hne2
    have hsqf_aux : ∀ T : Finset ℕ, T ⊆ P_z → Squarefree (∏ p ∈ T, p) := by
      intro T hT
      induction T using Finset.induction_on with
      | empty => simp
      | @insert a s has ih =>
        have ha_sub : a ∈ P_z := hT (Finset.mem_insert_self a s)
        have hs_sub : s ⊆ P_z := fun x hx => hT (Finset.mem_insert_of_mem hx)
        rw [Finset.prod_insert has]
        have ha_pr := hPz_prime a ha_sub
        have hcop : Nat.Coprime a (∏ x ∈ s, x) := by
          refine Nat.Coprime.prod_right fun x hx => ?_
          have hx_pr := hPz_prime x (hs_sub hx)
          exact (Nat.coprime_primes ha_pr hx_pr).mpr (fun hax => has (hax ▸ hx))
        exact (Nat.squarefree_mul hcop).mpr ⟨ha_pr.squarefree, ih hs_sub⟩
    have hsqf : Squarefree (∏ p ∈ S, p) := hsqf_aux S hS_sub
    have hcop : Nat.Coprime (∏ p ∈ S, p) N := by
      refine Nat.Coprime.prod_left fun p hp => ?_
      have hpP := Finset.mem_filter.mp (hS_sub hp)
      exact hpP.2.1.coprime_iff_not_dvd.mpr hpP.2.2
    exact ⟨hpos, hm.2, hodd, hsqf, hcop⟩
  have hlog_LS_z_gt10 : 10 < rayLogZLb 16 (asymptoticCert.X_LS : ℝ) := by
    have hzlb_ge := rayZIntLb_gt_1e12 hlogLS_ge.le
    rw [rayLogZLb_eq_sub hlogLS_pos (by norm_num) (by linarith)]
    have hinv : 1 / rayZIntLb 16 (asymptoticCert.X_LS : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  have hvj_pos_val : ∀ k : Fin L,
      0 < vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV 16 (asymptoticCert.X_LS : ℝ))
        (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
        (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
        (strips k).t (strips k).grid := by
    intro k
    have hdv_lt : rayDeltaV 16 (asymptoticCert.X_LS : ℝ) < 1 :=
      rayDeltaV_lt_one (by norm_num) (by norm_num) hXLS_pos hlogLS_160
    unfold vj_monotone_lb
    exact mul_pos (mul_pos (mul_pos consts.U_c_pos consts.eNegGamma_pos) (by linarith))
      (hvj_pos k)
  -- Helper: bound `((divisibleSievedShifted N z q).card : ℝ)` for `q ∈ rayStripPrimes N L k`
  have hq_selberg : ∀ (k : Fin L), ∀ q ∈ rayStripPrimes N L k,
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      let xi_k := Nat.floor ((z : ℝ) ^ r_k)
      let vj_lb := vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV 16 (asymptoticCert.X_LS : ℝ))
        (rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) r_k (strips k).t (strips k).grid
      ((divisibleSievedShifted N z q).card : ℝ) ≤
        (gTotRay q / vj_lb) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) +
          (∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card *
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)|) +
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| *
            (1 + ∑ L0 ∈ D_xi P_z (xi_k ^ 2),
              (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ)) := by
    intro k q hq
    dsimp only
    set r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
    set xi_k := Nat.floor ((z : ℝ) ^ r_k)
    set vj_lb := vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV 16 (asymptoticCert.X_LS : ℝ))
      (rayLogZLb 16 (asymptoticCert.X_LS : ℝ)) r_k (strips k).t (strips k).grid
    have hrk_pos : 0 ≤ r_k := (hr_bounds k).1.le.trans' zero_le_one
    have hxi_ge1 : 1 ≤ xi_k :=
      Nat.le_floor (Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ z)) hrk_pos)
    have hsel := selberg_optimal_upper_bound ((shiftedSet N).filter (q ∣ ·)) P_z
      (fun _ => (1 : ℝ)) gTotRay xi_k hPz_prime hg_Pz (fun _ _ => by norm_num) hxi_ge1
    rw [sieveCount_shiftedSet_filter_dvd] at hsel
    have hmass_q : sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) =
        gTotRay q * ((shiftedCoprimePrimes N).card : ℝ) +
          sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q := by
      rw [← hmass_eq]
      unfold sieveRem sieveDivMass sieveMass
      ring
    have hJ_pos : 0 < J_N N z ((z : ℝ) ^ r_k) := by linarith [hJ_ge1 r_k hrk_pos]
    have hJ_ge_one : 1 ≤ J_N N z ((z : ℝ) ^ r_k) := hJ_ge1 r_k hrk_pos
    have hmain_q : gTotRay q * ((shiftedCoprimePrimes N).card : ℝ) / J_N N z ((z : ℝ) ^ r_k) ≤
        (gTotRay q / vj_lb) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      have hvj_le : vj_lb ≤ External.VN N z * J_N N z ((z : ℝ) ^ r_k) := hvj_strip_lb k
      have hvj_pos_k := hvj_pos_val k
      have hg_nn : 0 ≤ gTotRay q := by unfold gTotRay; positivity
      have hratio : 1 / J_N N z ((z : ℝ) ^ r_k) ≤ External.VN N z / vj_lb := by
        rw [div_le_div_iff₀ hJ_pos hvj_pos_k, one_mul]
        exact hvj_le
      calc gTotRay q * ((shiftedCoprimePrimes N).card : ℝ) / J_N N z ((z : ℝ) ^ r_k)
          = (gTotRay q * ((shiftedCoprimePrimes N).card : ℝ)) * (1 / J_N N z ((z : ℝ) ^ r_k)) := by ring
        _ ≤ (gTotRay q * ((shiftedCoprimePrimes N).card : ℝ)) * (External.VN N z / vj_lb) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = (gTotRay q / vj_lb) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by ring
    have hq_mem := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
    have hq_pr : q.Prime := hq_mem.2.1
    have hq_dvdN : ¬ q ∣ N := hq_mem.2.2
    have hq_ge_z : z ≤ q := (Finset.mem_Ico.mp hq_mem.1).1
    have hq_cop_N : Nat.Coprime q N := hq_pr.coprime_iff_not_dvd.mpr hq_dvdN
    have hrem_q : |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| / J_N N z ((z : ℝ) ^ r_k) ≤
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| :=
      div_le_self (abs_nonneg _) hJ_ge_one
    have hrem_sum :
        ∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card *
          |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (gProd gTotRay) L0| ≤
        (∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card *
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)|) +
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| *
          ∑ L0 ∈ D_xi P_z (xi_k ^ 2),
            (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun L0 hL0 => ?_
      have hL0p := hD_xi_props (xi_k ^ 2) L0 hL0
      have hcop_qL0 : Nat.Coprime q L0 := by
        have hS := Finset.mem_filter.mp hL0
        rcases Finset.mem_image.mp hS.1 with ⟨S, hS_sub, rfl⟩
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hp_mem := Finset.mem_powerset.mp hS_sub hp
        have hp_lt_z : p < z := Finset.mem_range.mp (Finset.mem_filter.mp hp_mem).1
        exact (Nat.coprime_primes hq_pr (hPz_prime p hp_mem)).mpr (fun hqp => by omega)
      have hrem_eq := shifted_rem_aq_eq N q L0 hcop_qL0
      have hsrem_g : sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (gProd gTotRay) L0 =
          sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTotRay L0 := by
        unfold sieveRem
        rw [hgProd_sqf L0 hL0p.2.2.2.1]
      rw [hsrem_g]
      have hg_id : (gTotRay : ℕ → ℝ) = (fun k => 1 / (Nat.totient k : ℝ)) := rfl
      have habs_le : |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTotRay L0| ≤
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)| +
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| / (Nat.totient L0 : ℝ) := by
        rw [hg_id, hrem_eq]
        calc |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) (q * L0) -
              sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) q / (Nat.totient L0 : ℝ)|
            ≤ |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) (q * L0)| +
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) q / (Nat.totient L0 : ℝ)| :=
              abs_sub _ _
          _ = _ := by rw [abs_div, Nat.abs_cast]
      have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ L0.primeFactors.card := by positivity
      calc (3 : ℝ) ^ L0.primeFactors.card *
              |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTotRay L0|
          ≤ (3 : ℝ) ^ L0.primeFactors.card *
              (|sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)| +
                |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| / (Nat.totient L0 : ℝ)) :=
            mul_le_mul_of_nonneg_left habs_le h3nn
        _ = (3 : ℝ) ^ L0.primeFactors.card *
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)| +
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| *
                ((3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ)) := by ring
    have hrem_div : sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q / J_N N z ((z : ℝ) ^ r_k) ≤
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| :=
      (div_le_div_of_nonneg_right (le_abs_self _) hJ_pos.le).trans hrem_q
    rw [hmass_q, hj_eq_J_N r_k, add_div] at hsel
    linarith
  -- Helper: bound `∑ q ∈ rayStripPrimes N L k, gTotRay q`
  have hstrip_gsum : ∀ k : Fin L,
      ∑ q ∈ rayStripPrimes N L k, gTotRay q ≤
        (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) / (rayZIntLb 16 (asymptoticCert.X_LS : ℝ) - 1)) *
          raySumQSub 16 L k.1 (asymptoticCert.X_LS : ℝ) :=
    fun k => regime3_upper_strip_gsum_le hM hL hN k
  -- Bound the sum over `midPrimes N z y` of `(divisibleSievedShifted N z q).card`
  have hmain_biUnion :
      ∑ q ∈ midPrimes N z y, ((divisibleSievedShifted N z q).card : ℝ) =
        ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k, ((divisibleSievedShifted N z q).card : ℝ) := by
    rw [hmid_eq, Finset.sum_biUnion]
    intro i _ j _ hij
    exact rayStripPrimes_pairwiseDisjoint N L (Finset.mem_univ i) (Finset.mem_univ j) hij
  -- Bound `∑_{q ∈ midPrimes} ∑_{L0 ∈ D_xi P_z (xi_k^2)} 3^{ω(L0)} |R_{q*L0}|` (err_aq1)
  have herr_aq1_sum :
      ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
          ∑ L0 ∈ D_xi P_z ((Nat.floor ((z : ℝ) ^
              rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
            (3 : ℝ) ^ L0.primeFactors.card *
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)| ≤
        rayErrAq1Int consts 16 (N : ℝ) * rayScale consts.U_c 16 N := by
    set X_q_den : ℝ := (Real.log (N : ℝ)) ^ (11 / 2 : ℝ)
    have hX_q_den_pos : 0 < X_q_den := Real.rpow_pos_of_pos hlogN_pos _
    have hper_strip : ∀ k : Fin L, ∀ q ∈ rayStripPrimes N L k,
        let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
        let xi_k := Nat.floor ((z : ℝ) ^ r_k)
        (q : ℝ) * (xi_k : ℝ) ^ 2 ≤ Real.sqrt (N : ℝ) / X_q_den := by
      intro k q hq
      dsimp only
      set r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      set xi_k := Nat.floor ((z : ℝ) ^ r_k)
      have hrk_pos : 0 ≤ r_k := (hr_bounds k).1.le.trans' zero_le_one
      have hxi_le : (xi_k : ℝ) ≤ (z : ℝ) ^ r_k := Nat.floor_le (by positivity)
      have hxi2 : (xi_k : ℝ) ^ 2 ≤ (N : ℝ) ^ ((1 / 2 : ℝ) - rayAlphaQ (11 / 2 : ℝ) (N : ℝ) -
          rayStripU 16 L (k.1 + 1)) := by
        have h1 : (xi_k : ℝ) ^ 2 ≤ ((z : ℝ) ^ r_k) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hxi_le 2
        have h2 : ((z : ℝ) ^ r_k) ^ 2 ≤ ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * r_k) := by
          have hzr : (z : ℝ) ^ r_k ≤ ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ r_k :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hz_le_z0 hrk_pos
          have hpow := pow_le_pow_left₀ (by positivity) hzr 2
          have hmul2 : (((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ r_k) ^ 2 =
              ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * r_k) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            ring_nf
          exact hpow.trans_eq hmul2
        have h3 : ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) ^ (2 * r_k) = (N : ℝ) ^ (r_k / 8) := by
          rw [← Real.rpow_mul hN_pos.le]
          ring_nf
        have hexp_le : r_k / 8 ≤ (1 / 2 : ℝ) - rayAlphaQ (11 / 2 : ℝ) (N : ℝ) -
            rayStripU 16 L (k.1 + 1) := by
          have hr_def : r_k ≤ 0.5 * (16 : ℝ) * (0.5 - rayAlphaQ (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) -
              rayStripU 16 L (k.1 + 1)) := min_le_right _ _
          have haq_anti : rayAlphaQ (11 / 2 : ℝ) (N : ℝ) ≤
              rayAlphaQ (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) := by
            have he1 : Real.exp 1 ≤ Real.log (asymptoticCert.X_LS : ℝ) := by
              have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
              linarith
            exact rayAlphaQ_antitone (by norm_num) hXLS_pos he1 hN_real_ge
          linarith
        exact h1.trans (h2.trans (h3.le.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp_le)))
      have hq_lt : (q : ℝ) < (N : ℝ) ^ rayStripU 16 L (k.1 + 1) := by
        have hmf := (Finset.mem_filter.mp hq).2
        rcases Nat.eq_zero_or_pos k.1 with hk0 | hkpos
        · simpa [hk0] using hmf.1 hk0
        · exact (hmf.2 hkpos).2
      have hmul : (q : ℝ) * (xi_k : ℝ) ^ 2 ≤
          (N : ℝ) ^ rayStripU 16 L (k.1 + 1) *
            (N : ℝ) ^ ((1 / 2 : ℝ) - rayAlphaQ (11 / 2 : ℝ) (N : ℝ) - rayStripU 16 L (k.1 + 1)) :=
        mul_le_mul hq_lt.le hxi2 (sq_nonneg _) (by positivity)
      have hrp_eq : (N : ℝ) ^ rayStripU 16 L (k.1 + 1) *
            (N : ℝ) ^ ((1 / 2 : ℝ) - rayAlphaQ (11 / 2 : ℝ) (N : ℝ) - rayStripU 16 L (k.1 + 1)) =
          Real.sqrt (N : ℝ) / X_q_den := by
        rw [← Real.rpow_add hN_pos]
        have hexp : rayStripU 16 L (k.1 + 1) +
            ((1 / 2 : ℝ) - rayAlphaQ (11 / 2 : ℝ) (N : ℝ) - rayStripU 16 L (k.1 + 1)) =
            (1 / 2 : ℝ) - rayAlphaQ (11 / 2 : ℝ) (N : ℝ) := by ring
        rw [hexp, Real.rpow_sub hN_pos, Real.sqrt_eq_rpow]
        congr 1
        unfold rayAlphaQ X_q_den
        rw [Real.rpow_def_of_pos hN_pos, Real.rpow_def_of_pos hlogN_pos]
        congr 1
        field_simp [hlogN_pos.ne']
      exact hmul.trans_eq hrp_eq
    have hper_q : ∀ k : Fin L, ∀ q ∈ rayStripPrimes N L k,
        let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
        let xi_k := Nat.floor ((z : ℝ) ^ r_k)
        (∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card *
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)|) ≤
        ((1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / X_q_den) * ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 *
          (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ))) * ((1 : ℝ) / (q : ℝ)) := by
      intro k q hq
      dsimp only
      set r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      set xi_k := Nat.floor ((z : ℝ) ^ r_k)
      have hqm := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
      have hq_pr : q.Prime := hqm.2.1
      have hq_dvdN : ¬ q ∣ N := hqm.2.2
      have hq_ge_z : z ≤ q := (Finset.mem_Ico.mp hqm.1).1
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pr.pos
      have hbd := hper_strip k q hq
      have hX_q_ge1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den) := by
        have hxi_ge1 : 1 ≤ xi_k :=
          Nat.le_floor (Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ z))
            ((hr_bounds k).1.le.trans' zero_le_one))
        have h1 : (1 : ℝ) ≤ (xi_k : ℝ) ^ 2 := by exact_mod_cast (Nat.one_le_pow 2 xi_k hxi_ge1)
        have h1x : 1 * ((q : ℝ) * X_q_den) ≤ (xi_k : ℝ) ^ 2 * ((q : ℝ) * X_q_den) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hq_pos.le hX_q_den_pos.le)
        have hbd' : (xi_k : ℝ) ^ 2 * ((q : ℝ) * X_q_den) ≤ Real.sqrt (N : ℝ) := by
          rw [← mul_assoc, mul_comm ((xi_k : ℝ) ^ 2) (q : ℝ)]
          exact (le_div_iff₀ hX_q_den_pos).mp hbd
        exact (le_div_iff₀ (mul_pos hq_pos hX_q_den_pos)).mpr (h1x.trans hbd')
      have hX_q_le_sqrt : Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den) ≤ Real.sqrt (N : ℝ) := by
        have hden_ge1 : 1 ≤ (q : ℝ) * X_q_den := by
          have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.one_lt.le
          have hx1 : 1 ≤ X_q_den := Real.one_le_rpow (by linarith) (by norm_num)
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (q : ℝ) * X_q_den := mul_le_mul hq1 hx1 (by norm_num) (by linarith)
        exact div_le_self (Real.sqrt_nonneg _) hden_ge1
      have hrem_bd : ∀ L0 ∈ D_xi P_z (xi_k ^ 2),
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)| ≤
            rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
        intro L0 hL0
        have hL0p := hD_xi_props (xi_k ^ 2) L0 hL0
        have hq3 : 3 ≤ q := by
          have : (3 : ℝ) ≤ (z : ℝ) := by linarith
          have hz3 : 3 ≤ z := by exact_mod_cast this
          exact hz3.trans hq_ge_z
        have hqL0_3 : 3 ≤ q * L0 := hq3.trans (Nat.le_mul_of_pos_right q hL0p.1)
        have hqL0_sqrt : ((q * L0 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
          have hL0_le : (L0 : ℝ) ≤ (xi_k : ℝ) ^ 2 := by exact_mod_cast hL0p.2.1
          have h1 : ((q * L0 : ℕ) : ℝ) ≤ (q : ℝ) * (xi_k : ℝ) ^ 2 := by
            push_cast
            exact mul_le_mul_of_nonneg_left hL0_le hq_pos.le
          have h2 : Real.sqrt (N : ℝ) / X_q_den ≤ Real.sqrt (N : ℝ) :=
            div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow (by linarith) (by norm_num))
          exact h1.trans (hbd.trans h2)
        have hcop : Nat.Coprime (q * L0) N :=
          Nat.Coprime.mul_left (hq_pr.coprime_iff_not_dvd.mpr hq_dvdN) hL0p.2.2.2.2
        exact shifted_rem_bound_rayCPt consts hGRH hCls hN_4e18 hqL0_3 hqL0_sqrt hcop
      have hsum_rem :
          ∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card *
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)| ≤
          (∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card) *
            (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun L0 hL0 =>
          mul_le_mul_of_nonneg_left (hrem_bd L0 hL0) (pow_nonneg (by norm_num) _)
      have hD_sub_od : D_xi P_z (xi_k ^ 2) ⊆
          (Finset.Icc 1 (Nat.floor (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)))).filter
            (fun L0 => Odd L0 ∧ Squarefree L0) := by
        intro L0 hL0
        have hL0p := hD_xi_props (xi_k ^ 2) L0 hL0
        have hle_fl : L0 ≤ Nat.floor (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) := by
          refine Nat.le_floor ?_
          have h1 : (L0 : ℝ) ≤ (xi_k : ℝ) ^ 2 := by exact_mod_cast hL0p.2.1
          have h2 : (xi_k : ℝ) ^ 2 ≤ Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den) := by
            rw [le_div_iff₀ (mul_pos hq_pos hX_q_den_pos), ← mul_assoc]
            have hbd' : (xi_k : ℝ) ^ 2 * (q : ℝ) ≤ Real.sqrt (N : ℝ) / X_q_den := by
              rw [mul_comm]; exact hbd
            exact (le_div_iff₀ hX_q_den_pos).mp hbd'
          exact h1.trans h2
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hL0p.1, hle_fl⟩, hL0p.2.2.1, hL0p.2.2.2.1⟩
      have h3_le : ∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card ≤
          (1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) *
            ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 := by
        have h1 : ∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card ≤
            ∑ L0 ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)))).filter
              (fun L0 => Odd L0 ∧ Squarefree L0), (3 : ℝ) ^ L0.primeFactors.card :=
          Finset.sum_le_sum_of_subset_of_nonneg hD_sub_od fun _ _ _ => by positivity
        have h2 := odd_squarefree_three_pow_omega_le (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) hX_q_ge1
        have hlog_le : Real.log (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
          calc Real.log (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den))
              ≤ Real.log (Real.sqrt (N : ℝ)) :=
                Real.log_le_log (by positivity) hX_q_le_sqrt
            _ = (1 / 2 : ℝ) * Real.log (N : ℝ) := by rw [Real.log_sqrt hN_pos.le]; ring
        have hlog_nn : 0 ≤ Real.log (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) + 6 := by
          have := Real.log_nonneg hX_q_ge1; linarith
        have hsq_le : (Real.log (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) + 6) ^ 2 ≤
            ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 :=
          pow_le_pow_left₀ hlog_nn (by linarith) 2
        have hmul_le := mul_le_mul_of_nonneg_left hsq_le
          (show 0 ≤ (1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) by positivity)
        exact h1.trans (h2.trans hmul_le)
      have hrem_nn : 0 ≤ rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
        have hcpt_nn : 0 ≤ rayCPt consts (N : ℝ) := rayCPt_nonneg consts hN_pos (by
          linarith [Real.exp_one_lt_d9, hlogN_ge])
        positivity
      calc ∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card *
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)|
          ≤ (∑ L0 ∈ D_xi P_z (xi_k ^ 2), (3 : ℝ) ^ L0.primeFactors.card) *
              (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) := hsum_rem
        _ ≤ ((1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / ((q : ℝ) * X_q_den)) *
              ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2) *
              (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_right h3_le hrem_nn
        _ = ((1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / X_q_den) * ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 *
              (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ))) * ((1 : ℝ) / (q : ℝ)) := by
            ring
    have hsum_q_inv_mid : ∑ q ∈ midPrimes N z y, (1 : ℝ) / (q : ℝ) ≤ raySumQInvInt 16 (N : ℝ) := by
      set w0 : ℝ := (N : ℝ) ^ (1 / (16 : ℝ))
      set z1 : ℝ := (N : ℝ) ^ rayBeta 16
      have hw0_ge2 : 2 ≤ w0 := by
        have hz0 : (10 : ℝ) ^ 12 + 2 < w0 := by
          dsimp only [w0]; rw [show (1 / (16 : ℝ)) = (1 : ℝ) / ((16 : ℕ) : ℝ) by norm_num, ← rayZ0_eq_rpow hN_pos]
          have := rayZIntLb_gt_1e12 hlogN_ge.le; unfold rayZIntLb at this; linarith
        linarith
      have hw0_lt_z1 : w0 < z1 := Real.rpow_lt_rpow_of_exponent_lt (by linarith)
        (one_div_lt_rayBeta (by norm_num))
      have hmert := mertens_sum_Ico_le hM.mertensSumBounds hw0_ge2 hw0_lt_z1
      have hsub : midPrimes N z y ⊆
          insert z ((Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime) := by
        intro q hq
        have hqm := Finset.mem_filter.mp hq
        have hqb := Finset.mem_Ico.mp hqm.1
        rcases eq_or_lt_of_le hqb.1 with rfl | hqgt
        · exact Finset.mem_insert_self z _
        · apply Finset.mem_insert_of_mem
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hqm.2.1⟩
          · refine Nat.ceil_le.mpr ?_
            have hfl_lt : w0 < (z : ℝ) + 1 := by unfold z rayZ w0; exact Nat.lt_floor_add_one _
            have hz1_le : (z : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hqgt
            linarith
          · refine Nat.lt_ceil.mpr ?_
            exact lt_of_lt_of_le (by exact_mod_cast hqb.2) hy_le_beta
      have hsum_ins : ∑ q ∈ midPrimes N z y, (1 : ℝ) / (q : ℝ) ≤
          (1 / (z : ℝ)) +
            ∑ q ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) := by
        calc ∑ q ∈ midPrimes N z y, (1 : ℝ) / (q : ℝ)
            ≤ ∑ q ∈ insert z ((Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime),
                (1 : ℝ) / (q : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
          _ ≤ (1 : ℝ) / (z : ℝ) +
                ∑ q ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) := by
              by_cases hzmem : z ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime
              · rw [Finset.insert_eq_of_mem hzmem]
                exact le_add_of_nonneg_left (by positivity)
              · rw [Finset.sum_insert hzmem]
      have hz1_gt : (10 : ℝ) ^ 12 < z1 := by
        have hw0_1e12 : (10 : ℝ) ^ 12 < w0 := by
          have : (z : ℝ) ≤ w0 := hz_le_z0
          linarith [hz_1e12]
        exact hw0_1e12.trans hw0_lt_z1
      have hhi : External.jsMertensHiErr z1 ≤ (6.836e-6 : ℝ) / ((1 / (16 : ℝ)) * Real.log (N : ℝ)) := by
        unfold External.jsMertensHiErr
        simp only [hz1_gt, ↓reduceIte]
        have hlogz1 : Real.log z1 = rayBeta 16 * Real.log (N : ℝ) := by
          dsimp only [z1]; rw [Real.log_rpow hN_pos]
        have hle : (1 / (16 : ℝ)) * Real.log (N : ℝ) ≤ Real.log z1 := by
          rw [hlogz1]
          exact mul_le_mul_of_nonneg_right (one_div_lt_rayBeta (by norm_num)).le hlogN_pos.le
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hle
      have hlo : External.jsMertensLoErr w0 = (2.964e-6 : ℝ) / ((1 / (16 : ℝ)) * Real.log (N : ℝ)) := by
        unfold External.jsMertensLoErr
        dsimp only [w0]; rw [Real.log_rpow hN_pos]
      have hlog_ratio : Real.log (Real.log z1 / Real.log w0) = Real.log (rayBeta 16 * 16) := by
        have hlogw0 : Real.log w0 = (1 / (16 : ℝ)) * Real.log (N : ℝ) := by
          dsimp only [w0]; rw [Real.log_rpow hN_pos]
        have hlogz1 : Real.log z1 = rayBeta 16 * Real.log (N : ℝ) := by
          dsimp only [z1]; rw [Real.log_rpow hN_pos]
        rw [hlogz1, hlogw0, mul_div_mul_right _ _ hlogN_pos.ne']
        congr 1; ring
      have hz_inv : 1 / (z : ℝ) ≤ 1 / (rayZIntLb 16 (N : ℝ) - 1) := by
        have hzlb_20k : (20000 : ℝ) ≤ rayZIntLb 16 (N : ℝ) :=
          rayZIntLb_ge_20000 (by norm_num : 1 ≤ 16) hlogN_160
        have hpos : 0 < rayZIntLb 16 (N : ℝ) - 1 := by linarith
        exact one_div_le_one_div_of_le hpos ((sub_le_self _ zero_le_one).trans hz_ge_lb)
      unfold raySumQInvInt
      rw [hlog_ratio, hlo] at hmert
      have h16_cast : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
      have hhi_lo : External.jsMertensHiErr z1 + (2.964e-6 : ℝ) / (1 / 16 * Real.log (N : ℝ)) ≤
          ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / ((1 / ((16 : ℕ) : ℝ)) * Real.log (N : ℝ)) := by
        have h1 : External.jsMertensHiErr z1 + (2.964e-6 : ℝ) / (1 / 16 * Real.log (N : ℝ)) ≤
            (6.836e-6 : ℝ) / ((1 / (16 : ℝ)) * Real.log (N : ℝ)) +
              (2.964e-6 : ℝ) / (1 / 16 * Real.log (N : ℝ)) := add_le_add hhi le_rfl
        have h2 : (6.836e-6 : ℝ) / ((1 / (16 : ℝ)) * Real.log (N : ℝ)) +
              (2.964e-6 : ℝ) / (1 / 16 * Real.log (N : ℝ)) =
            ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / ((1 / ((16 : ℕ) : ℝ)) * Real.log (N : ℝ)) := by
          rw [h16_cast]; ring
        exact h1.trans_eq h2
      have hmert' : ∑ q ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ≤
          Real.log (rayBeta 16 * 16) +
            (External.jsMertensHiErr z1 + (2.964e-6 : ℝ) / (1 / 16 * Real.log (N : ℝ))) := by
        linarith
      have hsum_mert_hi :
          ∑ q ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ≤
            Real.log (rayBeta 16 * 16) +
              ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / ((1 / ((16 : ℕ) : ℝ)) * Real.log (N : ℝ)) :=
        hmert'.trans (add_le_add (le_refl (Real.log (rayBeta 16 * 16))) hhi_lo)
      calc ∑ q ∈ midPrimes N z y, (1 : ℝ) / (q : ℝ)
          ≤ (1 : ℝ) / (z : ℝ) +
              ∑ q ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil z1)).filter Nat.Prime, (1 : ℝ) / (q : ℝ) :=
            hsum_ins
        _ ≤ 1 / (rayZIntLb 16 (N : ℝ) - 1) +
              (Real.log (rayBeta 16 * 16) +
                ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / ((1 / ((16 : ℕ) : ℝ)) * Real.log (N : ℝ))) :=
            add_le_add hz_inv hsum_mert_hi
        _ = Real.log (rayBeta 16 * 16) +
              ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / ((1 / ((16 : ℕ) : ℝ)) * Real.log (N : ℝ)) +
              1 / (rayZIntLb 16 (N : ℝ) - 1) := by ring
    have hcoeff_nn : 0 ≤ (1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / X_q_den) *
        ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 *
        (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) := by
      have hcpt_nn : 0 ≤ rayCPt consts (N : ℝ) := rayCPt_nonneg consts hN_pos (by
        have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        linarith)
      positivity
    calc ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
            ∑ L0 ∈ D_xi P_z ((Nat.floor ((z : ℝ) ^
                rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
              (3 : ℝ) ^ L0.primeFactors.card *
                |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)|
        ≤ ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
            ((1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / X_q_den) * ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 *
              (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ))) * ((1 : ℝ) / (q : ℝ)) := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun q hq => hper_q k q hq
      _ = ((1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / X_q_den) * ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 *
            (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ))) *
              ∑ q ∈ midPrimes N z y, (1 : ℝ) / (q : ℝ) := by
          simp_rw [← Finset.mul_sum]
          rw [hmid_eq, Finset.sum_biUnion (fun i _ j _ hij =>
            rayStripPrimes_pairwiseDisjoint N L (Finset.mem_univ i) (Finset.mem_univ j) hij)]
      _ ≤ ((1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / X_q_den) * ((1 / 2 : ℝ) * Real.log (N : ℝ) + 6) ^ 2 *
            (rayCPt consts (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ))) * raySumQInvInt 16 (N : ℝ) :=
          mul_le_mul_of_nonneg_left hsum_q_inv_mid hcoeff_nn
      _ = rayErrAq1Int consts 16 (N : ℝ) * (16 * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
          unfold rayErrAq1Int
          dsimp only [X_q_den]
          set lN : ℝ := Real.log (N : ℝ)
          set lp : ℝ := Real.rpow lN ((11 / 2 : ℝ) - 3)
          set C : ℝ := rayCPt consts (N : ℝ)
          set Qinv : ℝ := raySumQInvInt 16 (N : ℝ)
          set U : ℝ := consts.U_c
          have hlog_ne : lN ≠ 0 := hlogN_pos.ne'
          have hUc_ne : U ≠ 0 := consts.U_c_pos.ne'
          have hsq_pow : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN_pos.le
          have hp2 : lp ≠ 0 := (Real.rpow_pos_of_pos hlogN_pos _).ne'
          have hrpow_eq : lN ^ (11 / 2 : ℝ) = lp * lN ^ 3 := by
            have h3 : lN ^ (3 : ℝ) = lN ^ (3 : ℕ) := Real.rpow_natCast lN 3
            calc lN ^ (11 / 2 : ℝ)
                = lN ^ (((11 / 2 : ℝ) - 3) + 3) := by congr 1; ring
              _ = lN ^ ((11 / 2 : ℝ) - 3) * lN ^ (3 : ℝ) := Real.rpow_add hlogN_pos _ _
              _ = lp * lN ^ (3 : ℕ) := by rw [h3]; rfl
          have h16_cast : ((16 : ℕ) : ℝ) = (16 : ℝ) := by norm_num
          have h05 : (0.5 : ℝ) = (1 / 2 : ℝ) := by norm_num
          have h00625 : (0.0625 : ℝ) = (1 / 16 : ℝ) := by norm_num
          rw [hrpow_eq, h16_cast, h05, h00625]
          change ((1 / 16 : ℝ) * (Real.sqrt (N : ℝ) / (lp * lN ^ 3)) * ((1 / 2 : ℝ) * lN + 6) ^ 2 *
              (C * Real.sqrt (N : ℝ) * lN)) * Qinv =
            (((1 / 16 : ℝ) * C * Qinv / (16 * U)) * ((1 / 2 : ℝ) * lN + 6) ^ 2 / lp) *
              (16 * U * (N : ℝ) / lN ^ 2)
          field_simp [hlog_ne, hUc_ne, hp2]
          simp only [hsq_pow]
          ring
      _ ≤ rayErrAq1Int consts 16 (N : ℝ) * rayScale consts.U_c 16 N :=
          mul_le_mul_of_nonneg_left
            (rayScale_ge_mul_div_log_sq (by norm_num) hGRH hCls hN_4e18)
            (rayErrAq1Int_nonneg consts hN_pos hlogN_ge)
  -- Bound `∑_{q ∈ midPrimes} |R_q| * (1 + ∑ 3^{ω(L0)} / φ(L0))` (`2 * rayErrAq2 * rayScale`)
  have herr_aq2_sum :
      ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| *
            (1 + ∑ L0 ∈ D_xi P_z ((Nat.floor ((z : ℝ) ^
                rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
              (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ)) ≤
        2 * rayErrAq2 consts 16 (N : ℝ) * rayScale consts.U_c 16 N :=
    regime3_upper_aq2_le consts hH_tilde halpha0 hGRH hCls hN hmid_eq hy_le_beta hr_bounds hD_xi_props
  -- Combine main term + `err_aq1` + `err_aq2`
  have hsum_all :
      ∑ q ∈ midPrimes N z y, ((divisibleSievedShifted N z q).card : ℝ) ≤
        raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips (asymptoticCert.X_LS : ℝ) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) +
          rayErrAq1Int consts 16 (N : ℝ) * rayScale consts.U_c 16 N +
          2 * rayErrAq2 consts 16 (N : ℝ) * rayScale consts.U_c 16 N := by
    rw [hmain_biUnion]
    have h1 : ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k, ((divisibleSievedShifted N z q).card : ℝ) ≤
        ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
          ((gTotRay q / vj_monotone_lb consts.U_c consts.eNegGamma
              (rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
              (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
              (strips k).t (strips k).grid) *
              (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) +
            (∑ L0 ∈ D_xi P_z ((Nat.floor ((z : ℝ) ^
                rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
              (3 : ℝ) ^ L0.primeFactors.card *
                |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)|) +
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay q| *
              (1 + ∑ L0 ∈ D_xi P_z ((Nat.floor ((z : ℝ) ^
                  rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
                (3 : ℝ) ^ L0.primeFactors.card / (Nat.totient L0 : ℝ))) :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun q hq => hq_selberg k q hq
    simp_rw [Finset.sum_add_distrib] at h1
    have hmain_sum :
        (∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
          (gTotRay q / vj_monotone_lb consts.U_c consts.eNegGamma
              (rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
              (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
              (strips k).t (strips k).grid) *
              (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z)) ≤
        raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips (asymptoticCert.X_LS : ℝ) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      have hfactor : ∀ k : Fin L,
          (∑ q ∈ rayStripPrimes N L k,
            (gTotRay q / vj_monotone_lb consts.U_c consts.eNegGamma
                (rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
                (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
                (strips k).t (strips k).grid) *
                (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z)) =
          ((∑ q ∈ rayStripPrimes N L k, gTotRay q) /
              vj_monotone_lb consts.U_c consts.eNegGamma
                (rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
                (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
                (strips k).t (strips k).grid) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
        intro k
        rw [← Finset.sum_mul, ← Finset.sum_div]
      simp_rw [hfactor]
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg _) hVN_pos.le)
      unfold raySumAqMain
      refine Finset.sum_le_sum fun k _ => ?_
      exact div_le_div_of_nonneg_right (hstrip_gsum k) (hvj_pos_val k).le
    linarith [h1, hmain_sum, herr_aq1_sum, herr_aq2_sum]
  have herr_aq1_nn : 0 ≤ rayErrAq1Int consts 16 (N : ℝ) * rayScale consts.U_c 16 N :=
    mul_nonneg (rayErrAq1Int_nonneg consts hN_pos hlogN_ge)
      (rayScale_pos (consts := consts) (M := 16) (N := N) (by norm_num) hGRH hCls hN_4e18).le
  linarith [hsum_all, herr_aq1_nn]

end SieveBounds

end

end BuchstabSwitching
