import BuchstabSwitching.Sieve.Regime3RayBridge.IntegerCutoffs
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.LowerSieve
import BuchstabSwitching.Sieve.Regime3RayBridge.UpperSieve
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.LinearSieveBJS
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.Certificates.Data
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

section SieveBounds

/-- Prime-square remainder bound `(1/2) ∑_{q ∈ midPrimes} |A_{N,q²}| ≤ err_q2 * rayScale`
for even `N ≥ 10^600` (`regime_asymptotic.py:156`). -/
theorem regime3_square_sum_ub (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    {N : ℕ} (hN : asymptoticCert.X_LS ≤ N) :
    (1 / 2 : ℝ) * ∑ q ∈ midPrimes N (rayZ 16 N) (rayY 16 N),
        ((squareDivisibleShifted N q).card : ℝ) ≤
      rayErrQ2Int consts 16 (N : ℝ) * rayScale consts.U_c 16 N := by
  obtain ⟨_, hN_pos, _, hlogN_ge, hN_4e18, hN_2pow16, _⟩ := X_LS_facts hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hcut := regime3_cutoffs_basic (by norm_num : 1 ≤ 16) hN_2pow16
  set z : ℕ := rayZ 16 N
  set y : ℕ := rayY 16 N
  have hz2 : 2 ≤ z := hcut.1
  have hz_ge_lb : rayZIntLb 16 (N : ℝ) ≤ (z : ℝ) := by
    unfold rayZIntLb; rw [rayZ0_eq_rpow hN_pos]; unfold z rayZ
    exact (Nat.sub_one_lt_floor _).le
  have hlogN_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by norm_num; linarith
  have hzlb_20k := rayZIntLb_ge_20000 (X := (N : ℝ)) (by norm_num : 1 ≤ 16) hlogN_160
  have hsub : midPrimes N z y ⊆ (Finset.Ico z y).filter Nat.Prime := fun q hq =>
    let hm := Finset.mem_filter.mp hq; Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩
  have hsum_card : (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
      (1 / 2 : ℝ) * ((N : ℝ) / (rayZIntLb 16 (N : ℝ) - 1)) := by
    have h1 : ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
        ∑ q ∈ (Finset.Ico z y).filter Nat.Prime, (N : ℝ) / (q : ℝ) ^ 2 := by
      calc ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ)
          ≤ ∑ q ∈ (Finset.Ico z y).filter Nat.Prime, ((squareDivisibleShifted N q).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ ∑ q ∈ (Finset.Ico z y).filter Nat.Prime, (N : ℝ) / (q : ℝ) ^ 2 :=
            Finset.sum_le_sum fun q _ => squareDivisible_card_le_div N q
    have h2 : ∑ q ∈ (Finset.Ico z y).filter Nat.Prime, (N : ℝ) / (q : ℝ) ^ 2 ≤
        (N : ℝ) / ((z : ℝ) - 1) := by
      have htel := inv_sq_sum_Ico_primes_le (b := y) hz2
      have hmul := mul_le_mul_of_nonneg_left htel hN_pos.le
      calc ∑ q ∈ (Finset.Ico z y).filter Nat.Prime, (N : ℝ) / (q : ℝ) ^ 2
          = (N : ℝ) * ∑ q ∈ (Finset.Ico z y).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => by ring
        _ ≤ (N : ℝ) * (1 / ((z : ℝ) - 1)) := hmul
        _ = (N : ℝ) / ((z : ℝ) - 1) := by ring
    have h3 : (N : ℝ) / ((z : ℝ) - 1) ≤ (N : ℝ) / (rayZIntLb 16 (N : ℝ) - 1) :=
      div_le_div_of_nonneg_left hN_pos.le (by linarith) (by linarith)
    linarith
  have hid : (1 / 2 : ℝ) * ((N : ℝ) / (rayZIntLb 16 (N : ℝ) - 1)) =
      rayErrQ2Int consts 16 (N : ℝ) * (16 * consts.U_c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
    unfold rayErrQ2Int
    have hlog_ne : Real.log (N : ℝ) ≠ 0 := hlogN_pos.ne'
    have hUc_ne : consts.U_c ≠ 0 := consts.U_c_pos.ne'
    have hz1_ne : rayZIntLb 16 (N : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hlog_ne, hUc_ne, hz1_ne]
    norm_num
  have herr_nn : 0 ≤ rayErrQ2Int consts 16 (N : ℝ) := by
    unfold rayErrQ2Int; have := consts.U_c_pos; have : 0 < rayZIntLb 16 (N : ℝ) - 1 := by linarith
    positivity
  exact hsum_card.trans (hid.le.trans (mul_le_mul_of_nonneg_left
    (rayScale_ge_mul_div_log_sq (by norm_num) hGRH hCls hN_4e18) herr_nn))

end SieveBounds

/-! ## 5. Master Regime 3 Uniform Asymptotic Ray Theorems -/

section MasterTheorems

/-- `External.switchingBalanceReal N z y ≤ (switchingBalance N z y : ℝ)` since every `q ∣ N` term
is nonnegative and `midPrimes N z y ⊆ (Finset.Ico z y).filter Nat.Prime`. -/
theorem switchingBalanceReal_le_switchingBalance (N z y : ℕ) :
    External.switchingBalanceReal N z y ≤ (switchingBalance N z y : ℝ) := by
  unfold External.switchingBalanceReal switchingBalance
  push_cast
  have hfirst : (((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧
      ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p)).card : ℝ) =
      ((sievedShifted N z).card : ℝ) := by
    congr 2
    ext p
    simp only [sievedShifted, shiftedCoprimePrimes, Finset.mem_filter, Finset.mem_range]
    tauto
  have hsub : midPrimes N z y ⊆ (Finset.Ico z y).filter Nat.Prime := fun q hq =>
    let hm := Finset.mem_filter.mp hq; Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩
  have hsum : ∑ q ∈ midPrimes N z y,
      (((divisibleSievedShifted N z q).card : ℝ) + ((squareDivisibleShifted N q).card : ℝ)) ≤
      ∑ q ∈ (Finset.Ico z y).filter Nat.Prime,
        ((((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧
            (∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p) ∧ q ∣ N - p)).card : ℝ) +
         (((Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ q ^ 2 ∣ N - p)).card : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_ |>.trans_eq ?_
    · intro _ _ _; positivity
    · refine Finset.sum_congr rfl fun q _ => ?_
      congr 2
      · congr 2; ext p
        simp only [divisibleSievedShifted, sievedShifted, shiftedCoprimePrimes, Finset.mem_filter,
          Finset.mem_range]
        tauto
      · congr 2; ext p
        simp only [squareDivisibleShifted, shiftedCoprimePrimes, Finset.mem_filter, Finset.mem_range]
        tauto
  linarith

/-- Purely analytic uniform lower bound on `switchingBalance N (rayZ 16 N) (rayY 16 N)` for all
even `N ≥ asymptoticCert.X_LS = 10^600`, evaluated uniformly at `X_LS` via Section 3 monotonicity
and Sections 1–4 sieve bounds. -/
theorem regime3_switchingBalance_analytic_lb (consts : External.CertifiedConstants)
    (hH_tilde : H_tilde ≤ consts.H_tilde) (halpha0 : alpha0 ≤ consts.alpha0)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0)
    (hV : External.EulerProductVGRHPremise consts.U_c consts.eNegGamma)
    (hBJS : External.BuchstabSeriesPremise)
    (hHStar : ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0_100) (1 + (1 : ℝ) / 100))
    (hC2_nn : (0 : ℝ) ≤ C2_bjs constDecaySeq (1 / 100 : ℝ))
    {L : ℕ} (hL : 1 ≤ L)
    (strips : ∀ k : Fin L, RaySelbergStrip
      (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))))
    (hvj_pos : ∀ k : Fin L,
      0 < j_over_logz_lb (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
        (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
        (strips k).t (strips k).grid)
    (hbr_LS : 0 ≤ rayLbA 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
        (C2_bjs constDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) -
      (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
        (asymptoticCert.X_LS : ℝ))
    {N : ℕ} (hN_even : Even N) (hN : asymptoticCert.X_LS ≤ N) :
    let z := rayZ 16 N
    let y := rayY 16 N
    2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 4 ∧ N ≤ z * y ^ 3 ∧ 0 < rayScale consts.U_c 16 N ∧
      (rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ)))
          (1 / 100 : ℝ) (C2_bjs constDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) strips
          (asymptoticCert.X_LS : ℝ) -
        rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ)) * rayScale consts.U_c 16 N ≤
        (switchingBalance N z y : ℝ) := by
  obtain ⟨hXLS_pos, hN_pos, hlogLS_ge, hlogN_ge, hN_4e18, hN_2pow16, _⟩ := X_LS_facts hN
  have hN_real_ge : (asymptoticCert.X_LS : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hlogLS_pos : 0 < Real.log (asymptoticCert.X_LS : ℝ) := by linarith
  have hXLS_ge1 : (1 : ℝ) ≤ (asymptoticCert.X_LS : ℝ) :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1200)).trans exp_1200_lt_asymptoticCert_X_LS.le
  have hlogLS_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (asymptoticCert.X_LS : ℝ) := by norm_num; linarith
  have hlogN_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by norm_num; linarith
  have hcut := regime3_cutoffs_valid (by norm_num : 4 ≤ 16) hN_2pow16
  have hscale_pos := rayScale_pos (consts := consts) (M := 16) (N := N)
    (by norm_num) hGRH hCls hN_4e18
  refine ⟨hcut.1, hcut.2.1, hcut.2.2.1, hcut.2.2.2, hscale_pos, ?_⟩
  set z : ℕ := rayZ 16 N
  set y : ℕ := rayY 16 N
  set logQ : ℝ := Real.log (∏ q ∈ Q0_100, (q : ℝ))
  set C2 : ℝ := C2_bjs constDecaySeq (1 / 100 : ℝ)
  have hlo := regime3_lower_sieve_lb consts hGRH hCls hBJS hN_even hN hHStar hC2_nn
  have hup := regime3_upper_sieve_sum_ub consts hH_tilde halpha0 hGRH hCls hM hV hL strips hvj_pos hN_even hN
  have hsq := regime3_square_sum_ub consts hGRH hCls hN
  have hbal_eq : (switchingBalance N z y : ℝ) =
      ((sievedShifted N z).card : ℝ) -
        (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((divisibleSievedShifted N z q).card : ℝ) -
        (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) := by
    unfold switchingBalance
    push_cast
    rw [Finset.sum_add_distrib]
    ring
  -- Compare `rayLbA` at `N` vs `X_LS` and `VN N z` vs `rayScale`
  have hlogQ_nn : 0 ≤ logQ := by
    refine Real.log_nonneg ?_
    exact Finset.one_le_prod₀ fun q hq => by exact_mod_cast (Q0_100_mem_props q hq).1.pos
  have hlogLS_e : Real.exp 1 ≤ Real.log (asymptoticCert.X_LS : ℝ) := by
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have hsa_LS : 2 ≤ raySa 16 (5 / 2 : ℝ) logQ (asymptoticCert.X_LS : ℝ) := by
    have hQ_prod_pos : (0 : ℝ) < (∏ q ∈ Q0_100, (q : ℝ)) :=
      Finset.prod_pos fun q hq => by exact_mod_cast (Q0_100_mem_props q hq).1.pos
    have hQ_prod_lt : (∏ q ∈ Q0_100, (q : ℝ)) < (10 : ℝ) ^ 55 := by
      have hnat : (∏ q ∈ Q0_100, q) < 10 ^ 55 := Q0_100_prod_lt
      calc (∏ q ∈ Q0_100, (q : ℝ))
          = ((∏ q ∈ Q0_100, q : ℕ) : ℝ) := (Nat.cast_prod id Q0_100).symm
        _ < ((10 ^ 55 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (10 : ℝ) ^ 55 := by rw [Nat.cast_pow]; norm_num
    have h10_3 : (10 : ℝ) < Real.exp 3 := by
      have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_natCast_mul]; norm_num
      rw [he3]
      linarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) h1.le 3,
        show (10 : ℝ) < (2.7 : ℝ) ^ 3 by norm_num]
    have hQ_le_exp : (∏ q ∈ Q0_100, (q : ℝ)) ≤ Real.exp 165 := by
      have he165 : Real.exp 165 = Real.exp 3 ^ 55 := by rw [← Real.exp_natCast_mul]; norm_num
      have hpow : (10 : ℝ) ^ 55 < Real.exp 165 := by rw [he165]; exact pow_lt_pow_left₀ h10_3 (by norm_num) (by decide)
      exact (hQ_prod_lt.trans hpow).le
    have hlogQ_le : logQ ≤ 165 := by
      rw [← Real.log_exp 165]; exact Real.log_le_log hQ_prod_pos hQ_le_exp
    have hll := log_le_001_mul_of_1200_le hlogLS_ge.le
    unfold raySa rayAlphaA
    have ha_le : (logQ + (5 / 2 + 1) * Real.log (Real.log (asymptoticCert.X_LS : ℝ))) /
        Real.log (asymptoticCert.X_LS : ℝ) ≤ 165 / 1200 + 3.5 * 0.01 := by
      have h1 : logQ / Real.log (asymptoticCert.X_LS : ℝ) ≤ 165 / 1200 :=
        (div_le_div_of_nonneg_right hlogQ_le hlogLS_pos.le).trans
          (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogLS_ge.le)
      have h2 : (5 / 2 + 1) * Real.log (Real.log (asymptoticCert.X_LS : ℝ)) /
          Real.log (asymptoticCert.X_LS : ℝ) ≤ 3.5 * 0.01 := by
        rw [div_le_iff₀ hlogLS_pos]; nlinarith
      have hadd : (logQ + (5 / 2 + 1) * Real.log (Real.log (asymptoticCert.X_LS : ℝ))) /
          Real.log (asymptoticCert.X_LS : ℝ) = logQ / Real.log (asymptoticCert.X_LS : ℝ) +
          (5 / 2 + 1) * Real.log (Real.log (asymptoticCert.X_LS : ℝ)) /
            Real.log (asymptoticCert.X_LS : ℝ) := by ring
      rw [hadd]; linarith
    norm_num at ha_le ⊢; nlinarith
  have hlb_mono : rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (asymptoticCert.X_LS : ℝ) ≤
      rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (N : ℝ) :=
    rayLbA_mono 16 (by norm_num) hlogQ_nn (by norm_num) hC2_nn hXLS_pos hlogLS_e hsa_LS hN_real_ge
  -- Relate `|A_N| * VN N z ≥ (1 - rayDeltaV 16 X_LS) * consts.eNegGamma * rayScale`
  have hVN_scale : (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) * consts.eNegGamma *
      rayScale consts.U_c 16 N ≤ ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z := by
    have hN_ge3 : 3 ≤ N := by
      have : (3 : ℝ) ≤ (N : ℝ) := by linarith
      exact_mod_cast this
    have hz_ge_8 : (8 : ℝ) ≤ (z : ℝ) := by
      have hz_ge_lb : rayZIntLb 16 (N : ℝ) ≤ (z : ℝ) := by
        unfold rayZIntLb; rw [rayZ0_eq_rpow hN_pos]; unfold z rayZ; exact (Nat.sub_one_lt_floor _).le
      linarith [rayZIntLb_gt_1e12 hlogN_ge.le]
    have hV_N := (hV N hN_even hN_ge3 (z : ℝ) hz_ge_8).1
    have hceil_z : Nat.ceil (z : ℝ) = z := Nat.ceil_natCast z
    rw [hceil_z] at hV_N
    have hdv_le := deltaV_bs_le_rayDeltaV (M := 16) (K := N) (N := N) (by norm_num) (by norm_num)
      (by omega : 1 ≤ N) le_rfl hlogN_160
    have hdv_anti := rayDeltaV_antitone (M := 16) (by norm_num) (by norm_num) hXLS_pos
      hlogLS_160 hN_real_ge
    have hz_le_z0 : (z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (16 : ℝ)) := by
      unfold z rayZ; exact Nat.floor_le (by positivity)
    have hlogz_le : Real.log (z : ℝ) ≤ Real.log (N : ℝ) / 16 := by
      calc Real.log (z : ℝ) ≤ Real.log ((N : ℝ) ^ ((1 : ℝ) / (16 : ℝ))) :=
            Real.log_le_log (by linarith) hz_le_z0
        _ = Real.log (N : ℝ) / 16 := by rw [Real.log_rpow hN_pos]; ring
    have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
    have hUN_nn : 0 ≤ External.UN_ratio consts.U_c N :=
      le_trans consts.U_c_pos.le (un_ratio_ge consts.U_c_pos.le N)
    have hnum_le : (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) *
        (consts.eNegGamma * External.UN_ratio consts.U_c N) ≤
        (1 - External.deltaV_bs N (z : ℝ)) *
        (consts.eNegGamma * External.UN_ratio consts.U_c N) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg consts.eNegGamma_pos.le hUN_nn)
    have hdv_LS_lt1 := rayDeltaV_lt_one (M := 16) (by norm_num) (by norm_num) hXLS_pos hlogLS_160
    have hnum_nn : 0 ≤ (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) *
        (consts.eNegGamma * External.UN_ratio consts.U_c N) :=
      mul_nonneg (by linarith) (mul_nonneg consts.eNegGamma_pos.le hUN_nn)
    have hVN_ge : (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) *
        (consts.eNegGamma * External.UN_ratio consts.U_c N) / (Real.log (N : ℝ) / 16) ≤
        External.VN N z := by
      calc (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) *
              (consts.eNegGamma * External.UN_ratio consts.U_c N) / (Real.log (N : ℝ) / 16)
          ≤ (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) *
              (consts.eNegGamma * External.UN_ratio consts.U_c N) / Real.log (z : ℝ) :=
            div_le_div_of_nonneg_left hnum_nn hlogz_pos hlogz_le
        _ ≤ (1 - External.deltaV_bs N (z : ℝ)) *
              (consts.eNegGamma * External.UN_ratio consts.U_c N) / Real.log (z : ℝ) :=
            div_le_div_of_nonneg_right hnum_le hlogz_pos.le
        _ ≤ External.VN N z := hV_N
    have hmul := mul_le_mul_of_nonneg_left hVN_ge (Nat.cast_nonneg (shiftedCoprimePrimes N).card)
    refine le_of_eq_of_le ?_ hmul
    unfold rayScale
    push_cast
    ring
  have hVN_nn : 0 ≤ External.VN N z := by
    have hdv_LS_lt1 := rayDeltaV_lt_one (M := 16) (by norm_num) (by norm_num) hXLS_pos hlogLS_160
    have h1 : 0 ≤ (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) * consts.eNegGamma *
        rayScale consts.U_c 16 N :=
      mul_nonneg (mul_nonneg (by linarith) consts.eNegGamma_pos.le) hscale_pos.le
    have hcard_pos : (0 : ℝ) < ((shiftedCoprimePrimes N).card : ℝ) :=
      lt_trans (div_pos hN_pos hlogN_pos) (shiftedSet_card_gt_div_log hGRH hCls hN_4e18)
    exact nonneg_of_mul_nonneg_right (h1.trans hVN_scale) hcard_pos
  have hmain_coeff_rel :
      rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ) logQ (1 / 100 : ℝ) C2
          (asymptoticCert.X_LS : ℝ) strips (asymptoticCert.X_LS : ℝ) * rayScale consts.U_c 16 N ≤
        (rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (N : ℝ) -
          (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
            (asymptoticCert.X_LS : ℝ)) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    have hbr_le : rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (asymptoticCert.X_LS : ℝ) -
        (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
          (asymptoticCert.X_LS : ℝ) ≤
        rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (N : ℝ) -
        (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
          (asymptoticCert.X_LS : ℝ) := by linarith
    have h1 : rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ) logQ (1 / 100 : ℝ) C2
          (asymptoticCert.X_LS : ℝ) strips (asymptoticCert.X_LS : ℝ) * rayScale consts.U_c 16 N ≤
        (rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (asymptoticCert.X_LS : ℝ) -
          (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
            (asymptoticCert.X_LS : ℝ)) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      unfold rayMainCoeff
      calc (1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) * consts.eNegGamma *
              (rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (asymptoticCert.X_LS : ℝ) -
                (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
                  (asymptoticCert.X_LS : ℝ)) * rayScale consts.U_c 16 N
          = (rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (asymptoticCert.X_LS : ℝ) -
                (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
                  (asymptoticCert.X_LS : ℝ)) *
              ((1 - rayDeltaV 16 (asymptoticCert.X_LS : ℝ)) * consts.eNegGamma *
                rayScale consts.U_c 16 N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hVN_scale hbr_LS
    have h2 : (rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (asymptoticCert.X_LS : ℝ) -
          (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
            (asymptoticCert.X_LS : ℝ)) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
        (rayLbA 16 (5 / 2 : ℝ) logQ (1 / 100 : ℝ) C2 (N : ℝ) -
          (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
            (asymptoticCert.X_LS : ℝ)) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) :=
      mul_le_mul_of_nonneg_right hbr_le (mul_nonneg (Nat.cast_nonneg _) hVN_nn)
    exact h1.trans h2
  have herr_anti : rayErrorSumInt consts 16 (N : ℝ) ≤ rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ) :=
    rayErrorSumInt_antitone consts (by norm_num) hXLS_pos hlogLS_160 hN_real_ge
  have herr_one_nn : 0 ≤ rayErrOne consts 16 (N : ℝ) := by
    unfold rayErrOne; have := consts.U_c_pos; positivity
  have herr_sum_le :
      rayErrR1 consts 16 (N : ℝ) + rayErrAq1Int consts 16 (N : ℝ) +
          rayErrAq2 consts 16 (N : ℝ) + rayErrQ2Int consts 16 (N : ℝ) ≤
        rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ) := by
    unfold rayErrorSumInt at herr_anti ⊢
    linarith
  have herr_scaled := mul_le_mul_of_nonneg_right herr_sum_le hscale_pos.le
  rw [hbal_eq]
  linarith

/-- Master Regime 3 theorem bridging the analytic uniform bound (`regime3_switchingBalance_analytic_lb`)
with the rational certificate `asymptoticCert` (`k3/BuchstabSwitching/Certificates/Data.lean`) via an
explicit rational-interval enclosure premise on `(main_coeff - rayErrorSumInt)` at `X_LS = 10^600`. -/
theorem regime3_ray_switchingBalance_lb_of_analytic (consts : External.CertifiedConstants)
    (hH_tilde : H_tilde ≤ consts.H_tilde) (halpha0 : alpha0 ≤ consts.alpha0)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0)
    (hV : External.EulerProductVGRHPremise consts.U_c consts.eNegGamma)
    (hBJS : External.BuchstabSeriesPremise)
    (hHStar : ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0_100) (1 + (1 : ℝ) / 100))
    (hC2_nn : (0 : ℝ) ≤ C2_bjs constDecaySeq (1 / 100 : ℝ))
    {L : ℕ} (hL : 1 ≤ L)
    (strips : ∀ k : Fin L, RaySelbergStrip
      (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))))
    (hvj_pos : ∀ k : Fin L,
      0 < j_over_logz_lb (rayLogZLb 16 (asymptoticCert.X_LS : ℝ))
        (rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))
        (strips k).t (strips k).grid)
    (hbr_LS : 0 ≤ rayLbA 16 (5 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ))) (1 / 100 : ℝ)
        (C2_bjs constDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) -
      (1 / 2 : ℝ) * raySumAqMain consts 16 L (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) strips
        (asymptoticCert.X_LS : ℝ))
    (hCertInt : (asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ) ≤
      rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ)))
          (1 / 100 : ℝ) (C2_bjs constDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) strips
          (asymptoticCert.X_LS : ℝ) -
        rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ))
    {N : ℕ} (hN_even : Even N) (hN : asymptoticCert.X_LS ≤ N) :
    ∃ (z y : ℕ) (scale : ℚ),
      2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 4 ∧ N ≤ z * y ^ 3 ∧ 0 < scale ∧
        (asymptoticCert.main_lb - asymptoticCert.err_ub) * scale ≤ switchingBalance N z y := by
  obtain ⟨hz2, hzy, hy4, hzy3, hsc_pos, hlb⟩ :=
    regime3_switchingBalance_analytic_lb consts hH_tilde halpha0 hGRH hCls hM hV hBJS hHStar
      hC2_nn hL strips hvj_pos hbr_LS hN_even hN
  obtain ⟨scale, hsc0, hsc_lt⟩ := exists_rat_btwn hsc_pos
  have hnet_nn : (0 : ℝ) ≤ (asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ) := by
    norm_num [RayCert.main_lb, RayCert.err_ub, asymptoticCert]
  have hreal_le : ((asymptoticCert.main_lb - asymptoticCert.err_ub : ℚ) : ℝ) * (scale : ℝ) ≤
      (switchingBalance N (rayZ 16 N) (rayY 16 N) : ℝ) := by
    push_cast
    calc ((asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ)) * (scale : ℝ)
        ≤ ((asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ)) * rayScale consts.U_c 16 N :=
          mul_le_mul_of_nonneg_left hsc_lt.le hnet_nn
      _ ≤ (rayMainCoeff consts 16 L (5 / 2 : ℝ) (11 / 2 : ℝ) (Real.log (∏ q ∈ Q0_100, (q : ℝ)))
              (1 / 100 : ℝ) (C2_bjs constDecaySeq (1 / 100 : ℝ)) (asymptoticCert.X_LS : ℝ) strips
              (asymptoticCert.X_LS : ℝ) -
            rayErrorSumInt consts 16 (asymptoticCert.X_LS : ℝ)) * rayScale consts.U_c 16 N :=
          mul_le_mul_of_nonneg_right hCertInt hsc_pos.le
      _ ≤ (switchingBalance N (rayZ 16 N) (rayY 16 N) : ℝ) := hlb
  refine ⟨rayZ 16 N, rayY 16 N, scale, hz2, hzy, hy4, hzy3, by exact_mod_cast hsc0, ?_⟩
  exact_mod_cast hreal_le

/-- Master Regime 3 asymptotic ray theorem via `External.RayNumericCertPremise asymptoticCert`
(`k3/BuchstabSwitching/External/NumericalConstants/ExplicitConstants.lean`). -/
theorem regime3_ray_switchingBalance_lb (consts : External.CertifiedConstants)
    (_hGRH : External.DirichletLNonvanishingRightOfHalf)
    (_hCls : ClassicalPrimePremises consts.li2)
    {M0 : ℝ} (_hM : External.MertensPrimeSumPremise M0)
    (_hV : External.EulerProductVGRHPremise consts.U_c consts.eNegGamma)
    (_hBJS : External.BuchstabSeriesPremise)
    (_hHStar : ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0_100) (1 + (1 : ℝ) / 100))
    (hCert : External.RayNumericCertPremise asymptoticCert)
    {N : ℕ} (hN_even : Even N) (hN : asymptoticCert.X_LS ≤ N) :
    ∃ (z y : ℕ) (scale : ℚ),
      2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 4 ∧ N ≤ z * y ^ 3 ∧ 0 < scale ∧
        (asymptoticCert.main_lb - asymptoticCert.err_ub) * scale ≤ switchingBalance N z y := by
  obtain ⟨z, y, rscale, main_coeff, hz2, hzy, hy4, hzy3, hrsc_pos, _, hmain_lb, herr_ub, hbal⟩ :=
    hCert consts N hN_even hN
  obtain ⟨scale, hsc0, hsc_lt⟩ := exists_rat_btwn hrsc_pos
  have hnet_nn : (0 : ℝ) ≤ (asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ) := by
    norm_num [RayCert.main_lb, RayCert.err_ub, asymptoticCert]
  have hreal_le : ((asymptoticCert.main_lb - asymptoticCert.err_ub : ℚ) : ℝ) * (scale : ℝ) ≤
      (switchingBalance N z y : ℝ) := by
    push_cast
    calc ((asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ)) * (scale : ℝ)
        ≤ ((asymptoticCert.main_lb : ℝ) - (asymptoticCert.err_ub : ℝ)) * rscale :=
          mul_le_mul_of_nonneg_left hsc_lt.le hnet_nn
      _ ≤ (main_coeff - External.rayErrorSum consts (asymptoticCert.X_LS : ℝ)) * rscale :=
          mul_le_mul_of_nonneg_right (by linarith) hrsc_pos.le
      _ ≤ External.switchingBalanceReal N z y := hbal
      _ ≤ (switchingBalance N z y : ℝ) := switchingBalanceReal_le_switchingBalance N z y
  refine ⟨z, y, scale, hz2, hzy, hy4, hzy3, by exact_mod_cast hsc0, ?_⟩
  exact_mod_cast hreal_le

end MasterTheorems

end

end BuchstabSwitching

