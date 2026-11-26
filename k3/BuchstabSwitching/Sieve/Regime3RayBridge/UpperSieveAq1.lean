import BuchstabSwitching.Sieve.Regime3RayBridge.IntegerCutoffs
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.StripAndErrorMonotonicity
import BuchstabSwitching.Sieve.Regime3RayBridge.LowerSieve
import BuchstabSwitching.Sieve.Regime3RayBridge.UpperSieveSetup
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.Certificates.Data
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

section SieveBounds

/-- Upper-sieve double-sum AP remainder bound (`err_aq1`) over `midPrimes N (rayZ 16 N) (rayY 16 N)`
for `N ≥ 10^600`. -/
lemma regime3_upper_aq1_le (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises consts.li2)
    {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0)
    {L N : ℕ} (hN : asymptoticCert.X_LS ≤ N)
    (hmid_eq : midPrimes N (rayZ 16 N) (rayY 16 N) = Finset.univ.biUnion (rayStripPrimes N L))
    (hy_le_beta : (rayY 16 N : ℝ) ≤ (N : ℝ) ^ rayBeta 16)
    (hr_bounds : ∀ k : Fin L,
      let r_k := rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1))
      1 < r_k ∧ r_k < 3)
    (hD_xi_props : ∀ (xi0 L0 : ℕ), L0 ∈ D_xi (shiftedPrimesBelow N (rayZ 16 N)) xi0 →
      1 ≤ L0 ∧ L0 ≤ xi0 ∧ Odd L0 ∧ Squarefree L0 ∧ L0.Coprime N) :
    ∑ k : Fin L, ∑ q ∈ rayStripPrimes N L k,
        ∑ L0 ∈ D_xi (shiftedPrimesBelow N (rayZ 16 N)) ((Nat.floor (((rayZ 16 N : ℕ) : ℝ) ^
            rayStripRExp 16 (11 / 2 : ℝ) (asymptoticCert.X_LS : ℝ) (rayStripU 16 L (k.1 + 1)))) ^ 2),
          (3 : ℝ) ^ L0.primeFactors.card *
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTotRay (q * L0)| ≤
      rayErrAq1Int consts 16 (N : ℝ) * rayScale consts.U_c 16 N := by
  obtain ⟨hXLS_pos, hN_pos, _, hlogN_ge, hN_4e18, hN_2pow16, _⟩ := X_LS_facts hN
  have hN_real_ge : (asymptoticCert.X_LS : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hlogN_160 : 10 * ((16 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by norm_num; linarith
  set z : ℕ := rayZ 16 N
  set y : ℕ := rayY 16 N
  set P_z : Finset ℕ := shiftedPrimesBelow N z
  have hcut := regime3_cutoffs_valid (by norm_num : 4 ≤ 16) hN_2pow16
  have hz2 : 2 ≤ z := hcut.1
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
            linarith [log_asymptoticCert_X_LS_ge]
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

end SieveBounds

end

end BuchstabSwitching
