import BuchstabSwitching.Sieve.Regime3RayBridge.DeltaVMonotonicity
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

section RayMonotonicity

/-- Selberg upper-sieve finite partition data on an interval `[1, r]`. -/
structure RaySelbergStrip (r : ℝ) : Type where
  k₁ : ℕ
  hk₁ : 1 ≤ k₁
  t : Fin (k₁ + 1) → ℝ
  ht0 : t 0 = 1
  ht_end : t ⟨k₁, Nat.lt_succ_self k₁⟩ = r
  ht_mono : StrictMono t
  grid : TwoPrimeExpGrid r

/-- Strip endpoint `u_k = 1/M + k * (β(M) - 1/M) / L` (`regime_asymptotic.py:113-114`). -/
def rayStripU (M L k : ℕ) : ℝ :=
  1 / (M : ℝ) + (k : ℝ) * ((rayBeta M - 1 / (M : ℝ)) / (L : ℝ))

/-- Fixed strip exponent `r_k = min 2.95 (0.5 * M * (0.5 - α_q(X_LS) - u_{k+1}))`. -/
noncomputable def rayStripRExp (M : ℕ) (b_q X_LS u_hi : ℝ) : ℝ :=
  min (2.95 : ℝ) (0.5 * (M : ℝ) * (0.5 - rayAlphaQ b_q X_LS - u_hi))

/-- Upper bound on the reciprocal prime sum over strip `k` (`regime_asymptotic.py:119-122`). -/
noncomputable def raySumQSub (M L k : ℕ) (X : ℝ) : ℝ :=
  let uk := rayStripU M L k
  let uk1 := rayStripU M L (k + 1)
  let mert_coeff : ℝ := (6.836e-6 : ℝ) + (2.964e-6 : ℝ)
  Real.log (uk1 / uk) + mert_coeff / (uk * Real.log X) + 1 / Real.exp (uk * Real.log X) +
    (if k = 0 then 1 / (rayZIntLb M X - 1) else 0)

/-- Sum of `1 / (q - 1)` strip contributions divided by monotone Selberg `vj_monotone_lb`
(`regime_asymptotic.py:111-123`). -/
noncomputable def raySumAqMain (consts : External.CertifiedConstants)
    (M L : ℕ) (b_q X_LS : ℝ)
    (strips : ∀ k : Fin L, RaySelbergStrip (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))))
    (X : ℝ) : ℝ :=
  let q_ratio_ub := rayZIntLb M X / (rayZIntLb M X - 1)
  ∑ k : Fin L,
    let r_k := rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))
    let s := strips k
    let vj_lb := vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV M X)
      (rayLogZLb M X) r_k s.t s.grid
    q_ratio_ub * raySumQSub M L k.1 X / vj_lb

/-- Normalized main-term coefficient `main_coeff(X)` (`regime_asymptotic.py:125-128`). -/
noncomputable def rayMainCoeff (consts : External.CertifiedConstants)
    (M L : ℕ) (b_a b_q logQ ε C2 X_LS : ℝ)
    (strips : ∀ k : Fin L, RaySelbergStrip (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))))
    (X : ℝ) : ℝ :=
  (1 - rayDeltaV M X) * consts.eNegGamma *
    (rayLbA M b_a logQ ε C2 X - (1 / 2 : ℝ) * raySumAqMain consts M L b_q X_LS strips X)

lemma one_div_lt_rayBeta {M : ℕ} (hM : 4 ≤ M) : 1 / (M : ℝ) < rayBeta M := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_ge4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h0 : 1 / (M : ℝ) ≤ (1 - 1 / (M : ℝ)) / 3 := by
    rw [div_le_div_iff₀ hM_pos (by norm_num)]
    have hmul : (1 - 1 / (M : ℝ)) * (M : ℝ) = (M : ℝ) - 1 := by
      field_simp [hM_pos.ne']
    rw [hmul]
    linarith
  unfold rayBeta
  linarith

lemma rayStripU_pos {M L : ℕ} (hM : 4 ≤ M) (hL : 1 ≤ L) (k : ℕ) (_hk : k ≤ L) :
    0 < rayStripU M L k := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hbeta_gt : 1 / (M : ℝ) < rayBeta M := one_div_lt_rayBeta hM
  unfold rayStripU
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  positivity

lemma rayStripU_mono {M L k : ℕ} (hM : 4 ≤ M) (hL : 1 ≤ L) :
    rayStripU M L k < rayStripU M L (k + 1) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hbeta_gt : 1 / (M : ℝ) < rayBeta M := one_div_lt_rayBeta hM
  unfold rayStripU
  push_cast
  have hdu : 0 < (rayBeta M - 1 / (M : ℝ)) / (L : ℝ) := by positivity
  linarith

lemma raySumQSub_nonneg {M L k : ℕ} (hM : 4 ≤ M) (hL : 1 ≤ L) (hk : k < L)
    {X : ℝ} (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    0 ≤ raySumQSub M L k X := by
  have huk_pos : 0 < rayStripU M L k := rayStripU_pos hM hL k hk.le
  have huk1_lt : rayStripU M L k < rayStripU M L (k + 1) := rayStripU_mono hM hL
  have hratio_gt1 : 1 < rayStripU M L (k + 1) / rayStripU M L k :=
    (one_lt_div huk_pos).mpr huk1_lt
  have hlog_ratio : 0 ≤ Real.log (rayStripU M L (k + 1) / rayStripU M L k) :=
    (Real.log_pos hratio_gt1).le
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlogX_pos : 0 < Real.log X := by nlinarith
  have hzlb_20k : (20000 : ℝ) ≤ rayZIntLb M X := rayZIntLb_ge_20000 (by omega) hlog
  have hz_sub : 0 < rayZIntLb M X - 1 := by linarith
  unfold raySumQSub
  split_ifs <;> positivity

lemma raySumQSub_antitone {M L k : ℕ} (hM : 4 ≤ M) (hL : 1 ≤ L) (hk : k < L)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    raySumQSub M L k X₂ ≤ raySumQSub M L k X₁ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlog₁_pos : 0 < Real.log X₁ := by nlinarith
  have hX₁_gt1 : 1 < X₁ := one_lt_of_pos_log_pos hX₁_pos hlog₁_pos
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have huk_pos : 0 < rayStripU M L k := rayStripU_pos hM hL k hk.le
  have hzlb₁ : (20000 : ℝ) ≤ rayZIntLb M X₁ := rayZIntLb_ge_20000 (by omega) hlog₁
  have hzlb₁₂ : rayZIntLb M X₁ ≤ rayZIntLb M X₂ := rayZIntLb_mono (by omega) hX₁_gt1.le hX₁₂
  have hmert : 0 ≤ (6.836e-6 : ℝ) + (2.964e-6 : ℝ) := by norm_num
  have h1 : ((6.836e-6 : ℝ) + 2.964e-6) / (rayStripU M L k * Real.log X₂) ≤
      ((6.836e-6 : ℝ) + 2.964e-6) / (rayStripU M L k * Real.log X₁) :=
    div_le_div_of_nonneg_left hmert (mul_pos huk_pos hlog₁_pos)
      (mul_le_mul_of_nonneg_left hlog₁₂ huk_pos.le)
  have h2 : 1 / Real.exp (rayStripU M L k * Real.log X₂) ≤
      1 / Real.exp (rayStripU M L k * Real.log X₁) := by
    apply one_div_le_one_div_of_le (Real.exp_pos _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog₁₂ huk_pos.le)
  unfold raySumQSub
  split_ifs
  · have h3 : 1 / (rayZIntLb M X₂ - 1) ≤ 1 / (rayZIntLb M X₁ - 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  · linarith

private lemma rayStrip_term_antitone (consts : External.CertifiedConstants)
    {M L : ℕ} (hM : 4 ≤ M) (hM_le : M ≤ 16) (hL : 1 ≤ L)
    (k : Fin L) {b_q X_LS : ℝ}
    (s : RaySelbergStrip (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))))
    (hr_pos : 0 < rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1)))
    (hvj_pos : 0 < j_over_logz_lb (rayLogZLb M X_LS)
      (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))) s.t s.grid)
    {X₁ X₂ : ℝ} (hXLS_pos : 0 < X_LS) (hLS : X_LS ≤ X₁)
    (hlogLS : 10 * (M : ℝ) ≤ Real.log X_LS) (hlog_z_LS : 10 < rayLogZLb M X_LS)
    (hX₁₂ : X₁ ≤ X₂) :
    (rayZIntLb M X₂ / (rayZIntLb M X₂ - 1)) * raySumQSub M L k.1 X₂ /
        vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV M X₂) (rayLogZLb M X₂)
          (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))) s.t s.grid ≤
      (rayZIntLb M X₁ / (rayZIntLb M X₁ - 1)) * raySumQSub M L k.1 X₁ /
        vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV M X₁) (rayLogZLb M X₁)
          (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))) s.t s.grid := by
  have hM1 : 1 ≤ M := by omega
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hXLS_gt1 : 1 < X_LS := one_lt_of_pos_log_pos hXLS_pos (by nlinarith)
  have hX₁_gt1 : 1 < X₁ := lt_of_lt_of_le hXLS_gt1 hLS
  have hX₁_pos : 0 < X₁ := lt_trans zero_lt_one hX₁_gt1
  have hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁ :=
    hlogLS.trans (Real.log_le_log hXLS_pos hLS)
  have hlog₂ : 10 * (M : ℝ) ≤ Real.log X₂ :=
    hlog₁.trans (Real.log_le_log hX₁_pos hX₁₂)
  have hzlb₁ : (20000 : ℝ) ≤ rayZIntLb M X₁ := rayZIntLb_ge_20000 hM1 hlog₁
  have hzlb₁₂ : rayZIntLb M X₁ ≤ rayZIntLb M X₂ := rayZIntLb_mono hM1 hX₁_gt1.le hX₁₂
  have hzlb₂ : (20000 : ℝ) ≤ rayZIntLb M X₂ := hzlb₁.trans hzlb₁₂
  have hqratio : rayZIntLb M X₂ / (rayZIntLb M X₂ - 1) ≤
      rayZIntLb M X₁ / (rayZIntLb M X₁ - 1) := by
    have id1 : rayZIntLb M X₁ / (rayZIntLb M X₁ - 1) = 1 + 1 / (rayZIntLb M X₁ - 1) := by
      have hne : rayZIntLb M X₁ - 1 ≠ 0 := by linarith
      field_simp [hne]; ring
    have id2 : rayZIntLb M X₂ / (rayZIntLb M X₂ - 1) = 1 + 1 / (rayZIntLb M X₂ - 1) := by
      have hne : rayZIntLb M X₂ - 1 ≠ 0 := by linarith
      field_simp [hne]; ring
    rw [id1, id2]
    linarith [one_div_le_one_div_of_le (show 0 < rayZIntLb M X₁ - 1 by linarith)
      (by linarith : rayZIntLb M X₁ - 1 ≤ rayZIntLb M X₂ - 1)]
  have hqratio_nn : 0 ≤ rayZIntLb M X₂ / (rayZIntLb M X₂ - 1) := by
    have : 0 < rayZIntLb M X₂ - 1 := by linarith
    positivity
  have hzlb_LS : (20000 : ℝ) ≤ rayZIntLb M X_LS := rayZIntLb_ge_20000 hM1 hlogLS
  have hlzb_LS_1 : rayLogZLb M X_LS ≤ rayLogZLb M X₁ :=
    rayLogZLb_mono hM1 hXLS_gt1 hLS (by linarith)
  have hlzb_1_2 : rayLogZLb M X₁ ≤ rayLogZLb M X₂ :=
    rayLogZLb_mono hM1 hX₁_gt1 hX₁₂ (by linarith)
  have hlzb₁ : 10 < rayLogZLb M X₁ := lt_of_lt_of_le hlog_z_LS hlzb_LS_1
  have hdv₁ : rayDeltaV M X₁ < 1 := rayDeltaV_lt_one hM1 hM_le hX₁_pos hlog₁
  have hdv₂ : rayDeltaV M X₂ < 1 := rayDeltaV_lt_one hM1 hM_le (lt_of_lt_of_le hX₁_pos hX₁₂) hlog₂
  have hdv₁₂ : rayDeltaV M X₂ ≤ rayDeltaV M X₁ := rayDeltaV_antitone hM1 hM_le hX₁_pos hlog₁ hX₁₂
  have hj_mono_LS1 : j_over_logz_lb (rayLogZLb M X_LS) _ s.t s.grid ≤
      j_over_logz_lb (rayLogZLb M X₁) _ s.t s.grid :=
    j_over_logz_lb_mono hr_pos s.t (by rw [s.ht0]) s.ht_mono (by rw [s.ht_end]) s.grid hlog_z_LS hlzb_LS_1
  have hj_mono_12 : j_over_logz_lb (rayLogZLb M X₁) _ s.t s.grid ≤
      j_over_logz_lb (rayLogZLb M X₂) _ s.t s.grid :=
    j_over_logz_lb_mono hr_pos s.t (by rw [s.ht0]) s.ht_mono (by rw [s.ht_end]) s.grid hlzb₁ hlzb_1_2
  have hj₁_pos : 0 < j_over_logz_lb (rayLogZLb M X₁) _ s.t s.grid :=
    lt_of_lt_of_le hvj_pos hj_mono_LS1
  have hvj₁_pos : 0 < vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV M X₁)
      (rayLogZLb M X₁) _ s.t s.grid := by
    unfold vj_monotone_lb
    exact mul_pos (mul_pos (mul_pos consts.U_c_pos consts.eNegGamma_pos) (by linarith)) hj₁_pos
  have hvj₁₂ : vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV M X₁) (rayLogZLb M X₁) _ s.t s.grid ≤
      vj_monotone_lb consts.U_c consts.eNegGamma (rayDeltaV M X₂) (rayLogZLb M X₂) _ s.t s.grid := by
    unfold vj_monotone_lb
    have h1dv : 1 - rayDeltaV M X₁ ≤ 1 - rayDeltaV M X₂ := by linarith
    have hc1 : consts.U_c * consts.eNegGamma * (1 - rayDeltaV M X₁) ≤
        consts.U_c * consts.eNegGamma * (1 - rayDeltaV M X₂) :=
      mul_le_mul_of_nonneg_left h1dv (mul_nonneg consts.U_c_pos.le consts.eNegGamma_pos.le)
    have h1dv2 : 0 ≤ 1 - rayDeltaV M X₂ := by linarith
    exact mul_le_mul hc1 hj_mono_12 hj₁_pos.le
      (mul_nonneg (mul_nonneg consts.U_c_pos.le consts.eNegGamma_pos.le) h1dv2)
  have hsq2_nn : 0 ≤ raySumQSub M L k.1 X₂ := raySumQSub_nonneg hM hL k.2 hlog₂
  have hqratio1_nn : 0 ≤ rayZIntLb M X₁ / (rayZIntLb M X₁ - 1) := by
    have : 0 < rayZIntLb M X₁ - 1 := by linarith
    positivity
  have hnum_le : rayZIntLb M X₂ / (rayZIntLb M X₂ - 1) * raySumQSub M L k.1 X₂ ≤
      rayZIntLb M X₁ / (rayZIntLb M X₁ - 1) * raySumQSub M L k.1 X₁ :=
    mul_le_mul hqratio (raySumQSub_antitone hM hL k.2 hX₁_pos hlog₁ hX₁₂) hsq2_nn hqratio1_nn
  have hnum_nn : 0 ≤ rayZIntLb M X₂ / (rayZIntLb M X₂ - 1) * raySumQSub M L k.1 X₂ :=
    mul_nonneg hqratio_nn hsq2_nn
  exact (div_le_div_of_nonneg_left hnum_nn hvj₁_pos hvj₁₂).trans
    (div_le_div_of_nonneg_right hnum_le hvj₁_pos.le)

theorem raySumAqMain_antitone (consts : External.CertifiedConstants)
    {M L : ℕ} (hM : 4 ≤ M) (hM_le : M ≤ 16) (hL : 1 ≤ L) {b_q X_LS : ℝ}
    (strips : ∀ k : Fin L, RaySelbergStrip (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))))
    (hr_pos : ∀ k : Fin L, 0 < rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1)))
    (hvj_pos : ∀ k : Fin L,
      0 < j_over_logz_lb (rayLogZLb M X_LS)
        (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))) (strips k).t (strips k).grid)
    {X₁ X₂ : ℝ} (hXLS_pos : 0 < X_LS) (hLS : X_LS ≤ X₁) (hlogLS : 10 * (M : ℝ) ≤ Real.log X_LS)
    (hlog_z_LS : 10 < rayLogZLb M X_LS) (hX₁₂ : X₁ ≤ X₂) :
    raySumAqMain consts M L b_q X_LS strips X₂ ≤
      raySumAqMain consts M L b_q X_LS strips X₁ := by
  unfold raySumAqMain
  refine Finset.sum_le_sum fun k _ => ?_
  exact rayStrip_term_antitone consts hM hM_le hL k (strips k) (hr_pos k) (hvj_pos k)
    hXLS_pos hLS hlogLS hlog_z_LS hX₁₂

theorem rayMainCoeff_mono (consts : External.CertifiedConstants)
    {M L : ℕ} (hM : 4 ≤ M) (hM_le : M ≤ 16) (hL : 1 ≤ L)
    {b_a b_q logQ ε C2 X_LS : ℝ}
    (hba : 0 ≤ b_a + 1) (hlogQ : 0 ≤ logQ) (hε : 0 ≤ ε) (hC2 : 0 ≤ C2)
    (strips : ∀ k : Fin L, RaySelbergStrip (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))))
    (hr_pos : ∀ k : Fin L, 0 < rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1)))
    (hvj_pos : ∀ k : Fin L,
      0 < j_over_logz_lb (rayLogZLb M X_LS)
        (rayStripRExp M b_q X_LS (rayStripU M L (k.1 + 1))) (strips k).t (strips k).grid)
    {X₁ X₂ : ℝ} (hXLS_pos : 0 < X_LS) (hLS : X_LS ≤ X₁) (hlogLS : 10 * (M : ℝ) ≤ Real.log X_LS)
    (hlog_z_LS : 10 < rayLogZLb M X_LS)
    (hsa_LS : 2 ≤ raySa M b_a logQ X_LS)
    (hbr_LS : 0 ≤ rayLbA M b_a logQ ε C2 X_LS -
      (1 / 2 : ℝ) * raySumAqMain consts M L b_q X_LS strips X_LS)
    (hX₁₂ : X₁ ≤ X₂) :
    rayMainCoeff consts M L b_a b_q logQ ε C2 X_LS strips X₁ ≤
      rayMainCoeff consts M L b_a b_q logQ ε C2 X_LS strips X₂ := by
  have hM1 : 1 ≤ M := by omega
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hlogLS_e : Real.exp 1 ≤ Real.log X_LS := by
    have he1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have : (40 : ℝ) ≤ Real.log X_LS := by
      have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    linarith
  have hX₁_pos : 0 < X₁ := lt_of_lt_of_le hXLS_pos hLS
  have hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁ := hlogLS.trans (Real.log_le_log hXLS_pos hLS)
  have hlog₁_e : Real.exp 1 ≤ Real.log X₁ := le_trans hlogLS_e (Real.log_le_log hXLS_pos hLS)
  have hsa₁ : 2 ≤ raySa M b_a logQ X₁ :=
    hsa_LS.trans (raySa_mono M hba hlogQ hXLS_pos hlogLS_e hLS)
  have hlb_LS1 : rayLbA M b_a logQ ε C2 X_LS ≤ rayLbA M b_a logQ ε C2 X₁ :=
    rayLbA_mono M hba hlogQ hε hC2 hXLS_pos hlogLS_e hsa_LS hLS
  have hlb_12 : rayLbA M b_a logQ ε C2 X₁ ≤ rayLbA M b_a logQ ε C2 X₂ :=
    rayLbA_mono M hba hlogQ hε hC2 hX₁_pos hlog₁_e hsa₁ hX₁₂
  have haq_LS1 : raySumAqMain consts M L b_q X_LS strips X₁ ≤
      raySumAqMain consts M L b_q X_LS strips X_LS :=
    raySumAqMain_antitone consts hM hM_le hL strips hr_pos hvj_pos hXLS_pos le_rfl hlogLS hlog_z_LS hLS
  have haq_12 : raySumAqMain consts M L b_q X_LS strips X₂ ≤
      raySumAqMain consts M L b_q X_LS strips X₁ :=
    raySumAqMain_antitone consts hM hM_le hL strips hr_pos hvj_pos hXLS_pos hLS hlogLS hlog_z_LS hX₁₂
  have hbr₁_nn : 0 ≤ rayLbA M b_a logQ ε C2 X₁ -
      (1 / 2 : ℝ) * raySumAqMain consts M L b_q X_LS strips X₁ := by linarith
  have hbr_12 : rayLbA M b_a logQ ε C2 X₁ -
      (1 / 2 : ℝ) * raySumAqMain consts M L b_q X_LS strips X₁ ≤
      rayLbA M b_a logQ ε C2 X₂ -
      (1 / 2 : ℝ) * raySumAqMain consts M L b_q X_LS strips X₂ := by linarith
  have hdv₁ : rayDeltaV M X₁ < 1 := rayDeltaV_lt_one hM1 hM_le hX₁_pos hlog₁
  have hdv₁₂ : rayDeltaV M X₂ ≤ rayDeltaV M X₁ := rayDeltaV_antitone hM1 hM_le hX₁_pos hlog₁ hX₁₂
  have hcoef_le : (1 - rayDeltaV M X₁) * consts.eNegGamma ≤
      (1 - rayDeltaV M X₂) * consts.eNegGamma :=
    mul_le_mul_of_nonneg_right (by linarith) consts.eNegGamma_pos.le
  unfold rayMainCoeff
  exact mul_le_mul hcoef_le hbr_12 hbr₁_nn
    (mul_nonneg (by linarith) consts.eNegGamma_pos.le)

/-- Integer-cutoff 5-term normalized error sum `rayErrorSumInt` matching `regime_asymptotic.py:136-158`
for `b_a = 5/2`, `b_q = 11/2`, `M = 16` (`z - 1 ≥ rayZIntLb M X - 1`). -/
noncomputable def rayErrR1 (consts : External.CertifiedConstants) (M : ℕ) (X : ℝ) : ℝ :=
  rayC4g consts X / ((M : ℝ) * consts.U_c * Real.rpow (Real.log X) ((5 / 2 : ℝ) - 2))

noncomputable def raySumQInvInt (M : ℕ) (X : ℝ) : ℝ :=
  Real.log (rayBeta M * (M : ℝ)) +
    ((6.836e-6 : ℝ) + (2.964e-6 : ℝ)) / ((1 / (M : ℝ)) * Real.log X) +
    1 / (rayZIntLb M X - 1)

noncomputable def rayErrAq1Int (consts : External.CertifiedConstants) (M : ℕ) (X : ℝ) : ℝ :=
  ((0.0625 : ℝ) * rayCPt consts X * raySumQInvInt M X / ((M : ℝ) * consts.U_c)) *
    ((0.5 : ℝ) * Real.log X + 6) ^ 2 / Real.rpow (Real.log X) ((11 / 2 : ℝ) - 3)

noncomputable def rayErrAq2 (consts : External.CertifiedConstants) (M : ℕ) (X : ℝ) : ℝ :=
  let y_over_n := Real.exp ((rayBeta M - (0.5 : ℝ)) * Real.log X)
  let g_phi_n05 := (13 / 10 : ℝ) * ((0.25 : ℝ) * Real.log X + (636 / 1000 : ℝ) + consts.C_f0)
  (0.5 : ℝ) * rayC4g consts X * y_over_n * Real.log X ^ 3 * (1 + g_phi_n05 ^ 3) /
    ((M : ℝ) * consts.U_c)

noncomputable def rayErrQ2Int (consts : External.CertifiedConstants) (M : ℕ) (X : ℝ) : ℝ :=
  Real.log X ^ 2 / (2 * (M : ℝ) * consts.U_c * (rayZIntLb M X - 1))

noncomputable def rayErrOne (consts : External.CertifiedConstants) (M : ℕ) (X : ℝ) : ℝ :=
  Real.log X ^ 2 / ((M : ℝ) * consts.U_c * X)

noncomputable def rayErrorSumInt (consts : External.CertifiedConstants) (M : ℕ) (X : ℝ) : ℝ :=
  rayErrR1 consts M X + rayErrAq1Int consts M X + rayErrAq2 consts M X +
    rayErrQ2Int consts M X + rayErrOne consts M X

theorem rayErrR1_antitone (consts : External.CertifiedConstants) {M : ℕ} (hM : 1 ≤ M)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 < Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayErrR1 consts M X₂ ≤ rayErrR1 consts M X₁ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hX₂_pos : 0 < X₂ := lt_of_lt_of_le hX₁_pos hX₁₂
  have hlog₁_pos : 0 < Real.log X₁ := lt_trans (Real.exp_pos 1) hlog₁
  have hlog₂ : Real.exp 1 < Real.log X₂ := lt_of_lt_of_le hlog₁ (Real.log_le_log hX₁_pos hX₁₂)
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hc4g := rayC4g_antitone consts hX₁_pos hlog₁ hX₁₂
  have hc4g_nn := rayC4g_nonneg consts hX₂_pos hlog₂
  have hrpow : Real.rpow (Real.log X₁) ((5 / 2 : ℝ) - 2) ≤
      Real.rpow (Real.log X₂) ((5 / 2 : ℝ) - 2) :=
    Real.rpow_le_rpow hlog₁_pos.le hlog₁₂ (by norm_num)
  have hden_pos : 0 < (M : ℝ) * consts.U_c * Real.rpow (Real.log X₁) ((5 / 2 : ℝ) - 2) :=
    mul_pos (mul_pos hM_pos consts.U_c_pos) (Real.rpow_pos_of_pos hlog₁_pos _)
  have hden_le : (M : ℝ) * consts.U_c * Real.rpow (Real.log X₁) ((5 / 2 : ℝ) - 2) ≤
      (M : ℝ) * consts.U_c * Real.rpow (Real.log X₂) ((5 / 2 : ℝ) - 2) :=
    mul_le_mul_of_nonneg_left hrpow (mul_nonneg hM_pos.le consts.U_c_pos.le)
  unfold rayErrR1
  exact (div_le_div_of_nonneg_left hc4g_nn hden_pos hden_le).trans
    (div_le_div_of_nonneg_right hc4g hden_pos.le)

theorem raySumQInvInt_nonneg {M : ℕ} (hM : 4 ≤ M) {X : ℝ}
    (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    0 ≤ raySumQInvInt M X := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_ge4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hbm : 1 < rayBeta M * (M : ℝ) := by
    unfold rayBeta
    have h2 : 1 ≤ ((1 - 1 / (M : ℝ)) / 3) * (M : ℝ) := by
      have hmul : ((1 - 1 / (M : ℝ)) / 3) * (M : ℝ) = ((M : ℝ) - 1) / 3 := by
        field_simp [hM_pos.ne']
      rw [hmul]
      linarith
    have h3 : 0 < (1e-9 : ℝ) * (M : ℝ) := by positivity
    nlinarith
  have hlogbm : 0 ≤ Real.log (rayBeta M * (M : ℝ)) := (Real.log_pos hbm).le
  have hlogX_pos : 0 < Real.log X := by nlinarith
  have hzlb : (20000 : ℝ) ≤ rayZIntLb M X := rayZIntLb_ge_20000 (by omega) hlog
  have hzsub : 0 < rayZIntLb M X - 1 := by linarith
  unfold raySumQInvInt
  positivity

theorem raySumQInvInt_antitone {M : ℕ} (hM : 4 ≤ M) {X₁ X₂ : ℝ}
    (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    raySumQInvInt M X₂ ≤ raySumQInvInt M X₁ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlog₁_pos : 0 < Real.log X₁ := by nlinarith
  have hX₁_gt1 : 1 < X₁ := one_lt_of_pos_log_pos hX₁_pos hlog₁_pos
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hzlb₁ : (20000 : ℝ) ≤ rayZIntLb M X₁ := rayZIntLb_ge_20000 (by omega) hlog₁
  have hzlb₁₂ : rayZIntLb M X₁ ≤ rayZIntLb M X₂ := rayZIntLb_mono (by omega) hX₁_gt1.le hX₁₂
  have hmert : 0 ≤ (6.836e-6 : ℝ) + (2.964e-6 : ℝ) := by norm_num
  have h1 : ((6.836e-6 : ℝ) + 2.964e-6) / ((1 / (M : ℝ)) * Real.log X₂) ≤
      ((6.836e-6 : ℝ) + 2.964e-6) / ((1 / (M : ℝ)) * Real.log X₁) :=
    div_le_div_of_nonneg_left hmert (by positivity) (by gcongr)
  have h2 : 1 / (rayZIntLb M X₂ - 1) ≤ 1 / (rayZIntLb M X₁ - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  unfold raySumQInvInt
  linarith

theorem rayErrAq1Int_antitone (consts : External.CertifiedConstants) {M : ℕ} (hM : 4 ≤ M)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayErrAq1Int consts M X₂ ≤ rayErrAq1Int consts M X₁ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlog₁_pos : 0 < Real.log X₁ := by nlinarith
  have hX₁_gt1 : 1 < X₁ := one_lt_of_pos_log_pos hX₁_pos hlog₁_pos
  have hX₂_pos : 0 < X₂ := lt_of_lt_of_le hX₁_pos hX₁₂
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hlog₂ : 10 * (M : ℝ) ≤ Real.log X₂ := hlog₁.trans hlog₁₂
  have hlog₂_pos : 0 < Real.log X₂ := by nlinarith
  have hlog₁_e : Real.exp 1 < Real.log X₁ := by
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have : (40 : ℝ) ≤ Real.log X₁ := by
      have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    linarith
  have hlog₂_e : Real.exp 1 < Real.log X₂ := lt_of_lt_of_le hlog₁_e hlog₁₂
  have hcpt_le := rayCPt_antitone consts hX₁_pos hlog₁_e hX₁₂
  have hqinv_le := raySumQInvInt_antitone hM hX₁_pos hlog₁ hX₁₂
  have hqinv_nn := raySumQInvInt_nonneg hM hlog₂
  have hcpt_nn := rayCPt_nonneg consts hX₂_pos hlog₂_e
  have hleft_le : (0.0625 : ℝ) * rayCPt consts X₂ * raySumQInvInt M X₂ / ((M : ℝ) * consts.U_c) ≤
      (0.0625 : ℝ) * rayCPt consts X₁ * raySumQInvInt M X₁ / ((M : ℝ) * consts.U_c) := by
    refine div_le_div_of_nonneg_right ?_ (mul_nonneg hM_pos.le consts.U_c_pos.le)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hcpt_le (by norm_num)) hqinv_le hqinv_nn
      (mul_nonneg (by norm_num) (rayCPt_nonneg consts hX₁_pos hlog₁_e))
  have hpoly_id : ∀ u : ℝ, 0 < u →
      ((0.5 : ℝ) * u + 6) ^ 2 / u ^ ((11 / 2 : ℝ) - 3) =
        ((0.5 : ℝ) * u ^ (-(1 / 4 : ℝ)) + 6 * u ^ (-(5 / 4 : ℝ))) ^ 2 := by
    intro u hu
    have hexp : ((11 / 2 : ℝ) - 3) = (5 / 2 : ℝ) := by norm_num
    rw [hexp]
    have hpow2 : (u ^ (5 / 4 : ℝ)) ^ 2 = u ^ (5 / 2 : ℝ) := by
      rw [sq, ← Real.rpow_add hu]
      norm_num
    have h1 : u ^ (-(1 / 4 : ℝ)) = u / u ^ (5 / 4 : ℝ) := by
      rw [eq_div_iff (Real.rpow_pos_of_pos hu _).ne', ← Real.rpow_add hu]
      have hsum : (-(1 / 4 : ℝ)) + (5 / 4 : ℝ) = 1 := by norm_num
      rw [hsum, Real.rpow_one]
    have h2 : u ^ (-(5 / 4 : ℝ)) = 1 / u ^ (5 / 4 : ℝ) := by
      rw [eq_div_iff (Real.rpow_pos_of_pos hu _).ne', ← Real.rpow_add hu]
      have hsum : (-(5 / 4 : ℝ)) + (5 / 4 : ℝ) = 0 := by norm_num
      rw [hsum, Real.rpow_zero]
    rw [h1, h2, ← hpow2]
    ring
  have hpoly_le :
      ((0.5 : ℝ) * Real.log X₂ + 6) ^ 2 / (Real.log X₂) ^ ((11 / 2 : ℝ) - 3) ≤
      ((0.5 : ℝ) * Real.log X₁ + 6) ^ 2 / (Real.log X₁) ^ ((11 / 2 : ℝ) - 3) := by
    rw [hpoly_id (Real.log X₁) hlog₁_pos, hpoly_id (Real.log X₂) hlog₂_pos]
    have hr1 : (Real.log X₂) ^ (-(1 / 4 : ℝ)) ≤ (Real.log X₁) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlog₁_pos hlog₁₂ (by norm_num)
    have hr2 : (Real.log X₂) ^ (-(5 / 4 : ℝ)) ≤ (Real.log X₁) ^ (-(5 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlog₁_pos hlog₁₂ (by norm_num)
    have hbase : (0.5 : ℝ) * (Real.log X₂) ^ (-(1 / 4 : ℝ)) +
        6 * (Real.log X₂) ^ (-(5 / 4 : ℝ)) ≤
        (0.5 : ℝ) * (Real.log X₁) ^ (-(1 / 4 : ℝ)) +
        6 * (Real.log X₁) ^ (-(5 / 4 : ℝ)) := by linarith
    have hbase_nn : 0 ≤ (0.5 : ℝ) * (Real.log X₂) ^ (-(1 / 4 : ℝ)) +
        6 * (Real.log X₂) ^ (-(5 / 4 : ℝ)) := by
      have r1nn : 0 ≤ (Real.log X₂) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hlog₂_pos.le _
      have r2nn : 0 ≤ (Real.log X₂) ^ (-(5 / 4 : ℝ)) := Real.rpow_nonneg hlog₂_pos.le _
      positivity
    exact pow_le_pow_left₀ hbase_nn hbase 2
  have hpoly_nn : 0 ≤ ((0.5 : ℝ) * Real.log X₂ + 6) ^ 2 /
      (Real.log X₂) ^ ((11 / 2 : ℝ) - 3) := by
    have : 0 ≤ (Real.log X₂) ^ ((11 / 2 : ℝ) - 3) := Real.rpow_nonneg hlog₂_pos.le _
    positivity
  unfold rayErrAq1Int
  have hqinv₁_nn : 0 ≤ raySumQInvInt M X₁ := raySumQInvInt_nonneg hM hlog₁
  have hcpt₁_nn : 0 ≤ rayCPt consts X₁ := rayCPt_nonneg consts hX₁_pos hlog₁_e
  have hleft₁_nn : 0 ≤ (0.0625 : ℝ) * rayCPt consts X₁ * raySumQInvInt M X₁ / ((M : ℝ) * consts.U_c) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcpt₁_nn) hqinv₁_nn)
      (mul_nonneg hM_pos.le consts.U_c_pos.le)
  simpa [mul_div_assoc] using mul_le_mul hleft_le hpoly_le hpoly_nn hleft₁_nn

theorem rayErrAq2_antitone (consts : External.CertifiedConstants) {M : ℕ} (hM : 4 ≤ M)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayErrAq2 consts M X₂ ≤ rayErrAq2 consts M X₁ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_ge4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hc_pos : (0.15 : ℝ) ≤ 0.5 - rayBeta M := by
    unfold rayBeta
    have hdiv_nn : 0 ≤ 1 / (M : ℝ) := by positivity
    linarith [show (1e-9 : ℝ) ≤ 0.001 by norm_num]
  set c : ℝ := 0.5 - rayBeta M
  have hc : 0 < c := by linarith
  have hlog₁_40 : (40 : ℝ) ≤ Real.log X₁ := by nlinarith
  have hX₂_pos : 0 < X₂ := lt_of_lt_of_le hX₁_pos hX₁₂
  have hlog₁_e : Real.exp 1 < Real.log X₁ := by
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hlog₂_40 : (40 : ℝ) ≤ Real.log X₂ := hlog₁_40.trans hlog₁₂
  have hlog₂_e : Real.exp 1 < Real.log X₂ := lt_of_lt_of_le hlog₁_e hlog₁₂
  set A : ℝ := (13 / 10 : ℝ) * (0.25 : ℝ)
  set B : ℝ := (13 / 10 : ℝ) * ((636 / 1000 : ℝ) + consts.C_f0)
  have hA_nn : 0 ≤ A := by dsimp [A]; norm_num
  have hB_nn : 0 ≤ B := by
    have h2 : 0 ≤ consts.C_f0 := by rw [consts.C_f0_eq]; norm_num
    dsimp [B]; positivity
  have hexpand : ∀ u : ℝ,
      Real.exp ((rayBeta M - 0.5) * u) * u ^ 3 *
        (1 + ((13 / 10 : ℝ) * (0.25 * u + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) =
      (1 + B ^ 3) * (u ^ 3 * Real.exp (-c * u)) +
      (3 * A * B ^ 2) * (u ^ 4 * Real.exp (-c * u)) +
      (3 * A ^ 2 * B) * (u ^ 5 * Real.exp (-c * u)) +
      A ^ 3 * (u ^ 6 * Real.exp (-c * u)) := by
    intro u
    have hc_neg : (rayBeta M - 0.5) * u = -c * u := by simp only [c]; ring
    have hlin : (13 / 10 : ℝ) * (0.25 * u + (636 / 1000 : ℝ) + consts.C_f0) = A * u + B := by
      simp only [A, B]; ring
    rw [hc_neg, hlin]
    ring
  have hpoly_anti : ∀ k : ℕ, k ≤ 6 →
      Real.log X₂ ^ k * Real.exp (-c * Real.log X₂) ≤
        Real.log X₁ ^ k * Real.exp (-c * Real.log X₁) := by
    intro k hk
    have hkc : (k : ℝ) / c ≤ 40 := by
      have hk_r : (k : ℝ) ≤ 6 := by exact_mod_cast hk
      exact (div_le_div_of_nonneg_right hk_r hc.le).trans
        ((div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc_pos).trans (by norm_num))
    exact antitoneOn_pow_mul_exp_neg k hc (hkc.trans hlog₁_40) (hkc.trans hlog₂_40) hlog₁₂
  have hmid_le :
      Real.exp ((rayBeta M - 0.5) * Real.log X₂) * Real.log X₂ ^ 3 *
        (1 + ((13 / 10 : ℝ) * (0.25 * Real.log X₂ + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) ≤
      Real.exp ((rayBeta M - 0.5) * Real.log X₁) * Real.log X₁ ^ 3 *
        (1 + ((13 / 10 : ℝ) * (0.25 * Real.log X₁ + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) := by
    rw [hexpand (Real.log X₁), hexpand (Real.log X₂)]
    have p3 := hpoly_anti 3 (by norm_num)
    have p4 := hpoly_anti 4 (by norm_num)
    have p5 := hpoly_anti 5 (by norm_num)
    have p6 := hpoly_anti 6 (by norm_num)
    have c0 : 0 ≤ 1 + B ^ 3 := by positivity
    have c1 : 0 ≤ 3 * A * B ^ 2 := by positivity
    have c2 : 0 ≤ 3 * A ^ 2 * B := by positivity
    have c3 : 0 ≤ A ^ 3 := by positivity
    nlinarith
  have hmid_nn : 0 ≤ Real.exp ((rayBeta M - 0.5) * Real.log X₂) * Real.log X₂ ^ 3 *
      (1 + ((13 / 10 : ℝ) * (0.25 * Real.log X₂ + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) := by
    have : 0 ≤ A * Real.log X₂ + B := by nlinarith
    have hlin : (13 / 10 : ℝ) * (0.25 * Real.log X₂ + (636 / 1000 : ℝ) + consts.C_f0) =
        A * Real.log X₂ + B := by simp only [A, B]; ring
    rw [hlin]
    positivity
  unfold rayErrAq2
  dsimp only
  refine div_le_div_of_nonneg_right ?_ (mul_nonneg hM_pos.le consts.U_c_pos.le)
  have hc4g_le := rayC4g_antitone consts hX₁_pos hlog₁_e hX₁₂
  have hc4g_nn := rayC4g_nonneg consts hX₂_pos hlog₂_e
  have hleft : (0.5 : ℝ) * rayC4g consts X₂ ≤ (0.5 : ℝ) * rayC4g consts X₁ := by linarith
  calc (0.5 : ℝ) * rayC4g consts X₂ *
        Real.exp ((rayBeta M - 0.5) * Real.log X₂) * Real.log X₂ ^ 3 *
          (1 + ((13 / 10 : ℝ) * (0.25 * Real.log X₂ + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3)
      = ((0.5 : ℝ) * rayC4g consts X₂) *
          (Real.exp ((rayBeta M - 0.5) * Real.log X₂) * Real.log X₂ ^ 3 *
            (1 + ((13 / 10 : ℝ) * (0.25 * Real.log X₂ + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3)) := by ring
    _ ≤ ((0.5 : ℝ) * rayC4g consts X₁) *
          (Real.exp ((rayBeta M - 0.5) * Real.log X₁) * Real.log X₁ ^ 3 *
            (1 + ((13 / 10 : ℝ) * (0.25 * Real.log X₁ + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3)) :=
        mul_le_mul hleft hmid_le hmid_nn (by linarith)
    _ = (0.5 : ℝ) * rayC4g consts X₁ *
          Real.exp ((rayBeta M - 0.5) * Real.log X₁) * Real.log X₁ ^ 3 *
            (1 + ((13 / 10 : ℝ) * (0.25 * Real.log X₁ + (636 / 1000 : ℝ) + consts.C_f0)) ^ 3) := by ring

theorem rayErrQ2Int_antitone (consts : External.CertifiedConstants) {M : ℕ} (hM : 1 ≤ M)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayErrQ2Int consts M X₂ ≤ rayErrQ2Int consts M X₁ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hlog₂ : 10 * (M : ℝ) ≤ Real.log X₂ := hlog₁.trans hlog₁₂
  have hrew : ∀ X : ℝ, 10 * (M : ℝ) ≤ Real.log X →
      Real.log X ^ 2 / (rayZIntLb M X - 1) =
        ((M : ℝ) ^ 2 * ((Real.log X / (M : ℝ)) ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log X / (M : ℝ))))) /
          (Real.exp ((1 / 2 : ℝ) * (Real.log X / (M : ℝ))) - 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log X / (M : ℝ)))) := by
    intro X hXlog
    set t : ℝ := Real.log X / (M : ℝ)
    have ht10 : 10 ≤ t := (le_div_iff₀ hM_pos).mpr hXlog
    have hlog_eq : Real.log X = (M : ℝ) * t := by
      dsimp only [t]; field_simp [hM_pos.ne']
    have hzlb : rayZIntLb M X - 1 = Real.exp t - 2 := by unfold rayZIntLb rayZ0; ring
    have he_gt2 : 2 < Real.exp ((1 / 2 : ℝ) * t) := by
      have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h5 : Real.exp 1 ≤ Real.exp ((1 / 2 : ℝ) * t) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hnum : (M : ℝ) ^ 2 * (t ^ 2 * Real.exp (-(1 / 2 : ℝ) * t)) =
        Real.log X ^ 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
      rw [hlog_eq]; ring
    have hden : (Real.exp t - 2) * Real.exp (-(1 / 2 : ℝ) * t) =
        Real.exp ((1 / 2 : ℝ) * t) - 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
      rw [sub_mul, ← Real.exp_add,
        show t + -(1 / 2 : ℝ) * t = (1 / 2 : ℝ) * t by ring]
    rw [hzlb, hnum, ← hden]
    have he1 : Real.exp t - 2 ≠ 0 := by
      have : 2 < Real.exp t := lt_trans he_gt2 (Real.exp_lt_exp.mpr (by linarith))
      linarith
    have he2 : Real.exp (-(1 / 2 : ℝ) * t) ≠ 0 := (Real.exp_pos _).ne'
    field_simp [he1, he2]
  have ht₁ : 10 ≤ Real.log X₁ / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog₁
  have ht₁₂ : Real.log X₁ / (M : ℝ) ≤ Real.log X₂ / (M : ℝ) :=
    div_le_div_of_nonneg_right hlog₁₂ hM_pos.le
  have hnum_le : (M : ℝ) ^ 2 * ((Real.log X₂ / (M : ℝ)) ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ)))) ≤
      (M : ℝ) ^ 2 * ((Real.log X₁ / (M : ℝ)) ^ 2 * Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact antitoneOn_pow_mul_exp_neg 2 (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : (2 : ℝ) / (1 / 2 : ℝ) ≤ Real.log X₁ / (M : ℝ))
      (by linarith : (2 : ℝ) / (1 / 2 : ℝ) ≤ Real.log X₂ / (M : ℝ)) ht₁₂
  have hnum_nn : 0 ≤ (M : ℝ) ^ 2 * ((Real.log X₂ / (M : ℝ)) ^ 2 *
      Real.exp (-(1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ)))) := by positivity
  have hden_pos : 0 < Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) -
      2 * Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) := by
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h5 : Real.exp 1 ≤ Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hneg : Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hden_le : Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) -
      2 * Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) ≤
      Real.exp ((1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ))) -
      2 * Real.exp (-(1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ))) := by
    have ha : Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) ≤
        Real.exp ((1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    have hb : Real.exp (-(1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ))) ≤
        Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hratio_le : Real.log X₂ ^ 2 / (rayZIntLb M X₂ - 1) ≤
      Real.log X₁ ^ 2 / (rayZIntLb M X₁ - 1) := by
    rw [hrew X₁ hlog₁, hrew X₂ hlog₂]
    exact (div_le_div_of_nonneg_left hnum_nn hden_pos hden_le).trans
      (div_le_div_of_nonneg_right hnum_le hden_pos.le)
  unfold rayErrQ2Int
  have hden_pos : ∀ X : ℝ, 10 * (M : ℝ) ≤ Real.log X → 0 < rayZIntLb M X - 1 := by
    intro X hXlog
    have := rayZIntLb_ge_20000 hM hXlog
    linarith
  have hscale : ∀ X : ℝ, 10 * (M : ℝ) ≤ Real.log X →
      Real.log X ^ 2 / (2 * (M : ℝ) * consts.U_c * (rayZIntLb M X - 1)) =
        (Real.log X ^ 2 / (rayZIntLb M X - 1)) / (2 * (M : ℝ) * consts.U_c) := by
    intro X hXlog
    have hsub := (hden_pos X hXlog).ne'
    field_simp [hM_pos.ne', consts.U_c_pos.ne', hsub]
  rw [hscale X₁ hlog₁, hscale X₂ hlog₂]
  have hUc_pos := consts.U_c_pos
  exact div_le_div_of_nonneg_right hratio_le (by positivity)

theorem rayErrOne_antitone (consts : External.CertifiedConstants) {M : ℕ} (hM : 1 ≤ M)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 2 ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayErrOne consts M X₂ ≤ rayErrOne consts M X₁ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hX₂_pos : 0 < X₂ := lt_of_lt_of_le hX₁_pos hX₁₂
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hanti := antitoneOn_pow_mul_exp_neg 2 (by norm_num : (0 : ℝ) < 1)
    (by linarith : (2 : ℝ) / 1 ≤ Real.log X₁) (by linarith : (2 : ℝ) / 1 ≤ Real.log X₂) hlog₁₂
  have heq : ∀ X : ℝ, 0 < X → Real.log X ^ 2 / ((M : ℝ) * consts.U_c * X) =
      (Real.log X ^ 2 * Real.exp (-1 * Real.log X)) / ((M : ℝ) * consts.U_c) := by
    intro X hX
    rw [neg_one_mul, Real.exp_neg, Real.exp_log hX]
    ring
  unfold rayErrOne
  rw [heq X₁ hX₁_pos, heq X₂ hX₂_pos]
  exact div_le_div_of_nonneg_right hanti (mul_nonneg hM_pos.le consts.U_c_pos.le)

theorem rayErrorSumInt_antitone (consts : External.CertifiedConstants) {M : ℕ}
    (hM : 4 ≤ M) {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁)
    (hX₁₂ : X₁ ≤ X₂) :
    rayErrorSumInt consts M X₂ ≤ rayErrorSumInt consts M X₁ := by
  have hM1 : 1 ≤ M := by omega
  have hlog₁_e : Real.exp 1 < Real.log X₁ := by
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have : (40 : ℝ) ≤ Real.log X₁ := by
      have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    linarith
  have hlog₁_2 : (2 : ℝ) ≤ Real.log X₁ := by
    have : (40 : ℝ) ≤ Real.log X₁ := by
      have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    linarith
  unfold rayErrorSumInt
  have e1 := rayErrR1_antitone consts hM1 hX₁_pos hlog₁_e hX₁₂
  have e2 := rayErrAq1Int_antitone consts hM hX₁_pos hlog₁ hX₁₂
  have e3 := rayErrAq2_antitone consts hM hX₁_pos hlog₁ hX₁₂
  have e4 := rayErrQ2Int_antitone consts hM1 hX₁_pos hlog₁ hX₁₂
  have e5 := rayErrOne_antitone consts hM1 hX₁_pos hlog₁_2 hX₁₂
  linarith

end RayMonotonicity

end

end BuchstabSwitching
