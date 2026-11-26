import BuchstabSwitching.Sieve.Regime3RayBridge.IntegerCutoffs
import BuchstabSwitching.Sieve.LinearSieveBJS
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.Certificates.Data
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ## 3a. Core Ray Cutoffs and Generic Analytic Monotonicity Helpers -/

section RayCoreEnvelopes

private lemma exp_two_lt_ten : Real.exp 2 < (10 : ℝ) := by
  have h1 : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 1]

private lemma two_lt_log_ten : (2 : ℝ) < Real.log 10 := by
  rw [← Real.log_exp 2]
  exact Real.log_lt_log (Real.exp_pos 2) exp_two_lt_ten

private lemma log_ten_lt_three : Real.log 10 < (3 : ℝ) := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : (10 : ℝ) < Real.exp 3 := by
    have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_natCast_mul]; norm_num
    rw [he3]
    have hp : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) h1.le 3
    linarith [show (10 : ℝ) < (2.7 : ℝ) ^ 3 by norm_num]
  rw [← Real.log_exp 3]
  exact Real.log_lt_log (by positivity) h3

theorem ten_pow_600_eq_asymptoticCert_X_LS :
    ((10 ^ 200 : ℕ) ^ 3) = asymptoticCert.X_LS := by
  rfl

theorem asymptoticCert_X_LS_cast :
    (asymptoticCert.X_LS : ℝ) = ((10 : ℝ) ^ 200) ^ 3 := by
  rw [← ten_pow_600_eq_asymptoticCert_X_LS, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]

theorem log_asymptoticCert_X_LS_ge :
    (1200 : ℝ) < Real.log (asymptoticCert.X_LS : ℝ) := by
  rw [asymptoticCert_X_LS_cast, Real.log_pow, Real.log_pow]
  push_cast
  linarith [two_lt_log_ten]

theorem exp_1200_lt_asymptoticCert_X_LS :
    Real.exp 1200 < (asymptoticCert.X_LS : ℝ) := by
  have hpos : (0 : ℝ) < (asymptoticCert.X_LS : ℝ) := by
    rw [asymptoticCert_X_LS_cast]; positivity
  rw [← Real.exp_log hpos]
  exact Real.exp_lt_exp.mpr log_asymptoticCert_X_LS_ge

theorem log_asymptoticCert_X_LS_lt :
    Real.log (asymptoticCert.X_LS : ℝ) < (1800 : ℝ) := by
  rw [asymptoticCert_X_LS_cast, Real.log_pow, Real.log_pow]
  have h3_200 : (3 : ℕ) * (200 : ℕ) = 600 := by decide
  push_cast
  linarith [log_ten_lt_three]

theorem log_log_asymptoticCert_X_LS_lt :
    Real.log (Real.log (asymptoticCert.X_LS : ℝ)) < (8 : ℝ) := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h8 : (1800 : ℝ) < Real.exp 8 := by
    have he8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_natCast_mul]; norm_num
    rw [he8]
    have hp : (2.7 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 :=
      pow_le_pow_left₀ (by norm_num) h1.le 8
    linarith [show (1800 : ℝ) < (2.7 : ℝ) ^ 8 by norm_num]
  have hlpos : 0 < Real.log (asymptoticCert.X_LS : ℝ) := by linarith [log_asymptoticCert_X_LS_ge]
  rw [← Real.log_exp 8]
  exact Real.log_lt_log hlpos (log_asymptoticCert_X_LS_lt.trans h8)

/-- Generic antitonicity: for `k : ℕ` and `0 < c`, `u ↦ u ^ k * exp (-c * u)` is antitone on
`[k / c, ∞)`. -/
lemma antitoneOn_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun u : ℝ => u ^ k * Real.exp (-c * u)) (Set.Ici ((k : ℝ) / c)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · intro u _ v _ huv
    simp only [pow_zero, one_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · refine antitoneOn_of_deriv_nonpos (convex_Ici ((k : ℝ) / c)) ?_ ?_ ?_
    · exact ((continuous_pow k).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
    · exact ((differentiable_pow k).mul
        (Real.differentiable_exp.comp (differentiable_const _ |>.mul differentiable_id))).differentiableOn
    · intro u hu
      have hu_ge : (k : ℝ) / c < u := by
        simpa [interior_Ici] using hu
      have hu_pos : 0 < u := by
        have hk0 : (0 : ℝ) ≤ (k : ℝ) / c := div_nonneg (Nat.cast_nonneg k) hc.le
        linarith
      have hcu : (k : ℝ) < c * u := (div_lt_iff₀ hc).mp hu_ge |>.trans_eq (mul_comm u c)
      have hderiv : HasDerivAt (fun x : ℝ => x ^ k * Real.exp (-c * x))
          ((k : ℝ) * u ^ (k - 1) * Real.exp (-c * u) +
            u ^ k * (-c * Real.exp (-c * u))) u := by
        have hp : HasDerivAt (fun x : ℝ => x ^ k) ((k : ℝ) * u ^ (k - 1)) u := hasDerivAt_pow k u
        have hlin : HasDerivAt (fun x : ℝ => -c * x) (-c) u := by
          simpa using (hasDerivAt_const u (-c)).fun_mul (hasDerivAt_id u)
        have he : HasDerivAt (fun x : ℝ => Real.exp (-c * x)) (-c * Real.exp (-c * u)) u := by
          simpa [mul_comm] using hlin.exp
        exact hp.fun_mul he
      rw [hderiv.deriv]
      have hfac : (k : ℝ) * u ^ (k - 1) * Real.exp (-c * u) + u ^ k * (-c * Real.exp (-c * u)) =
          ((k : ℝ) - c * u) * u ^ (k - 1) * Real.exp (-c * u) := by
        have hpow : u ^ k = u * u ^ (k - 1) := by
          conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ']
        rw [hpow]
        ring
      rw [hfac]
      have h1 : (k : ℝ) - c * u ≤ 0 := by linarith
      have h2 : 0 ≤ u ^ (k - 1) * Real.exp (-c * u) :=
        mul_nonneg (pow_nonneg hu_pos.le _) (Real.exp_pos _).le
      nlinarith

/-- Generic antitonicity: `u ↦ log u / u` is antitone on `[exp 1, ∞)`. -/
lemma antitoneOn_log_div_id :
    AntitoneOn (fun u : ℝ => Real.log u / u) (Set.Ici (Real.exp 1)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici (Real.exp 1)) ?_ ?_ ?_
  · intro u hu
    have hu_pos : u ≠ 0 := (lt_of_lt_of_le (Real.exp_pos 1) (Set.mem_Ici.mp hu)).ne'
    exact ((Real.continuousAt_log hu_pos).div continuousAt_id hu_pos).continuousWithinAt
  · intro u hu
    have hu_pos : u ≠ 0 :=
      (lt_of_lt_of_le (Real.exp_pos 1) (Set.mem_Ici.mp (interior_subset hu))).ne'
    exact ((Real.differentiableAt_log hu_pos).div differentiableAt_id hu_pos).differentiableWithinAt
  · intro u hu
    have hu_gt : Real.exp 1 < u := by simpa [interior_Ici] using hu
    have hu_pos : 0 < u := lt_trans (Real.exp_pos 1) hu_gt
    have hderiv : HasDerivAt (fun x : ℝ => Real.log x / x)
        ((1 / u * u - Real.log u * 1) / u ^ 2) u := by
      simpa [one_div] using (Real.hasDerivAt_log hu_pos.ne').fun_div (hasDerivAt_id u) hu_pos.ne'
    rw [hderiv.deriv]
    have hlog_gt1 : 1 < Real.log u := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) hu_gt
    have h1u : 1 / u * u = 1 := one_div_mul_cancel hu_pos.ne'
    rw [h1u, mul_one]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg u)

/-- Parameter `β(M) = (1 - 1/M)/3 + 10^-9`. -/
def rayBeta (M : ℕ) : ℝ :=
  (1 - 1 / (M : ℝ)) / 3 + (1e-9 : ℝ)

/-- Real cutoff `z0(M, X) = exp ((log X) / M)`. -/
noncomputable def rayZ0 (M : ℕ) (X : ℝ) : ℝ :=
  Real.exp (Real.log X / (M : ℝ))

/-- Lower bound `z_int_lb(M, X) = z0(M, X) - 1` on `rayZ M N` for `N ≥ X`. -/
noncomputable def rayZIntLb (M : ℕ) (X : ℝ) : ℝ :=
  rayZ0 M X - 1

/-- Lower bound `log_z_lb(M, X)` on `log (rayZ M N)` for `N ≥ X`. -/
noncomputable def rayLogZLb (M : ℕ) (X : ℝ) : ℝ :=
  (Real.log X / (M : ℝ)) * (1 - 1 / (rayZIntLb M X * (Real.log X / (M : ℝ))))

lemma rayZ0_eq_rpow {M : ℕ} {X : ℝ} (hX : 0 < X) :
    rayZ0 M X = X ^ ((1 : ℝ) / (M : ℝ)) := by
  unfold rayZ0
  rw [Real.rpow_def_of_pos hX, mul_one_div]

lemma rayZ0_mono {M : ℕ} (hM : 1 ≤ M) {X₁ X₂ : ℝ} (hX₁ : 1 ≤ X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayZ0 M X₁ ≤ rayZ0 M X₂ := by
  unfold rayZ0
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
    (Real.log_le_log (by linarith) hX₁₂) hM_pos.le)

lemma rayZIntLb_mono {M : ℕ} (hM : 1 ≤ M) {X₁ X₂ : ℝ} (hX₁ : 1 ≤ X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayZIntLb M X₁ ≤ rayZIntLb M X₂ := by
  unfold rayZIntLb
  linarith [rayZ0_mono hM hX₁ hX₁₂]

lemma rayZ0_ge_exp_75 {X : ℝ} (hlogX : (1200 : ℝ) ≤ Real.log X) :
    Real.exp 75 ≤ rayZ0 16 X := by
  unfold rayZ0
  exact Real.exp_le_exp.mpr (by linarith)

lemma one_lt_of_pos_log_pos {X : ℝ} (hX : 0 < X) (hlog : 0 < Real.log X) : 1 < X := by
  by_contra hle
  push Not at hle
  linarith [Real.log_nonpos hX.le hle]

lemma exp_ten_ge_20001 : (20001 : ℝ) ≤ Real.exp 10 := by
  have h27 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he5 : (142 : ℝ) ≤ Real.exp 5 := by
    have h1 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_natCast_mul]; norm_num
    rw [h1]
    have hp : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h27.le 5
    linarith [show (142 : ℝ) ≤ (2.7 : ℝ) ^ 5 by norm_num]
  have hsq : Real.exp 10 = Real.exp 5 ^ 2 := by rw [← Real.exp_natCast_mul]; norm_num
  rw [hsq]
  have hp : (142 : ℝ) ^ 2 ≤ Real.exp 5 ^ 2 := pow_le_pow_left₀ (by norm_num) he5 2
  linarith [show (20001 : ℝ) ≤ (142 : ℝ) ^ 2 by norm_num]

lemma rayZIntLb_gt_1e12 {X : ℝ} (hlogX : (1200 : ℝ) ≤ Real.log X) :
    (10 : ℝ) ^ 12 + 2 ≤ rayZIntLb 16 X := by
  have hz0 : Real.exp 75 ≤ rayZ0 16 X := rayZ0_ge_exp_75 hlogX
  have he30 : (10 : ℝ) ^ 12 + 3 ≤ Real.exp 30 := by
    have he : Real.exp 30 = Real.exp 10 ^ 3 := by rw [← Real.exp_natCast_mul]; norm_num
    rw [he]
    have hp : (20001 : ℝ) ^ 3 ≤ Real.exp 10 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) exp_ten_ge_20001 3
    linarith [show (10 : ℝ) ^ 12 + 3 ≤ (20001 : ℝ) ^ 3 by norm_num]
  have he75 : Real.exp 30 ≤ Real.exp 75 := Real.exp_le_exp.mpr (by norm_num)
  unfold rayZIntLb
  linarith

lemma rayZIntLb_ge_20000 {M : ℕ} (hM : 1 ≤ M) {X : ℝ}
    (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    (20000 : ℝ) ≤ rayZIntLb M X := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have h10 : 10 ≤ Real.log X / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog
  have hz0 : Real.exp 10 ≤ rayZ0 M X := Real.exp_le_exp.mpr h10
  have he10 : (20001 : ℝ) ≤ Real.exp 10 := exp_ten_ge_20001
  unfold rayZIntLb
  linarith

lemma rayLogZLb_eq_sub {M : ℕ} {X : ℝ} (hlogX : 0 < Real.log X) (hM : 1 ≤ M)
    (hzlb : 0 < rayZIntLb M X) :
    rayLogZLb M X = Real.log X / (M : ℝ) - 1 / rayZIntLb M X := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  unfold rayLogZLb
  field_simp [hlogX.ne', hM_pos.ne', hzlb.ne']

lemma rayLogZLb_mono {M : ℕ} (hM : 1 ≤ M) {X₁ X₂ : ℝ} (hX₁ : 1 < X₁) (hX₁₂ : X₁ ≤ X₂)
    (hzlb : 0 < rayZIntLb M X₁) :
    rayLogZLb M X₁ ≤ rayLogZLb M X₂ := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hX₂ : 1 < X₂ := lt_of_lt_of_le hX₁ hX₁₂
  have hlog₁ : 0 < Real.log X₁ := Real.log_pos hX₁
  have hlog₂ : 0 < Real.log X₂ := Real.log_pos hX₂
  have hzlb₁₂ : rayZIntLb M X₁ ≤ rayZIntLb M X₂ := rayZIntLb_mono hM hX₁.le hX₁₂
  have hzlb₂ : 0 < rayZIntLb M X₂ := lt_of_lt_of_le hzlb hzlb₁₂
  rw [rayLogZLb_eq_sub hlog₁ hM hzlb, rayLogZLb_eq_sub hlog₂ hM hzlb₂]
  have hdiv1 : Real.log X₁ / (M : ℝ) ≤ Real.log X₂ / (M : ℝ) :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hX₁₂) hM_pos.le
  have hdiv2 : 1 / rayZIntLb M X₂ ≤ 1 / rayZIntLb M X₁ :=
    one_div_le_one_div_of_le hzlb hzlb₁₂
  linarith

end RayCoreEnvelopes

end

end BuchstabSwitching
