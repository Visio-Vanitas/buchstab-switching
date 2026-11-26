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

/-! ## 3. Asymptotic Ray Envelopes and Monotonicity for `X ≥ X_LS` -/

section RayMonotonicity

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

/-- Generic antitonicity: for `0 ≤ a`, `0 ≤ b`, `0 < c`, `t ↦ (a * t + b) * exp (-c * t)` is
antitone on `[1 / c, ∞)`. -/
private lemma antitoneOn_lin_mul_exp_neg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    AntitoneOn (fun t : ℝ => (a * t + b) * Real.exp (-c * t)) (Set.Ici (1 / c)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici (1 / c)) ?_ ?_ ?_
  · exact (((continuous_const.mul continuous_id).add continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  · exact (((differentiable_const a |>.mul differentiable_id).add (differentiable_const b)).mul
      (Real.differentiable_exp.comp (differentiable_const (-c) |>.mul differentiable_id))).differentiableOn
  · intro t ht
    have ht_gt : 1 / c < t := by simpa [interior_Ici] using ht
    have hct : 1 < c * t := (div_lt_iff₀ hc).mp ht_gt |>.trans_eq (mul_comm t c)
    have hderiv : HasDerivAt (fun x : ℝ => (a * x + b) * Real.exp (-c * x))
        (a * Real.exp (-c * t) + (a * t + b) * (-c * Real.exp (-c * t))) t := by
      have hl : HasDerivAt (fun x : ℝ => a * x + b) a t := by
        simpa using ((hasDerivAt_const t a).fun_mul (hasDerivAt_id t)).fun_add (hasDerivAt_const t b)
      have hlin : HasDerivAt (fun x : ℝ => -c * x) (-c) t := by
        simpa using (hasDerivAt_const t (-c)).fun_mul (hasDerivAt_id t)
      have he : HasDerivAt (fun x : ℝ => Real.exp (-c * x)) (-c * Real.exp (-c * t)) t := by
        simpa [mul_comm] using hlin.exp
      exact hl.fun_mul he
    rw [hderiv.deriv]
    have hfac : a * Real.exp (-c * t) + (a * t + b) * (-c * Real.exp (-c * t)) =
        (a * (1 - c * t) - b * c) * Real.exp (-c * t) := by ring
    rw [hfac]
    have hneg : a * (1 - c * t) - b * c ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hneg (Real.exp_pos _).le

/-- Generic antitonicity: `t ↦ t / (exp t - 1)` is antitone on `(0, ∞)`. -/
private lemma antitoneOn_id_div_exp_sub_one :
    AntitoneOn (fun t : ℝ => t / (Real.exp t - 1)) (Set.Ioi 0) := by
  have hmono : MonotoneOn (fun t : ℝ => (Real.exp t - 1) / t) (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · intro t ht
      exact ((Real.continuous_exp.sub continuous_const).continuousAt.div
        continuous_id.continuousAt (Set.mem_Ioi.mp ht).ne').continuousWithinAt
    · intro t ht
      exact ((Real.differentiableAt_exp.sub (differentiableAt_const 1)).div
        differentiableAt_id (Set.mem_Ioi.mp (interior_subset ht)).ne').differentiableWithinAt
    · intro t ht
      have ht_pos : 0 < t := by simpa [interior_Ioi] using ht
      have hderiv : HasDerivAt (fun x : ℝ => (Real.exp x - 1) / x)
          ((Real.exp t * t - (Real.exp t - 1) * 1) / t ^ 2) t := by
        have hnum : HasDerivAt (fun x : ℝ => Real.exp x - 1) (Real.exp t) t := by
          simpa using (Real.hasDerivAt_exp t).fun_sub (hasDerivAt_const t 1)
        exact hnum.fun_div (hasDerivAt_id t) ht_pos.ne'
      rw [hderiv.deriv]
      have hnum : 0 ≤ Real.exp t * t - (Real.exp t - 1) * 1 := by
        have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
        have h2 : (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
        linarith
      exact div_nonneg hnum (sq_nonneg t)
  intro t ht s hs hts
  have ht_pos : 0 < t := ht
  have hs_pos : 0 < s := hs
  have het : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht_pos)
  have hes : 0 < Real.exp s - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hs_pos)
  have hle := hmono ht hs hts
  calc s / (Real.exp s - 1) = ((Real.exp s - 1) / s)⁻¹ := (inv_div _ _).symm
    _ ≤ ((Real.exp t - 1) / t)⁻¹ :=
        inv_anti₀ (div_pos het ht_pos) hle
    _ = t / (Real.exp t - 1) := inv_div _ _

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

/-- Uniform relative error envelope `delta_v` for `V_N(z)` at `X ≥ 10^600` (`z ≥ rayZIntLb M X`,
`log z ≤ log X / M`). Bounds both `External.deltaV_bs 4 (rayZ M N)` and
`External.deltaV_bs N (rayZ M N)`. -/
noncomputable def rayDeltaV (M : ℕ) (X : ℝ) : ℝ :=
  let zlb := rayZIntLb M X
  let f1 := (3 * (Real.log X / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt zlb)
  let f2 := (2 : ℝ) / zlb
  let f3 := (8 * Real.log X) / zlb
  let f4 := (1 : ℝ) / (zlb - 1)
  let d_lo := 1 - (1 - f1) * (1 - f2) * (1 - f3) * (1 - f4)
  let d_hi := (1 + f1) * (1 + f2) * (1 + f3) * (1 + f4) - 1
  max d_lo d_hi

lemma rayZIntLb_ge_20000 {M : ℕ} (hM : 1 ≤ M) {X : ℝ}
    (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    (20000 : ℝ) ≤ rayZIntLb M X := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have h10 : 10 ≤ Real.log X / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog
  have hz0 : Real.exp 10 ≤ rayZ0 M X := Real.exp_le_exp.mpr h10
  have he10 : (20001 : ℝ) ≤ Real.exp 10 := exp_ten_ge_20001
  unfold rayZIntLb
  linarith

private lemma rayDeltaV_parts_antitone {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    let f1 := fun X : ℝ => (3 * (Real.log X / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M X))
    let f2 := fun X : ℝ => (2 : ℝ) / rayZIntLb M X
    let f3 := fun X : ℝ => (8 * Real.log X) / rayZIntLb M X
    let f4 := fun X : ℝ => (1 : ℝ) / (rayZIntLb M X - 1)
    0 ≤ f1 X₂ ∧ f1 X₂ ≤ f1 X₁ ∧ f1 X₁ < 1 ∧
    0 ≤ f2 X₂ ∧ f2 X₂ ≤ f2 X₁ ∧ f2 X₁ < 1 ∧
    0 ≤ f3 X₂ ∧ f3 X₂ ≤ f3 X₁ ∧ f3 X₁ < 1 ∧
    0 ≤ f4 X₂ ∧ f4 X₂ ≤ f4 X₁ ∧ f4 X₁ < 1 := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_le_r : (M : ℝ) ≤ 16 := by exact_mod_cast hM_le
  have hlog₁_pos : 10 ≤ Real.log X₁ := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have hX₁_gt1 : 1 < X₁ := one_lt_of_pos_log_pos hX₁_pos (by linarith)
  have hX₂_gt1 : 1 < X₂ := lt_of_lt_of_le hX₁_gt1 hX₁₂
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have hlog₂ : 10 * (M : ℝ) ≤ Real.log X₂ := hlog₁.trans hlog₁₂
  have hz₁_20k : (20000 : ℝ) ≤ rayZIntLb M X₁ := rayZIntLb_ge_20000 hM hlog₁
  have hz₁₂ : rayZIntLb M X₁ ≤ rayZIntLb M X₂ := rayZIntLb_mono hM hX₁_gt1.le hX₁₂
  have hz₂_20k : (20000 : ℝ) ≤ rayZIntLb M X₂ := hz₁_20k.trans hz₁₂
  have ht₁ : 10 ≤ Real.log X₁ / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog₁
  have ht₂ : 10 ≤ Real.log X₂ / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog₂
  have ht₁₂ : Real.log X₁ / (M : ℝ) ≤ Real.log X₂ / (M : ℝ) :=
    div_le_div_of_nonneg_right hlog₁₂ hM_pos.le
  -- `f1`
  have hf1_eq : ∀ X : ℝ, 10 * (M : ℝ) ≤ Real.log X →
      (3 * (Real.log X / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M X)) =
        ((3 * (Real.log X / (M : ℝ)) + 5) * Real.exp (-(1 / 4 : ℝ) * (Real.log X / (M : ℝ)))) /
          (8 * Real.pi * Real.sqrt (Real.exp ((1 / 2 : ℝ) * (Real.log X / (M : ℝ))) -
            Real.exp (-(1 / 2 : ℝ) * (Real.log X / (M : ℝ))))) := by
    intro X hXlog
    set t : ℝ := Real.log X / (M : ℝ)
    have hzlb_eq : rayZIntLb M X = Real.exp t - 1 := rfl
    have hdiff_pos : 0 < Real.exp ((1 / 2 : ℝ) * t) - Real.exp (-(1 / 2 : ℝ) * t) := by
      have : 0 < t := by have := (le_div_iff₀ hM_pos).mpr hXlog; linarith
      rw [sub_pos, Real.exp_lt_exp]; linarith
    have hsqrt_id : Real.sqrt (Real.exp t - 1) =
        Real.exp ((1 / 4 : ℝ) * t) *
          Real.sqrt (Real.exp ((1 / 2 : ℝ) * t) - Real.exp (-(1 / 2 : ℝ) * t)) := by
      have he2 : Real.exp ((1 / 4 : ℝ) * t) ^ 2 = Real.exp ((1 / 2 : ℝ) * t) := by
        rw [sq, ← Real.exp_add, show (1 / 4 : ℝ) * t + (1 / 4 : ℝ) * t = (1 / 2 : ℝ) * t by ring]
      rw [← Real.sqrt_sq (Real.exp_pos ((1 / 4 : ℝ) * t)).le, ← Real.sqrt_mul (sq_nonneg _), he2]
      congr 1
      rw [mul_sub, ← Real.exp_add, ← Real.exp_add,
        show (1 / 2 : ℝ) * t + (1 / 2 : ℝ) * t = t by ring,
        show (1 / 2 : ℝ) * t + -(1 / 2 : ℝ) * t = 0 by ring, Real.exp_zero]
    rw [hzlb_eq, hsqrt_id]
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hexp_ne : Real.exp ((1 / 4 : ℝ) * t) ≠ 0 := (Real.exp_pos _).ne'
    have hsq_ne : Real.sqrt (Real.exp ((1 / 2 : ℝ) * t) - Real.exp (-(1 / 2 : ℝ) * t)) ≠ 0 :=
      (Real.sqrt_pos.mpr hdiff_pos).ne'
    have heinv : Real.exp (-(1 / 4 : ℝ) * t) = (Real.exp ((1 / 4 : ℝ) * t))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [heinv]
    field_simp [hpi_ne, hexp_ne, hsq_ne]
  have hf1_nn : 0 ≤ (3 * (Real.log X₂ / (M : ℝ)) + 5) /
      (8 * Real.pi * Real.sqrt (rayZIntLb M X₂)) := by positivity
  have hf1_anti :
      (3 * (Real.log X₂ / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M X₂)) ≤
      (3 * (Real.log X₁ / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M X₁)) := by
    rw [hf1_eq X₁ hlog₁, hf1_eq X₂ hlog₂]
    have hnum : (3 * (Real.log X₂ / (M : ℝ)) + 5) * Real.exp (-(1 / 4 : ℝ) * (Real.log X₂ / (M : ℝ))) ≤
        (3 * (Real.log X₁ / (M : ℝ)) + 5) * Real.exp (-(1 / 4 : ℝ) * (Real.log X₁ / (M : ℝ))) := by
      have hlin := antitoneOn_lin_mul_exp_neg (a := 3) (b := 5) (c := 1 / 4)
        (by norm_num) (by norm_num) (by norm_num)
      exact hlin (show (1 / (1 / 4 : ℝ) : ℝ) ≤ Real.log X₁ / (M : ℝ) by linarith)
        (show (1 / (1 / 4 : ℝ) : ℝ) ≤ Real.log X₂ / (M : ℝ) by linarith) ht₁₂
    have hden_pos : 0 < 8 * Real.pi * Real.sqrt (Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) -
        Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ)))) := by
      have hdiff : 0 < Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) -
          Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) := by
        rw [sub_pos, Real.exp_lt_exp]; linarith
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.sqrt_pos.mpr hdiff)
    have hden_le : 8 * Real.pi * Real.sqrt (Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) -
        Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ)))) ≤
        8 * Real.pi * Real.sqrt (Real.exp ((1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ))) -
        Real.exp (-(1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      have ha : Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) ≤
          Real.exp ((1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      have hb : Real.exp (-(1 / 2 : ℝ) * (Real.log X₂ / (M : ℝ))) ≤
          Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hnum_nn : 0 ≤ (3 * (Real.log X₂ / (M : ℝ)) + 5) *
        Real.exp (-(1 / 4 : ℝ) * (Real.log X₂ / (M : ℝ))) := by positivity
    exact (div_le_div_of_nonneg_left hnum_nn hden_pos hden_le).trans
      (div_le_div_of_nonneg_right hnum hden_pos.le)
  have hf1_lt_005 : (3 * (Real.log X₁ / (M : ℝ)) + 5) /
      (8 * Real.pi * Real.sqrt (rayZIntLb M X₁)) < (0.05 : ℝ) := by
    have hX0_pos : 0 < Real.exp (10 * (M : ℝ)) := Real.exp_pos _
    have hX0_log : 10 * (M : ℝ) ≤ Real.log (Real.exp (10 * (M : ℝ))) := by rw [Real.log_exp]
    have hX0_le : Real.exp (10 * (M : ℝ)) ≤ X₁ := by
      rw [← Real.exp_log hX₁_pos]; exact Real.exp_le_exp.mpr hlog₁
    have hmono0 : (3 * (Real.log X₁ / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M X₁)) ≤
        (3 * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ)) + 5) /
          (8 * Real.pi * Real.sqrt (rayZIntLb M (Real.exp (10 * (M : ℝ))))) := by
      -- apply `hf1_eq` directly between `Real.exp (10 * M)` and `X₁`
      rw [hf1_eq (Real.exp (10 * (M : ℝ))) hX0_log, hf1_eq X₁ hlog₁]
      have hlog01 : Real.log (Real.exp (10 * (M : ℝ))) ≤ Real.log X₁ := by
        rw [Real.log_exp]; exact hlog₁
      have ht01 : Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ) ≤ Real.log X₁ / (M : ℝ) :=
        div_le_div_of_nonneg_right hlog01 hM_pos.le
      have hnum : (3 * (Real.log X₁ / (M : ℝ)) + 5) * Real.exp (-(1 / 4 : ℝ) * (Real.log X₁ / (M : ℝ))) ≤
          (3 * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ)) + 5) *
            Real.exp (-(1 / 4 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ))) := by
        have hlin := antitoneOn_lin_mul_exp_neg (a := 3) (b := 5) (c := 1 / 4)
          (by norm_num) (by norm_num) (by norm_num)
        refine hlin ?_ ?_ ht01
        · rw [Real.log_exp, mul_div_cancel_right₀ _ hM_pos.ne']; norm_num
        · show (1 / (1 / 4 : ℝ) : ℝ) ≤ Real.log X₁ / (M : ℝ); linarith
      have hden_pos : 0 < 8 * Real.pi * Real.sqrt
          (Real.exp ((1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ))) -
            Real.exp (-(1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ)))) := by
        have ht0 : 0 < Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ) := by
          rw [Real.log_exp, mul_div_cancel_right₀ _ hM_pos.ne']; norm_num
        have hdiff : 0 < Real.exp ((1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ))) -
            Real.exp (-(1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ))) := by
          rw [sub_pos, Real.exp_lt_exp]; linarith
        exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.sqrt_pos.mpr hdiff)
      have hden_le : 8 * Real.pi * Real.sqrt
            (Real.exp ((1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ))) -
              Real.exp (-(1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ)))) ≤
          8 * Real.pi * Real.sqrt (Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) -
            Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
        have ha : Real.exp ((1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ))) ≤
            Real.exp ((1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) := Real.exp_le_exp.mpr (by linarith)
        have hb : Real.exp (-(1 / 2 : ℝ) * (Real.log X₁ / (M : ℝ))) ≤
            Real.exp (-(1 / 2 : ℝ) * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ))) :=
          Real.exp_le_exp.mpr (by linarith)
        linarith
      have hnum_nn : 0 ≤ (3 * (Real.log X₁ / (M : ℝ)) + 5) *
          Real.exp (-(1 / 4 : ℝ) * (Real.log X₁ / (M : ℝ))) := by positivity
      exact (div_le_div_of_nonneg_left hnum_nn hden_pos hden_le).trans
        (div_le_div_of_nonneg_right hnum hden_pos.le)
    have hval0 : (3 * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ)) + 5) /
        (8 * Real.pi * Real.sqrt (rayZIntLb M (Real.exp (10 * (M : ℝ))))) < (0.05 : ℝ) := by
      have hlogeq : Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ) = 10 := by
        rw [Real.log_exp, mul_div_cancel_right₀ _ hM_pos.ne']
      have hz0 : (20000 : ℝ) ≤ rayZIntLb M (Real.exp (10 * (M : ℝ))) := by
        unfold rayZIntLb rayZ0; rw [hlogeq]; linarith [exp_ten_ge_20001]
      have hrt : (140 : ℝ) ≤ Real.sqrt (rayZIntLb M (Real.exp (10 * (M : ℝ)))) := by
        rw [Real.le_sqrt' (by norm_num)]; linarith [show (140 : ℝ) ^ 2 ≤ 20000 by norm_num]
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      rw [hlogeq, div_lt_iff₀ (by positivity)]
      nlinarith
    exact lt_of_le_of_lt hmono0 hval0
  have hf1_lt1 : (3 * (Real.log X₁ / (M : ℝ)) + 5) /
      (8 * Real.pi * Real.sqrt (rayZIntLb M X₁)) < 1 := lt_trans hf1_lt_005 (by norm_num)
  -- `f2`
  have hf2_nn : 0 ≤ (2 : ℝ) / rayZIntLb M X₂ := by positivity
  have hf2_anti : (2 : ℝ) / rayZIntLb M X₂ ≤ (2 : ℝ) / rayZIntLb M X₁ :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hz₁₂
  have hf2_lt1 : (2 : ℝ) / rayZIntLb M X₁ < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  -- `f3`
  have hf3_nn : 0 ≤ (8 * Real.log X₂) / rayZIntLb M X₂ := by
    have hlog₂_nn : 0 ≤ Real.log X₂ := by linarith
    positivity
  have hf3_anti : (8 * Real.log X₂) / rayZIntLb M X₂ ≤ (8 * Real.log X₁) / rayZIntLb M X₁ := by
    have heq : ∀ X : ℝ, (8 * Real.log X) / rayZIntLb M X =
        (8 * (M : ℝ)) * ((Real.log X / (M : ℝ)) / (Real.exp (Real.log X / (M : ℝ)) - 1)) := by
      intro X; unfold rayZIntLb rayZ0; field_simp [hM_pos.ne']
    rw [heq X₁, heq X₂]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact antitoneOn_id_div_exp_sub_one (by linarith : 0 < Real.log X₁ / (M : ℝ))
      (by linarith : 0 < Real.log X₂ / (M : ℝ)) ht₁₂
  have hf3_lt1 : (8 * Real.log X₁) / rayZIntLb M X₁ < 1 := by
    have hratio : (8 * Real.log X₁) / rayZIntLb M X₁ ≤
        (8 * (M : ℝ) * 10) / (Real.exp 10 - 1) := by
      have h1 := antitoneOn_id_div_exp_sub_one (show (0 : ℝ) < 10 by norm_num)
        (show 0 < Real.log X₁ / (M : ℝ) by linarith) ht₁
      have hleft : (8 * Real.log X₁) / rayZIntLb M X₁ =
          (8 * (M : ℝ)) * ((Real.log X₁ / (M : ℝ)) / (Real.exp (Real.log X₁ / (M : ℝ)) - 1)) := by
        unfold rayZIntLb rayZ0; field_simp [hM_pos.ne']
      rw [hleft]
      calc (8 * (M : ℝ)) * ((Real.log X₁ / (M : ℝ)) / (Real.exp (Real.log X₁ / (M : ℝ)) - 1))
          ≤ (8 * (M : ℝ)) * (10 / (Real.exp 10 - 1)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (8 * (M : ℝ) * 10) / (Real.exp 10 - 1) := by ring
    have he10_20k : (20001 : ℝ) ≤ Real.exp 10 := exp_ten_ge_20001
    have hnum_lt : 8 * (M : ℝ) * 10 < Real.exp 10 - 1 := by nlinarith
    exact lt_of_le_of_lt hratio ((div_lt_one (by linarith)).mpr hnum_lt)
  -- `f4`
  have hf4_nn : 0 ≤ (1 : ℝ) / (rayZIntLb M X₂ - 1) := by
    have : 0 < rayZIntLb M X₂ - 1 := by linarith
    positivity
  have hf4_anti : (1 : ℝ) / (rayZIntLb M X₂ - 1) ≤ (1 : ℝ) / (rayZIntLb M X₁ - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hf4_lt1 : (1 : ℝ) / (rayZIntLb M X₁ - 1) < 1 :=
    (div_lt_one (by linarith)).mpr (by linarith)
  exact ⟨hf1_nn, hf1_anti, hf1_lt1, hf2_nn, hf2_anti, hf2_lt1,
    hf3_nn, hf3_anti, hf3_lt1, hf4_nn, hf4_anti, hf4_lt1⟩

private lemma four_factor_delta_mono {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ℝ}
    (ha0 : 0 ≤ a₁) (ha : a₁ ≤ a₂) (ha1 : a₂ < 1)
    (hb0 : 0 ≤ b₁) (hb : b₁ ≤ b₂) (hb1 : b₂ < 1)
    (hc0 : 0 ≤ c₁) (hc : c₁ ≤ c₂) (hc1 : c₂ < 1)
    (hd0 : 0 ≤ d₁) (hd : d₁ ≤ d₂) (hd1 : d₂ < 1) :
    max (1 - (1 - a₁) * (1 - b₁) * (1 - c₁) * (1 - d₁))
        ((1 + a₁) * (1 + b₁) * (1 + c₁) * (1 + d₁) - 1) ≤
    max (1 - (1 - a₂) * (1 - b₂) * (1 - c₂) * (1 - d₂))
        ((1 + a₂) * (1 + b₂) * (1 + c₂) * (1 + d₂) - 1) := by
  have h1a : 0 ≤ 1 - a₂ := by linarith
  have h1b : 0 ≤ 1 - b₂ := by linarith
  have h1c : 0 ≤ 1 - c₂ := by linarith
  have h1d : 0 ≤ 1 - d₂ := by linarith
  have h1a' : 0 ≤ 1 - a₁ := by linarith
  have h1b' : 0 ≤ 1 - b₁ := by linarith
  have h1c' : 0 ≤ 1 - c₁ := by linarith
  have h1d' : 0 ≤ 1 - d₁ := by linarith
  have hd_lo : 1 - (1 - a₁) * (1 - b₁) * (1 - c₁) * (1 - d₁) ≤
      1 - (1 - a₂) * (1 - b₂) * (1 - c₂) * (1 - d₂) := by
    have h12 : (1 - a₂) * (1 - b₂) ≤ (1 - a₁) * (1 - b₁) :=
      mul_le_mul (by linarith) (by linarith) h1b h1a'
    have h123 : (1 - a₂) * (1 - b₂) * (1 - c₂) ≤ (1 - a₁) * (1 - b₁) * (1 - c₁) :=
      mul_le_mul h12 (by linarith) h1c (mul_nonneg h1a' h1b')
    have h1234 : (1 - a₂) * (1 - b₂) * (1 - c₂) * (1 - d₂) ≤
        (1 - a₁) * (1 - b₁) * (1 - c₁) * (1 - d₁) :=
      mul_le_mul h123 (by linarith) h1d (mul_nonneg (mul_nonneg h1a' h1b') h1c')
    linarith
  have hd_hi : (1 + a₁) * (1 + b₁) * (1 + c₁) * (1 + d₁) - 1 ≤
      (1 + a₂) * (1 + b₂) * (1 + c₂) * (1 + d₂) - 1 := by
    have h12 : (1 + a₁) * (1 + b₁) ≤ (1 + a₂) * (1 + b₂) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h123 : (1 + a₁) * (1 + b₁) * (1 + c₁) ≤ (1 + a₂) * (1 + b₂) * (1 + c₂) :=
      mul_le_mul h12 (by linarith) (by linarith) (mul_nonneg (by linarith) (by linarith))
    have h1234 : (1 + a₁) * (1 + b₁) * (1 + c₁) * (1 + d₁) ≤
        (1 + a₂) * (1 + b₂) * (1 + c₂) * (1 + d₂) :=
      mul_le_mul h123 (by linarith) (by linarith)
        (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
    linarith
  exact max_le_max hd_lo hd_hi

theorem rayDeltaV_antitone {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : 10 * (M : ℝ) ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayDeltaV M X₂ ≤ rayDeltaV M X₁ := by
  obtain ⟨hf1_nn, hf1_anti, hf1_lt1, hf2_nn, hf2_anti, hf2_lt1,
      hf3_nn, hf3_anti, hf3_lt1, hf4_nn, hf4_anti, hf4_lt1⟩ :=
    rayDeltaV_parts_antitone hM hM_le hX₁_pos hlog₁ hX₁₂
  exact four_factor_delta_mono hf1_nn hf1_anti hf1_lt1 hf2_nn hf2_anti hf2_lt1
    hf3_nn hf3_anti hf3_lt1 hf4_nn hf4_anti hf4_lt1

theorem rayDeltaV_lt_one {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X : ℝ} (hX_pos : 0 < X) (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    rayDeltaV M X < 1 := by
  obtain ⟨hf1_nn, _, hf1_lt1, hf2_nn, _, hf2_lt1,
      hf3_nn, _, hf3_lt1, hf4_nn, _, hf4_lt1⟩ :=
    rayDeltaV_parts_antitone hM hM_le hX_pos hlog le_rfl
  set a := (3 * (Real.log X / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M X))
  set b := (2 : ℝ) / rayZIntLb M X
  set c := (8 * Real.log X) / rayZIntLb M X
  set d := (1 : ℝ) / (rayZIntLb M X - 1)
  have hd_lo : 1 - (1 - a) * (1 - b) * (1 - c) * (1 - d) < 1 := by
    have hpos : 0 < (1 - a) * (1 - b) * (1 - c) * (1 - d) :=
      mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)
    linarith
  have hd_hi : (1 + a) * (1 + b) * (1 + c) * (1 + d) - 1 < 1 := by
    have hz : (20000 : ℝ) ≤ rayZIntLb M X := rayZIntLb_ge_20000 hM hlog
    have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hM_le_r : (M : ℝ) ≤ 16 := by exact_mod_cast hM_le
    have ha_ub : a < (0.05 : ℝ) := by
      have hX0_log : 10 * (M : ℝ) ≤ Real.log (Real.exp (10 * (M : ℝ))) := by rw [Real.log_exp]
      have hanti := (rayDeltaV_parts_antitone hM hM_le (Real.exp_pos _) hX0_log
        (show Real.exp (10 * (M : ℝ)) ≤ X by rw [← Real.exp_log hX_pos]; exact Real.exp_le_exp.mpr hlog)).2.1
      have hlogeq : Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ) = 10 := by
        rw [Real.log_exp, mul_div_cancel_right₀ _ hM_pos.ne']
      have hz0 : (20000 : ℝ) ≤ rayZIntLb M (Real.exp (10 * (M : ℝ))) := by
        unfold rayZIntLb rayZ0; rw [hlogeq]; linarith [exp_ten_ge_20001]
      have hrt : (140 : ℝ) ≤ Real.sqrt (rayZIntLb M (Real.exp (10 * (M : ℝ)))) := by
        rw [Real.le_sqrt' (by norm_num)]; linarith [show (140 : ℝ) ^ 2 ≤ 20000 by norm_num]
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hval0 : (3 * (Real.log (Real.exp (10 * (M : ℝ))) / (M : ℝ)) + 5) /
          (8 * Real.pi * Real.sqrt (rayZIntLb M (Real.exp (10 * (M : ℝ))))) < (0.05 : ℝ) := by
        rw [hlogeq, div_lt_iff₀ (by positivity)]
        nlinarith
      exact lt_of_le_of_lt hanti hval0
    have hb_ub : b < (0.01 : ℝ) := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    have hd_ub : d < (0.01 : ℝ) := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    have hc_ub : c < (0.1 : ℝ) := by
      have h10 : 10 ≤ Real.log X / (M : ℝ) := (le_div_iff₀ hM_pos).mpr hlog
      have h1 := antitoneOn_id_div_exp_sub_one (show (0 : ℝ) < 10 by norm_num)
        (show 0 < Real.log X / (M : ℝ) by linarith) h10
      have hleft : c = (8 * (M : ℝ)) * ((Real.log X / (M : ℝ)) / (Real.exp (Real.log X / (M : ℝ)) - 1)) := by
        dsimp only [c]; unfold rayZIntLb rayZ0; field_simp [hM_pos.ne']
      have he10_20k : (20001 : ℝ) ≤ Real.exp 10 := exp_ten_ge_20001
      rw [hleft]
      have hstep : (8 * (M : ℝ)) * (10 / (Real.exp 10 - 1)) < 0.1 := by
        have : (8 * (M : ℝ)) * (10 / (Real.exp 10 - 1)) = (80 * (M : ℝ)) / (Real.exp 10 - 1) := by ring
        rw [this, div_lt_iff₀ (by linarith)]
        nlinarith
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 (by positivity)) hstep
    have h12 : (1 + a) * (1 + b) < 1.07 := by nlinarith
    have h123 : (1 + a) * (1 + b) * (1 + c) < 1.2 := by nlinarith
    have h1234 : (1 + a) * (1 + b) * (1 + c) * (1 + d) < 1.3 := by nlinarith
    linarith
  exact max_lt hd_lo hd_hi

lemma rayDeltaV_nonneg {M : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16)
    {X : ℝ} (hX_pos : 0 < X) (hlog : 10 * (M : ℝ) ≤ Real.log X) :
    0 ≤ rayDeltaV M X := by
  obtain ⟨hf1_nn, _, _, hf2_nn, _, _, hf3_nn, _, _, hf4_nn, _, _⟩ :=
    rayDeltaV_parts_antitone hM hM_le hX_pos hlog le_rfl
  set a := (3 * (Real.log X / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M X))
  set b := (2 : ℝ) / rayZIntLb M X
  set c := (8 * Real.log X) / rayZIntLb M X
  set d := (1 : ℝ) / (rayZIntLb M X - 1)
  have h1 : 1 ≤ (1 + a) * (1 + b) := by nlinarith
  have h2 : 1 ≤ (1 + a) * (1 + b) * (1 + c) := by nlinarith
  have h3 : 1 ≤ (1 + a) * (1 + b) * (1 + c) * (1 + d) := by nlinarith
  exact le_trans (by linarith) (le_max_right _ _)

/-- Upper bound `External.deltaV_bs K (rayZ M N) ≤ rayDeltaV M N` whenever `K ≤ N`, `M ≤ 16`,
and `10 * M ≤ log N`. -/
theorem deltaV_bs_le_rayDeltaV {M K N : ℕ} (hM : 1 ≤ M) (hM_le : M ≤ 16) (hK : 1 ≤ K)
    (hKN : K ≤ N) (hlog : 10 * (M : ℝ) ≤ Real.log (N : ℝ)) :
    External.deltaV_bs K (rayZ M N : ℝ) ≤ rayDeltaV M (N : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hN_pos_nat : 0 < N := lt_of_lt_of_le hK hKN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hz_ge : rayZIntLb M (N : ℝ) ≤ (rayZ M N : ℝ) := by
    have hz_eq : rayZ0 M (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := rayZ0_eq_rpow hN_pos
    unfold rayZIntLb rayZ
    rw [hz_eq]
    have := Nat.sub_one_lt_floor ((N : ℝ) ^ ((1 : ℝ) / (M : ℝ)))
    linarith
  have hz_le : (rayZ M N : ℝ) ≤ rayZ0 M (N : ℝ) := by
    rw [rayZ0_eq_rpow hN_pos]
    unfold rayZ
    exact Nat.floor_le (by positivity)
  have hzlb_20k : (20000 : ℝ) ≤ rayZIntLb M (N : ℝ) := rayZIntLb_ge_20000 hM hlog
  have hz_pos : 0 < (rayZ M N : ℝ) := by linarith
  have h1z : (1 : ℝ) ≤ (rayZ M N : ℝ) := by linarith
  have hlogz_le : Real.log (rayZ M N : ℝ) ≤ Real.log (N : ℝ) / (M : ℝ) := by
    calc Real.log (rayZ M N : ℝ) ≤ Real.log (rayZ0 M (N : ℝ)) :=
          Real.log_le_log hz_pos hz_le
      _ = Real.log (N : ℝ) / (M : ℝ) := Real.log_exp _
  obtain ⟨_, _, hf1_lt1, _, _, hf2_lt1, _, _, hf3_lt1, _, _, hf4_lt1⟩ :=
    rayDeltaV_parts_antitone hM hM_le hN_pos hlog le_rfl
  set a₁ := (3 * Real.log (rayZ M N : ℝ) + 5) / (8 * Real.pi * Real.sqrt (rayZ M N : ℝ))
  set a₂ := (3 * (Real.log (N : ℝ) / (M : ℝ)) + 5) / (8 * Real.pi * Real.sqrt (rayZIntLb M (N : ℝ)))
  set b₁ := (2 : ℝ) / (rayZ M N : ℝ)
  set b₂ := (2 : ℝ) / rayZIntLb M (N : ℝ)
  set c₁ := (8 * Real.log (K : ℝ)) / (rayZ M N : ℝ)
  set c₂ := (8 * Real.log (N : ℝ)) / rayZIntLb M (N : ℝ)
  set d₁ := (1 : ℝ) / ((rayZ M N : ℝ) - 1)
  set d₂ := (1 : ℝ) / (rayZIntLb M (N : ℝ) - 1)
  have ha_nn : 0 ≤ a₁ := by
    have := Real.log_nonneg h1z; have := Real.pi_pos; positivity
  have hb_nn : 0 ≤ b₁ := by positivity
  have hc_nn : 0 ≤ c₁ := by
    have h1K : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have := Real.log_nonneg h1K; positivity
  have hd_nn : 0 ≤ d₁ := by
    have : 0 < (rayZ M N : ℝ) - 1 := by linarith
    positivity
  have ha_le : a₁ ≤ a₂ := by
    have hnum_le : 3 * Real.log (rayZ M N : ℝ) + 5 ≤ 3 * (Real.log (N : ℝ) / (M : ℝ)) + 5 := by linarith
    have hnum_nn : 0 ≤ 3 * Real.log (rayZ M N : ℝ) + 5 := by
      have := Real.log_nonneg h1z; linarith
    have hden_pos : 0 < 8 * Real.pi * Real.sqrt (rayZIntLb M (N : ℝ)) := by
      have := Real.pi_pos; positivity
    have hden_le : 8 * Real.pi * Real.sqrt (rayZIntLb M (N : ℝ)) ≤
        8 * Real.pi * Real.sqrt (rayZ M N : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hz_ge) (by positivity)
    exact (div_le_div_of_nonneg_left hnum_nn hden_pos hden_le).trans
      (div_le_div_of_nonneg_right hnum_le hden_pos.le)
  have hb_le : b₁ ≤ b₂ := div_le_div_of_nonneg_left (by norm_num) (by linarith) hz_ge
  have hc_le : c₁ ≤ c₂ := by
    have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have h1K : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hlogK_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg h1K
    have hlogKN : Real.log (K : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hK_pos (by exact_mod_cast hKN)
    exact (div_le_div_of_nonneg_left (by positivity) (by linarith) hz_ge).trans
      (div_le_div_of_nonneg_right (by linarith) (by linarith))
  have hd_le : d₁ ≤ d₂ := one_div_le_one_div_of_le (by linarith) (by linarith)
  exact four_factor_delta_mono ha_nn ha_le hf1_lt1 hb_nn hb_le hf2_lt1
    hc_nn hc_le hf3_lt1 hd_nn hd_le hf4_lt1

/-- `cPi` is antitone on `(1, ∞)`. -/
theorem cPi_antitone (consts : External.CertifiedConstants) :
    AntitoneOn (External.cPi consts) (Set.Ioi 1) := by
  intro X₁ hX₁ X₂ hX₂ hX₁₂
  have hX₁_gt1 : 1 < X₁ := hX₁
  have hlog₁ : 0 < Real.log X₁ := Real.log_pos hX₁_gt1
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log (by linarith) hX₁₂
  have hsq₁ : 0 < Real.sqrt X₁ := Real.sqrt_pos.mpr (by linarith)
  have hsq₁₂ : Real.sqrt X₁ ≤ Real.sqrt X₂ := Real.sqrt_le_sqrt hX₁₂
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold External.cPi
  have t1 : (6 + 1 / Real.pi) / (4 * Real.log X₂) ≤ (6 + 1 / Real.pi) / (4 * Real.log X₁) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have t2 : 6 / Real.log X₂ ^ 2 ≤ 6 / Real.log X₁ ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hlog₁)
      (pow_le_pow_left₀ hlog₁.le hlog₁₂ 2)
  have t3 : consts.li2 / (Real.sqrt X₂ * Real.log X₂) ≤
      consts.li2 / (Real.sqrt X₁ * Real.log X₁) :=
    div_le_div_of_nonneg_left consts.li2_pos.le (mul_pos hsq₁ hlog₁)
      (mul_le_mul hsq₁₂ hlog₁₂ hlog₁.le (Real.sqrt_nonneg _))
  linarith

/-- Pointwise AP remainder coefficient `c_pt(X)` (`regime_asymptotic.py:132`). -/
noncomputable def rayCPt (consts : External.CertifiedConstants) (X : ℝ) : ℝ :=
  External.cPi consts X + 1 / (16 * Real.pi) +
    (1.3841 : ℝ) / (Real.sqrt X * Real.log (Real.log X))

theorem rayCPt_nonneg (consts : External.CertifiedConstants) {X : ℝ}
    (hX_pos : 0 < X) (hlog : Real.exp 1 < Real.log X) :
    0 ≤ rayCPt consts X := by
  have hX_gt1 : 1 < X := one_lt_of_pos_log_pos hX_pos (lt_trans (Real.exp_pos 1) hlog)
  have hlogpos : 0 < Real.log X := Real.log_pos hX_gt1
  have hlog_gt1 : 1 < Real.log X := lt_trans (by linarith [Real.exp_one_gt_d9]) hlog
  have hllpos : 0 < Real.log (Real.log X) := Real.log_pos hlog_gt1
  have hcpi_pos : 0 ≤ External.cPi consts X := by
    unfold External.cPi
    have := Real.pi_pos
    have := consts.li2_pos
    positivity
  unfold rayCPt
  have := Real.pi_pos
  positivity

theorem rayCPt_antitone (consts : External.CertifiedConstants) {X₁ X₂ : ℝ}
    (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 < Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayCPt consts X₂ ≤ rayCPt consts X₁ := by
  have hX₁_gt1 : 1 < X₁ := one_lt_of_pos_log_pos hX₁_pos (lt_trans (Real.exp_pos 1) hlog₁)
  have hX₂_gt1 : 1 < X₂ := lt_of_lt_of_le hX₁_gt1 hX₁₂
  have hcpi := cPi_antitone consts hX₁_gt1 hX₂_gt1 hX₁₂
  have hlog₁_pos : 0 < Real.log X₁ := Real.log_pos hX₁_gt1
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log (by linarith) hX₁₂
  have hlog₁_gt1 : 1 < Real.log X₁ := lt_trans (by linarith [Real.exp_one_gt_d9]) hlog₁
  have hll₁ : 0 < Real.log (Real.log X₁) := Real.log_pos hlog₁_gt1
  have hll₁₂ : Real.log (Real.log X₁) ≤ Real.log (Real.log X₂) :=
    Real.log_le_log hlog₁_pos hlog₁₂
  have hden : Real.sqrt X₁ * Real.log (Real.log X₁) ≤
      Real.sqrt X₂ * Real.log (Real.log X₂) :=
    mul_le_mul (Real.sqrt_le_sqrt hX₁₂) hll₁₂ hll₁.le (Real.sqrt_nonneg _)
  have htail : (1.3841 : ℝ) / (Real.sqrt X₂ * Real.log (Real.log X₂)) ≤
      (1.3841 : ℝ) / (Real.sqrt X₁ * Real.log (Real.log X₁)) :=
    div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (Real.sqrt_pos.mpr (by linarith)) hll₁) hden
  unfold rayCPt
  linarith

/-- Odd squarefree density factor `odd_sf(X) = 4/π² + exp (-0.1 * log X)` (`regime_asymptotic.py:133`). -/
noncomputable def rayOddSf (X : ℝ) : ℝ :=
  4 / Real.pi ^ 2 + 1 / Real.exp ((0.1 : ℝ) * Real.log X)

theorem rayOddSf_nonneg (X : ℝ) : 0 ≤ rayOddSf X := by
  unfold rayOddSf
  positivity

theorem rayOddSf_antitone {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayOddSf X₂ ≤ rayOddSf X₁ := by
  unfold rayOddSf
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁ hX₁₂
  have hexp : Real.exp ((0.1 : ℝ) * Real.log X₁) ≤ Real.exp ((0.1 : ℝ) * Real.log X₂) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith [one_div_le_one_div_of_le (Real.exp_pos _) hexp]

/-- Combined squarefree AP remainder factor `c4g(X) = odd_sf(X) * c_pt(X)`. -/
noncomputable def rayC4g (consts : External.CertifiedConstants) (X : ℝ) : ℝ :=
  rayOddSf X * rayCPt consts X

theorem rayC4g_nonneg (consts : External.CertifiedConstants) {X : ℝ}
    (hX_pos : 0 < X) (hlog : Real.exp 1 < Real.log X) :
    0 ≤ rayC4g consts X :=
  mul_nonneg (rayOddSf_nonneg X) (rayCPt_nonneg consts hX_pos hlog)

theorem rayC4g_antitone (consts : External.CertifiedConstants) {X₁ X₂ : ℝ}
    (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 < Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayC4g consts X₂ ≤ rayC4g consts X₁ := by
  have hX₂_pos : 0 < X₂ := lt_of_lt_of_le hX₁_pos hX₁₂
  have hlog₂ : Real.exp 1 < Real.log X₂ :=
    lt_of_lt_of_le hlog₁ (Real.log_le_log hX₁_pos hX₁₂)
  exact mul_le_mul (rayOddSf_antitone hX₁_pos hX₁₂) (rayCPt_antitone consts hX₁_pos hlog₁ hX₁₂)
    (rayCPt_nonneg consts hX₂_pos hlog₂) (rayOddSf_nonneg X₁)

/-- Exponent savings `α_a(X)` for the lower sieve (`regime_asymptotic.py:65-68`). -/
noncomputable def rayAlphaA (b_a logQ : ℝ) (X : ℝ) : ℝ :=
  (logQ + (b_a + 1) * Real.log (Real.log X)) / Real.log X

/-- Exponent savings `α_q(X)` for the upper sieve (`regime_asymptotic.py:104`). -/
noncomputable def rayAlphaQ (b_q : ℝ) (X : ℝ) : ℝ :=
  b_q * Real.log (Real.log X) / Real.log X

/-- Effective Buchstab parameter `s_a(X) = M * (1/2 - α_a(X))` (`regime_asymptotic.py:88`). -/
noncomputable def raySa (M : ℕ) (b_a logQ : ℝ) (X : ℝ) : ℝ :=
  (M : ℝ) * (1 / 2 - rayAlphaA b_a logQ X)

/-- Linear sieve normalized lower-bound coefficient `lb_a(X)` (`regime_asymptotic.py:91`). -/
noncomputable def rayLbA (M : ℕ) (b_a logQ ε C2 : ℝ) (X : ℝ) : ℝ :=
  buchstabf cBuchstab (raySa M b_a logQ X) -
    ε * C2 * Real.exp 2 * h_bjs (raySa M b_a logQ X)

theorem rayAlphaA_antitone {b_a logQ : ℝ} (hba : 0 ≤ b_a + 1) (hlogQ : 0 ≤ logQ)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayAlphaA b_a logQ X₂ ≤ rayAlphaA b_a logQ X₁ := by
  have hlog₁_pos : 0 < Real.log X₁ := lt_of_lt_of_le (Real.exp_pos 1) hlog₁
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  have h1 : logQ / Real.log X₂ ≤ logQ / Real.log X₁ :=
    div_le_div_of_nonneg_left hlogQ hlog₁_pos hlog₁₂
  have h2 : (b_a + 1) * (Real.log (Real.log X₂) / Real.log X₂) ≤
      (b_a + 1) * (Real.log (Real.log X₁) / Real.log X₁) :=
    mul_le_mul_of_nonneg_left
      (antitoneOn_log_div_id hlog₁ (hlog₁.trans hlog₁₂) hlog₁₂) hba
  unfold rayAlphaA
  have heq : ∀ X : ℝ, (logQ + (b_a + 1) * Real.log (Real.log X)) / Real.log X =
      logQ / Real.log X + (b_a + 1) * (Real.log (Real.log X) / Real.log X) := fun _ => by ring
  rw [heq X₁, heq X₂]
  linarith

theorem rayAlphaQ_antitone {b_q : ℝ} (hbq : 0 ≤ b_q) {X₁ X₂ : ℝ}
    (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayAlphaQ b_q X₂ ≤ rayAlphaQ b_q X₁ := by
  have hlog₁₂ : Real.log X₁ ≤ Real.log X₂ := Real.log_le_log hX₁_pos hX₁₂
  unfold rayAlphaQ
  have heq : ∀ X : ℝ, b_q * Real.log (Real.log X) / Real.log X =
      b_q * (Real.log (Real.log X) / Real.log X) := fun _ => by ring
  rw [heq X₁, heq X₂]
  exact mul_le_mul_of_nonneg_left
    (antitoneOn_log_div_id hlog₁ (hlog₁.trans hlog₁₂) hlog₁₂) hbq

theorem raySa_mono (M : ℕ) {b_a logQ : ℝ} (hba : 0 ≤ b_a + 1) (hlogQ : 0 ≤ logQ)
    {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁) (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hX₁₂ : X₁ ≤ X₂) :
    raySa M b_a logQ X₁ ≤ raySa M b_a logQ X₂ := by
  unfold raySa
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg M)
  linarith [rayAlphaA_antitone hba hlogQ hX₁_pos hlog₁ hX₁₂]

theorem rayLbA_mono (M : ℕ) {b_a logQ ε C2 : ℝ} (hba : 0 ≤ b_a + 1) (hlogQ : 0 ≤ logQ)
    (hε : 0 ≤ ε) (hC2 : 0 ≤ C2) {X₁ X₂ : ℝ} (hX₁_pos : 0 < X₁)
    (hlog₁ : Real.exp 1 ≤ Real.log X₁) (hsa₁ : 2 ≤ raySa M b_a logQ X₁) (hX₁₂ : X₁ ≤ X₂) :
    rayLbA M b_a logQ ε C2 X₁ ≤ rayLbA M b_a logQ ε C2 X₂ := by
  have hsa₁₂ : raySa M b_a logQ X₁ ≤ raySa M b_a logQ X₂ :=
    raySa_mono M hba hlogQ hX₁_pos hlog₁ hX₁₂
  have hsa₂ : 2 ≤ raySa M b_a logQ X₂ := hsa₁.trans hsa₁₂
  have hf_le : buchstabf cBuchstab (raySa M b_a logQ X₁) ≤
      buchstabf cBuchstab (raySa M b_a logQ X₂) :=
    buchstabf_monotoneOn cBuchstab_pos
      (show (0 : ℝ) < raySa M b_a logQ X₁ by linarith)
      (show (0 : ℝ) < raySa M b_a logQ X₂ by linarith) hsa₁₂
  have hh_le : h_bjs (raySa M b_a logQ X₂) ≤ h_bjs (raySa M b_a logQ X₁) :=
    h_bjs_antitone hsa₁₂
  have hcoef : 0 ≤ ε * C2 * Real.exp 2 := by positivity
  unfold rayLbA
  nlinarith

end RayMonotonicity

end

end BuchstabSwitching
