import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Elementary Sieve Inequalities, Shifted-Prime Product Splitting, and Two-Variable Mertens

Formalizes:
1. Elementary analytic inequalities used in the explicit linear-sieve regime (`all-even-1p4-under-grh.md` §0.4):
   - `neg_log_one_sub_le`: `-log (1 - x) ≤ x + x^2 / (2 * (1 - x))` for `0 ≤ x < 1`
   - `neg_log_one_sub_ratio_mono`: monotonicity of `(-log (1 - x) - x) / x^2` on `(0, 1)`
   - `log_sub_one_div_strictMonoOn`: strict monotonicity of `log (t - 1) / t` on `[2, 4]`
   - `offsetLogIntegral_lt_div_log_sub_two`: `∫ t in 2..x, 1 / log t < x / (log x - 2)` for `x ≥ exp 5`
2. Shifted-prime Euler-product splitting (`1 - 1/(p-1)` vs twin-prime factor and `1 - 1/p`) and
   monotonicity under omitting divisors `p ∣ N`.
3. Causal running-minimum two-variable Mertens condition (`two_var_mertens_cond_of_excursion`)
   and the large-`u` analytic bound (`eps_large_u_two_var_sound`).
-/

namespace BuchstabSwitching

/-! ## 1. Elementary Analytic Inequalities -/

/-- For `0 ≤ x < 1`, `-Real.log (1 - x) ≤ x + x^2 / (2 * (1 - x))`. -/
theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / (2 * (1 - x)) := by
  rcases eq_or_lt_of_le hx0 with rfl | hx_pos
  · simp
  let f : ℝ → ℝ := fun t => t + t ^ 2 / (2 * (1 - t)) + Real.log (1 - t)
  have hf_hasDeriv : ∀ t ∈ Set.Icc 0 x,
      HasDerivAt f (t ^ 2 / (2 * (1 - t) ^ 2)) t := by
    intro t ht
    have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
    have h2t1 : 2 * (1 - t) ≠ 0 := mul_ne_zero two_ne_zero ht1
    have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h1mt : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
    have hden : HasDerivAt (fun s : ℝ => 2 * (1 - s)) (-2) t := by
      simpa using (hasDerivAt_const t (2 : ℝ)).fun_mul h1mt
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / (2 * (1 - s)))
        ((2 * t ^ (2 - 1) * (2 * (1 - t)) - t ^ 2 * (-2)) / (2 * (1 - t)) ^ 2) t :=
      (hasDerivAt_pow 2 t).fun_div hden h2t1
    have h3 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) ((1 - t)⁻¹ * (-1)) t :=
      (Real.hasDerivAt_log ht1).comp t h1mt
    convert (h1.fun_add h2).fun_add h3 using 1
    field_simp
    ring
  have hf_cont : ContinuousOn f (Set.Icc 0 x) := fun t ht =>
    (hf_hasDeriv t ht).continuousAt.continuousWithinAt
  have hf_diff : DifferentiableOn ℝ f (interior (Set.Icc 0 x)) := fun t ht =>
    (hf_hasDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hf_nonneg : ∀ t ∈ interior (Set.Icc 0 x), 0 ≤ deriv f t := by
    intro t ht
    rw [(hf_hasDeriv t (interior_subset ht)).deriv]
    positivity
  have hmono : MonotoneOn f (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hf_cont hf_diff hf_nonneg
  have hle : f 0 ≤ f x :=
    hmono ⟨le_rfl, hx_pos.le⟩ ⟨hx_pos.le, le_rfl⟩ hx_pos.le
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hle
  dsimp only [f] at hle
  linarith

/-- On `(0, 1)`, `x ↦ (-Real.log (1 - x) - x) / x^2` is monotone increasing. -/
theorem neg_log_one_sub_ratio_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    (-Real.log (1 - x) - x) / x ^ 2 ≤ (-Real.log (1 - y) - y) / y ^ 2 := by
  let g : ℝ → ℝ := fun t => (-Real.log (1 - t) - t) / t ^ 2
  have hg_hasDeriv : ∀ t ∈ Set.Ioo 0 1,
      HasDerivAt g (2 * (t + t ^ 2 / (2 * (1 - t)) + Real.log (1 - t)) / t ^ 3) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    have h1mt : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (1 - s)) ((1 - t)⁻¹ * (-1)) t :=
      (Real.hasDerivAt_log ht1).comp t h1mt
    have hnum : HasDerivAt (fun s : ℝ => -Real.log (1 - s) - s) (-((1 - t)⁻¹ * (-1)) - 1) t :=
      hlog.fun_neg.fun_sub (hasDerivAt_id t)
    have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
    convert hnum.fun_div hden ht2 using 1
    field_simp
    ring
  have hg_cont : ContinuousOn g (Set.Ioo 0 1) := fun t ht =>
    (hg_hasDeriv t ht).continuousAt.continuousWithinAt
  have hg_diff : DifferentiableOn ℝ g (interior (Set.Ioo 0 1)) := fun t ht =>
    (hg_hasDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hg_nonneg : ∀ t ∈ interior (Set.Ioo 0 1), 0 ≤ deriv g t := by
    intro t ht
    have ht' : t ∈ Set.Ioo 0 1 := interior_subset ht
    rw [(hg_hasDeriv t ht').deriv]
    have hle := neg_log_one_sub_le ht'.1.le ht'.2
    have hnum_nonneg : 0 ≤ t + t ^ 2 / (2 * (1 - t)) + Real.log (1 - t) := by linarith
    exact div_nonneg (mul_nonneg (by norm_num) hnum_nonneg) (pow_nonneg ht'.1.le 3)
  have hmono : MonotoneOn g (Set.Ioo 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ioo 0 1) hg_cont hg_diff hg_nonneg
  exact hmono ⟨hx, lt_of_le_of_lt hxy hy⟩ ⟨lt_of_lt_of_le hx hxy, hy⟩ hxy

/-- `t ↦ Real.log (t - 1) / t` is strictly increasing on `[2, 4]`. -/
theorem log_sub_one_div_strictMonoOn :
    StrictMonoOn (fun t : ℝ => Real.log (t - 1) / t) (Set.Icc 2 4) := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hexp_ge : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    exact hsum
  have hlog3_lt : Real.log 3 < 4 / 3 := by
    have hexp4 : (27 : ℝ) < Real.exp 4 := by
      have h1 : (27 : ℝ) < (5 / 2 : ℝ) ^ 4 := by norm_num
      have h2 : (5 / 2 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp_ge 4
      have h3 : (Real.exp 1) ^ 4 = Real.exp 4 := by
        rw [← Real.exp_natCast_mul]
        norm_num
      linarith
    have hexp43 : (3 : ℝ) < Real.exp (4 / 3) := by
      by_contra hle
      push Not at hle
      have hpow : (Real.exp (4 / 3)) ^ 3 ≤ (3 : ℝ) ^ 3 :=
        pow_le_pow_left₀ (Real.exp_pos _).le hle 3
      have h4 : (Real.exp (4 / 3)) ^ 3 = Real.exp 4 := by
        rw [← Real.exp_natCast_mul]
        norm_num
      rw [h4] at hpow
      norm_num at hpow
      linarith
    calc Real.log 3 < Real.log (Real.exp (4 / 3)) := Real.log_lt_log (by norm_num) hexp43
      _ = 4 / 3 := Real.log_exp (4 / 3)
  have hf_hasDeriv : ∀ t ∈ Set.Icc (2 : ℝ) 4,
      HasDerivAt f ((t / (t - 1) - Real.log (t - 1)) / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
    have hsub : HasDerivAt (fun s : ℝ => s - 1) 1 t := by
      simpa using (hasDerivAt_id' t).fun_sub (hasDerivAt_const t (1 : ℝ))
    have hnum : HasDerivAt (fun s : ℝ => Real.log (s - 1)) ((t - 1)⁻¹ * 1) t := by
      simpa [Function.comp_def] using (Real.hasDerivAt_log ht1).comp t hsub
    convert hnum.fun_div (hasDerivAt_id' t) ht0 using 1
    field_simp
  have hf_cont : ContinuousOn f (Set.Icc (2 : ℝ) 4) := fun t ht =>
    (hf_hasDeriv t ht).continuousAt.continuousWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Icc 2 4) hf_cont ?_
  intro t ht
  rw [interior_Icc] at ht
  have ht_icc : t ∈ Set.Icc (2 : ℝ) 4 := ⟨ht.1.le, ht.2.le⟩
  rw [(hf_hasDeriv t ht_icc).deriv]
  have ht1_pos : 0 < t - 1 := by linarith [ht.1]
  have ht1_lt3 : t - 1 < 3 := by linarith [ht.2]
  have hfrac : (4 / 3 : ℝ) < t / (t - 1) := by
    have h1 : t / (t - 1) = 1 + 1 / (t - 1) := by
      field_simp [ht1_pos.ne']
      ring
    have h2 : (1 / 3 : ℝ) < 1 / (t - 1) :=
      one_div_lt_one_div_of_lt ht1_pos ht1_lt3
    linarith
  have hlog_lt : Real.log (t - 1) < Real.log 3 := Real.log_lt_log ht1_pos ht1_lt3
  have hnum_pos : 0 < t / (t - 1) - Real.log (t - 1) := by linarith
  exact div_pos hnum_pos (sq_pos_of_pos (by linarith [ht.1]))

private lemma exp_one_gt_27_div_10 : (27 / 10 : ℝ) < Real.exp 1 := by
  have hsum := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  linarith

private lemma exp_one_lt_three : Real.exp 1 < 3 := by
  have hbd := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by omega : 0 < 4)
  have hsum : (∑ m ∈ Finset.range 4, (1 : ℝ) ^ m / ↑m.factorial) = 8 / 3 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum, abs_of_pos (by norm_num : (0 : ℝ) < 1)] at hbd
  norm_num [Nat.factorial] at hbd
  linarith [le_of_abs_le hbd]

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have hexp_half_lt : Real.exp (1 / 2) < 2 := by
    by_contra hle
    push Not at hle
    have hsq : (2 : ℝ) ^ 2 ≤ (Real.exp (1 / 2)) ^ 2 := pow_le_pow_left₀ (by norm_num) hle 2
    have h1 : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_natCast_mul]
      norm_num
    rw [h1] at hsq
    linarith [exp_one_lt_three]
  calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp (1 / 2)).symm
    _ < Real.log 2 := Real.log_lt_log (Real.exp_pos _) hexp_half_lt

private lemma inv_log_continuousOn_Ioi :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [Set.mem_Ioi.mp ht]
  have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (Set.mem_Ioi.mp ht))
  exact (continuousAt_const.div (Real.continuousAt_log ht0) hlog0).continuousWithinAt

private lemma integral_inv_log_le_const {a b c : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hc_pos : 0 < c) (hc : c ≤ Real.log a) :
    ∫ t in a..b, 1 / Real.log t ≤ (b - a) / c := by
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact Set.mem_Ioi.mpr (by linarith [ht.1])
  have hint1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b :=
    (inv_log_continuousOn_Ioi.mono hsub).intervalIntegrable
  have hint2 : IntervalIntegrable (fun _ : ℝ => 1 / c) MeasureTheory.volume a b :=
    intervalIntegrable_const
  calc ∫ t in a..b, 1 / Real.log t
      ≤ ∫ _ in a..b, (1 / c : ℝ) := by
        refine intervalIntegral.integral_mono_on hab hint1 hint2 ?_
        intro t ht
        have hlog_le : c ≤ Real.log t :=
          hc.trans (Real.log_le_log (by linarith) ht.1)
        exact one_div_le_one_div_of_le hc_pos hlog_le
    _ = (b - a) / c := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

private lemma integral_inv_log_exp_five_lt :
    ∫ t in (2 : ℝ)..(Real.exp 5), 1 / Real.log t < Real.exp 5 / 3 := by
  set e : ℝ := Real.exp 1
  have he_gt : (27 / 10 : ℝ) < e := exp_one_gt_27_div_10
  have he_lt : e < 3 := exp_one_lt_three
  have he_pow : ∀ k : ℕ, Real.exp (k : ℝ) = e ^ k := fun k => by
    have hk : (k : ℝ) = (k : ℝ) * 1 := (mul_one _).symm
    conv_lhs => rw [hk, Real.exp_natCast_mul]
  have hp1 : (2 : ℝ) ≤ e := by linarith
  have hp2 : e ≤ e ^ 2 := by nlinarith
  have hp3 : e ^ 2 ≤ e ^ 3 := by nlinarith
  have hp4 : e ^ 3 ≤ e ^ 4 := by nlinarith
  have hp5 : e ^ 4 ≤ e ^ 5 := by nlinarith
  have hi : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
    intro a b ha hab
    refine (inv_log_continuousOn_Ioi.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact Set.mem_Ioi.mpr (by linarith [ht.1])
  have hsplit : ∫ t in (2 : ℝ)..(e ^ 5), 1 / Real.log t =
      (∫ t in (2 : ℝ)..e, 1 / Real.log t) +
      (∫ t in e..(e ^ 2), 1 / Real.log t) +
      (∫ t in (e ^ 2)..(e ^ 3), 1 / Real.log t) +
      (∫ t in (e ^ 3)..(e ^ 4), 1 / Real.log t) +
      (∫ t in (e ^ 4)..(e ^ 5), 1 / Real.log t) := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals
      (hi 2 e (le_refl 2) hp1) (hi e (e ^ 2) hp1 hp2)
    have h13 := intervalIntegral.integral_add_adjacent_intervals
      (hi 2 (e ^ 2) (le_refl 2) (hp1.trans hp2)) (hi (e ^ 2) (e ^ 3) (hp1.trans hp2) hp3)
    have h14 := intervalIntegral.integral_add_adjacent_intervals
      (hi 2 (e ^ 3) (le_refl 2) (hp1.trans (hp2.trans hp3)))
      (hi (e ^ 3) (e ^ 4) (hp1.trans (hp2.trans hp3)) hp4)
    have h15 := intervalIntegral.integral_add_adjacent_intervals
      (hi 2 (e ^ 4) (le_refl 2) (hp1.trans (hp2.trans (hp3.trans hp4))))
      (hi (e ^ 4) (e ^ 5) (hp1.trans (hp2.trans (hp3.trans hp4))) hp5)
    linarith
  have hb1 : ∫ t in (2 : ℝ)..e, 1 / Real.log t ≤ (e - 2) / (1 / 2) :=
    integral_inv_log_le_const (le_refl 2) hp1 (by norm_num) half_lt_log_two.le
  have hb2 : ∫ t in e..(e ^ 2), 1 / Real.log t ≤ (e ^ 2 - e) / 1 :=
    integral_inv_log_le_const hp1 hp2 (by norm_num) (by simp [e])
  have hb3 : ∫ t in (e ^ 2)..(e ^ 3), 1 / Real.log t ≤ (e ^ 3 - e ^ 2) / 2 :=
    integral_inv_log_le_const (hp1.trans hp2) hp3 (by norm_num)
      (by rw [← he_pow 2, Real.log_exp]; norm_num)
  have hb4 : ∫ t in (e ^ 3)..(e ^ 4), 1 / Real.log t ≤ (e ^ 4 - e ^ 3) / 3 :=
    integral_inv_log_le_const (hp1.trans (hp2.trans hp3)) hp4 (by norm_num)
      (by rw [← he_pow 3, Real.log_exp]; norm_num)
  have hb5 : ∫ t in (e ^ 4)..(e ^ 5), 1 / Real.log t ≤ (e ^ 5 - e ^ 4) / 4 :=
    integral_inv_log_le_const (hp1.trans (hp2.trans (hp3.trans hp4))) hp5 (by norm_num)
      (by rw [← he_pow 4, Real.log_exp]; norm_num)
  have hsum_le : ∫ t in (2 : ℝ)..(e ^ 5), 1 / Real.log t ≤
      (e - 2) / (1 / 2) + (e ^ 2 - e) / 1 + (e ^ 3 - e ^ 2) / 2 +
      (e ^ 4 - e ^ 3) / 3 + (e ^ 5 - e ^ 4) / 4 := by
    linarith
  have hpoly : 0 < (4 - e) + e ^ 2 * (e ^ 3 - e ^ 2 - 2 * e - 6) / 12 := by
    have h4e : 0 < 4 - e := by linarith
    have hfac : e ^ 3 - e ^ 2 - 2 * e - 6 =
        (e - 27 / 10) * (e ^ 2 + (17 / 10) * e + 259 / 100) + 993 / 1000 := by ring
    have hpos1 : 0 < (e - 27 / 10) * (e ^ 2 + (17 / 10) * e + 259 / 100) := by
      refine mul_pos (by linarith) (by positivity)
    have hpos2 : 0 < e ^ 3 - e ^ 2 - 2 * e - 6 := by linarith
    have hpos3 : 0 < e ^ 2 * (e ^ 3 - e ^ 2 - 2 * e - 6) / 12 := by positivity
    linarith
  have hid : e ^ 5 / 3 -
      ((e - 2) / (1 / 2) + (e ^ 2 - e) / 1 + (e ^ 3 - e ^ 2) / 2 +
        (e ^ 4 - e ^ 3) / 3 + (e ^ 5 - e ^ 4) / 4) =
      (4 - e) + e ^ 2 * (e ^ 3 - e ^ 2 - 2 * e - 6) / 12 := by ring
  have h5 : Real.exp 5 = e ^ 5 := by simpa using he_pow 5
  rw [h5]
  linarith

/-- For all `x ≥ Real.exp 5`, `∫ t in 2..x, 1 / Real.log t < x / (Real.log x - 2)`. -/
theorem offsetLogIntegral_lt_div_log_sub_two {x : ℝ} (hx : Real.exp 5 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t < x / (Real.log x - 2) := by
  rcases eq_or_lt_of_le hx with rfl | hlt
  · rw [Real.log_exp]
    norm_num
    simpa [one_div] using integral_inv_log_exp_five_lt
  let G : ℝ → ℝ := fun t => t / (Real.log t - 2) - ∫ s in (2 : ℝ)..t, 1 / Real.log s
  have hexp5_gt2 : (2 : ℝ) < Real.exp 5 := by
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [exp_one_gt_27_div_10]
    have h5 : Real.exp 1 ≤ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hG_hasDeriv : ∀ t ∈ Set.Icc (Real.exp 5) x,
      HasDerivAt G ((Real.log t - 4) / (Real.log t * (Real.log t - 2) ^ 2)) t := by
    intro t ht
    have hlog_ge5 : 5 ≤ Real.log t := by
      calc (5 : ℝ) = Real.log (Real.exp 5) := (Real.log_exp 5).symm
        _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 5) ht.1
    have ht_pos : 0 < t := lt_of_lt_of_le (Real.exp_pos 5) ht.1
    have ht_gt2 : 2 < t := lt_of_lt_of_le hexp5_gt2 ht.1
    have hlog_pos : 0 < Real.log t := by linarith
    have hlog2_ne : Real.log t - 2 ≠ 0 := by linarith
    have hden : HasDerivAt (fun s : ℝ => Real.log s - 2) (t⁻¹ - 0) t :=
      (Real.hasDerivAt_log ht_pos.ne').fun_sub (hasDerivAt_const t (2 : ℝ))
    have hfrac : HasDerivAt (fun s : ℝ => s / (Real.log s - 2))
        (((1 : ℝ) * (Real.log t - 2) - t * (t⁻¹ - 0)) / (Real.log t - 2) ^ 2) t :=
      (hasDerivAt_id t).fun_div hden hlog2_ne
    have hint_sub : Set.uIcc 2 t ⊆ Set.Ioi 1 := by
      rw [Set.uIcc_of_le ht_gt2.le]
      intro s hs
      exact Set.mem_Ioi.mpr (by linarith [hs.1])
    have hint : IntervalIntegrable (fun s : ℝ => 1 / Real.log s) MeasureTheory.volume 2 t :=
      (inv_log_continuousOn_Ioi.mono hint_sub).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => 1 / Real.log s)
        (nhds t) MeasureTheory.volume :=
      inv_log_continuousOn_Ioi.stronglyMeasurableAtFilter isOpen_Ioi t (Set.mem_Ioi.mpr (by linarith))
    have hcont : ContinuousAt (fun s : ℝ => 1 / Real.log s) t :=
      inv_log_continuousOn_Ioi.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))
    have hintDeriv : HasDerivAt (fun u : ℝ => ∫ s in (2 : ℝ)..u, 1 / Real.log s)
        (1 / Real.log t) t :=
      intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
    convert hfrac.fun_sub hintDeriv using 1
    field_simp [ht_pos.ne', hlog_pos.ne', hlog2_ne]
    ring
  have hG_cont : ContinuousOn G (Set.Icc (Real.exp 5) x) := fun t ht =>
    (hG_hasDeriv t ht).continuousAt.continuousWithinAt
  have hG_diff : DifferentiableOn ℝ G (interior (Set.Icc (Real.exp 5) x)) := fun t ht =>
    (hG_hasDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hG_nonneg : ∀ t ∈ interior (Set.Icc (Real.exp 5) x), 0 ≤ deriv G t := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (Real.exp 5) x := interior_subset ht
    rw [(hG_hasDeriv t ht_icc).deriv]
    have hlog_ge5 : 5 ≤ Real.log t := by
      calc (5 : ℝ) = Real.log (Real.exp 5) := (Real.log_exp 5).symm
        _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 5) ht_icc.1
    have hnum : 0 ≤ Real.log t - 4 := by linarith
    have hden : 0 ≤ Real.log t * (Real.log t - 2) ^ 2 := by positivity
    exact div_nonneg hnum hden
  have hmono : MonotoneOn G (Set.Icc (Real.exp 5) x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hG_cont hG_diff hG_nonneg
  have hle : G (Real.exp 5) ≤ G x := hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt.le
  have hG0 : 0 < G (Real.exp 5) := by
    dsimp only [G]
    rw [Real.log_exp]
    have := integral_inv_log_exp_five_lt
    linarith
  have hGx : 0 < G x := lt_of_lt_of_le hG0 hle
  dsimp only [G] at hGx
  linarith

/-! ## 2. Shifted-Prime Density Product Splitting -/

/-- Exact factor identity `(1 - 1/(p - 1))⁻¹ = ((p - 1)^2 / (p * (p - 2))) * (1 - 1/p)⁻¹`
for `p > 2`. -/
theorem inv_one_sub_inv_pred_eq {p : ℝ} (hp : 2 < p) :
    (1 - 1 / (p - 1))⁻¹ = ((p - 1) ^ 2 / (p * (p - 2))) * (1 - 1 / p)⁻¹ := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hp2 : p - 2 ≠ 0 := by linarith
  have h1 : 1 - 1 / (p - 1) = (p - 2) / (p - 1) := by field_simp; ring
  have h2 : 1 - 1 / p = (p - 1) / p := by field_simp
  rw [h1, h2, inv_div, inv_div]
  field_simp

/-- The shifted-prime quadratic tail constant
`c_p(u) = (-Real.log (1 - 1 / u) - 1 / u) / (1 / u) ^ 2`. -/
noncomputable def c_p (u : ℝ) : ℝ :=
  (-Real.log (1 - 1 / u) - 1 / u) / (1 / u) ^ 2

theorem c_p_pos {u : ℝ} (hu : 1 < u) : 0 < c_p u := by
  have hx_pos : 0 < 1 / u := one_div_pos.mpr (by linarith)
  have hx_lt : 1 / u < 1 := by
    rw [one_div_lt (by linarith) zero_lt_one]
    linarith
  have h1mx_pos : 0 < 1 - 1 / u := by linarith
  have hlog : Real.log (1 - 1 / u) < (1 - 1 / u) - 1 :=
    Real.log_lt_sub_one_of_pos h1mx_pos (by linarith)
  have hnum : 0 < -Real.log (1 - 1 / u) - 1 / u := by linarith
  exact div_pos hnum (sq_pos_of_pos hx_pos)

theorem c_p_le {u : ℝ} (hu : 1 < u) : c_p u ≤ u / (2 * (u - 1)) := by
  have hx_pos : 0 < 1 / u := one_div_pos.mpr (by linarith)
  have hx_lt : 1 / u < 1 := by
    rw [one_div_lt (by linarith) zero_lt_one]
    linarith
  have hle := neg_log_one_sub_le hx_pos.le hx_lt
  have hsub : -Real.log (1 - 1 / u) - 1 / u ≤ (1 / u) ^ 2 / (2 * (1 - 1 / u)) := by linarith
  have hdiv : (-Real.log (1 - 1 / u) - 1 / u) / (1 / u) ^ 2 ≤
      ((1 / u) ^ 2 / (2 * (1 - 1 / u))) / (1 / u) ^ 2 :=
    div_le_div_of_nonneg_right hsub (sq_nonneg _)
  have hsimp : ((1 / u) ^ 2 / (2 * (1 - 1 / u))) / (1 / u) ^ 2 = u / (2 * (u - 1)) := by
    have hu0 : u ≠ 0 := by linarith
    have hu1 : u - 1 ≠ 0 := by linarith
    field_simp
  exact hdiv.trans_eq hsimp

/-- Real-threshold version of `prod_inv_one_sub_le_twin_mul_exp`:
for any `S : Finset ℕ` with `∀ p ∈ S, u ≤ (p : ℝ)` (`2 < u`), the product of
`(1 - 1 / (p - 1))⁻¹` over `S` is bounded by the twin-prime product times
`Real.exp (∑ p ∈ S, 1/p + c_p u * ∑ p ∈ S, 1/p^2)`. -/
theorem prod_inv_one_sub_le_twin_mul_exp_real {u : ℝ} (hu : 2 < u) (S : Finset ℕ)
    (hS : ∀ p ∈ S, u ≤ (p : ℝ)) :
    ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      (∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
        Real.exp (∑ p ∈ S, (1 / (p : ℝ)) + c_p u * ∑ p ∈ S, (1 / (p : ℝ) ^ 2)) := by
  have hsplit : ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ =
      (∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
        (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    exact inv_one_sub_inv_pred_eq (lt_of_lt_of_le hu (hS p hp))
  rw [hsplit]
  have htwin_nonneg : 0 ≤ ∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hp2 : (2 : ℝ) < p := lt_of_lt_of_le hu (hS p hp)
    positivity
  refine mul_le_mul_of_nonneg_left ?_ htwin_nonneg
  have hsum_eq : ∑ p ∈ S, (1 / (p : ℝ)) + c_p u * ∑ p ∈ S, (1 / (p : ℝ) ^ 2) =
      ∑ p ∈ S, (1 / (p : ℝ) + c_p u * (1 / (p : ℝ) ^ 2)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum_eq, Real.exp_sum]
  refine Finset.prod_le_prod₀ ?_ ?_
  · intro p hp
    have hp2 : (2 : ℝ) < p := lt_of_lt_of_le hu (hS p hp)
    have h1mp : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 / (p : ℝ) < 1 := by
        rw [one_div_lt (by linarith) zero_lt_one]
        linarith
      linarith
    exact (inv_pos.mpr h1mp).le
  · intro p hp
    have hpu : u ≤ (p : ℝ) := hS p hp
    have hp2 : (2 : ℝ) < p := lt_of_lt_of_le hu hpu
    have h1p_pos : 0 < 1 / (p : ℝ) := one_div_pos.mpr (by linarith)
    have h1u_lt : 1 / u < 1 := by
      rw [one_div_lt (by linarith) zero_lt_one]
      linarith
    have h1p_le_1u : 1 / (p : ℝ) ≤ 1 / u :=
      one_div_le_one_div_of_le (by linarith) hpu
    have hmono := neg_log_one_sub_ratio_mono h1p_pos h1p_le_1u h1u_lt
    change (-Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ)) / (1 / (p : ℝ)) ^ 2 ≤ c_p u at hmono
    have h1p2_pos : 0 < (1 / (p : ℝ)) ^ 2 := sq_pos_of_pos h1p_pos
    have hlog_le : -Real.log (1 - 1 / (p : ℝ)) ≤ 1 / (p : ℝ) + c_p u * (1 / (p : ℝ)) ^ 2 := by
      have hmul := (div_le_iff₀ h1p2_pos).mp hmono
      linarith
    have h1mp_pos : 0 < 1 - 1 / (p : ℝ) := by linarith [h1p_le_1u, h1u_lt]
    have hinv_eq : (1 - 1 / (p : ℝ))⁻¹ = Real.exp (-Real.log (1 - 1 / (p : ℝ))) := by
      rw [Real.exp_neg, Real.exp_log h1mp_pos]
    rw [hinv_eq]
    have hexp_le := Real.exp_le_exp.mpr hlog_le
    simpa [one_div, inv_pow] using hexp_le

/-- Shifted-prime product splitting for any `S : Finset ℕ` with `∀ p ∈ S, p_* ≤ p` (`3 ≤ p_*`). -/
theorem prod_inv_one_sub_le_twin_mul_exp {p_star : ℕ} (hp_star : 3 ≤ p_star) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p_star ≤ p) :
    ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      (∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
        Real.exp (∑ p ∈ S, (1 / (p : ℝ)) + c_p (p_star : ℝ) * ∑ p ∈ S, (1 / (p : ℝ) ^ 2)) :=
  prod_inv_one_sub_le_twin_mul_exp_real (by exact_mod_cast (by omega : 2 < p_star)) S
    fun p hp => by exact_mod_cast hS p hp

/-- Dropping primes dividing `N` only decreases the product of `(1 - 1/(p-1))⁻¹` over `p ≥ 3`. -/
theorem prod_inv_one_sub_omission_le (S : Finset ℕ) (hS : ∀ p ∈ S, 3 ≤ p) (N : ℕ) :
    ∏ p ∈ S.filter (fun p => ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  refine Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ S) ?_ ?_
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hS p (Finset.filter_subset _ S hp)
    have hp1_pos : 0 < (p : ℝ) - 1 := by linarith
    have hpos : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      have : 1 / ((p : ℝ) - 1) < 1 := by
        rw [one_div_lt hp1_pos zero_lt_one]
        linarith
      linarith
    exact (inv_pos.mpr hpos).le
  · intro p hp _
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have hp1_pos : 0 < (p : ℝ) - 1 := by linarith
    have hlt1 : 1 - 1 / ((p : ℝ) - 1) ≤ 1 := by
      have : 0 ≤ 1 / ((p : ℝ) - 1) := one_div_nonneg.mpr hp1_pos.le
      linarith
    have hpos : 0 < 1 - 1 / ((p : ℝ) - 1) := by
      have : 1 / ((p : ℝ) - 1) < 1 := by
        rw [one_div_lt hp1_pos zero_lt_one]
        linarith
      linarith
    exact (one_le_inv₀ hpos).mpr hlt1

/-! ## 3. Causal Running-Minimum Two-Variable Mertens Condition -/

/-- Two-sided Mertens sum bounds for `∑_{p < x} 1/p` valid for all `x ≥ 2`. -/
def MertensSumBounds (M0 : ℝ) (E_lo E_hi : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    Real.log (Real.log x) + M0 - E_lo x ≤
        (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / p) ∧
      (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / p) ≤
        Real.log (Real.log x) + M0 + E_hi x

/-- Pre-prime Mertens excursion `∑_{r < q} 1/r - log(log q) - M0`. -/
noncomputable def mertensBefore (M0 : ℝ) (q : ℕ) : ℝ :=
  (∑ r ∈ (Finset.range q).filter Nat.Prime, (1 : ℝ) / r) - Real.log (Real.log q) - M0

/-- Post-prime Mertens excursion `∑_{r ≤ p} 1/r - log(log p) - M0`. -/
noncomputable def mertensAfter (M0 : ℝ) (p : ℕ) : ℝ :=
  (∑ r ∈ (Finset.range (p + 1)).filter Nat.Prime, (1 : ℝ) / r) - Real.log (Real.log p) - M0

private lemma mertens_Ico_sum_eq_sub (w z_1 : ℝ) (hwz : w ≤ z_1) :
    (∑ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter Nat.Prime, (1 : ℝ) / p) =
      (∑ p ∈ (Finset.range (Nat.ceil z_1)).filter Nat.Prime, (1 : ℝ) / p) -
        (∑ p ∈ (Finset.range (Nat.ceil w)).filter Nat.Prime, (1 : ℝ) / p) := by
  have hceil : Nat.ceil w ≤ Nat.ceil z_1 := Nat.ceil_mono hwz
  simp only [Finset.sum_filter]
  exact Finset.sum_Ico_eq_sub (fun p => if p.Prime then (1 : ℝ) / p else 0) hceil

/-- Difference of `MertensSumBounds` over `[w, z_1)`. -/
theorem mertens_sum_Ico_le {M0 : ℝ} {E_lo E_hi : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi) {w z_1 : ℝ} (hw : 2 ≤ w) (hwz : w < z_1) :
    ∑ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log z_1 / Real.log w) + E_hi z_1 + E_lo w := by
  have hz : 2 ≤ z_1 := le_trans hw hwz.le
  have hlo := (hM w hw).1
  have hhi := (hM z_1 hz).2
  rw [mertens_Ico_sum_eq_sub w z_1 hwz.le]
  have hlogw_pos : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz_pos : 0 < Real.log z_1 := Real.log_pos (by linarith)
  rw [Real.log_div hlogz_pos.ne' hlogw_pos.ne']
  linarith

/-- Causal running-minimum two-variable Mertens sieve condition (`NOTES_K3_DERIVATION.md` §3,
`primes_and_mertens.py:eps_sup_two_var`). -/
theorem two_var_mertens_cond_of_excursion
    {p_star X_0 : ℕ} (hp_star : 3 ≤ p_star)
    (hP_ne : ((Finset.Icc p_star X_0).filter Nat.Prime).Nonempty)
    {M0 : ℝ} {E_lo E_hi : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi)
    (hE_lo_anti : AntitoneOn E_lo (Set.Ici (p_star : ℝ)))
    {D_max twin_tail s2_tail : ℝ}
    (h_excur : ∀ q ∈ (Finset.Icc p_star X_0).filter Nat.Prime,
      ∀ p ∈ (Finset.Icc p_star X_0).filter Nat.Prime, q ≤ p →
        mertensAfter M0 p - mertensBefore M0 q ≤ D_max)
    (h_tail : ∀ x : ℝ, (X_0 : ℝ) ≤ x →
      E_hi x - min (((Finset.Icc p_star X_0).filter Nat.Prime).inf' hP_ne (mertensBefore M0))
        (-E_lo (p_star : ℝ)) ≤ D_max)
    (h_twin : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p_star ≤ p) →
      ∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) ≤ twin_tail)
    (h_s2 : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p_star ≤ p) →
      ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ s2_tail)
    {w z_1 : ℝ} (hw : (p_star : ℝ) ≤ w) (hwz : w < z_1) (N : ℕ) :
    ∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
      (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      (twin_tail * Real.exp (D_max + c_p (p_star : ℝ) * s2_tail)) * (Real.log z_1 / Real.log w) := by
  let S : Finset ℕ := (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter Nat.Prime
  have hS_ge : ∀ p ∈ S, p_star ≤ p := by
    intro p hp
    have hp_ico := (Finset.mem_filter.mp hp).1
    have hceil_w : p_star ≤ Nat.ceil w := by
      exact_mod_cast hw.trans (Nat.le_ceil w)
    exact hceil_w.trans (Finset.mem_Ico.mp hp_ico).1
  have hS_ge3 : ∀ p ∈ S, 3 ≤ p := fun p hp => hp_star.trans (hS_ge p hp)
  have h_omit :
      ∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    have hfilt : (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N) =
        S.filter (fun p => ¬ p ∣ N) := by
      ext p
      simp only [S, Finset.mem_filter]
      tauto
    rw [hfilt]
    exact prod_inv_one_sub_omission_le S hS_ge3 N
  have h_split := prod_inv_one_sub_le_twin_mul_exp hp_star S hS_ge
  have h_sum1 : ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log z_1 / Real.log w) + D_max := by
    rcases le_or_gt z_1 (X_0 : ℝ) with hzX | hXz
    · by_cases hS_ne : S.Nonempty
      · let q := S.min' hS_ne
        let p := S.max' hS_ne
        have hqS : q ∈ S := Finset.min'_mem S hS_ne
        have hpS : p ∈ S := Finset.max'_mem S hS_ne
        have hqp : q ≤ p := Finset.min'_le S p hpS
        have hq_prime : q.Prime := (Finset.mem_filter.mp hqS).2
        have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
        have hp_lt_z : (p : ℝ) < z_1 :=
          Nat.lt_ceil.mp (Finset.mem_Ico.mp (Finset.mem_filter.mp hpS).1).2
        have hp_le_X : p ≤ X_0 := by
          have : (p : ℝ) < (X_0 : ℝ) := lt_of_lt_of_le hp_lt_z hzX
          exact_mod_cast this.le
        have hq_in_excur : q ∈ (Finset.Icc p_star X_0).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hS_ge q hqS, hqp.trans hp_le_X⟩, hq_prime⟩
        have hp_in_excur : p ∈ (Finset.Icc p_star X_0).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hS_ge p hpS, hp_le_X⟩, hp_prime⟩
        have hex := h_excur q hq_in_excur p hp_in_excur hqp
        have hS_eq : S = (Finset.Ico q (p + 1)).filter Nat.Prime := by
          ext r
          simp only [S, Finset.mem_filter, Finset.mem_Ico]
          constructor
          · rintro ⟨⟨_, _⟩, hr_prime⟩
            have hrS : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨‹_›, ‹_›⟩, hr_prime⟩
            exact ⟨⟨Finset.min'_le S r hrS, Nat.lt_succ_of_le (Finset.le_max' S r hrS)⟩, hr_prime⟩
          · rintro ⟨⟨hqr, hrp⟩, hr_prime⟩
            have hq_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hqS).1
            have hp_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hpS).1
            exact ⟨⟨hq_ico.1.trans hqr, lt_of_le_of_lt (Nat.lt_succ_iff.mp hrp) hp_ico.2⟩, hr_prime⟩
        have hsum_eq : ∑ r ∈ S, (1 : ℝ) / r =
            (∑ r ∈ (Finset.range (p + 1)).filter Nat.Prime, (1 : ℝ) / r) -
              (∑ r ∈ (Finset.range q).filter Nat.Prime, (1 : ℝ) / r) := by
          rw [hS_eq]
          simp only [Finset.sum_filter]
          exact Finset.sum_Ico_eq_sub (fun r => if r.Prime then (1 : ℝ) / r else 0) (Nat.le_succ_of_le hqp)
        have hw_le_q : w ≤ (q : ℝ) :=
          Nat.ceil_le.mp (Finset.mem_Ico.mp (Finset.mem_filter.mp hqS).1).1
        have hq_gt2 : (2 : ℝ) < q := by
          have : (3 : ℝ) ≤ q := by exact_mod_cast hS_ge3 q hqS
          linarith
        have hp_gt2 : (2 : ℝ) < p := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hS_ge3 p hpS
          linarith
        have hw_gt2 : (2 : ℝ) < w := by
          have : (3 : ℝ) ≤ w := le_trans (by exact_mod_cast hp_star) hw
          linarith
        have hz_gt2 : (2 : ℝ) < z_1 := lt_trans hw_gt2 hwz
        have hlogw_pos : 0 < Real.log w := Real.log_pos (by linarith)
        have hlogq_pos : 0 < Real.log q := Real.log_pos (by linarith)
        have hlogp_pos : 0 < Real.log p := Real.log_pos (by linarith)
        have hlogz_pos : 0 < Real.log z_1 := Real.log_pos (by linarith)
        have hlog_w_q : Real.log (Real.log w) ≤ Real.log (Real.log q) :=
          Real.log_le_log hlogw_pos (Real.log_le_log (by linarith) hw_le_q)
        have hlog_p_z : Real.log (Real.log p) ≤ Real.log (Real.log z_1) :=
          Real.log_le_log hlogp_pos (Real.log_le_log (by linarith) hp_lt_z.le)
        rw [hsum_eq, Real.log_div hlogz_pos.ne' hlogw_pos.ne']
        dsimp only [mertensAfter, mertensBefore] at hex
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hS_ne, Finset.sum_empty]
        obtain ⟨r0, hr0⟩ := hP_ne
        have hr0_prime : r0.Prime := (Finset.mem_filter.mp hr0).2
        have hr0_pos : (0 : ℝ) < r0 := by exact_mod_cast hr0_prime.pos
        have hex0 := h_excur r0 hr0 r0 hr0 le_rfl
        have hD_nonneg : 0 ≤ D_max := by
          dsimp only [mertensAfter, mertensBefore] at hex0
          have hsub : (∑ r ∈ (Finset.range (r0 + 1)).filter Nat.Prime, (1 : ℝ) / r) -
              (∑ r ∈ (Finset.range r0).filter Nat.Prime, (1 : ℝ) / r) = (1 : ℝ) / r0 := by
            have hmem : r0 ∉ (Finset.range r0).filter Nat.Prime := by simp
            rw [Finset.range_add_one, Finset.filter_insert]
            simp only [hr0_prime, ↓reduceIte]
            rw [Finset.sum_insert hmem]
            ring
          have hr0_inv : (0 : ℝ) ≤ (1 : ℝ) / r0 := one_div_nonneg.mpr hr0_pos.le
          linarith
        have hw_gt1 : 1 < w := by
          have : (3 : ℝ) ≤ w := le_trans (by exact_mod_cast hp_star) hw
          linarith
        have hlogw_pos : 0 < Real.log w := Real.log_pos hw_gt1
        have hlogw_lt : Real.log w < Real.log z_1 := Real.log_lt_log (by linarith) hwz
        have hlog_ratio_pos : 0 < Real.log (Real.log z_1 / Real.log w) := by
          apply Real.log_pos
          rw [one_lt_div hlogw_pos]
          exact hlogw_lt
        linarith
    · have hw2 : 2 ≤ w := le_trans (by exact_mod_cast (by omega : 2 ≤ p_star)) hw
      have hIco := mertens_sum_Ico_le hM hw2 hwz
      have hElo : E_lo w ≤ E_lo (p_star : ℝ) :=
        hE_lo_anti (Set.mem_Ici.mpr (le_refl _)) (Set.mem_Ici.mpr hw) hw
      have htail := h_tail z_1 hXz.le
      have hmin : min (((Finset.Icc p_star X_0).filter Nat.Prime).inf' hP_ne (mertensBefore M0))
          (-E_lo (p_star : ℝ)) ≤ -E_lo (p_star : ℝ) := min_le_right _ _
      dsimp only [S]
      linarith
  have hS_prime_ge : ∀ p ∈ S, p.Prime ∧ p_star ≤ p := fun p hp =>
    ⟨(Finset.mem_filter.mp hp).2, hS_ge p hp⟩
  have htwin_le : ∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) ≤ twin_tail :=
    h_twin S hS_prime_ge
  have hs2_le : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ s2_tail :=
    h_s2 S hS_prime_ge
  have hc_pos : 0 < c_p (p_star : ℝ) := c_p_pos (by exact_mod_cast (by omega : 1 < p_star))
  have hexp_arg : ∑ p ∈ S, (1 / (p : ℝ)) + c_p (p_star : ℝ) * ∑ p ∈ S, (1 / (p : ℝ) ^ 2) ≤
      Real.log (Real.log z_1 / Real.log w) + (D_max + c_p (p_star : ℝ) * s2_tail) := by
    have hmul : c_p (p_star : ℝ) * ∑ p ∈ S, (1 / (p : ℝ) ^ 2) ≤ c_p (p_star : ℝ) * s2_tail :=
      mul_le_mul_of_nonneg_left hs2_le hc_pos.le
    linarith
  have hw_gt1 : 1 < w := by
    have : (3 : ℝ) ≤ w := le_trans (by exact_mod_cast hp_star) hw
    linarith
  have hlogw_pos : 0 < Real.log w := Real.log_pos hw_gt1
  have hlogz_pos : 0 < Real.log z_1 := lt_trans hlogw_pos (Real.log_lt_log (by linarith) hwz)
  have hratio_pos : 0 < Real.log z_1 / Real.log w := div_pos hlogz_pos hlogw_pos
  have hexp_le : Real.exp (∑ p ∈ S, (1 / (p : ℝ)) + c_p (p_star : ℝ) * ∑ p ∈ S, (1 / (p : ℝ) ^ 2)) ≤
      Real.exp (D_max + c_p (p_star : ℝ) * s2_tail) * (Real.log z_1 / Real.log w) := by
    calc Real.exp (∑ p ∈ S, (1 / (p : ℝ)) + c_p (p_star : ℝ) * ∑ p ∈ S, (1 / (p : ℝ) ^ 2))
        ≤ Real.exp (Real.log (Real.log z_1 / Real.log w) + (D_max + c_p (p_star : ℝ) * s2_tail)) :=
          Real.exp_le_exp.mpr hexp_arg
      _ = Real.exp (D_max + c_p (p_star : ℝ) * s2_tail) *
            Real.exp (Real.log (Real.log z_1 / Real.log w)) := by
          rw [add_comm, Real.exp_add]
      _ = Real.exp (D_max + c_p (p_star : ℝ) * s2_tail) * (Real.log z_1 / Real.log w) := by
          rw [Real.exp_log hratio_pos]
  have htwin_nonneg : 0 ≤ ∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (by omega : 2 < p_star).trans_le (hS_ge p hp)
    positivity
  calc ∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))⁻¹
      ≤ ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ := h_omit
    _ ≤ (∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
          Real.exp (∑ p ∈ S, (1 / (p : ℝ)) + c_p (p_star : ℝ) * ∑ p ∈ S, (1 / (p : ℝ) ^ 2)) :=
        h_split
    _ ≤ twin_tail * (Real.exp (D_max + c_p (p_star : ℝ) * s2_tail) * (Real.log z_1 / Real.log w)) :=
        mul_le_mul htwin_le hexp_le (Real.exp_pos _).le (le_trans htwin_nonneg htwin_le)
    _ = (twin_tail * Real.exp (D_max + c_p (p_star : ℝ) * s2_tail)) * (Real.log z_1 / Real.log w) := by
        ring

/-! ## 4. Large-`u` Two-Variable Soundness (`eps_large_u_two_var`) -/

private lemma sum_Ico_recip_sub_tele (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
      1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
  have htele : ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 1) - 1 / (((n + 1 : ℕ) : ℝ) - 1)) =
      1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk, ih]
      push_cast
      ring
  rw [← htele]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring_nf

private lemma sum_Ico_recip_sub_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have hterm : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn_ge : a ≤ n := (Finset.mem_Ico.mp hn).1
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast ha.trans hn_ge
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hdiff : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      field_simp
      ring
    rw [hdiff]
    have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    exact one_div_le_one_div_of_le hpos (by nlinarith)
  have htele := sum_Ico_recip_sub_tele a b hab
  have hb_nonneg : 0 ≤ 1 / ((b : ℝ) - 1) := by
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
    exact one_div_nonneg.mpr (by linarith)
  linarith

private lemma sum_Ico_recip_sub_two_tele (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) =
      1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2) := by
  have htele : ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 2) - 1 / (((n + 1 : ℕ) : ℝ) - 2)) =
      1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2) := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk, ih]
      push_cast
      ring
  rw [← htele]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring_nf

private lemma sum_Ico_recip_sub_two_le (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) ≤ 1 / ((a : ℝ) - 2) := by
  have hterm : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) ≤
      ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn_ge : a ≤ n := (Finset.mem_Ico.mp hn).1
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast ha.trans hn_ge
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
    have hdiff : 1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1) =
        1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
      field_simp
      ring
    rw [hdiff]
    have hpos : 0 < ((n : ℝ) - 1) * ((n : ℝ) - 2) := mul_pos (by linarith) (by linarith)
    exact one_div_le_one_div_of_le hpos (by nlinarith)
  have htele := sum_Ico_recip_sub_two_tele a b hab
  have hb_nonneg : 0 ≤ 1 / ((b : ℝ) - 2) := by
    have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
    exact one_div_nonneg.mpr (by linarith)
  linarith

/-- Uniform large-`u` bound on the twin-prime tail and `s2_tail` contribution:
for `u ≥ Real.exp 10.1` and any finite `S` of primes `p ≥ u`,
`twin_tail(S) * exp(c_p(u) * s2_tail(S)) ≤ exp(2.0002 / u)`. -/
theorem twin_tail_mul_exp_s2_tail_le {u : ℝ} (hu : Real.exp 10.1 ≤ u) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ u ≤ (p : ℝ)) :
    (∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
        Real.exp (c_p u * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      Real.exp (2.0002 / u) := by
  have hu_ge_1024 : (1024 : ℝ) ≤ u := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [exp_one_gt_27_div_10]
    have h10 : (1024 : ℝ) ≤ Real.exp 10 := by
      calc (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
        _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
        _ = Real.exp 10 := by rw [← Real.exp_natCast_mul]; norm_num
    have h101 : Real.exp 10 ≤ Real.exp 10.1 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hu3 : 3 ≤ u := by linarith
  let a : ℕ := Nat.ceil u
  let b : ℕ := max a (S.sup id + 1)
  have hua : u ≤ (a : ℝ) := Nat.le_ceil u
  have ha3 : 3 ≤ a := by exact_mod_cast hu3.trans hua
  have hab : a ≤ b := le_max_left _ _
  have hS_sub : S ⊆ Finset.Ico a b := by
    intro p hp
    refine Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr (hS p hp).2, ?_⟩
    have hsup : p ≤ S.sup id := Finset.le_sup (f := id) hp
    exact lt_of_le_of_lt hsup (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right a _))
  have hs2_le : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (u - 1) := by
    have hsub_sum : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤
        ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun _ _ _ => by positivity
    have hIco_le := sum_Ico_recip_sub_le a b (by omega) hab
    have h1 : 1 / ((a : ℝ) - 1) ≤ 1 / (u - 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have htwin_le : ∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) ≤
      Real.exp (1 / (u - 2)) := by
    have hprod_exp : ∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) ≤
        ∏ p ∈ S, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
      refine Finset.prod_le_prod₀ ?_ ?_
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := le_trans hu3 (hS p hp).2
        have hp2 : 0 < (p : ℝ) - 2 := by linarith
        positivity
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := le_trans hu3 (hS p hp).2
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
        have heq : ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) =
            1 / ((p : ℝ) * ((p : ℝ) - 2)) + 1 := by
          field_simp
          ring
        rw [heq]
        exact Real.add_one_le_exp _
    rw [← Real.exp_sum] at hprod_exp
    refine hprod_exp.trans (Real.exp_le_exp.mpr ?_)
    have hsub_sum : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
        ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun n hn _ => by
        have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast ha3.trans (Finset.mem_Ico.mp hn).1
        have hn2 : 0 < (n : ℝ) - 2 := by linarith
        positivity
    have hIco_le := sum_Ico_recip_sub_two_le a b ha3 hab
    have h1 : 1 / ((a : ℝ) - 2) ≤ 1 / (u - 2) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have hcp_nonneg : 0 ≤ c_p u := (c_p_pos (by linarith)).le
  have hcp_le : c_p u ≤ u / (2 * (u - 1)) := c_p_le (by linarith)
  have hcp_s2 : c_p u * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ u / (2 * (u - 1) ^ 2) := by
    have hu1_pos : 0 < u - 1 := by linarith
    have h1 : c_p u * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ (u / (2 * (u - 1))) * (1 / (u - 1)) :=
      mul_le_mul hcp_le hs2_le (Finset.sum_nonneg fun _ _ => by positivity)
        (div_nonneg (by linarith) (by linarith))
    have h2 : u / (2 * (u - 1)) * (1 / (u - 1)) = u / (2 * (u - 1) ^ 2) := by
      field_simp [hu1_pos.ne']
    linarith
  have hexp_bound : 1 / (u - 2) + u / (2 * (u - 1) ^ 2) ≤ 2.0002 / u := by
    have hu0 : 0 < u := by linarith
    have hu1 : 0 < u - 1 := by linarith
    have hu2 : 0 < u - 2 := by linarith
    rw [div_add_div _ _ hu2.ne' (by positivity), div_le_div_iff₀ (by positivity) hu0]
    nlinarith
  calc (∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
          Real.exp (c_p u * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2)
      ≤ Real.exp (1 / (u - 2)) * Real.exp (u / (2 * (u - 1) ^ 2)) :=
        mul_le_mul htwin_le (Real.exp_le_exp.mpr hcp_s2) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (1 / (u - 2) + u / (2 * (u - 1) ^ 2)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2.0002 / u) := Real.exp_le_exp.mpr hexp_bound

/-- Soundness of `eps_large_u_two_var` (`primes_and_mertens.py`):
when `Real.exp 10.1 ≤ u ≤ w < z_1`, we have both the interval Mertens sum bound
`∑_{w ≤ p < z_1} 1/p ≤ log (log z_1 / log w) + E_hi z_1 + E_lo w` and the shifted-prime
product bound with prefactor `Real.exp (2.0002 / u + E_hi z_1 + E_lo w)` for all `N`. -/
theorem eps_large_u_two_var_sound
    {M0 : ℝ} {E_lo E_hi : ℝ → ℝ} (hM : MertensSumBounds M0 E_lo E_hi)
    {u w z_1 : ℝ} (hu : Real.exp 10.1 ≤ u) (huw : u ≤ w) (hwz : w < z_1) (N : ℕ) :
    (∑ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter Nat.Prime, (1 : ℝ) / p ≤
        Real.log (Real.log z_1 / Real.log w) + E_hi z_1 + E_lo w) ∧
      (∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        Real.exp (2.0002 / u + E_hi z_1 + E_lo w) * (Real.log z_1 / Real.log w)) := by
  have hu_ge_1024 : (1024 : ℝ) ≤ u := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [exp_one_gt_27_div_10]
    have h10 : (1024 : ℝ) ≤ Real.exp 10 := by
      calc (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
        _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
        _ = Real.exp 10 := by rw [← Real.exp_natCast_mul]; norm_num
    have h101 : Real.exp 10 ≤ Real.exp 10.1 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hw2 : 2 ≤ w := by linarith
  have hsum := mertens_sum_Ico_le hM hw2 hwz
  refine ⟨hsum, ?_⟩
  let S : Finset ℕ := (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter Nat.Prime
  have hS_ge_u : ∀ p ∈ S, p.Prime ∧ u ≤ (p : ℝ) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hw_le_p : w ≤ (p : ℝ) := Nat.ceil_le.mp (Finset.mem_Ico.mp hp'.1).1
    exact ⟨hp'.2, huw.trans hw_le_p⟩
  have hS_ge3 : ∀ p ∈ S, 3 ≤ p := by
    intro p hp
    have hp_ge : (1024 : ℝ) ≤ p := le_trans hu_ge_1024 (hS_ge_u p hp).2
    exact_mod_cast (by linarith : (3 : ℝ) ≤ p)
  have h_omit :
      ∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    have hfilt : (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N) =
        S.filter (fun p => ¬ p ∣ N) := by
      ext p
      simp only [S, Finset.mem_filter]
      tauto
    rw [hfilt]
    exact prod_inv_one_sub_omission_le S hS_ge3 N
  have h_split := prod_inv_one_sub_le_twin_mul_exp_real (by linarith : 2 < u) S
    fun p hp => (hS_ge_u p hp).2
  have htail := twin_tail_mul_exp_s2_tail_le hu S hS_ge_u
  have hlogw_pos : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz_pos : 0 < Real.log z_1 := lt_trans hlogw_pos (Real.log_lt_log (by linarith) hwz)
  have hratio_pos : 0 < Real.log z_1 / Real.log w := div_pos hlogz_pos hlogw_pos
  have hexp_sum : Real.exp (∑ p ∈ S, (1 : ℝ) / p) ≤
      Real.exp (E_hi z_1 + E_lo w) * (Real.log z_1 / Real.log w) := by
    calc Real.exp (∑ p ∈ S, (1 : ℝ) / p)
        ≤ Real.exp (Real.log (Real.log z_1 / Real.log w) + (E_hi z_1 + E_lo w)) := by
          refine Real.exp_le_exp.mpr ?_
          dsimp only [S] at *
          linarith
      _ = Real.exp (E_hi z_1 + E_lo w) * Real.exp (Real.log (Real.log z_1 / Real.log w)) := by
          rw [add_comm, Real.exp_add]
      _ = Real.exp (E_hi z_1 + E_lo w) * (Real.log z_1 / Real.log w) := by
          rw [Real.exp_log hratio_pos]
  calc ∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z_1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        (1 - 1 / ((p : ℝ) - 1))⁻¹
      ≤ ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ := h_omit
    _ ≤ (∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
          Real.exp (∑ p ∈ S, (1 / (p : ℝ)) + c_p u * ∑ p ∈ S, (1 / (p : ℝ) ^ 2)) := h_split
    _ = ((∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) *
            Real.exp (c_p u * ∑ p ∈ S, (1 / (p : ℝ) ^ 2))) *
          Real.exp (∑ p ∈ S, (1 : ℝ) / p) := by
        rw [Real.exp_add]
        ring
    _ ≤ Real.exp (2.0002 / u) * (Real.exp (E_hi z_1 + E_lo w) * (Real.log z_1 / Real.log w)) :=
        mul_le_mul htail hexp_sum (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2.0002 / u + E_hi z_1 + E_lo w) * (Real.log z_1 / Real.log w) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf

end BuchstabSwitching
