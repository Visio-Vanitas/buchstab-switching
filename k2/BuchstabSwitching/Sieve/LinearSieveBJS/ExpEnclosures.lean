import BuchstabSwitching.Sieve.LinearSieveInduction
import Mathlib.Tactic

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 1. Numerical Exponential Enclosures and `E₁(3)` Upper Bound -/

section ExpEnclosures

theorem exp_one_gt_d9' : (27182818283 / 10000000000 : ℝ) < Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

theorem exp_one_lt_d9' : Real.exp 1 < (27182818286 / 10000000000 : ℝ) := by
  linarith [Real.exp_one_lt_d9]

theorem exp_neg_one_gt : (10000000000 / 27182818286 : ℝ) < Real.exp (-1) := by
  rw [Real.exp_neg, ← one_div]
  have h1 : Real.exp 1 < (27182818286 / 10000000000 : ℝ) := exp_one_lt_d9'
  have h2 := one_div_lt_one_div_of_lt (Real.exp_pos 1) h1
  linarith

theorem exp_neg_one_lt : Real.exp (-1) < (10000000000 / 27182818283 : ℝ) := by
  rw [Real.exp_neg, ← one_div]
  have h1 : (27182818283 / 10000000000 : ℝ) < Real.exp 1 := exp_one_gt_d9'
  have h2 := one_div_lt_one_div_of_lt (by norm_num) h1
  linarith

theorem exp_neg_nat_eq (k : ℕ) : Real.exp (-(k : ℝ)) = (Real.exp (-1)) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem exp_one_fifth_gt : (12214027 / 10000000 : ℝ) < Real.exp (1 / 5 : ℝ) := by
  have hpow : ((12214027 / 10000000 : ℝ) ^ 5) < (Real.exp (1 / 5 : ℝ)) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
    linarith [exp_one_gt_d9']
  exact lt_of_pow_lt_pow_left₀ 5 (Real.exp_pos _).le hpow

theorem exp_one_fifth_lt : Real.exp (1 / 5 : ℝ) < (12214028 / 10000000 : ℝ) := by
  have hpow : (Real.exp (1 / 5 : ℝ)) ^ 5 < (12214028 / 10000000 : ℝ) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
    linarith [exp_one_lt_d9']
  exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) hpow

theorem exp_two_fifths_lt : Real.exp (2 / 5 : ℝ) < (12214028 / 10000000 : ℝ) ^ 2 := by
  have h : Real.exp (2 / 5 : ℝ) = (Real.exp (1 / 5 : ℝ)) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  exact pow_lt_pow_left₀ exp_one_fifth_lt (Real.exp_pos _).le (by norm_num)

theorem exp_three_fifths_lt : Real.exp (3 / 5 : ℝ) < (12214028 / 10000000 : ℝ) ^ 3 := by
  have h : Real.exp (3 / 5 : ℝ) = (Real.exp (1 / 5 : ℝ)) ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  exact pow_lt_pow_left₀ exp_one_fifth_lt (Real.exp_pos _).le (by norm_num)

theorem exp_four_fifths_lt : Real.exp (4 / 5 : ℝ) < (12214028 / 10000000 : ℝ) ^ 4 := by
  have h : Real.exp (4 / 5 : ℝ) = (Real.exp (1 / 5 : ℝ)) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  exact pow_lt_pow_left₀ exp_one_fifth_lt (Real.exp_pos _).le (by norm_num)

theorem log_two_lt_seven_tenths : Real.log 2 < (7 / 10 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hpow : (2 : ℝ) ^ 10 < (Real.exp (7 / 10 : ℝ)) ^ 10 := by
    rw [← Real.exp_nat_mul]
    have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [exp_one_gt_d9']
    have h7 : (2.7 : ℝ) ^ 7 < (Real.exp 1) ^ 7 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul] at h7
    norm_num at h7 ⊢
    linarith
  exact lt_of_pow_lt_pow_left₀ 10 (Real.exp_pos _).le hpow

theorem log_three_lt_eleven_tenths : Real.log 3 < (11 / 10 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hpow : (3 : ℝ) ^ 10 < (Real.exp (11 / 10 : ℝ)) ^ 10 := by
    rw [← Real.exp_nat_mul]
    have h1 : (2.718 : ℝ) < Real.exp 1 := by linarith [exp_one_gt_d9']
    have h11 : (2.718 : ℝ) ^ 11 < (Real.exp 1) ^ 11 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul] at h11
    norm_num at h11 ⊢
    linarith
  exact lt_of_pow_lt_pow_left₀ 10 (Real.exp_pos _).le hpow

/-- Antiderivative of `(x - m)^j * exp (-x)`. -/
def expPowAntideriv (m : ℝ) : ℕ → ℝ → ℝ
  | 0, x => -Real.exp (-x)
  | j + 1, x => -(x - m) ^ (j + 1) * Real.exp (-x) + ((j : ℝ) + 1) * expPowAntideriv m j x

theorem hasDerivAt_expPowAntideriv (m : ℝ) :
    ∀ (j : ℕ) (t : ℝ), HasDerivAt (expPowAntideriv m j) ((t - m) ^ j * Real.exp (-t)) t := by
  intro j
  induction j with
  | zero =>
    intro t
    have hneg : HasDerivAt (fun x : ℝ => -x) (-1) t := (hasDerivAt_id t).neg
    have h1 : HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-t)) t := by
      refine (hneg.exp.neg).congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)
      ring
    simpa [expPowAntideriv] using h1
  | succ j ih =>
    intro t
    have hsub : HasDerivAt (fun x : ℝ => x - m) 1 t := by
      refine ((hasDerivAt_id t).sub_const m).congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)
    have hpow := hsub.pow (j + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hpow
    have hpoly : HasDerivAt (fun x : ℝ => -(x - m) ^ (j + 1)) (-(((j : ℝ) + 1) * (t - m) ^ j * 1)) t :=
      hpow.neg
    have hneg : HasDerivAt (fun x : ℝ => -x) (-1) t := (hasDerivAt_id t).neg
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t := hneg.exp
    have hmul := hpoly.mul hexp
    have hterm := hmul.add ((ih t).const_mul ((j : ℝ) + 1))
    refine hterm.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · ring
    · simp [expPowAntideriv]

theorem integral_sub_pow_mul_exp_neg (m a b : ℝ) (j : ℕ) :
    ∫ x in a..b, (x - m) ^ j * Real.exp (-x) =
      expPowAntideriv m j b - expPowAntideriv m j a := by
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (expPowAntideriv m j) ((t - m) ^ j * Real.exp (-t)) t :=
    fun t _ => hasDerivAt_expPowAntideriv m j t
  have hint : IntervalIntegrable (fun x => (x - m) ^ j * Real.exp (-x)) volume a b :=
    (((continuous_id.sub continuous_const).pow j).mul
      (Real.continuous_exp.comp continuous_neg)).intervalIntegrable a b
  exact integral_eq_sub_of_hasDerivAt hderiv hint

/-- Shifted-by-`e²` antiderivative helper: `exp 2 * (expPowAntideriv m j b - expPowAntideriv m j a)`.
Evaluated on `x ↦ Real.exp 2 * expPowAntideriv m j x` for integer `a, b`. -/
theorem inv_eq_taylor4_add_rem {x m : ℝ} (hx : x ≠ 0) (hm : m ≠ 0) :
    1 / x = 1 / m - (x - m) / m ^ 2 + (x - m) ^ 2 / m ^ 3 - (x - m) ^ 3 / m ^ 4 +
      (x - m) ^ 4 / (m ^ 4 * x) := by
  field_simp
  ring

theorem integral_exp_neg_div_le_taylor4 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.exp (-x) / x ≤
      let m := (a + b) / 2
      (1 / m) * (expPowAntideriv m 0 b - expPowAntideriv m 0 a) -
        (1 / m ^ 2) * (expPowAntideriv m 1 b - expPowAntideriv m 1 a) +
        (1 / m ^ 3) * (expPowAntideriv m 2 b - expPowAntideriv m 2 a) -
        (1 / m ^ 4) * (expPowAntideriv m 3 b - expPowAntideriv m 3 a) +
        (1 / (m ^ 4 * a)) * (expPowAntideriv m 4 b - expPowAntideriv m 4 a) := by
  set m : ℝ := (a + b) / 2
  have hm : 0 < m := by dsimp [m]; linarith
  let ub : ℝ → ℝ := fun x =>
    ((1 / m) * (x - m) ^ 0 - (1 / m ^ 2) * (x - m) ^ 1 + (1 / m ^ 3) * (x - m) ^ 2 -
      (1 / m ^ 4) * (x - m) ^ 3 + (1 / (m ^ 4 * a)) * (x - m) ^ 4) * Real.exp (-x)
  have hc1 : IntervalIntegrable (fun x => Real.exp (-x) / x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hc2 : IntervalIntegrable ub volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    dsimp [ub]
    fun_prop
  have hmono : ∫ x in a..b, Real.exp (-x) / x ≤ ∫ x in a..b, ub x := by
    refine intervalIntegral.integral_mono_on hab hc1 hc2 fun x hx => ?_
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    have hid := inv_eq_taylor4_add_rem hx_pos.ne' hm.ne'
    have hrem : (x - m) ^ 4 / (m ^ 4 * x) ≤ (x - m) ^ 4 / (m ^ 4 * a) := by
      have h4 : 0 ≤ (x - m) ^ 4 := by positivity
      exact div_le_div_of_nonneg_left h4 (by positivity) (mul_le_mul_of_nonneg_left hx.1 (by positivity))
    have hinv_le : 1 / x ≤ 1 / m - (x - m) / m ^ 2 + (x - m) ^ 2 / m ^ 3 - (x - m) ^ 3 / m ^ 4 +
        (x - m) ^ 4 / (m ^ 4 * a) := by linarith
    have hexp_nn : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
    calc Real.exp (-x) / x
        = (1 / x) * Real.exp (-x) := by ring
      _ ≤ (1 / m - (x - m) / m ^ 2 + (x - m) ^ 2 / m ^ 3 - (x - m) ^ 3 / m ^ 4 +
            (x - m) ^ 4 / (m ^ 4 * a)) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hinv_le hexp_nn
      _ = ub x := by dsimp [ub]; ring
  have hint_j : ∀ j : ℕ, IntervalIntegrable (fun x => (x - m) ^ j * Real.exp (-x)) volume a b :=
    fun j => (((continuous_id.sub continuous_const).pow j).mul
      (Real.continuous_exp.comp continuous_neg)).intervalIntegrable a b
  have hub_eq : ∫ x in a..b, ub x =
      (1 / m) * (expPowAntideriv m 0 b - expPowAntideriv m 0 a) -
        (1 / m ^ 2) * (expPowAntideriv m 1 b - expPowAntideriv m 1 a) +
        (1 / m ^ 3) * (expPowAntideriv m 2 b - expPowAntideriv m 2 a) -
        (1 / m ^ 4) * (expPowAntideriv m 3 b - expPowAntideriv m 3 a) +
        (1 / (m ^ 4 * a)) * (expPowAntideriv m 4 b - expPowAntideriv m 4 a) := by
    have hsplit : ub = fun x =>
        (1 / m) * ((x - m) ^ 0 * Real.exp (-x)) +
        (-(1 / m ^ 2) * ((x - m) ^ 1 * Real.exp (-x))) +
        (1 / m ^ 3) * ((x - m) ^ 2 * Real.exp (-x)) +
        (-(1 / m ^ 4) * ((x - m) ^ 3 * Real.exp (-x))) +
        (1 / (m ^ 4 * a)) * ((x - m) ^ 4 * Real.exp (-x)) := by
      ext x; dsimp [ub]; ring
    rw [hsplit]
    rw [intervalIntegral.integral_add ((hint_j 0).const_mul _ |>.add ((hint_j 1).const_mul _) |>.add
        ((hint_j 2).const_mul _) |>.add ((hint_j 3).const_mul _)) ((hint_j 4).const_mul _),
      intervalIntegral.integral_add ((hint_j 0).const_mul _ |>.add ((hint_j 1).const_mul _) |>.add
        ((hint_j 2).const_mul _)) ((hint_j 3).const_mul _),
      intervalIntegral.integral_add ((hint_j 0).const_mul _ |>.add ((hint_j 1).const_mul _))
        ((hint_j 2).const_mul _),
      intervalIntegral.integral_add ((hint_j 0).const_mul _) ((hint_j 1).const_mul _)]
    simp_rw [intervalIntegral.integral_const_mul, integral_sub_pow_mul_exp_neg]
    ring
  linarith

theorem integral_exp_neg_div_tail_le {a M : ℝ} (ha : 0 < a) (haM : a ≤ M) :
    ∫ x in a..M, Real.exp (-x) / x ≤ (1 / a) * Real.exp (-a) := by
  have hc1 : IntervalIntegrable (fun x => Real.exp (-x) / x) volume a M := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le haM]
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hc2 : IntervalIntegrable (fun x => (1 / a) * Real.exp (-x)) volume a M :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).intervalIntegrable a M
  have h1 : ∫ x in a..M, Real.exp (-x) / x ≤ ∫ x in a..M, (1 / a) * Real.exp (-x) := by
    refine intervalIntegral.integral_mono_on haM hc1 hc2 fun x hx => ?_
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    rw [show Real.exp (-x) / x = (1 / x) * Real.exp (-x) by ring]
    exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ha hx.1) (Real.exp_pos _).le
  have h2 : ∫ x in a..M, (1 / a) * Real.exp (-x) = (1 / a) * (Real.exp (-a) - Real.exp (-M)) := by
    rw [intervalIntegral.integral_const_mul]
    have hd : ∀ t ∈ uIcc a M, HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-t)) t := by
      intro t _
      have hneg : HasDerivAt (fun x : ℝ => -x) (-1) t := (hasDerivAt_id t).neg
      convert hneg.exp.neg using 1
      ring
    have hci : IntervalIntegrable (fun x => Real.exp (-x)) volume a M :=
      (Real.continuous_exp.comp continuous_neg).intervalIntegrable a M
    rw [integral_eq_sub_of_hasDerivAt hd hci]
    ring
  have h3 : (1 / a) * (Real.exp (-a) - Real.exp (-M)) ≤ (1 / a) * Real.exp (-a) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [Real.exp_pos (-M)]
  linarith

private lemma expPowAntideriv_zero (m x : ℝ) :
    expPowAntideriv m 0 x = -Real.exp (-x) := rfl

private lemma expPowAntideriv_one (m x : ℝ) :
    expPowAntideriv m 1 x = -((x - m) + 1) * Real.exp (-x) := by
  simp [expPowAntideriv]; ring

private lemma expPowAntideriv_two (m x : ℝ) :
    expPowAntideriv m 2 x = -((x - m) ^ 2 + 2 * (x - m) + 2) * Real.exp (-x) := by
  simp [expPowAntideriv]; ring

private lemma expPowAntideriv_three (m x : ℝ) :
    expPowAntideriv m 3 x =
      -((x - m) ^ 3 + 3 * (x - m) ^ 2 + 6 * (x - m) + 6) * Real.exp (-x) := by
  simp [expPowAntideriv]; ring

private lemma expPowAntideriv_four (m x : ℝ) :
    expPowAntideriv m 4 x =
      -((x - m) ^ 4 + 4 * (x - m) ^ 3 + 12 * (x - m) ^ 2 + 24 * (x - m) + 24) * Real.exp (-x) := by
  simp [expPowAntideriv]; ring

private lemma integral_exp_div_3_4 :
    ∫ x in (3 : ℝ)..4, Real.exp (-x) / x ≤
      (2033 / 7203 : ℝ) * Real.exp (-3) - (627 / 2401 : ℝ) * Real.exp (-4) := by
  have h := integral_exp_neg_div_le_taylor4 (a := 3) (b := 4) (by norm_num) (by norm_num)
  dsimp only at h
  simp only [expPowAntideriv_zero, expPowAntideriv_one, expPowAntideriv_two,
    expPowAntideriv_three, expPowAntideriv_four] at h
  refine h.trans_eq ?_
  ring

private lemma integral_exp_div_4_6 :
    ∫ x in (4 : ℝ)..6, Real.exp (-x) / x ≤
      (521 / 2500 : ℝ) * Real.exp (-4) - (401 / 2500 : ℝ) * Real.exp (-6) := by
  have h := integral_exp_neg_div_le_taylor4 (a := 4) (b := 6) (by norm_num) (by norm_num)
  dsimp only at h
  simp only [expPowAntideriv_zero, expPowAntideriv_one, expPowAntideriv_two,
    expPowAntideriv_three, expPowAntideriv_four] at h
  refine h.trans_eq ?_
  ring

private lemma integral_exp_div_6_9 :
    ∫ x in (6 : ℝ)..9, Real.exp (-x) / x ≤
      (14723 / 101250 : ℝ) * Real.exp (-6) - (10499 / 101250 : ℝ) * Real.exp (-9) := by
  have h := integral_exp_neg_div_le_taylor4 (a := 6) (b := 9) (by norm_num) (by norm_num)
  dsimp only at h
  simp only [expPowAntideriv_zero, expPowAntideriv_one, expPowAntideriv_two,
    expPowAntideriv_three, expPowAntideriv_four] at h
  refine h.trans_eq ?_
  ring

private lemma integral_exp_div_9_14 :
    ∫ x in (9 : ℝ)..14, Real.exp (-x) / x ≤
      (84683 / 839523 : ℝ) * Real.exp (-9) - (170489 / 2518569 : ℝ) * Real.exp (-14) := by
  have h := integral_exp_neg_div_le_taylor4 (a := 9) (b := 14) (by norm_num) (by norm_num)
  dsimp only at h
  simp only [expPowAntideriv_zero, expPowAntideriv_one, expPowAntideriv_two,
    expPowAntideriv_three, expPowAntideriv_four] at h
  refine h.trans_eq ?_
  ring

private lemma integral_h_bjs_sub_one_at_three_mul_exp_two_le_aux {M' : ℝ} (h15 : 15 ≤ M') :
    Real.exp 2 * ∫ t in (3 : ℝ)..M', h_bjs (t - 1) ≤ (921371 / 1000000 : ℝ) := by
  have hcont : Continuous (fun t => h_bjs (t - 1)) :=
    h_bjs_continuous.comp (continuous_id.sub continuous_const)
  have hsplit1 : ∫ t in (3 : ℝ)..M', h_bjs (t - 1) =
      (∫ t in (3 : ℝ)..4, h_bjs (t - 1)) + ∫ t in (4 : ℝ)..M', h_bjs (t - 1) :=
    (integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) (3 : ℝ) 4)
      (hcont.intervalIntegrable (μ := volume) (4 : ℝ) M')).symm
  have h34 : ∫ t in (3 : ℝ)..4, h_bjs (t - 1) = Real.exp (-2) - Real.exp (-3) := by
    have hEq : EqOn (fun t => h_bjs (t - 1)) (fun t => Real.exp (-(t - 1))) (uIcc (3 : ℝ) 4) := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      exact h_bjs_of_two_to_three (by linarith [ht.1]) (by linarith [ht.2])
    rw [integral_congr hEq, integral_exp_neg_sub_one]
    norm_num
  have h4M' : ∫ t in (4 : ℝ)..M', h_bjs (t - 1) = 3 * ∫ x in (3 : ℝ)..(M' - 1), Real.exp (-x) / x := by
    have hEq : EqOn (fun t => h_bjs (t - 1)) (fun t => 3 * (Real.exp (-(t - 1)) / (t - 1)))
        (uIcc (4 : ℝ) M') := by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      dsimp only
      rw [h_bjs_of_three_le (by linarith [ht.1])]
      ring
    rw [integral_congr hEq, intervalIntegral.integral_const_mul]
    congr 1
    have hcomp := intervalIntegral.integral_comp_sub_right (fun x => Real.exp (-x) / x) (1 : ℝ)
      (a := (4 : ℝ)) (b := M')
    rw [show (4 : ℝ) - 1 = 3 by norm_num] at hcomp
    simpa [sub_eq_add_neg] using hcomp
  have hc_div : ∀ a b : ℝ, 3 ≤ a → a ≤ b →
      IntervalIntegrable (fun x => Real.exp (-x) / x) volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      fun x hx => ne_of_gt (by linarith [hx.1])
  have hsplit_E : ∫ x in (3 : ℝ)..(M' - 1), Real.exp (-x) / x =
      (∫ x in (3 : ℝ)..4, Real.exp (-x) / x) +
      (∫ x in (4 : ℝ)..6, Real.exp (-x) / x) +
      (∫ x in (6 : ℝ)..9, Real.exp (-x) / x) +
      (∫ x in (9 : ℝ)..14, Real.exp (-x) / x) +
      (∫ x in (14 : ℝ)..(M' - 1), Real.exp (-x) / x) := by
    have h1 := (integral_add_adjacent_intervals (hc_div 3 4 (by norm_num) (by norm_num))
      (hc_div 4 (M' - 1) (by norm_num) (by linarith))).symm
    have h2 := (integral_add_adjacent_intervals (hc_div 4 6 (by norm_num) (by norm_num))
      (hc_div 6 (M' - 1) (by norm_num) (by linarith))).symm
    have h3 := (integral_add_adjacent_intervals (hc_div 6 9 (by norm_num) (by norm_num))
      (hc_div 9 (M' - 1) (by norm_num) (by linarith))).symm
    have h4 := (integral_add_adjacent_intervals (hc_div 9 14 (by norm_num) (by norm_num))
      (hc_div 14 (M' - 1) (by norm_num) (by linarith))).symm
    linarith
  have b1 := integral_exp_div_3_4
  have b2 := integral_exp_div_4_6
  have b3 := integral_exp_div_6_9
  have b4 := integral_exp_div_9_14
  have b5 := integral_exp_neg_div_tail_le (a := 14) (M := M' - 1) (by norm_num) (by linarith)
  have hsum_bd : ∫ t in (3 : ℝ)..M', h_bjs (t - 1) ≤
      Real.exp (-2) - Real.exp (-3) +
        3 * ((2033 / 7203 : ℝ) * Real.exp (-3) - (627 / 2401 : ℝ) * Real.exp (-4) +
             ((521 / 2500 : ℝ) * Real.exp (-4) - (401 / 2500 : ℝ) * Real.exp (-6)) +
             ((14723 / 101250 : ℝ) * Real.exp (-6) - (10499 / 101250 : ℝ) * Real.exp (-9)) +
             ((84683 / 839523 : ℝ) * Real.exp (-9) - (170489 / 2518569 : ℝ) * Real.exp (-14)) +
             (1 / 14 : ℝ) * Real.exp (-14)) := by
    rw [hsplit1, h34, h4M', hsplit_E]
    linarith
  have h2m2 : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
  have h2m3 : Real.exp 2 * Real.exp (-3) = Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  have h2m4 : Real.exp 2 * Real.exp (-4) = Real.exp (-2) := by rw [← Real.exp_add]; norm_num
  have h2m6 : Real.exp 2 * Real.exp (-6) = Real.exp (-4) := by rw [← Real.exp_add]; norm_num
  have h2m9 : Real.exp 2 * Real.exp (-9) = Real.exp (-7) := by rw [← Real.exp_add]; norm_num
  have h2m14 : Real.exp 2 * Real.exp (-14) = Real.exp (-12) := by rw [← Real.exp_add]; norm_num
  have hcomb : Real.exp 2 * ∫ t in (3 : ℝ)..M', h_bjs (t - 1) ≤
      1 - Real.exp (-1) +
        (2033 / 2401 : ℝ) * Real.exp (-1) -
        (949737 / 6002500 : ℝ) * Real.exp (-2) -
        (607 / 13500 : ℝ) * Real.exp (-4) -
        (79999409 / 9444633750 : ℝ) * Real.exp (-7) +
        (131723 / 11753322 : ℝ) * Real.exp (-12) := by
    have hmul := mul_le_mul_of_nonneg_left hsum_bd (Real.exp_pos 2).le
    have hexp_eq :
        Real.exp 2 * (Real.exp (-2) - Real.exp (-3) +
          3 * ((2033 / 7203 : ℝ) * Real.exp (-3) - (627 / 2401 : ℝ) * Real.exp (-4) +
               ((521 / 2500 : ℝ) * Real.exp (-4) - (401 / 2500 : ℝ) * Real.exp (-6)) +
               ((14723 / 101250 : ℝ) * Real.exp (-6) - (10499 / 101250 : ℝ) * Real.exp (-9)) +
               ((84683 / 839523 : ℝ) * Real.exp (-9) - (170489 / 2518569 : ℝ) * Real.exp (-14)) +
               (1 / 14 : ℝ) * Real.exp (-14))) =
          1 - Real.exp (-1) +
            (2033 / 2401 : ℝ) * Real.exp (-1) -
            (949737 / 6002500 : ℝ) * Real.exp (-2) -
            (607 / 13500 : ℝ) * Real.exp (-4) -
            (79999409 / 9444633750 : ℝ) * Real.exp (-7) +
            (131723 / 11753322 : ℝ) * Real.exp (-12) := by
      ring_nf
      rw [h2m2, h2m3, h2m4, h2m6, h2m9, h2m14]
      ring
    linarith
  have h1 : Real.exp (-1) ≤ (10000000000 / 27182818283 : ℝ) := exp_neg_one_lt.le
  have h1_lo : (10000000000 / 27182818286 : ℝ) ≤ Real.exp (-1) := exp_neg_one_gt.le
  have he_nn : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have h2_lo : (10000000000 / 27182818286 : ℝ) ^ 2 ≤ Real.exp (-2) := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, exp_neg_nat_eq 2]
    exact pow_le_pow_left₀ (by norm_num) h1_lo 2
  have h4_lo : (10000000000 / 27182818286 : ℝ) ^ 4 ≤ Real.exp (-4) := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, exp_neg_nat_eq 4]
    exact pow_le_pow_left₀ (by norm_num) h1_lo 4
  have h7_lo : (10000000000 / 27182818286 : ℝ) ^ 7 ≤ Real.exp (-7) := by
    rw [show (-7 : ℝ) = -((7 : ℕ) : ℝ) by norm_num, exp_neg_nat_eq 7]
    exact pow_le_pow_left₀ (by norm_num) h1_lo 7
  have h12_hi : Real.exp (-12) ≤ (10000000000 / 27182818283 : ℝ) ^ 12 := by
    rw [show (-12 : ℝ) = -((12 : ℕ) : ℝ) by norm_num, exp_neg_nat_eq 12]
    exact pow_le_pow_left₀ he_nn h1 12
  have hnum : 1 - (10000000000 / 27182818286 : ℝ) +
        (2033 / 2401 : ℝ) * (10000000000 / 27182818283 : ℝ) -
        (949737 / 6002500 : ℝ) * (10000000000 / 27182818286 : ℝ) ^ 2 -
        (607 / 13500 : ℝ) * (10000000000 / 27182818286 : ℝ) ^ 4 -
        (79999409 / 9444633750 : ℝ) * (10000000000 / 27182818286 : ℝ) ^ 7 +
        (131723 / 11753322 : ℝ) * (10000000000 / 27182818283 : ℝ) ^ 12 ≤
      (921371 / 1000000 : ℝ) := by norm_num
  linarith

theorem integral_h_bjs_sub_one_at_three_mul_exp_two_le {M : ℝ} (_hM : 3 ≤ M) :
    Real.exp 2 * ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ (921371 / 1000000 : ℝ) := by
  have hcont : Continuous (fun t => h_bjs (t - 1)) :=
    h_bjs_continuous.comp (continuous_id.sub continuous_const)
  by_cases hM15 : M ≤ 15
  · have hadd := integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) (3 : ℝ) M)
      (hcont.intervalIntegrable (μ := volume) M (15 : ℝ))
    have hnn : 0 ≤ ∫ t in M..(15 : ℝ), h_bjs (t - 1) :=
      intervalIntegral.integral_nonneg hM15 fun t _ => h_bjs_nonneg _
    have hle : ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ ∫ t in (3 : ℝ)..15, h_bjs (t - 1) := by linarith
    have hstep := mul_le_mul_of_nonneg_left hle (Real.exp_pos 2).le
    exact hstep.trans (integral_h_bjs_sub_one_at_three_mul_exp_two_le_aux (by norm_num))
  · exact integral_h_bjs_sub_one_at_three_mul_exp_two_le_aux (le_of_not_ge hM15)

end ExpEnclosures

end

end BuchstabSwitching
