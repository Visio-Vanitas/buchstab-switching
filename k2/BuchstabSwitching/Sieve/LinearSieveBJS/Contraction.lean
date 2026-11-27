import BuchstabSwitching.Sieve.LinearSieveBJS.ExpEnclosures
import Mathlib.Tactic

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 2. Contraction of `h_bjs` (BJS v6 Lemmas 9 & 10) -/

section ContractionBounds

/-- Piecewise contraction factors `κ_{s₀}` and `\tilde{κ}` from BJS v6 Lemma 10. -/
def kappa2 : ℝ := 9607 / 10000
def kappa22 : ℝ := 9557 / 10000
def kappa24 : ℝ := 9457 / 10000
def kappa26 : ℝ := 9261 / 10000
def kappa28 : ℝ := 8914 / 10000
def kappa3 : ℝ := 8349 / 10000
def kappaTilde : ℝ := 9214 / 10000

/-- Shift contraction factor `γ_{s₀}` on `[s₀, s₀ + 0.2]` (`γ_{s₀} = exp (s₀ + 0.2 - 2)`)
and `γ_3 = 4 * exp 1 / 3` on `[3, ∞)`. -/
def gammaBJS (s₀ : ℝ) : ℝ :=
  if s₀ ≤ 14 / 5 then Real.exp (s₀ + 1 / 5 - 2) else 4 * Real.exp 1 / 3

theorem gammaBJS_two : gammaBJS 2 = Real.exp (1 / 5 : ℝ) := by
  have hle : (2 : ℝ) ≤ 14 / 5 := by norm_num
  simp only [gammaBJS, hle, ↓reduceIte]
  congr 1; norm_num

theorem gammaBJS_three : gammaBJS 3 = 4 * Real.exp 1 / 3 := by
  have hnot : ¬ (3 : ℝ) ≤ 14 / 5 := by norm_num
  simp only [gammaBJS, hnot, ↓reduceIte]

theorem h_bjs_sub_one_le_of_le {s s₀ : ℝ} (hs2 : 2 ≤ s) (hss₀ : s ≤ s₀) (hs₀3 : s₀ ≤ 3) :
    h_bjs (s - 1) ≤ Real.exp (s₀ - 2) * h_bjs s := by
  rw [h_bjs_of_le_two (by linarith), h_bjs_of_two_to_three hs2 (hss₀.trans hs₀3)]
  have hexp : Real.exp (-2) = Real.exp (s - 2) * Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le

theorem h_bjs_sub_one_le_step {s s₀ : ℝ} (hs2 : 2 ≤ s) (hss₀ : s ≤ s₀ + 1 / 5)
    (hs₀ : s₀ ≤ 14 / 5) :
    h_bjs (s - 1) ≤ Real.exp (s₀ + 1 / 5 - 2) * h_bjs s :=
  h_bjs_sub_one_le_of_le hs2 hss₀ (by linarith)

theorem h_bjs_sub_one_le_ge_three {s : ℝ} (hs3 : 3 ≤ s) :
    h_bjs (s - 1) ≤ (4 * Real.exp 1 / 3) * h_bjs s := by
  rw [h_bjs_of_three_le hs3]
  have hexp : Real.exp (-(s - 1)) = Real.exp 1 * Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  by_cases hs4 : s ≤ 4
  · rw [h_bjs_of_two_to_three (by linarith) (by linarith), hexp]
    have h4 : (1 : ℝ) ≤ (4 / s) := by
      rw [one_le_div (by linarith)]; exact hs4
    calc Real.exp 1 * Real.exp (-s)
        ≤ (4 / s) * (Real.exp 1 * Real.exp (-s)) :=
          le_mul_of_one_le_left (by positivity) h4
      _ = (4 * Real.exp 1 / 3) * ((3 / s) * Real.exp (-s)) := by
          have hs0 : s ≠ 0 := by linarith
          field_simp [hs0]
  · have hs4' : 4 ≤ s := le_of_not_ge hs4
    rw [h_bjs_of_three_le (by linarith), hexp]
    have hfrac : 3 / (s - 1) ≤ 4 / s := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    calc (3 / (s - 1)) * (Real.exp 1 * Real.exp (-s))
        ≤ (4 / s) * (Real.exp 1 * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = (4 * Real.exp 1 / 3) * ((3 / s) * Real.exp (-s)) := by
          have hs0 : s ≠ 0 := by linarith
          field_simp [hs0]

/-- **BJS v6 Lemma 9**: contraction of `h_bjs (s - 1)` relative to `h_bjs s` on `[2, s₀ + 0.2]`
and `[3, ∞)`, plus `(3 / s) * h_bjs 2 ≤ 3 * h_bjs s` on `[1, 3]`. -/
theorem h_bjs_sub_one_le :
    (∀ {s₀ s : ℝ}, s₀ ≤ 14 / 5 → 2 ≤ s → s ≤ s₀ + 1 / 5 →
      h_bjs (s - 1) ≤ gammaBJS s₀ * h_bjs s) ∧
    (∀ {s : ℝ}, 3 ≤ s → h_bjs (s - 1) ≤ gammaBJS 3 * h_bjs s) ∧
    (∀ {s : ℝ}, 1 ≤ s → s ≤ 3 → (3 / s) * h_bjs 2 ≤ 3 * h_bjs s) := by
  refine ⟨fun {s₀ s} hs₀ hs2 hss₀ => ?_, fun {s} hs3 => ?_, fun {s} hs1 hs3 => ?_⟩
  · simp only [gammaBJS, hs₀, ↓reduceIte]
    exact h_bjs_sub_one_le_step hs2 hss₀ hs₀
  · rw [gammaBJS_three]
    exact h_bjs_sub_one_le_ge_three hs3
  · rw [h_bjs_of_le_two (le_refl 2)]
    by_cases hs2 : s ≤ 2
    · rw [h_bjs_of_le_two hs2]
      have h3s : 3 / s ≤ 3 := div_le_self (by norm_num) hs1
      exact mul_le_mul_of_nonneg_right h3s (Real.exp_pos _).le
    · have hs2' : 2 ≤ s := le_of_not_ge hs2
      rw [h_bjs_of_two_to_three hs2' hs3]
      have h3e : Real.exp 1 ≤ 3 := exp_one_lt_d9'.le.trans (by norm_num)
      have hdec : (1 : ℝ) ≤ s * Real.exp (-(s - 2)) := by
        let w : ℝ → ℝ := fun t => t * Real.exp (-(t - 2))
        have hw_deriv : ∀ t ∈ uIcc s 3, HasDerivAt w ((1 - t) * Real.exp (-(t - 2))) t := by
          intro t _
          have hsub : HasDerivAt (fun x : ℝ => -(x - 2)) (-1) t := by
            refine ((hasDerivAt_id t).sub_const (2 : ℝ)).neg.congr_of_eventuallyEq
              (Eventually.of_forall fun _ => rfl) |>.congr_deriv (by ring)
          have hm := (hasDerivAt_id t).mul hsub.exp
          refine hm.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
          simp only [id_eq]
          ring
        have hcont_d : Continuous (fun t : ℝ => (1 - t) * Real.exp (-(t - 2))) := by fun_prop
        have hFTC := integral_eq_sub_of_hasDerivAt hw_deriv (hcont_d.intervalIntegrable s 3)
        have hnonpos : ∫ t in s..3, (1 - t) * Real.exp (-(t - 2)) ≤ 0 := by
          have hpos : 0 ≤ -∫ t in s..3, (1 - t) * Real.exp (-(t - 2)) := by
            rw [← intervalIntegral.integral_neg]
            refine intervalIntegral.integral_nonneg hs3 fun t ht => ?_
            have ht1 : 0 ≤ t - 1 := by linarith [ht.1]
            have hexp_nn : 0 ≤ Real.exp (-(t - 2)) := (Real.exp_pos _).le
            nlinarith
          linarith
        have hw3 : 1 ≤ w 3 := by
          dsimp [w]
          rw [show -(3 - 2 : ℝ) = -1 by norm_num, Real.exp_neg]
          have h1 : (1 : ℝ) / 3 ≤ (Real.exp 1)⁻¹ := by
            rw [one_div]
            exact inv_anti₀ (Real.exp_pos 1) h3e
          linarith
        linarith
      have hs0 : 0 < s := by linarith
      have hexp_le : Real.exp (s - 2) ≤ s := by
        have := mul_le_mul_of_nonneg_left hdec (Real.exp_pos (s - 2)).le
        rw [← mul_assoc, mul_comm (Real.exp (s - 2)) s, mul_assoc, ← Real.exp_add] at this
        simpa using this
      calc (3 / s) * Real.exp (-2)
          = (3 / s) * Real.exp (s - 2) * Real.exp (-s) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ (3 / s) * s * Real.exp (-s) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
        _ = 3 * Real.exp (-s) := by field_simp [hs0.ne']

theorem three_div_mul_h_bjs_two_le {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    (3 / s) * h_bjs 2 ≤ 3 * h_bjs s :=
  h_bjs_sub_one_le.2.2 hs1 hs3

private lemma H_bjs_le_from_endpoint {s₀ κ : ℝ} (hs₀2 : 2 ≤ s₀) (hs₀3 : s₀ ≤ 3)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hend : ∀ M : ℝ, 3 ≤ M → ∫ t in s₀..M, h_bjs (t - 1) ≤ κ * s₀ * h_bjs s₀)
    {s M : ℝ} (hs : s₀ ≤ s) (hs3 : s ≤ 3) (_hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ κ * s * h_bjs s := by
  have hcont : Continuous (fun t => h_bjs (t - 1)) :=
    h_bjs_continuous.comp (continuous_id.sub continuous_const)
  set M₁ : ℝ := max M 3
  have hle_M₁ : ∫ t in s..M, h_bjs (t - 1) ≤ ∫ t in s..M₁, h_bjs (t - 1) := by
    by_cases hM3 : M ≤ 3
    · have hM₁ : M₁ = 3 := max_eq_right hM3
      rw [hM₁]
      have hadd := integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) s M)
        (hcont.intervalIntegrable (μ := volume) M (3 : ℝ))
      have hnn : 0 ≤ ∫ t in M..(3 : ℝ), h_bjs (t - 1) :=
        intervalIntegral.integral_nonneg hM3 fun t _ => h_bjs_nonneg _
      linarith
    · have hM₁ : M₁ = M := max_eq_left (le_of_not_ge hM3)
      rw [hM₁]
  have h3M₁ : 3 ≤ M₁ := le_max_right M 3
  have hs₀M₁ : ∫ t in s₀..M₁, h_bjs (t - 1) =
      (∫ t in s₀..s, h_bjs (t - 1)) + ∫ t in s..M₁, h_bjs (t - 1) :=
    (integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) s₀ s)
      (hcont.intervalIntegrable (μ := volume) s M₁)).symm
  have hs₀s : ∫ t in s₀..s, h_bjs (t - 1) = (s - s₀) * Real.exp (-2) := by
    have hEq : EqOn (fun t => h_bjs (t - 1)) (fun _ => Real.exp (-2)) (uIcc s₀ s) := by
      intro t ht
      rw [uIcc_of_le hs] at ht
      exact h_bjs_of_le_two (by linarith [ht.2, hs3])
    rw [integral_congr hEq, intervalIntegral.integral_const, smul_eq_mul]
  let w : ℝ → ℝ := fun t => -t * Real.exp (-2) - κ * t * Real.exp (-t)
  have hw_deriv : ∀ t ∈ uIcc s₀ s,
      HasDerivAt w (κ * (t - 1) * Real.exp (-t) - Real.exp (-2)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => -x * Real.exp (-2)) (-Real.exp (-2)) t := by
      refine ((hasDerivAt_id t).neg.mul_const (Real.exp (-2))).congr_deriv ?_
      ring
    have hneg : HasDerivAt (fun x : ℝ => -x) (-1) t := (hasDerivAt_id t).neg
    have h2 : HasDerivAt (fun x : ℝ => (κ * x) * Real.exp (-x))
        (κ * Real.exp (-t) + (κ * t) * (-Real.exp (-t))) t := by
      have hkx : HasDerivAt (fun x : ℝ => κ * x) κ t := by
        simpa using (hasDerivAt_id t).const_mul κ
      have he := hneg.exp
      convert hkx.mul he using 1
      ring
    have hsub := h1.sub h2
    refine hsub.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    ring
  have hw_anti : w s ≤ w s₀ := by
    have hcont_d : Continuous (fun t => κ * (t - 1) * Real.exp (-t) - Real.exp (-2)) := by fun_prop
    have hFTC := integral_eq_sub_of_hasDerivAt hw_deriv (hcont_d.intervalIntegrable s₀ s)
    have hnonpos : ∫ t in s₀..s, (κ * (t - 1) * Real.exp (-t) - Real.exp (-2)) ≤ 0 := by
      have hpos : 0 ≤ -∫ t in s₀..s, (κ * (t - 1) * Real.exp (-t) - Real.exp (-2)) := by
        rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_nonneg hs fun t ht => ?_
        have ht2 : 2 ≤ t := by linarith [hs₀2, ht.1]
        have h1 : t - 1 ≤ Real.exp (t - 2) := by
          have := Real.add_one_le_exp (t - 2)
          linarith
        have h2 : (t - 1) * Real.exp (-t) ≤ Real.exp (-2) := by
          have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-t)).le
          rw [← Real.exp_add] at this
          simpa [show t - 2 + -t = -2 by ring] using this
        have h3 : κ * (t - 1) * Real.exp (-t) ≤ 1 * Real.exp (-2) := by
          have hexp_nn : 0 ≤ Real.exp (-2) := (Real.exp_pos (-2 : ℝ)).le
          have h12 : κ * (t - 1) * Real.exp (-t) ≤ κ * Real.exp (-2) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left h2 hκ0
          have h23 : κ * Real.exp (-2) ≤ 1 * Real.exp (-2) :=
            mul_le_mul_of_nonneg_right hκ1 hexp_nn
          exact h12.trans h23
        linarith
      linarith
    linarith
  have hend_M₁ := hend M₁ h3M₁
  rw [h_bjs_of_two_to_three hs₀2 hs₀3] at hend_M₁
  rw [h_bjs_of_two_to_three (hs₀2.trans hs) hs3]
  have hdiff_s : ∫ t in s..M₁, h_bjs (t - 1) ≤
      κ * s₀ * Real.exp (-s₀) - (s - s₀) * Real.exp (-2) := by linarith
  have hw_ineq : -s * Real.exp (-2) - κ * s * Real.exp (-s) ≤
      -s₀ * Real.exp (-2) - κ * s₀ * Real.exp (-s₀) := hw_anti
  linarith

theorem H_bjs_le_three {s M : ℝ} (hs : 3 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ kappa3 * s * h_bjs s := by
  have hcont : Continuous (fun t => h_bjs (t - 1)) :=
    h_bjs_continuous.comp (continuous_id.sub continuous_const)
  rw [h_bjs_of_three_le hs]
  have hrhs_eq : kappa3 * s * ((3 / s) * Real.exp (-s)) = 3 * kappa3 * Real.exp (-s) := by
    have hs0 : s ≠ 0 := by linarith
    field_simp [hs0]
  rw [hrhs_eq]
  rcases le_or_gt s 4 with hs4 | hs4
  · -- `3 ≤ s ≤ 4`
    set M₁ : ℝ := max M 4
    have hle_M₁ : ∫ t in s..M, h_bjs (t - 1) ≤ ∫ t in s..M₁, h_bjs (t - 1) := by
      by_cases hM4 : M ≤ 4
      · have hM₁ : M₁ = 4 := max_eq_right hM4
        rw [hM₁]
        have hadd := integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) s M)
          (hcont.intervalIntegrable (μ := volume) M (4 : ℝ))
        have hnn : 0 ≤ ∫ t in M..(4 : ℝ), h_bjs (t - 1) :=
          intervalIntegral.integral_nonneg hM4 fun t _ => h_bjs_nonneg _
        linarith
      · have hM₁ : M₁ = M := max_eq_left (le_of_not_ge hM4)
        rw [hM₁]
    have h4M₁ : 4 ≤ M₁ := le_max_right M 4
    have hsplit : ∫ t in (3 : ℝ)..M₁, h_bjs (t - 1) =
        (∫ t in (3 : ℝ)..s, h_bjs (t - 1)) + ∫ t in s..M₁, h_bjs (t - 1) :=
      (integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) (3 : ℝ) s)
        (hcont.intervalIntegrable (μ := volume) s M₁)).symm
    have h3s : ∫ t in (3 : ℝ)..s, h_bjs (t - 1) = Real.exp (-2) - Real.exp (-(s - 1)) := by
      have hEq : EqOn (fun t => h_bjs (t - 1)) (fun t => Real.exp (-(t - 1))) (uIcc (3 : ℝ) s) := by
        intro t ht
        rw [uIcc_of_le hs] at ht
        exact h_bjs_of_two_to_three (by linarith [ht.1]) (by linarith [ht.2])
      rw [integral_congr hEq, integral_exp_neg_sub_one]
      norm_num
    have h3M₁ := integral_h_bjs_sub_one_at_three_mul_exp_two_le (by linarith : 3 ≤ M₁)
    have h3M₁' : ∫ t in (3 : ℝ)..M₁, h_bjs (t - 1) ≤ (921371 / 1000000 : ℝ) * Real.exp (-2) := by
      have h1 := mul_le_mul_of_nonneg_left h3M₁ (Real.exp_pos (-2)).le
      rw [← mul_assoc, ← Real.exp_add] at h1
      simpa [mul_comm] using h1
    have h_diff : ∫ t in s..M, h_bjs (t - 1) ≤
        Real.exp (-(s - 1)) - (78629 / 1000000 : ℝ) * Real.exp (-2) := by linarith
    have hexp_s1 : Real.exp (-(s - 1)) = Real.exp 1 * Real.exp (-s) := by
      rw [← Real.exp_add]; ring_nf
    have hexp_2 : Real.exp (-2) = Real.exp (s - 2) * Real.exp (-s) := by
      rw [← Real.exp_add]; ring_nf
    have hs2_ge : Real.exp 1 ≤ Real.exp (s - 2) := Real.exp_le_exp.mpr (by linarith)
    rw [hexp_s1, hexp_2] at h_diff
    have h1 : Real.exp 1 * Real.exp (-s) - (78629 / 1000000 : ℝ) * (Real.exp (s - 2) * Real.exp (-s)) ≤
        (Real.exp 1 * (1 - 78629 / 1000000 : ℝ)) * Real.exp (-s) := by
      have hmul : (78629 / 1000000 : ℝ) * Real.exp 1 * Real.exp (-s) ≤
          (78629 / 1000000 : ℝ) * (Real.exp (s - 2) * Real.exp (-s)) := by
        nlinarith [Real.exp_pos (-s)]
      linarith
    have hcoeff : Real.exp 1 * (1 - 78629 / 1000000 : ℝ) ≤ 3 * kappa3 := by
      have he := exp_one_lt_d9'
      unfold kappa3
      linarith
    calc ∫ t in s..M, h_bjs (t - 1)
        ≤ (Real.exp 1 * (1 - 78629 / 1000000 : ℝ)) * Real.exp (-s) := by linarith
      _ ≤ (3 * kappa3) * Real.exp (-s) := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
  · have hs4' : 4 ≤ s := hs4.le
    rcases le_or_gt (426 / 100 : ℝ) s with hs426 | hs426
    · -- `4.26 ≤ s`: use `inv_mul_intervalIntegral_h_bjs_le_of_ge_four`
      have h4 := inv_mul_intervalIntegral_h_bjs_le_of_ge_four hs4' hM
      rw [h_bjs_of_three_le hs] at h4
      have hs0 : 0 < s := by linarith
      have hs1 : 0 < s - 1 := by linarith
      have hdiv : Real.exp 1 / (s - 1) ≤ kappa3 := by
        have h1 : Real.exp 1 / (s - 1) ≤ (27182818286 / 10000000000 : ℝ) / (326 / 100 : ℝ) :=
          div_le_div₀ (by positivity) exp_one_lt_d9'.le (by norm_num) (by linarith)
        unfold kappa3
        linarith
      have hmul := mul_le_mul_of_nonneg_left h4 hs0.le
      have hlhs : s * ((1 / s) * ∫ t in s..M, h_bjs (t - 1)) = ∫ t in s..M, h_bjs (t - 1) := by
        field_simp [hs0.ne']
      rw [hlhs] at hmul
      calc ∫ t in s..M, h_bjs (t - 1)
          ≤ s * ((Real.exp 1 / (s - 1)) * ((3 / s) * Real.exp (-s))) := hmul
        _ = (Real.exp 1 / (s - 1)) * (3 * Real.exp (-s)) := by field_simp [hs0.ne']
        _ ≤ kappa3 * (3 * Real.exp (-s)) := mul_le_mul_of_nonneg_right hdiv (by positivity)
        _ = 3 * kappa3 * Real.exp (-s) := by ring
    · -- `4 < s < 4.26`
      have hsplit : ∫ t in (3 : ℝ)..M, h_bjs (t - 1) =
          (∫ t in (3 : ℝ)..4, h_bjs (t - 1)) + (∫ t in (4 : ℝ)..s, h_bjs (t - 1)) +
            ∫ t in s..M, h_bjs (t - 1) := by
        have h1 := (integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) (3 : ℝ) 4)
          (hcont.intervalIntegrable (μ := volume) (4 : ℝ) M)).symm
        have h2 := (integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) (4 : ℝ) s)
          (hcont.intervalIntegrable (μ := volume) s M)).symm
        linarith
      have h34 : ∫ t in (3 : ℝ)..4, h_bjs (t - 1) = Real.exp (-2) - Real.exp (-3) := by
        have hEq : EqOn (fun t => h_bjs (t - 1)) (fun t => Real.exp (-(t - 1))) (uIcc (3 : ℝ) 4) := by
          intro t ht
          rw [uIcc_of_le (by norm_num)] at ht
          exact h_bjs_of_two_to_three (by linarith [ht.1]) (by linarith [ht.2])
        rw [integral_congr hEq, integral_exp_neg_sub_one]
        norm_num
      have h4s_lb : (3 / (326 / 100 : ℝ)) * (Real.exp (-3) - Real.exp (-(s - 1))) ≤
          ∫ t in (4 : ℝ)..s, h_bjs (t - 1) := by
        have hc1 : IntervalIntegrable (fun t => (3 / (326 / 100 : ℝ)) * Real.exp (-(t - 1))) volume 4 s :=
          (continuous_const.mul (Real.continuous_exp.comp (continuous_id.sub continuous_const).neg)).intervalIntegrable 4 s
        have hc2 := hcont.intervalIntegrable (μ := volume) (4 : ℝ) s
        have hmono : ∫ t in (4 : ℝ)..s, (3 / (326 / 100 : ℝ)) * Real.exp (-(t - 1)) ≤
            ∫ t in (4 : ℝ)..s, h_bjs (t - 1) := by
          refine intervalIntegral.integral_mono_on hs4' hc1 hc2 fun t ht => ?_
          rw [h_bjs_of_three_le (by linarith [ht.1])]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact div_le_div_of_nonneg_left (by norm_num) (by linarith [ht.1]) (by linarith [ht.2, hs426])
        rw [intervalIntegral.integral_const_mul, integral_exp_neg_sub_one] at hmono
        simpa [show (-(4 - 1) : ℝ) = -3 by norm_num] using hmono
      have h3M := integral_h_bjs_sub_one_at_three_mul_exp_two_le (by linarith : 3 ≤ M)
      have h3M' : ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ (921371 / 1000000 : ℝ) * Real.exp (-2) := by
        have h1 := mul_le_mul_of_nonneg_left h3M (Real.exp_pos (-2)).le
        rw [← mul_assoc, ← Real.exp_add] at h1
        simpa [mul_comm] using h1
      have h_ub : ∫ t in s..M, h_bjs (t - 1) ≤
          (Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * (Real.exp (-3) - Real.exp (-(s - 1))) := by linarith
      have h_coef_neg :
          (Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * Real.exp (-3) ≤ 0 := by
        have h3m2 : Real.exp (-3) = Real.exp (-1) * Real.exp (-2) := by rw [← Real.exp_add]; ring_nf
        rw [h3m2]
        have h_c : (1 - 3 / (326 / 100 : ℝ)) * Real.exp (-1) - 78629 / 1000000 ≤ 0 := by
          have := exp_neg_one_lt
          linarith
        nlinarith [Real.exp_pos (-2 : ℝ)]
      have h_es_ge : Real.exp 4 ≤ Real.exp s := Real.exp_le_exp.mpr hs4'
      have hmul_es :
          ((Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * Real.exp (-3)) * Real.exp s ≤
          ((Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * Real.exp (-3)) * Real.exp 4 :=
        mul_le_mul_of_nonpos_left h_es_ge h_coef_neg
      have h_eq4 :
          ((Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * Real.exp (-3)) * Real.exp 4 +
            (3 / (326 / 100 : ℝ)) * Real.exp 1 =
          Real.exp 1 - (78629 / 1000000 : ℝ) * Real.exp 2 := by
        have h1 : Real.exp (-3) * Real.exp 4 = Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have h2 : Real.exp (-2) * Real.exp 4 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
        ring_nf
        rw [h1, h2]
        ring
      have h_e12 : Real.exp 1 - (78629 / 1000000 : ℝ) * Real.exp 2 ≤ 3 * kappa3 := by
        have h2_gt : (27182818283 / 10000000000 : ℝ) ^ 2 ≤ Real.exp 2 := by
          have hsq : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
          rw [hsq]
          exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9'.le 2
        have he1 := exp_one_lt_d9'
        unfold kappa3
        linarith
      have hmul_es2 :
          ((Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * Real.exp (-3)) * Real.exp s +
            (3 / (326 / 100 : ℝ)) * Real.exp 1 ≤ 3 * kappa3 := by linarith
      have h_fin := mul_le_mul_of_nonneg_right hmul_es2 (Real.exp_pos (-s)).le
      have h_e_simp :
          (((Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * Real.exp (-3)) * Real.exp s +
            (3 / (326 / 100 : ℝ)) * Real.exp 1) * Real.exp (-s) =
          (Real.exp (-3) - (78629 / 1000000 : ℝ) * Real.exp (-2)) -
            (3 / (326 / 100 : ℝ)) * (Real.exp (-3) - Real.exp (-(s - 1))) := by
        have h1 : Real.exp (-3) * Real.exp s * Real.exp (-s) = Real.exp (-3) := by
          rw [mul_assoc, ← Real.exp_add]; simp
        have h2 : Real.exp (-2) * Real.exp s * Real.exp (-s) = Real.exp (-2) := by
          rw [mul_assoc, ← Real.exp_add]; simp
        have h3 : Real.exp 1 * Real.exp (-s) = Real.exp (-(s - 1)) := by
          rw [← Real.exp_add]; ring_nf
        ring_nf
        rw [show Real.exp (-3) * Real.exp s * Real.exp (-s) = Real.exp (-3) from h1,
          show Real.exp (-2) * Real.exp s * Real.exp (-s) = Real.exp (-2) from h2,
          show Real.exp 1 * Real.exp (-s) = Real.exp (1 - s) from by simpa [sub_eq_add_neg] using h3]
      linarith

private lemma H_bjs_le_at_two_point_aux {s₀ κ : ℝ} (hs₀2 : 2 ≤ s₀) (hs₀3 : s₀ ≤ 3)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ3 : kappa3 ≤ κ)
    (hend : (3 - s₀ + 921371 / 1000000 : ℝ) * Real.exp (s₀ - 2) ≤ κ * s₀)
    {s M : ℝ} (hs : s₀ ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ κ * s * h_bjs s := by
  by_cases hs3 : s ≤ 3
  · refine H_bjs_le_from_endpoint hs₀2 hs₀3 hκ0 hκ1 ?_ hs hs3 hM
    intro M' hM'3
    have hcont : Continuous (fun t => h_bjs (t - 1)) :=
      h_bjs_continuous.comp (continuous_id.sub continuous_const)
    have hsplit : ∫ t in s₀..M', h_bjs (t - 1) =
        (∫ t in s₀..3, h_bjs (t - 1)) + ∫ t in (3 : ℝ)..M', h_bjs (t - 1) :=
      (integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume) s₀ (3 : ℝ))
        (hcont.intervalIntegrable (μ := volume) (3 : ℝ) M')).symm
    have h1 : ∫ t in s₀..3, h_bjs (t - 1) = (3 - s₀) * Real.exp (-2) := by
      have hEq : EqOn (fun t => h_bjs (t - 1)) (fun _ => Real.exp (-2)) (uIcc s₀ 3) := by
        intro t ht
        rw [uIcc_of_le hs₀3] at ht
        exact h_bjs_of_le_two (by linarith [ht.2])
      rw [integral_congr hEq, intervalIntegral.integral_const, smul_eq_mul]
    have h2 : ∫ t in (3 : ℝ)..M', h_bjs (t - 1) ≤ (921371 / 1000000 : ℝ) * Real.exp (-2) := by
      have h3M := integral_h_bjs_sub_one_at_three_mul_exp_two_le hM'3
      have hmul := mul_le_mul_of_nonneg_left h3M (Real.exp_pos (-2)).le
      rw [← mul_assoc, ← Real.exp_add] at hmul
      simpa [mul_comm] using hmul
    rw [h_bjs_of_two_to_three hs₀2 hs₀3]
    have hsum : ∫ t in s₀..M', h_bjs (t - 1) ≤ (3 - s₀ + 921371 / 1000000 : ℝ) * Real.exp (-2) := by
      linarith
    have hexp2 : Real.exp (-2) = Real.exp (s₀ - 2) * Real.exp (-s₀) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp2] at hsum
    have hmul : (3 - s₀ + 921371 / 1000000 : ℝ) * Real.exp (s₀ - 2) * Real.exp (-s₀) ≤
        κ * s₀ * Real.exp (-s₀) :=
      mul_le_mul_of_nonneg_right hend (Real.exp_pos (-s₀)).le
    linarith
  · have hs3' : 3 ≤ s := le_of_not_ge hs3
    have h3 := H_bjs_le_three hs3' hM
    have hmul : kappa3 * s * h_bjs s ≤ κ * s * h_bjs s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ3 (by linarith)) (h_bjs_nonneg s)
    exact h3.trans hmul

theorem H_bjs_le_two {s M : ℝ} (hs : 2 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ kappa2 * s * h_bjs s := by
  refine H_bjs_le_at_two_point_aux (by norm_num) (by norm_num) (by unfold kappa2; norm_num)
    (by unfold kappa2; norm_num) (by unfold kappa3 kappa2; norm_num) ?_ hs hM
  unfold kappa2; norm_num

theorem H_bjs_le_two_two {s M : ℝ} (hs : 22 / 10 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ kappa22 * s * h_bjs s := by
  refine H_bjs_le_at_two_point_aux (by norm_num) (by norm_num) (by unfold kappa22; norm_num)
    (by unfold kappa22; norm_num) (by unfold kappa3 kappa22; norm_num) ?_ hs hM
  rw [show (22 / 10 : ℝ) - 2 = 1 / 5 by norm_num]
  have h1 := exp_one_fifth_lt
  unfold kappa22
  linarith

theorem H_bjs_le_two_four {s M : ℝ} (hs : 24 / 10 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ kappa24 * s * h_bjs s := by
  refine H_bjs_le_at_two_point_aux (by norm_num) (by norm_num) (by unfold kappa24; norm_num)
    (by unfold kappa24; norm_num) (by unfold kappa3 kappa24; norm_num) ?_ hs hM
  rw [show (24 / 10 : ℝ) - 2 = 2 / 5 by norm_num]
  have h1 := exp_two_fifths_lt
  unfold kappa24
  nlinarith

theorem H_bjs_le_two_six {s M : ℝ} (hs : 26 / 10 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ kappa26 * s * h_bjs s := by
  refine H_bjs_le_at_two_point_aux (by norm_num) (by norm_num) (by unfold kappa26; norm_num)
    (by unfold kappa26; norm_num) (by unfold kappa3 kappa26; norm_num) ?_ hs hM
  rw [show (26 / 10 : ℝ) - 2 = 3 / 5 by norm_num]
  have h1 := exp_three_fifths_lt
  unfold kappa26
  nlinarith

theorem H_bjs_le_two_eight {s M : ℝ} (hs : 28 / 10 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ kappa28 * s * h_bjs s := by
  refine H_bjs_le_at_two_point_aux (by norm_num) (by norm_num) (by unfold kappa28; norm_num)
    (by unfold kappa28; norm_num) (by unfold kappa3 kappa28; norm_num) ?_ hs hM
  rw [show (28 / 10 : ℝ) - 2 = 4 / 5 by norm_num]
  have h1 := exp_four_fifths_lt
  unfold kappa28
  nlinarith

theorem H_bjs_three_le_tilde {s M : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hM : 3 ≤ M) :
    ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ kappaTilde * s * h_bjs s := by
  have h3M := integral_h_bjs_sub_one_at_three_mul_exp_two_le hM
  have hle : ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ kappaTilde * Real.exp (-2) := by
    have h1 := mul_le_mul_of_nonneg_left h3M (Real.exp_pos (-2)).le
    rw [← mul_assoc, ← Real.exp_add] at h1
    have h2 : ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ (921371 / 1000000 : ℝ) * Real.exp (-2) := by
      simpa [mul_comm] using h1
    have h3 : (921371 / 1000000 : ℝ) ≤ kappaTilde := by unfold kappaTilde; norm_num
    exact h2.trans (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le)
  by_cases hs2 : s ≤ 2
  · rw [h_bjs_of_le_two hs2]
    have hmul : kappaTilde * Real.exp (-2) ≤ kappaTilde * s * Real.exp (-2) := by
      have hk : 0 ≤ kappaTilde := by unfold kappaTilde; norm_num
      have h1 : Real.exp (-2) ≤ s * Real.exp (-2) := by nlinarith [Real.exp_pos (-2 : ℝ)]
      calc kappaTilde * Real.exp (-2) ≤ kappaTilde * (s * Real.exp (-2)) :=
            mul_le_mul_of_nonneg_left h1 hk
        _ = kappaTilde * s * Real.exp (-2) := by ring
    exact hle.trans hmul
  · have hs2' : 2 ≤ s := le_of_not_ge hs2
    have h3 := H_bjs_le_three (le_refl 3) hM
    rw [h_bjs_of_three_le (le_refl 3), show kappa3 * 3 * ((3 / 3) * Real.exp (-3)) = 3 * kappa3 * Real.exp (-3) by ring] at h3
    rw [h_bjs_of_two_to_three hs2' hs3]
    -- On `[2, 3]`, `s * exp (-s)` is antitone, so `3 * exp (-3) ≤ s * exp (-s)`
    have hmono : 3 * Real.exp (-3) ≤ s * Real.exp (-s) := by
      let w : ℝ → ℝ := fun t => t * Real.exp (-t)
      have hw_deriv : ∀ t ∈ uIcc s 3, HasDerivAt w ((1 - t) * Real.exp (-t)) t := by
        intro t _
        have hneg : HasDerivAt (fun x : ℝ => -x) (-1) t := (hasDerivAt_id t).neg
        have hm := (hasDerivAt_id t).mul hneg.exp
        refine hm.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
        simp only [id_eq]; ring
      have hcont_d : Continuous (fun t : ℝ => (1 - t) * Real.exp (-t)) := by fun_prop
      have hFTC := integral_eq_sub_of_hasDerivAt hw_deriv (hcont_d.intervalIntegrable s 3)
      have hnonpos : ∫ t in s..3, (1 - t) * Real.exp (-t) ≤ 0 := by
        have hpos : 0 ≤ -∫ t in s..3, (1 - t) * Real.exp (-t) := by
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_nonneg hs3 fun t ht => ?_
          have ht1 : 0 ≤ t - 1 := by linarith [ht.1]
          nlinarith [Real.exp_pos (-t)]
        linarith
      linarith
    have hk_le : kappa3 ≤ kappaTilde := by unfold kappa3 kappaTilde; norm_num
    calc ∫ t in (3 : ℝ)..M, h_bjs (t - 1)
        ≤ 3 * kappa3 * Real.exp (-3) := h3
      _ = kappa3 * (3 * Real.exp (-3)) := by ring
      _ ≤ kappaTilde * (s * Real.exp (-s)) := by
          refine mul_le_mul hk_le hmono (by positivity) (by unfold kappaTilde; norm_num)
      _ = kappaTilde * s * Real.exp (-s) := by ring

/-- **BJS v6 Lemma 10**: piecewise bounds `∫ t in s..M, h_bjs (t - 1) ≤ κ_{s₀} * s * h_bjs s`
for `s₀ ∈ {2, 2.2, 2.4, 2.6, 2.8, 3}` and `H(3) ≤ 0.9214 * s * h_bjs s` on `[1, 3]`. -/
theorem H_bjs_le :
    (∀ {s M : ℝ}, 2 ≤ s → s ≤ M → ∫ t in s..M, h_bjs (t - 1) ≤ (9607 / 10000 : ℝ) * s * h_bjs s) ∧
    (∀ {s M : ℝ}, 22 / 10 ≤ s → s ≤ M → ∫ t in s..M, h_bjs (t - 1) ≤ (9557 / 10000 : ℝ) * s * h_bjs s) ∧
    (∀ {s M : ℝ}, 24 / 10 ≤ s → s ≤ M → ∫ t in s..M, h_bjs (t - 1) ≤ (9457 / 10000 : ℝ) * s * h_bjs s) ∧
    (∀ {s M : ℝ}, 26 / 10 ≤ s → s ≤ M → ∫ t in s..M, h_bjs (t - 1) ≤ (9261 / 10000 : ℝ) * s * h_bjs s) ∧
    (∀ {s M : ℝ}, 28 / 10 ≤ s → s ≤ M → ∫ t in s..M, h_bjs (t - 1) ≤ (8914 / 10000 : ℝ) * s * h_bjs s) ∧
    (∀ {s M : ℝ}, 3 ≤ s → s ≤ M → ∫ t in s..M, h_bjs (t - 1) ≤ (8349 / 10000 : ℝ) * s * h_bjs s) ∧
    (∀ {s M : ℝ}, 1 ≤ s → s ≤ 3 → 3 ≤ M →
      ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ (9214 / 10000 : ℝ) * s * h_bjs s) :=
  ⟨fun hs hM => H_bjs_le_two hs hM,
   fun hs hM => H_bjs_le_two_two hs hM,
   fun hs hM => H_bjs_le_two_four hs hM,
   fun hs hM => H_bjs_le_two_six hs hM,
   fun hs hM => H_bjs_le_two_eight hs hM,
   fun hs hM => H_bjs_le_three hs hM,
   fun hs1 hs3 hM => H_bjs_three_le_tilde hs1 hs3 hM⟩

end ContractionBounds

end

end BuchstabSwitching
