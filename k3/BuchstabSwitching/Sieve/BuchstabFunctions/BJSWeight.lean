import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# Linear Sieve Constants and BJS Error Weight `h_bjs`

Formalizes the Euler–Mascheroni constant `eGamma`, the Buchstab normalization constant
`cBuchstab = 2 * exp γ`, and the BJS Lyapunov-type error weight `h_bjs`, including positivity,
antitonicity, continuity, and integral comparison bounds for `(1 / s) * ∫_s^M h_bjs (t - 1) dt`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

section Constants

/-- Euler–Mascheroni constant `γ`. -/
noncomputable def eGamma : ℝ := Real.eulerMascheroniConstant

/-- Standard linear-sieve normalization constant `2 * exp γ`. -/
noncomputable def cBuchstab : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

theorem cBuchstab_pos : 0 < cBuchstab := by
  unfold cBuchstab
  positivity

theorem three_lt_cBuchstab : 3 < cBuchstab := by
  unfold cBuchstab
  have hγ : (1 / 2 : ℝ) < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hexp1 : (9 / 4 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hsq : (3 / 2 : ℝ) ^ 2 < (Real.exp (1 / 2 : ℝ)) ^ 2 := by
    rw [← Real.exp_natCast_mul]
    norm_num
    exact hexp1
  have hhalf : (3 / 2 : ℝ) < Real.exp (1 / 2 : ℝ) := by
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hmono : Real.exp (1 / 2 : ℝ) < Real.exp Real.eulerMascheroniConstant :=
    Real.exp_lt_exp.mpr hγ
  linarith

end Constants

section BJSWeight

/-- BJS Lyapunov-type error weight `h(s)`: `e⁻²` for `s ≤ 2`, `e⁻ˢ` for `2 < s ≤ 3`, and
`(3 / s) * e⁻ˢ` for `s > 3`. -/
noncomputable def h_bjs (s : ℝ) : ℝ :=
  if s ≤ 2 then Real.exp (-2)
  else if s ≤ 3 then Real.exp (-s)
  else (3 / s) * Real.exp (-s)

@[simp]
theorem h_bjs_of_le_two {s : ℝ} (hs : s ≤ 2) : h_bjs s = Real.exp (-2) := by
  simp [h_bjs, hs]

theorem h_bjs_of_two_to_three {s : ℝ} (h2 : 2 ≤ s) (h3 : s ≤ 3) :
    h_bjs s = Real.exp (-s) := by
  by_cases hs : s ≤ 2
  · have : s = 2 := le_antisymm hs h2
    subst this
    simp [h_bjs]
  · simp [h_bjs, hs, h3]

theorem h_bjs_of_three_le {s : ℝ} (hs : 3 ≤ s) :
    h_bjs s = (3 / s) * Real.exp (-s) := by
  by_cases h3 : s ≤ 3
  · have : s = 3 := le_antisymm h3 hs
    subst this
    have hnot : ¬ (3 : ℝ) ≤ 2 := by norm_num
    simp [h_bjs, hnot]
  · have hnot2 : ¬ s ≤ 2 := by linarith
    simp [h_bjs, hnot2, h3]

theorem h_bjs_pos (s : ℝ) : 0 < h_bjs s := by
  unfold h_bjs
  split_ifs with h2 h3
  · exact Real.exp_pos _
  · exact Real.exp_pos _
  · have hs3 : 3 < s := lt_of_not_ge h3
    positivity

theorem h_bjs_nonneg (s : ℝ) : 0 ≤ h_bjs s := (h_bjs_pos s).le

theorem h_bjs_antitone : Antitone h_bjs := by
  intro a b hab
  by_cases ha2 : a ≤ 2
  · rw [h_bjs_of_le_two ha2]
    by_cases hb2 : b ≤ 2
    · rw [h_bjs_of_le_two hb2]
    · have hb2' : 2 ≤ b := le_of_not_ge hb2
      by_cases hb3 : b ≤ 3
      · rw [h_bjs_of_two_to_three hb2' hb3]
        exact Real.exp_le_exp.mpr (by linarith)
      · have hb3' : 3 ≤ b := le_of_not_ge hb3
        rw [h_bjs_of_three_le hb3']
        have h3b : 3 / b ≤ 1 := div_le_one_of_le₀ hb3' (by linarith)
        have hexp : Real.exp (-b) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
        calc (3 / b) * Real.exp (-b)
            ≤ 1 * Real.exp (-b) := mul_le_mul_of_nonneg_right h3b (Real.exp_pos _).le
          _ = Real.exp (-b) := one_mul _
          _ ≤ Real.exp (-2) := hexp
  · have ha2' : 2 ≤ a := le_of_not_ge ha2
    have hb2' : 2 ≤ b := le_trans ha2' hab
    by_cases ha3 : a ≤ 3
    · rw [h_bjs_of_two_to_three ha2' ha3]
      by_cases hb3 : b ≤ 3
      · rw [h_bjs_of_two_to_three hb2' hb3]
        exact Real.exp_le_exp.mpr (by linarith)
      · have hb3' : 3 ≤ b := le_of_not_ge hb3
        rw [h_bjs_of_three_le hb3']
        have h3b : 3 / b ≤ 1 := div_le_one_of_le₀ hb3' (by linarith)
        have hexp : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
        calc (3 / b) * Real.exp (-b)
            ≤ 1 * Real.exp (-b) := mul_le_mul_of_nonneg_right h3b (Real.exp_pos _).le
          _ = Real.exp (-b) := one_mul _
          _ ≤ Real.exp (-a) := hexp
    · have ha3' : 3 ≤ a := le_of_not_ge ha3
      have hb3' : 3 ≤ b := le_trans ha3' hab
      rw [h_bjs_of_three_le ha3', h_bjs_of_three_le hb3']
      refine mul_le_mul ?_ (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hab

theorem h_bjs_antitoneOn_zero : AntitoneOn h_bjs (Set.Ici 0) :=
  h_bjs_antitone.antitoneOn _

theorem h_bjs_antitoneOn_one : AntitoneOn h_bjs (Set.Ici 1) :=
  h_bjs_antitone.antitoneOn _

theorem h_bjs_continuous : Continuous h_bjs := by
  let g2 : ℝ → ℝ := fun s =>
    if s ≤ 3 then Real.exp (-s)
    else (3 / max s 1) * Real.exp (-s)
  have hg2_cont : Continuous g2 := by
    refine Continuous.if_le (Real.continuous_exp.comp continuous_neg) ?_ continuous_id continuous_const
      (fun s hs => by rw [hs]; norm_num)
    refine Continuous.mul ?_ (Real.continuous_exp.comp continuous_neg)
    refine continuous_const.div (continuous_id.max continuous_const) fun s =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right s 1))
  let g : ℝ → ℝ := fun s => if s ≤ 2 then Real.exp (-2) else g2 s
  have hg_cont : Continuous g := by
    refine Continuous.if_le continuous_const hg2_cont continuous_id continuous_const fun s hs => ?_
    rw [hs]
    have h23 : (2 : ℝ) ≤ 3 := by norm_num
    simp [g2, h23]
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s < 2
  · have hev : h_bjs =ᶠ[𝓝 s] (fun _ => Real.exp (-2)) := by
      filter_upwards [Iio_mem_nhds hs] with x hx
      exact h_bjs_of_le_two (le_of_lt hx)
    exact continuousAt_const.congr hev.symm
  · have hs1 : 1 < s := by linarith [le_of_not_gt hs]
    have hev : h_bjs =ᶠ[𝓝 s] g := by
      filter_upwards [Ioi_mem_nhds hs1] with x hx
      have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
      simp only [h_bjs, g, g2, max_eq_left hx1]
    exact hg_cont.continuousAt.congr hev.symm

theorem h_bjs_continuousOn : ContinuousOn h_bjs (Set.Ici 1) :=
  h_bjs_continuous.continuousOn

theorem h_bjs_sub_one_le_exp {t : ℝ} (ht : 3 ≤ t) :
    h_bjs (t - 1) ≤ Real.exp (-(t - 1)) := by
  by_cases ht4 : t ≤ 4
  · rw [h_bjs_of_two_to_three (by linarith) (by linarith)]
  · have ht4' : 4 ≤ t := le_of_not_ge ht4
    rw [h_bjs_of_three_le (by linarith)]
    have hdiv : 3 / (t - 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    calc (3 / (t - 1)) * Real.exp (-(t - 1))
        ≤ 1 * Real.exp (-(t - 1)) := mul_le_mul_of_nonneg_right hdiv (Real.exp_pos _).le
      _ = Real.exp (-(t - 1)) := one_mul _

theorem integral_exp_neg_sub_one (a b : ℝ) :
    ∫ t in a..b, Real.exp (-(t - 1)) = Real.exp (-(a - 1)) - Real.exp (-(b - 1)) := by
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun x : ℝ => -Real.exp (-(x - 1))) (Real.exp (-(t - 1))) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => -(x - 1)) (-1) t := by
      convert ((hasDerivAt_id t).sub_const (1 : ℝ)).neg using 1
      ext x; simp
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(x - 1))) (Real.exp (-(t - 1)) * (-1)) t := by
      convert h1.exp using 1
    convert h2.neg using 1
    ring
  have hint : IntervalIntegrable (fun t => Real.exp (-(t - 1))) volume a b :=
    ((Real.continuous_exp.comp (continuous_id.sub continuous_const).neg).continuousOn).intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

theorem intervalIntegral_h_bjs_sub_one_le_of_ge_three {s M : ℝ} (hs : 3 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ Real.exp (-(s - 1)) - Real.exp (-(M - 1)) := by
  have hc1 : IntervalIntegrable (fun t => h_bjs (t - 1)) volume s M :=
    (h_bjs_continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable s M
  have hc2 : IntervalIntegrable (fun t => Real.exp (-(t - 1))) volume s M :=
    (Real.continuous_exp.comp (continuous_id.sub continuous_const).neg).intervalIntegrable s M
  calc ∫ t in s..M, h_bjs (t - 1)
      ≤ ∫ t in s..M, Real.exp (-(t - 1)) := by
        refine integral_mono_on hM hc1 hc2 fun t ht => ?_
        exact h_bjs_sub_one_le_exp (by linarith [ht.1])
    _ = Real.exp (-(s - 1)) - Real.exp (-(M - 1)) := integral_exp_neg_sub_one s M

theorem intervalIntegral_h_bjs_sub_one_le_exp_of_ge_three {s M : ℝ} (hs : 3 ≤ s) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ Real.exp (-(s - 1)) := by
  have h := intervalIntegral_h_bjs_sub_one_le_of_ge_three hs hM
  linarith [Real.exp_pos (-(M - 1))]

theorem inv_mul_intervalIntegral_h_bjs_le_of_ge_three {s M : ℝ} (hs : 3 ≤ s) (hM : s ≤ M) :
    (1 / s) * ∫ t in s..M, h_bjs (t - 1) ≤ (Real.exp 1 / 3) * h_bjs s := by
  have hI : ∫ t in s..M, h_bjs (t - 1) ≤ Real.exp (-(s - 1)) :=
    intervalIntegral_h_bjs_sub_one_le_exp_of_ge_three hs hM
  have hexp : Real.exp (-(s - 1)) = Real.exp 1 * Real.exp (-s) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h_bjs_of_three_le hs]
  have hs0 : 0 < s := by linarith
  calc (1 / s) * ∫ t in s..M, h_bjs (t - 1)
      ≤ (1 / s) * Real.exp (-(s - 1)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (1 / s) * (Real.exp 1 * Real.exp (-s)) := by rw [hexp]
    _ = (Real.exp 1 / 3) * ((3 / s) * Real.exp (-s)) := by field_simp

theorem inv_mul_intervalIntegral_h_bjs_le_of_ge_four {s M : ℝ} (hs : 4 ≤ s) (hM : s ≤ M) :
    (1 / s) * ∫ t in s..M, h_bjs (t - 1) ≤ (Real.exp 1 / (s - 1)) * h_bjs s := by
  have hc1 : IntervalIntegrable (fun t => h_bjs (t - 1)) volume s M :=
    (h_bjs_continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable s M
  have hc2 : IntervalIntegrable (fun t => (3 / (s - 1)) * Real.exp (-(t - 1))) volume s M :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_id.sub continuous_const).neg)).intervalIntegrable s M
  have hs1 : 0 < s - 1 := by linarith
  have hI : ∫ t in s..M, h_bjs (t - 1) ≤ (3 / (s - 1)) * Real.exp (-(s - 1)) := by
    calc ∫ t in s..M, h_bjs (t - 1)
        ≤ ∫ t in s..M, (3 / (s - 1)) * Real.exp (-(t - 1)) := by
          refine integral_mono_on hM hc1 hc2 fun t ht => ?_
          have ht3 : 3 ≤ t - 1 := by linarith [ht.1]
          rw [h_bjs_of_three_le ht3]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact div_le_div_of_nonneg_left (by norm_num) hs1 (by linarith [ht.1])
      _ = (3 / (s - 1)) * ∫ t in s..M, Real.exp (-(t - 1)) := intervalIntegral.integral_const_mul _ _
      _ = (3 / (s - 1)) * (Real.exp (-(s - 1)) - Real.exp (-(M - 1))) := by
          rw [integral_exp_neg_sub_one]
      _ ≤ (3 / (s - 1)) * Real.exp (-(s - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [Real.exp_pos (-(M - 1))]
  have hexp : Real.exp (-(s - 1)) = Real.exp 1 * Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  rw [h_bjs_of_three_le (by linarith)]
  have hs0 : 0 < s := by linarith
  calc (1 / s) * ∫ t in s..M, h_bjs (t - 1)
      ≤ (1 / s) * ((3 / (s - 1)) * Real.exp (-(s - 1))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (Real.exp 1 / (s - 1)) * ((3 / s) * Real.exp (-s)) := by
        rw [hexp]; field_simp

theorem intervalIntegral_h_bjs_sub_one_le_of_le_three {s M : ℝ} (hs : s ≤ 3) (hM : s ≤ M) :
    ∫ t in s..M, h_bjs (t - 1) ≤ (4 - s) * Real.exp (-2) := by
  have hint_fn : Continuous (fun t => h_bjs (t - 1)) :=
    h_bjs_continuous.comp (continuous_id.sub continuous_const)
  by_cases hM3 : M ≤ 3
  · have hEq : EqOn (fun t => h_bjs (t - 1)) (fun _ => Real.exp (-2)) (uIcc s M) := by
      intro t ht
      rw [uIcc_of_le hM] at ht
      exact h_bjs_of_le_two (by linarith [ht.2])
    rw [integral_congr hEq, intervalIntegral.integral_const, smul_eq_mul]
    nlinarith [Real.exp_pos (-2 : ℝ)]
  · have h3M : 3 ≤ M := le_of_not_ge hM3
    have hsplit : ∫ t in s..M, h_bjs (t - 1) =
        (∫ t in s..3, h_bjs (t - 1)) + ∫ t in (3 : ℝ)..M, h_bjs (t - 1) :=
      (integral_add_adjacent_intervals (hint_fn.intervalIntegrable s 3)
        (hint_fn.intervalIntegrable 3 M)).symm
    have hEq1 : EqOn (fun t => h_bjs (t - 1)) (fun _ => Real.exp (-2)) (uIcc s 3) := by
      intro t ht
      rw [uIcc_of_le hs] at ht
      exact h_bjs_of_le_two (by linarith [ht.2])
    have hI1 : ∫ t in s..3, h_bjs (t - 1) = (3 - s) * Real.exp (-2) := by
      rw [integral_congr hEq1, intervalIntegral.integral_const, smul_eq_mul]
    have hI2 : ∫ t in (3 : ℝ)..M, h_bjs (t - 1) ≤ Real.exp (-2) := by
      have h := intervalIntegral_h_bjs_sub_one_le_exp_of_ge_three (le_refl 3) h3M
      rwa [show (-(3 - 1) : ℝ) = -2 by norm_num] at h
    linarith

/-- Key inequality `(4 - s) * exp (-2) ≤ s * exp (-s)` for `2 ≤ s ≤ 3`. -/
theorem four_sub_mul_exp_neg_two_le {s : ℝ} (h2 : 2 ≤ s) (_h3 : s ≤ 3) :
    (4 - s) * Real.exp (-2) ≤ s * Real.exp (-s) := by
  let g : ℝ → ℝ := fun t => (4 - t) * Real.exp (t - 2) - t
  have hg_deriv : ∀ t ∈ uIcc 2 s, HasDerivAt g ((3 - t) * Real.exp (t - 2) - 1) t := by
    intro t _
    have h4t : HasDerivAt (fun x : ℝ => 4 - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (4 : ℝ)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (x - 2)) (Real.exp (t - 2)) t := by
      have hsub := (hasDerivAt_id t).sub_const (2 : ℝ)
      simpa using hsub.exp
    have hmul := h4t.mul hexp
    have hsub := hmul.sub (hasDerivAt_id t)
    refine hsub.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · ring
    · simp [g]
  have hg_nonpos : ∀ t ∈ Icc 2 s, (3 - t) * Real.exp (t - 2) - 1 ≤ 0 := by
    intro t _
    have h1' : 3 - t ≤ Real.exp (-(t - 2)) := by
      have := Real.add_one_le_exp (-(t - 2))
      linarith
    have hexp_pos : 0 < Real.exp (t - 2) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right h1' hexp_pos.le
    rw [← Real.exp_add] at hmul
    simp only [neg_add_cancel, Real.exp_zero] at hmul
    linarith
  have hcont_d : Continuous (fun t : ℝ => (3 - t) * Real.exp (t - 2) - 1) :=
    ((continuous_const.sub continuous_id).mul
      (Real.continuous_exp.comp (continuous_id.sub continuous_const))).sub continuous_const
  have hg_int : ∫ t in (2 : ℝ)..s, ((3 - t) * Real.exp (t - 2) - 1) = g s - g 2 :=
    integral_eq_sub_of_hasDerivAt hg_deriv (hcont_d.intervalIntegrable 2 s)
  have hg_le : g s ≤ g 2 := by
    have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..s, -((3 - t) * Real.exp (t - 2) - 1) := by
      refine intervalIntegral.integral_nonneg h2 fun t ht => ?_
      linarith [hg_nonpos t ht]
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith [hg_int]
  have hg2 : g 2 = 0 := by
    dsimp [g]
    norm_num
  have hgs : (4 - s) * Real.exp (s - 2) ≤ s := by
    have : g s ≤ 0 := hg_le.trans_eq hg2
    dsimp [g] at this
    linarith
  have hmul := mul_le_mul_of_nonneg_right hgs (Real.exp_pos (-s)).le
  calc (4 - s) * Real.exp (-2)
      = (4 - s) * Real.exp (s - 2) * Real.exp (-s) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ s * Real.exp (-s) := hmul

theorem inv_mul_intervalIntegral_h_bjs_le {s M : ℝ} (hs : 2 ≤ s) (hM : s ≤ M) :
    (1 / s) * ∫ t in s..M, h_bjs (t - 1) ≤ h_bjs s := by
  by_cases hs3 : s ≤ 3
  · rw [h_bjs_of_two_to_three hs hs3]
    have hI := intervalIntegral_h_bjs_sub_one_le_of_le_three hs3 hM
    have h4 := four_sub_mul_exp_neg_two_le hs hs3
    have hs0 : 0 < s := by linarith
    calc (1 / s) * ∫ t in s..M, h_bjs (t - 1)
        ≤ (1 / s) * ((4 - s) * Real.exp (-2)) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ ≤ (1 / s) * (s * Real.exp (-s)) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = Real.exp (-s) := by field_simp
  · have hs3' : 3 ≤ s := le_of_not_ge hs3
    have h1 := inv_mul_intervalIntegral_h_bjs_le_of_ge_three hs3' hM
    have hexp_lt : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have hdiv : Real.exp 1 / 3 ≤ 1 := div_le_one_of_le₀ hexp_lt.le (by norm_num)
    calc (1 / s) * ∫ t in s..M, h_bjs (t - 1)
        ≤ (Real.exp 1 / 3) * h_bjs s := h1
      _ ≤ 1 * h_bjs s := mul_le_mul_of_nonneg_right hdiv (h_bjs_nonneg s)
      _ = h_bjs s := one_mul _

theorem inv_mul_intervalIntegral_h_bjs_le_of_one_to_two {s M : ℝ}
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hM : s ≤ M) :
    (1 / s) * ∫ t in s..M, h_bjs (t - 1) ≤ 3 * h_bjs s := by
  have hI := intervalIntegral_h_bjs_sub_one_le_of_le_three (by linarith) hM
  rw [h_bjs_of_le_two hs2]
  have hs0 : 0 < s := by linarith
  have h4s : (4 - s) / s ≤ 3 := by
    rw [div_le_iff₀ hs0]
    linarith
  calc (1 / s) * ∫ t in s..M, h_bjs (t - 1)
      ≤ (1 / s) * ((4 - s) * Real.exp (-2)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ((4 - s) / s) * Real.exp (-2) := by ring
    _ ≤ 3 * Real.exp (-2) := mul_le_mul_of_nonneg_right h4s (Real.exp_pos _).le

end BJSWeight

end BuchstabSwitching
