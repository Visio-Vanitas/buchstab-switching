import BuchstabSwitching.External.BuchstabSeries.EulerMascheroniIntegral
import BuchstabSwitching.Sieve.LinearSieveBJS.FHatDecay
import Mathlib.Tactic

/-!
# Jurkat–Richert Series `F_ser` and `f_ser` Convergence Bounds

Defines the Jurkat–Richert upper and lower Buchstab series `F_ser` and `f_ser`, proves uniform
geometric convergence via `fHat_le_bjs_universal`, continuity on `[1, ∞)`, and asymptotic decay
`s^2 * (F_ser s - f_ser s) → 0`, `F_ser s → 1`, `f_ser s → 1`.
-/

namespace BuchstabSwitching.External

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

noncomputable section

section SeriesBounds

/-- Upper Buchstab series `F_ser s = 1 + ∑_{k=0}^∞ fHat (2k + 1) s`. -/
def F_ser (s : ℝ) : ℝ :=
  1 + ∑' k : ℕ, fHat (2 * k + 1) s

/-- Lower Buchstab series `f_ser s = 1 - ∑_{k=0}^∞ fHat (2(k + 1)) s`. -/
def f_ser (s : ℝ) : ℝ :=
  1 - ∑' k : ℕ, fHat (2 * (k + 1)) s

/-- Geometric ratio `(9607 / 10000)^2 < 1` governing two-step decay of `fHat`. -/
def qBJS : ℝ := (9607 / 10000 : ℝ) ^ 2

lemma qBJS_nonneg : 0 ≤ qBJS := by unfold qBJS; positivity

lemma qBJS_lt_one : qBJS < 1 := by unfold qBJS; norm_num

lemma summable_qBJS : Summable (fun k : ℕ => qBJS ^ k) :=
  summable_geometric_of_lt_one qBJS_nonneg qBJS_lt_one

lemma fHat_odd_le_bjs (k : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    fHat (2 * k + 1) s ≤ 2 * Real.exp 2 * qBJS ^ k * h_bjs s := by
  have h := fHat_le_bjs_universal (2 * k + 1) s (by omega) hs
  have hpow : (9607 / 10000 : ℝ) ^ (2 * k + 1 - 1) = qBJS ^ k := by
    rw [Nat.add_sub_cancel]
    unfold qBJS
    rw [pow_mul]
  rwa [hpow] at h

lemma fHat_even_le_bjs (k : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    fHat (2 * (k + 1)) s ≤ 2 * Real.exp 2 * qBJS ^ k * h_bjs s := by
  have h := fHat_le_bjs_universal (2 * (k + 1)) s (by omega) hs
  have hle : (9607 / 10000 : ℝ) ^ (2 * (k + 1) - 1) ≤ qBJS ^ k := by
    have hpow : (9607 / 10000 : ℝ) ^ (2 * k + 1) = (9607 / 10000 : ℝ) * qBJS ^ k := by
      unfold qBJS
      rw [pow_succ', pow_mul]
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, hpow]
    nlinarith [pow_nonneg qBJS_nonneg k]
  calc fHat (2 * (k + 1)) s
      ≤ 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (2 * (k + 1) - 1) * h_bjs s := h
    _ ≤ 2 * Real.exp 2 * qBJS ^ k * h_bjs s := by
      gcongr
      exact h_bjs_nonneg s

lemma h_bjs_le_exp_neg_two (s : ℝ) : h_bjs s ≤ Real.exp (-2) := by
  by_cases hs : s ≤ 2
  · rw [h_bjs_of_le_two hs]
  · have := h_bjs_antitone (le_of_not_ge hs)
    rwa [h_bjs_of_le_two (le_refl 2)] at this

private lemma bjs_geom_norm_le {x s : ℝ} {k : ℕ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 * Real.exp 2 * qBJS ^ k * h_bjs s) : ‖x‖ ≤ 2 * qBJS ^ k := by
  rw [Real.norm_of_nonneg hx0]
  have h2 := h_bjs_le_exp_neg_two s
  have h3 : 2 * Real.exp 2 * qBJS ^ k * h_bjs s ≤ 2 * Real.exp 2 * qBJS ^ k * Real.exp (-2) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg (by positivity) (pow_nonneg qBJS_nonneg k))
  have h4 : 2 * Real.exp 2 * qBJS ^ k * Real.exp (-2) = 2 * qBJS ^ k := by
    calc 2 * Real.exp 2 * qBJS ^ k * Real.exp (-2)
        = 2 * qBJS ^ k * (Real.exp 2 * Real.exp (-2)) := by ring
      _ = 2 * qBJS ^ k := by rw [← Real.exp_add]; norm_num
  exact hx.trans (h3.trans_eq h4)

lemma fHat_odd_norm_le (k : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ‖fHat (2 * k + 1) s‖ ≤ 2 * qBJS ^ k :=
  bjs_geom_norm_le (fHat_nonneg _ _) (fHat_odd_le_bjs k hs)

lemma fHat_even_norm_le (k : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ‖fHat (2 * (k + 1)) s‖ ≤ 2 * qBJS ^ k :=
  bjs_geom_norm_le (fHat_nonneg _ _) (fHat_even_le_bjs k hs)

lemma summable_fHat_odd {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun k : ℕ => fHat (2 * k + 1) s) :=
  Summable.of_norm_bounded (summable_qBJS.mul_left 2) fun k => fHat_odd_norm_le k hs

lemma summable_fHat_even {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun k : ℕ => fHat (2 * (k + 1)) s) :=
  Summable.of_norm_bounded (summable_qBJS.mul_left 2) fun k => fHat_even_norm_le k hs

lemma F_ser_continuousOn : ContinuousOn F_ser (Set.Ici 1) := by
  refine continuousOn_const.add ?_
  refine continuousOn_tsum (u := fun k : ℕ => 2 * qBJS ^ k) ?_ (summable_qBJS.mul_left 2) ?_
  · intro k
    exact fHat_continuousOn (2 * k + 1) (by omega)
  · intro k s hs
    exact fHat_odd_norm_le k (Set.mem_Ici.mp hs)

lemma f_ser_continuousOn : ContinuousOn f_ser (Set.Ici 1) := by
  refine continuousOn_const.sub ?_
  refine continuousOn_tsum (u := fun k : ℕ => 2 * qBJS ^ k) ?_ (summable_qBJS.mul_left 2) ?_
  · intro k
    exact fHat_continuousOn (2 * (k + 1)) (by omega)
  · intro k s hs
    exact fHat_even_norm_le k (Set.mem_Ici.mp hs)

private lemma tsum_bjs_bounds {a : ℕ → ℝ} {s : ℝ} (hsum : Summable a)
    (hnn : ∀ k, 0 ≤ a k) (hle : ∀ k, a k ≤ 2 * Real.exp 2 * qBJS ^ k * h_bjs s) :
    0 ≤ ∑' k : ℕ, a k ∧ ∑' k : ℕ, a k ≤ (2 * Real.exp 2 / (1 - qBJS)) * h_bjs s := by
  have h0 : 0 ≤ ∑' k : ℕ, a k := tsum_nonneg hnn
  have h1 : ∑' k : ℕ, a k ≤ ∑' k : ℕ, (2 * Real.exp 2 * h_bjs s) * qBJS ^ k := by
    refine hsum.tsum_le_tsum (fun k => ?_) (summable_qBJS.mul_left _)
    linarith [hle k]
  rw [tsum_mul_left, tsum_geometric_of_lt_one qBJS_nonneg qBJS_lt_one] at h1
  exact ⟨h0, by linarith [show (2 * Real.exp 2 * h_bjs s) * (1 - qBJS)⁻¹ =
    (2 * Real.exp 2 / (1 - qBJS)) * h_bjs s by ring]⟩

lemma F_ser_sub_one_bounds {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ F_ser s - 1 ∧ F_ser s - 1 ≤ (2 * Real.exp 2 / (1 - qBJS)) * h_bjs s := by
  simpa [F_ser] using tsum_bjs_bounds (summable_fHat_odd hs)
    (fun k => fHat_nonneg (2 * k + 1) s) (fun k => fHat_odd_le_bjs k hs)

lemma one_sub_f_ser_bounds {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ 1 - f_ser s ∧ 1 - f_ser s ≤ (2 * Real.exp 2 / (1 - qBJS)) * h_bjs s := by
  simpa [f_ser] using tsum_bjs_bounds (summable_fHat_even hs)
    (fun k => fHat_nonneg (2 * (k + 1)) s) (fun k => fHat_even_le_bjs k hs)

lemma tendsto_sq_mul_h_bjs_atTop :
    Tendsto (fun s : ℝ => s ^ 2 * h_bjs s) atTop (𝓝 0) := by
  have h0 : Tendsto (fun s : ℝ => 3 * (s * Real.exp (-s))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 3
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with s hs
  rw [h_bjs_of_three_le hs]
  have hs0 : s ≠ 0 := by linarith
  field_simp

lemma tendsto_h_bjs_atTop : Tendsto h_bjs atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => (s ^ 2 * h_bjs s) * (s ^ 2)⁻¹) atTop (𝓝 (0 * 0)) :=
    tendsto_sq_mul_h_bjs_atTop.mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0)))
  simp only [mul_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  have hs0 : s ≠ 0 := by linarith
  field_simp

lemma tendsto_sq_mul_F_ser_sub_f_ser :
    Tendsto (fun s : ℝ => s ^ 2 * (F_ser s - f_ser s)) atTop (𝓝 0) := by
  set C₀ : ℝ := 2 * (2 * Real.exp 2 / (1 - qBJS))
  have hC₀ : Tendsto (fun s : ℝ => C₀ * (s ^ 2 * h_bjs s)) atTop (𝓝 0) := by
    simpa using tendsto_sq_mul_h_bjs_atTop.const_mul C₀
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC₀ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hF := (F_ser_sub_one_bounds hs).1
    have hf := (one_sub_f_ser_bounds hs).1
    exact mul_nonneg (sq_nonneg s) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hF := (F_ser_sub_one_bounds hs).2
    have hf := (one_sub_f_ser_bounds hs).2
    have hsum : F_ser s - f_ser s ≤ C₀ * h_bjs s := by
      dsimp [C₀]; linarith
    calc s ^ 2 * (F_ser s - f_ser s)
        ≤ s ^ 2 * (C₀ * h_bjs s) := mul_le_mul_of_nonneg_left hsum (sq_nonneg s)
      _ = C₀ * (s ^ 2 * h_bjs s) := by ring

lemma tendsto_F_ser_atTop : Tendsto F_ser atTop (𝓝 1) := by
  have h_h : Tendsto (fun s : ℝ => (2 * Real.exp 2 / (1 - qBJS)) * h_bjs s) atTop (𝓝 0) := by
    simpa using tendsto_h_bjs_atTop.const_mul (2 * Real.exp 2 / (1 - qBJS))
  have hsub : Tendsto (fun s : ℝ => F_ser s - 1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_h
      (eventually_ge_atTop (1 : ℝ) |>.mono fun s hs => (F_ser_sub_one_bounds hs).1)
      (eventually_ge_atTop (1 : ℝ) |>.mono fun s hs => (F_ser_sub_one_bounds hs).2)
  simpa using hsub.add_const 1

lemma tendsto_f_ser_atTop : Tendsto f_ser atTop (𝓝 1) := by
  have h_h : Tendsto (fun s : ℝ => (2 * Real.exp 2 / (1 - qBJS)) * h_bjs s) atTop (𝓝 0) := by
    simpa using tendsto_h_bjs_atTop.const_mul (2 * Real.exp 2 / (1 - qBJS))
  have hsub : Tendsto (fun s : ℝ => 1 - f_ser s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_h
      (eventually_ge_atTop (1 : ℝ) |>.mono fun s hs => (one_sub_f_ser_bounds hs).1)
      (eventually_ge_atTop (1 : ℝ) |>.mono fun s hs => (one_sub_f_ser_bounds hs).2)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsub

end SeriesBounds

end

end BuchstabSwitching.External
