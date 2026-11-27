import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.BuchstabSeries.EulerMascheroniIntegral
import BuchstabSwitching.External.BuchstabSeries.SeriesConvergence
import BuchstabSwitching.External.BuchstabSeries.SeriesUniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Buchstab Adjoint `pAdj` and Evaluation `3 * F_ser 3 = cBuchstab`

Formalizes the Buchstab adjoint `pAdj s = ∫_0^∞ exp (-s t - expIntE t) dt`, its ODE
`s * pAdj' s = -pAdj (s + 1)`, `pAdj 1 = exp (-γ)`, invariance of the pairing functional
`J_buf C s` on `[2, ∞)`, and concludes `three_mul_F_ser_three_eq_cBuchstab` and
`buchstabSeriesPremise_proved : BuchstabSeriesPremise`.
-/

namespace BuchstabSwitching.External

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

noncomputable section

section AdjointEvaluation

/-- Buchstab adjoint function `p(s) = ∫_0^∞ exp(-s t - E(t)) dt` for `s > 0`. -/
def pAdj (s : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t - expIntE t)

lemma pAdj_integrableOn {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t - expIntE t)) (Set.Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-s * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  refine hexp.mono' ?_ ?_
  · exact (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub continuous_expIntE)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by linarith [expIntE_nonneg ht.le])

lemma pAdj_bounds {s : ℝ} (hs : 0 < s) : 1 / (s + 1) ≤ pAdj s ∧ pAdj s ≤ 1 / s := by
  have hi_lo : IntegrableOn (fun t : ℝ => Real.exp (-(s + 1) * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hi_hi : IntegrableOn (fun t : ℝ => Real.exp (-s * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hi_mid := pAdj_integrableOn hs
  have h1 : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s + 1) * t) ≤ pAdj s := by
    refine setIntegral_mono_on hi_lo hi_mid measurableSet_Ioi fun t ht => ?_
    exact Real.exp_le_exp.mpr (by linarith [expIntE_le ht.le])
  have h2 : pAdj s ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t) := by
    refine setIntegral_mono_on hi_mid hi_hi measurableSet_Ioi fun t ht => ?_
    exact Real.exp_le_exp.mpr (by linarith [expIntE_nonneg ht.le])
  have h1' : -Real.exp (-(s + 1) * 0) / -(s + 1) = 1 / (s + 1) := by
    simp only [mul_zero, Real.exp_zero]; field_simp
  have h2' : -Real.exp (-s * 0) / -s = 1 / s := by
    simp only [mul_zero, Real.exp_zero]; field_simp
  rw [integral_exp_mul_Ioi (by linarith) 0, h1'] at h1
  rw [integral_exp_mul_Ioi (by linarith) 0, h2'] at h2
  exact ⟨h1, h2⟩

lemma tendsto_mul_pAdj_atTop : Tendsto (fun s : ℝ => s * pAdj s) atTop (𝓝 1) := by
  have hlo : Tendsto (fun s : ℝ => s / (s + 1)) atTop (𝓝 1) := by
    have h' : Tendsto (fun s : ℝ => 1 / (1 + s⁻¹)) atTop (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_inv_atTop_zero) (by norm_num)
    simp only [add_zero, div_one] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : s ≠ 0 := by linarith
    have hs1 : s + 1 ≠ 0 := by linarith
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have h := (pAdj_bounds (by linarith : 0 < s)).1
    calc s / (s + 1) = s * (1 / (s + 1)) := by ring
      _ ≤ s * pAdj s := mul_le_mul_of_nonneg_left h (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have h := (pAdj_bounds (by linarith : 0 < s)).2
    have hs0 : 0 < s := by linarith
    calc s * pAdj s ≤ s * (1 / s) := mul_le_mul_of_nonneg_left h hs0.le
      _ = 1 := by field_simp

lemma pAdj_hasDerivAt {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasDerivAt pAdj (-(pAdj (s₀ + 1)) / s₀) s₀ := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℝ := fun s t => Real.exp (-s * t - expIntE t)
  let F' : ℝ → ℝ → ℝ := fun s t => -t * Real.exp (-s * t - expIntE t)
  let bound : ℝ → ℝ := fun t => (4 / s₀) * Real.exp (-(s₀ / 4) * t)
  have hs_nhds : Set.Ioo (s₀ / 2) (2 * s₀) ∈ 𝓝 s₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) μ := by
    filter_upwards with s
    exact (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub continuous_expIntE)).aestronglyMeasurable
  have hF_int : Integrable (F s₀) μ := pAdj_integrableOn hs₀
  have hF'_meas : AEStronglyMeasurable (F' s₀) μ :=
    ((continuous_id.neg).mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub continuous_expIntE))).aestronglyMeasurable
  have hbound_int : Integrable bound μ :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul (4 / s₀)
  have h_bound : ∀ᵐ t ∂μ, ∀ s ∈ Set.Ioo (s₀ / 2) (2 * s₀), ‖F' s t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) s hs
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
    have hexp_e : Real.exp (-s * t - expIntE t) ≤ Real.exp (-(s₀ / 2) * t) :=
      Real.exp_le_exp.mpr (by nlinarith [hs.1, expIntE_nonneg ht.le])
    have hu : (s₀ / 4) * t ≤ Real.exp ((s₀ / 4) * t) := by
      linarith [Real.add_one_le_exp ((s₀ / 4) * t)]
    have hexp_u : (s₀ / 4) * t * Real.exp (-(s₀ / 4) * t) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hu (Real.exp_pos (-(s₀ / 4) * t)).le
      rwa [← Real.exp_add, show (s₀ / 4) * t + -(s₀ / 4) * t = 0 by ring, Real.exp_zero] at this
    have ht_le : t * Real.exp (-(s₀ / 4) * t) ≤ 4 / s₀ := by
      have := mul_le_mul_of_nonneg_left hexp_u (by positivity : 0 ≤ 4 / s₀)
      have heq : (4 / s₀) * ((s₀ / 4) * t * Real.exp (-(s₀ / 4) * t)) =
          t * Real.exp (-(s₀ / 4) * t) := by field_simp
      linarith
    have hsplit : Real.exp (-(s₀ / 2) * t) = Real.exp (-(s₀ / 4) * t) * Real.exp (-(s₀ / 4) * t) := by
      rw [← Real.exp_add]; ring_nf
    calc t * Real.exp (-s * t - expIntE t)
        ≤ t * Real.exp (-(s₀ / 2) * t) := mul_le_mul_of_nonneg_left hexp_e ht.le
      _ = (t * Real.exp (-(s₀ / 4) * t)) * Real.exp (-(s₀ / 4) * t) := by rw [hsplit]; ring
      _ ≤ (4 / s₀) * Real.exp (-(s₀ / 4) * t) :=
          mul_le_mul_of_nonneg_right ht_le (Real.exp_pos _).le
  have h_diff : ∀ᵐ t ∂μ, ∀ s ∈ Set.Ioo (s₀ / 2) (2 * s₀), HasDerivAt (fun x => F x t) (F' s t) s := by
    filter_upwards with t s _
    have hlin : HasDerivAt (fun x : ℝ => -x * t - expIntE t) (-t) s := by
      simpa using (((hasDerivAt_id s).neg.mul_const t).sub_const (expIntE t))
    convert hlin.exp using 1
    dsimp [F']
    ring
  obtain ⟨hF'_int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hIBP_eq : s₀ * ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-s₀ * t - expIntE t) = pAdj (s₀ + 1) := by
    have hIBP_T : ∀ T : ℝ, 0 ≤ T →
        T * Real.exp (-s₀ * T - expIntE T) =
          (∫ t in (0 : ℝ)..T, Real.exp (-(s₀ + 1) * t - expIntE t)) -
            s₀ * ∫ t in (0 : ℝ)..T, t * Real.exp (-s₀ * t - expIntE t) := by
      intro T hT
      have hderiv_t : ∀ t ∈ uIcc (0 : ℝ) T,
          HasDerivAt (fun x => x * Real.exp (-s₀ * x - expIntE x))
            (Real.exp (-(s₀ + 1) * t - expIntE t) - s₀ * (t * Real.exp (-s₀ * t - expIntE t))) t := by
        intro t ht
        rw [uIcc_of_le hT] at ht
        have hlin : HasDerivAt (fun x : ℝ => -s₀ * x) (-s₀) t := by
          simpa using (hasDerivAt_id' t).const_mul (-s₀)
        have hexp_d : HasDerivAt (fun x : ℝ => -s₀ * x - expIntE x) (-s₀ - expIntKernel t) t :=
          hlin.sub (hasDerivAt_expIntE t)
        refine ((hasDerivAt_id t).mul (hexp_d.exp)).congr_deriv ?_
        by_cases ht0 : t = 0
        · subst ht0
          simp [expIntE]
        · rw [expIntKernel_of_ne_zero ht0]
          have h1 : Real.exp (-(s₀ + 1) * t - expIntE t) =
              Real.exp (-t) * Real.exp (-s₀ * t - expIntE t) := by
            rw [← Real.exp_add]; ring_nf
          rw [h1]
          simp only [id_eq]
          field_simp [ht0]
          ring
      have hi1 : IntervalIntegrable (fun t : ℝ => Real.exp (-(s₀ + 1) * t - expIntE t)) volume 0 T :=
        (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub continuous_expIntE)).intervalIntegrable 0 T
      have hi2 : IntervalIntegrable (fun t : ℝ => s₀ * (t * Real.exp (-s₀ * t - expIntE t))) volume 0 T :=
        (continuous_const.mul (continuous_id.mul (Real.continuous_exp.comp
          ((continuous_const.mul continuous_id).sub continuous_expIntE)))).intervalIntegrable 0 T
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_t (hi1.sub hi2)
      rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul] at hFTC
      simp only [zero_mul, sub_zero] at hFTC
      linarith
    have hL : Tendsto (fun T : ℝ => T * Real.exp (-s₀ * T - expIntE T)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun T : ℝ => s₀⁻¹ * ((s₀ * T) * Real.exp (-(s₀ * T)))) atTop (𝓝 0) := by
        have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          (tendsto_id.const_mul_atTop hs₀)
        simpa using ht.const_mul s₀⁻¹
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 ?_ ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        exact mul_nonneg hT (Real.exp_pos _).le
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        have hexp : Real.exp (-s₀ * T - expIntE T) ≤ Real.exp (-(s₀ * T)) :=
          Real.exp_le_exp.mpr (by linarith [expIntE_nonneg hT])
        have heq : s₀⁻¹ * ((s₀ * T) * Real.exp (-(s₀ * T))) = T * Real.exp (-(s₀ * T)) := by
          field_simp
        rw [heq]
        exact mul_le_mul_of_nonneg_left hexp hT
    have hI1 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, Real.exp (-(s₀ + 1) * t - expIntE t))
        atTop (𝓝 (pAdj (s₀ + 1))) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 (pAdj_integrableOn (by linarith)) tendsto_id
    have ht_int : IntegrableOn (fun t : ℝ => t * Real.exp (-s₀ * t - expIntE t)) (Set.Ioi 0) := by
      change Integrable (fun t : ℝ => t * Real.exp (-s₀ * t - expIntE t)) μ
      have hneg : Integrable (fun t => -F' s₀ t) μ := hF'_int.neg
      simpa [F'] using hneg
    have hI2 : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, t * Real.exp (-s₀ * t - expIntE t))
        atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-s₀ * t - expIntE t))) :=
      MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 ht_int tendsto_id
    have hR := hI1.sub (hI2.const_mul s₀)
    have hR' : Tendsto (fun T : ℝ => T * Real.exp (-s₀ * T - expIntE T))
        atTop (𝓝 (pAdj (s₀ + 1) - s₀ * ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-s₀ * t - expIntE t))) := by
      refine hR.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      linarith [hIBP_T T hT]
    have heq0 := tendsto_nhds_unique hL hR'
    linarith
  have hderiv_eq : ∫ t in Set.Ioi (0 : ℝ), F' s₀ t = -(pAdj (s₀ + 1)) / s₀ := by
    have hneg : ∫ t in Set.Ioi (0 : ℝ), F' s₀ t =
        - ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-s₀ * t - expIntE t) := by
      rw [← MeasureTheory.integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by dsimp [F']; ring
    rw [hneg]
    have hmul : s₀ * (- ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-s₀ * t - expIntE t)) = -(pAdj (s₀ + 1)) := by
      linarith
    exact eq_div_of_mul_eq hs₀.ne' (by linarith)
  have hderiv' : HasDerivAt pAdj (∫ a, F' s₀ a ∂μ) s₀ := hderiv
  rwa [hderiv_eq] at hderiv'

lemma pAdj_one_eq : pAdj 1 = Real.exp (-Real.eulerMascheroniConstant) := by
  have hT : ∀ T : ℝ, 0 ≤ T →
      ∫ t in (0 : ℝ)..T, Real.exp (-1 * t - expIntE t) = T * Real.exp (-expIntE T) := by
    intro T hT
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) T,
        HasDerivAt (fun x => x * Real.exp (-expIntE x)) (Real.exp (-1 * t - expIntE t)) t := by
      intro t _
      have hexp : HasDerivAt (fun x => Real.exp (-expIntE x))
          (Real.exp (-expIntE t) * (-expIntKernel t)) t :=
        (hasDerivAt_expIntE t).neg.exp
      refine ((hasDerivAt_id t).mul hexp).congr_deriv ?_
      by_cases ht0 : t = 0
      · subst ht0; simp [expIntE]
      · rw [expIntKernel_of_ne_zero ht0]
        have heq : Real.exp (-1 * t - expIntE t) = Real.exp (-t) * Real.exp (-expIntE t) := by
          rw [← Real.exp_add]; ring_nf
        rw [heq]
        simp only [id_eq]
        field_simp [ht0]
        ring
    have hi : IntervalIntegrable (fun t : ℝ => Real.exp (-1 * t - expIntE t)) volume 0 T :=
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub continuous_expIntE)).intervalIntegrable 0 T
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi
    simpa using hFTC
  have hL : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, Real.exp (-1 * t - expIntE t))
      atTop (𝓝 (pAdj 1)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 (pAdj_integrableOn one_pos) tendsto_id
  have hR : Tendsto (fun T : ℝ => T * Real.exp (-expIntE T))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    have h0 : Tendsto (fun T : ℝ => Real.exp (-(expIntE T - Real.log T)))
        atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) :=
      Real.continuous_exp.continuousAt.tendsto.comp tendsto_expIntE_sub_log.neg
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T (hT : 0 < T)
    rw [neg_sub, Real.exp_sub, Real.exp_log hT, mul_comm, div_eq_mul_inv, ← Real.exp_neg, mul_comm]
  have hL' : Tendsto (fun T : ℝ => T * Real.exp (-expIntE T)) atTop (𝓝 (pAdj 1)) := by
    refine hL.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT_nonneg
    exact hT T hT_nonneg
  exact tendsto_nhds_unique hL' hR

lemma pAdj_continuousOn : ContinuousOn pAdj (Set.Ioi 0) := by
  intro s hs
  exact (pAdj_hasDerivAt (Set.mem_Ioi.mp hs)).continuousAt.continuousWithinAt

/-- Adjoint pairing functional `J(C, s) = s * (F(C, s) + f(C, s)) * p(s) + ∫_{s-1}^s (F(C, t) + f(C, t)) * p(t+1) dt`. -/
def J_buf (C s : ℝ) : ℝ :=
  s * (buchstabF C s + buchstabf C s) * pAdj s +
    ∫ t in (s - 1)..s, (buchstabF C t + buchstabf C t) * pAdj (t + 1)

lemma J_buf_const (C : ℝ) {s : ℝ} (hs : 2 ≤ s) : J_buf C s = J_buf C 2 := by
  let S : ℝ → ℝ := fun t => buchstabF C t + buchstabf C t
  let H : ℝ → ℝ := fun t => S t * pAdj (t + 1)
  have hS_cont : ContinuousOn S (Set.Ioi 0) :=
    (buchstabF_continuousOn C).add (buchstabf_continuousOn C)
  have hp1_cont : ContinuousOn (fun t : ℝ => pAdj (t + 1)) (Set.Ici 0) :=
    pAdj_continuousOn.comp (continuousOn_id.add continuousOn_const) fun t ht => by
      simp only [Set.mem_Ioi]; linarith [Set.mem_Ici.mp ht]
  have hH_cont : ContinuousOn H (Set.Ioi 0) :=
    hS_cont.mul (hp1_cont.mono fun _ ht => by simp only [Set.mem_Ici]; linarith [Set.mem_Ioi.mp ht])
  have hS_eq : ∀ t : ℝ, 2 ≤ t → t * S t = 2 * S 2 + ∫ u in (2 : ℝ)..t, S (u - 1) := by
    intro t ht
    have hF := buchstabF_integral_eq C (le_refl 2) ht
    have hf := buchstabf_integral_eq C (le_refl 2) ht
    have hiF : IntervalIntegrable (fun u => buchstabF C (u - 1)) volume 2 t :=
      buchstab_intervalIntegrable_shift (buchstabF_continuousOn C) (by norm_num) (by linarith)
    have hif : IntervalIntegrable (fun u => buchstabf C (u - 1)) volume 2 t :=
      buchstab_intervalIntegrable_shift (buchstabf_continuousOn C) (by norm_num) (by linarith)
    have hadd := intervalIntegral.integral_add hiF hif
    dsimp [S] at hadd ⊢
    linarith [hF, hf]
  have hH_int : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable H volume a b := fun a b ha hb =>
    (hH_cont.mono fun t ht => by
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith).intervalIntegrable
  have hJ_cont : ContinuousOn (J_buf C) (Set.Icc 2 s) := by
    have h1 : ContinuousOn (fun x => x * S x * pAdj x) (Set.Icc 2 s) :=
      (continuousOn_id.mul (hS_cont.mono fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])).mul
        (pAdj_continuousOn.mono fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])
    have hI_cont : ContinuousOn (fun x => ∫ t in (1 : ℝ)..x, H t) (Set.Ici 1) := by
      intro x hx
      have hx1 : 1 ≤ x := Set.mem_Ici.mp hx
      have hIcc : ContinuousOn (fun v => ∫ t in (1 : ℝ)..v, H t) (Set.Icc 1 (x + 1)) := by
        simpa [uIcc_of_le (by linarith : (1 : ℝ) ≤ x + 1)] using
          intervalIntegral.continuousOn_primitive_interval' (hH_int 1 (x + 1) (by norm_num) (by linarith)) left_mem_uIcc
      have hnhds : Set.Icc (1 : ℝ) (x + 1) ∈ 𝓝[Set.Ici 1] x := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Set.Iio (x + 1), Iio_mem_nhds (by linarith), fun y ⟨hy1, hy2⟩ => ⟨hy2, hy1.le⟩⟩
      exact (hIcc x ⟨hx1, by linarith⟩).mono_of_mem_nhdsWithin hnhds
    have h2 : ContinuousOn (fun x => ∫ t in (x - 1)..x, H t) (Set.Icc 2 s) := by
      have hsub_eq : EqOn (fun x => ∫ t in (x - 1)..x, H t)
          (fun x => (∫ t in (1 : ℝ)..x, H t) - ∫ t in (1 : ℝ)..(x - 1), H t) (Set.Icc 2 s) := by
        intro x hx
        have hadd := intervalIntegral.integral_add_adjacent_intervals
          (hH_int 1 (x - 1) (by norm_num) (by linarith [hx.1]))
          (hH_int (x - 1) x (by linarith [hx.1]) (by linarith [hx.1]))
        linarith
      refine ContinuousOn.congr ?_ hsub_eq
      refine (hI_cont.mono fun x hx => by simp only [Set.mem_Ici]; linarith [hx.1]).sub ?_
      exact hI_cont.comp (continuousOn_id.sub continuousOn_const) fun x hx => by
        simp only [Set.mem_Ici]; linarith [hx.1]
    exact h1.add h2
  have hderiv : ∀ x ∈ Set.Ioo 2 s, HasDerivAt (J_buf C) 0 x := by
    intro x hx
    have hx2 : 2 < x := hx.1
    have hx0 : 0 < x := by linarith
    have hx1 : 1 < x := by linarith
    have hS_shift_cont : ContinuousOn (fun u => S (u - 1)) (Set.Ioi 1) :=
      hS_cont.comp (continuousOn_id.sub continuousOn_const) fun u hu => by
        simp only [Set.mem_Ioi] at hu ⊢; linarith
    have hi_S : IntervalIntegrable (fun u => S (u - 1)) volume 2 x :=
      (hS_shift_cont.mono fun u hu => by
        rw [Set.mem_uIcc] at hu
        rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith).intervalIntegrable
    have hI_S := intervalIntegral.integral_hasDerivAt_right hi_S
      (hS_shift_cont.stronglyMeasurableAtFilter isOpen_Ioi x hx1)
      (hS_shift_cont.continuousAt (Ioi_mem_nhds hx1))
    have hxS_d : HasDerivAt (fun t => t * S t) (S (x - 1)) x := by
      refine (((hasDerivAt_const x (2 * S 2)).add hI_S).congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx2] with t ht
      exact hS_eq t ht.le
    have hp_d := pAdj_hasDerivAt hx0
    have hprod_d := hxS_d.mul hp_d
    have hI_top := intervalIntegral.integral_hasDerivAt_right (hH_int 1 x (by norm_num) hx0)
      (hH_cont.stronglyMeasurableAtFilter isOpen_Ioi x hx0)
      (hH_cont.continuousAt (Ioi_mem_nhds hx0))
    have hI_bot_base := intervalIntegral.integral_hasDerivAt_right (hH_int 1 (x - 1) (by norm_num) (by linarith))
      (hH_cont.stronglyMeasurableAtFilter isOpen_Ioi (x - 1) (by simp only [Set.mem_Ioi]; linarith))
      (hH_cont.continuousAt (Ioi_mem_nhds (by linarith)))
    have hI_bot : HasDerivAt (fun t => ∫ u in (1 : ℝ)..(t - 1), H u) (H (x - 1)) x := by
      have hlin : HasDerivAt (fun t : ℝ => t - 1) 1 x := by
        simpa using (hasDerivAt_id x).sub_const (1 : ℝ)
      simpa [Function.comp_def] using hI_bot_base.comp x hlin
    have hI_d : HasDerivAt (fun t => ∫ u in (t - 1)..t, H u) (H x - H (x - 1)) x := by
      refine (hI_top.sub hI_bot).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx2] with t (ht : (2 : ℝ) < t)
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hH_int 1 (t - 1) (by norm_num) (by linarith))
        (hH_int (t - 1) t (by linarith) (by linarith))
      exact eq_sub_iff_add_eq'.mpr hadd
    have hsum_d := hprod_d.add hI_d
    refine hsum_d.congr_deriv ?_
    dsimp [H, S]
    rw [show x - 1 + 1 = x by ring]
    field_simp [hx0.ne']
    ring
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hs hJ_cont hderiv intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hFTC
  linarith

lemma J_buf_at_two (C : ℝ) : J_buf C 2 = C * Real.exp (-Real.eulerMascheroniConstant) := by
  have hF2 : buchstabF C 2 = C / 2 := buchstabF_on_zero_two C (by norm_num) (le_refl 2)
  have hf2 : buchstabf C 2 = 0 := buchstabf_le_two C (le_refl 2)
  have hcongr : ∫ t in (1 : ℝ)..2, (buchstabF C t + buchstabf C t) * pAdj (t + 1) =
      ∫ t in (1 : ℝ)..2, C * (pAdj (t + 1) / t) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    rw [buchstabF_on_zero_two C (by linarith [ht.1]) ht.2, buchstabf_le_two C ht.2]
    ring
  have hIBP : ∫ t in (1 : ℝ)..2, pAdj (t + 1) / t = pAdj 1 - pAdj 2 := by
    have hderiv : ∀ t ∈ uIcc (1 : ℝ) 2, HasDerivAt (fun x => -pAdj x) (pAdj (t + 1) / t) t := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      exact (pAdj_hasDerivAt (by linarith [ht.1])).neg.congr_deriv (by ring)
    have hint : IntervalIntegrable (fun t => pAdj (t + 1) / t) volume 1 2 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by norm_num)]
      refine (pAdj_continuousOn.comp (continuousOn_id.add continuousOn_const)
        fun t ht => by dsimp; simp only [Set.mem_Ioi]; linarith [ht.1]).div continuousOn_id
        fun t ht => by show t ≠ 0; linarith [ht.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  unfold J_buf
  rw [show (2 : ℝ) - 1 = 1 by norm_num, hF2, hf2, hcongr, intervalIntegral.integral_const_mul, hIBP,
    pAdj_one_eq]
  ring

lemma tendsto_J_buf_atTop : Tendsto (J_buf (3 * F_ser 3)) atTop (𝓝 2) := by
  set C : ℝ := 3 * F_ser 3
  have hF_lim : Tendsto (buchstabF C) atTop (𝓝 1) := by
    refine tendsto_F_ser_atTop.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact F_ser_and_f_ser_eq_buchstab.1 s hs
  have hf_lim : Tendsto (buchstabf C) atTop (𝓝 1) := by
    refine tendsto_f_ser_atTop.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    exact F_ser_and_f_ser_eq_buchstab.2 s hs
  have h1 : Tendsto (fun s : ℝ => s * (buchstabF C s + buchstabf C s) * pAdj s) atTop (𝓝 2) := by
    have hmul := (hF_lim.add hf_lim).mul tendsto_mul_pAdj_atTop
    simp only [show (1 + 1 : ℝ) * 1 = 2 by norm_num] at hmul
    refine hmul.congr' ?_
    filter_upwards with s
    ring
  have h2 : Tendsto (fun s : ℝ => ∫ t in (s - 1)..s, (buchstabF C t + buchstabf C t) * pAdj (t + 1))
      atTop (𝓝 0) := by
    have hev_bd : ∀ᶠ t in atTop, |buchstabF C t + buchstabf C t| ≤ 3 := by
      have hlim : Tendsto (fun t : ℝ => |buchstabF C t + buchstabf C t|) atTop (𝓝 2) := by
        simpa [show |(1 : ℝ) + 1| = 2 by norm_num] using (hF_lim.add hf_lim).abs
      exact (hlim.eventually (Iio_mem_nhds (by norm_num))).mono fun _ h => h.le
    rw [eventually_atTop] at hev_bd
    obtain ⟨M, hM⟩ := hev_bd
    have hzero : Tendsto (fun s : ℝ => 3 / s) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 3
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hzero (Eventually.of_forall fun _ => norm_nonneg _) ?_)
    filter_upwards [eventually_ge_atTop (max M 1 + 1)] with s hs
    have hsM : M ≤ s - 1 := by linarith [le_max_left M 1]
    have hs1 : 1 ≤ s - 1 := by linarith [le_max_right M 1]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := s - 1) (b := s)
      (C := 3 / s) (f := fun t => (buchstabF C t + buchstabf C t) * pAdj (t + 1)) fun t ht => by
        rw [uIoc_of_le (by linarith)] at ht
        have hpb := pAdj_bounds (s := t + 1) (by linarith [ht.1, hs1])
        have hp_nn : 0 ≤ pAdj (t + 1) := le_trans (div_nonneg zero_le_one (by linarith [ht.1, hs1])) hpb.1
        have hp_le : pAdj (t + 1) ≤ 1 / s :=
          hpb.2.trans (one_div_le_one_div_of_le (by linarith) (by linarith [ht.1, hs1]))
        have hS_bd : |buchstabF C t + buchstabf C t| ≤ 3 := hM t (by linarith [ht.1])
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp_nn]
        calc |buchstabF C t + buchstabf C t| * pAdj (t + 1)
            ≤ 3 * (1 / s) := mul_le_mul hS_bd hp_le hp_nn (by norm_num)
          _ = 3 / s := by ring
    simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] using hnorm
  have h12 := h1.add h2
  simp only [add_zero] at h12
  exact h12

theorem three_mul_F_ser_three_eq_cBuchstab : 3 * F_ser 3 = cBuchstab := by
  have hconst : Tendsto (J_buf (3 * F_ser 3)) atTop (𝓝 (J_buf (3 * F_ser 3) 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    exact (J_buf_const (3 * F_ser 3) hs).symm
  have h2 := tendsto_nhds_unique hconst tendsto_J_buf_atTop
  rw [J_buf_at_two] at h2
  unfold cBuchstab
  have hexp_ne : Real.exp (-Real.eulerMascheroniConstant) ≠ 0 := (Real.exp_pos _).ne'
  calc 3 * F_ser 3 = (3 * F_ser 3 * Real.exp (-Real.eulerMascheroniConstant)) *
      Real.exp Real.eulerMascheroniConstant := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = 2 * Real.exp Real.eulerMascheroniConstant := by rw [h2]

theorem buchstabSeriesPremise_proved : BuchstabSeriesPremise := by
  constructor
  · intro s hs
    have hsum := (summable_fHat_odd hs).hasSum
    have heq : ∑' k : ℕ, fHat (2 * k + 1) s = buchstabF cBuchstab s - 1 := by
      have h1 : F_ser s = buchstabF (3 * F_ser 3) s := F_ser_and_f_ser_eq_buchstab.1 s hs
      rw [three_mul_F_ser_three_eq_cBuchstab] at h1
      unfold F_ser at h1
      linarith
    rwa [heq] at hsum
  · intro s hs
    have hs1 : 1 ≤ s := by linarith
    have hsum := (summable_fHat_even hs1).hasSum
    have heq : ∑' k : ℕ, fHat (2 * (k + 1)) s = 1 - buchstabf cBuchstab s := by
      have h1 : f_ser s = buchstabf (3 * F_ser 3) s := F_ser_and_f_ser_eq_buchstab.2 s hs
      rw [three_mul_F_ser_three_eq_cBuchstab] at h1
      unfold f_ser at h1
      linarith
    rwa [heq] at hsum

end AdjointEvaluation

end

end BuchstabSwitching.External
