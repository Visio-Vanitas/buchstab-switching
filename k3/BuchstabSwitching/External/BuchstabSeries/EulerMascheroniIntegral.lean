import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Exponential Integral `expIntE` and Euler–Mascheroni Asymptotic

Formalizes the exponential integral kernel `expIntKernel u = (1 - exp (-u)) / u`,
`expIntE t = ∫_0^t expIntKernel u du`, and the asymptotic limit
`tendsto_expIntE_sub_log : expIntE T - log T → γ` via integration by parts from
`Real.eulerMascheroniConstant_eq_neg_integral_log`.
-/

namespace BuchstabSwitching.External

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

noncomputable section

section ExpInt

/-- Continuous kernel `(1 - exp(-u)) / u` extended by `1` at `u = 0`. -/
def expIntKernel (u : ℝ) : ℝ :=
  if u = 0 then 1 else (1 - Real.exp (-u)) / u

/-- Exponential integral `E(t) = ∫_0^t (1 - e^{-u}) / u du`. -/
def expIntE (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, expIntKernel u

lemma expIntKernel_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    expIntKernel u = (1 - Real.exp (-u)) / u := by
  simp [expIntKernel, hu]

lemma expIntKernel_zero : expIntKernel 0 = 1 := by
  simp [expIntKernel]

lemma continuous_expIntKernel : Continuous expIntKernel := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    have hderiv : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
      have h1 := ((hasDerivAt_id (0 : ℝ)).neg).exp.const_sub 1
      simpa using h1
    have hlim : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / x) (𝓝[≠] 0) (𝓝 1) := by
      have hsl := hderiv.tendsto_slope_zero
      refine hsl.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x _
      simp [div_eq_inv_mul]
    have hlim' : Tendsto expIntKernel (𝓝[≠] 0) (𝓝 (expIntKernel 0)) := by
      rw [expIntKernel_zero]
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (expIntKernel_of_ne_zero hx).symm
    exact continuousAt_iff_punctured_nhds.mpr hlim'
  · have hcont : ContinuousAt (fun x : ℝ => (1 - Real.exp (-x)) / x) u :=
      ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt).div
        continuousAt_id hu
    refine hcont.congr ?_
    filter_upwards [eventually_ne_nhds hu] with x hx
    exact (expIntKernel_of_ne_zero hx).symm

lemma expIntKernel_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ expIntKernel u := by
  rcases eq_or_lt_of_le hu with rfl | hpos
  · simp [expIntKernel]
  · rw [expIntKernel_of_ne_zero hpos.ne']
    have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact div_nonneg (by linarith) hpos.le

lemma expIntKernel_le_one {u : ℝ} (hu : 0 ≤ u) : expIntKernel u ≤ 1 := by
  rcases eq_or_lt_of_le hu with rfl | hpos
  · simp [expIntKernel]
  · rw [expIntKernel_of_ne_zero hpos.ne', div_le_one hpos]
    have := Real.add_one_le_exp (-u)
    linarith

lemma expIntE_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ expIntE t :=
  intervalIntegral.integral_nonneg ht fun _ hu => expIntKernel_nonneg hu.1

lemma expIntE_le {t : ℝ} (ht : 0 ≤ t) : expIntE t ≤ t := by
  have hint : IntervalIntegrable expIntKernel volume 0 t :=
    continuous_expIntKernel.intervalIntegrable 0 t
  calc expIntE t = ∫ u in (0 : ℝ)..t, expIntKernel u := rfl
    _ ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) :=
      intervalIntegral.integral_mono_on ht hint intervalIntegrable_const fun _ hu =>
        expIntKernel_le_one hu.1
    _ = t := by simp

lemma hasDerivAt_expIntE (t : ℝ) : HasDerivAt expIntE (expIntKernel t) t := by
  have hi : IntervalIntegrable expIntKernel volume 0 t :=
    continuous_expIntKernel.intervalIntegrable 0 t
  exact intervalIntegral.integral_hasDerivAt_right hi
    continuous_expIntKernel.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_expIntKernel.continuousAt

lemma continuous_expIntE : Continuous expIntE :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_expIntE t).continuousAt

lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Set.Ioi 0) := by
  have h1 : IntegrableOn (fun x : ℝ => 2 * (Real.exp (-x) * x ^ ((1 / 2 : ℝ) - 1))) (Set.Ioi 0) :=
    (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)
  refine (h1.add h2).mono' ?_ ?_
  · exact ((Real.continuousOn_log.mono fun _ hx => ne_of_gt hx).aestronglyMeasurable
      measurableSet_Ioi).mul (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-t))]
    by_cases ht1 : t ≤ 1
    · have hlog_neg : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
      have hsub : |Real.log t| = 2 * Real.log (t ^ (-(1 / 2 : ℝ))) := by
        rw [abs_of_nonpos hlog_neg, Real.log_rpow ht0]
        ring
      have hlog_le : Real.log (t ^ (-(1 / 2 : ℝ))) ≤ t ^ (-(1 / 2 : ℝ)) := by
        have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (-(1 / 2 : ℝ)))
        linarith
      have hpow_eq : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
      have hnn : 0 ≤ Real.exp (-t) * t ^ ((2 : ℝ) - 1) := by positivity
      have hexp_pos : 0 ≤ Real.exp (-t) := (Real.exp_pos (-t)).le
      rw [hpow_eq]
      calc |Real.log t| * Real.exp (-t)
          = (2 * Real.log (t ^ (-(1 / 2 : ℝ)))) * Real.exp (-t) := by rw [hsub]
        _ ≤ (2 * t ^ (-(1 / 2 : ℝ))) * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right (by linarith) hexp_pos
        _ = 2 * (Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ 2 * (Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) + Real.exp (-t) * t ^ ((2 : ℝ) - 1) :=
            le_add_of_nonneg_right hnn
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1'
      have hlog_le : |Real.log t| ≤ t ^ ((2 : ℝ) - 1) := by
        rw [abs_of_nonneg hlog_nn, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
        linarith [Real.log_le_sub_one_of_pos ht0]
      have hnn : 0 ≤ 2 * (Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) := by positivity
      have hexp_pos : 0 ≤ Real.exp (-t) := (Real.exp_pos (-t)).le
      calc |Real.log t| * Real.exp (-t)
          ≤ t ^ ((2 : ℝ) - 1) * Real.exp (-t) := mul_le_mul_of_nonneg_right hlog_le hexp_pos
        _ = Real.exp (-t) * t ^ ((2 : ℝ) - 1) := by ring
        _ ≤ 2 * (Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) + Real.exp (-t) * t ^ ((2 : ℝ) - 1) :=
            le_add_of_nonneg_left hnn

private lemma expIntE_one_eq :
    expIntE 1 = - ∫ u in Set.Ioc (0 : ℝ) 1, Real.log u * Real.exp (-u) := by
  have hIoc_int : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioc 0 1) :=
    integrableOn_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self
  have hIBP : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∫ u in ε..1, expIntKernel u =
        -(Real.log ε * (1 - Real.exp (-ε))) - ∫ u in ε..1, Real.log u * Real.exp (-u) := by
    intro ε hε0 hε1
    have hderiv : ∀ u ∈ uIcc ε 1,
        HasDerivAt (fun x => Real.log x * (1 - Real.exp (-x)))
          (expIntKernel u + Real.log u * Real.exp (-u)) u := by
      intro u hu
      rw [uIcc_of_le hε1.le] at hu
      have hu0 : 0 < u := lt_of_lt_of_le hε0 hu.1
      have hlog := Real.hasDerivAt_log hu0.ne'
      have hexp : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-u)) u := by
        simpa using ((hasDerivAt_id u).neg.exp).const_sub 1
      have hmul := hlog.mul hexp
      convert hmul using 1
      rw [expIntKernel_of_ne_zero hu0.ne']
      field_simp [hu0.ne']
    have hint1 : IntervalIntegrable expIntKernel volume ε 1 :=
      continuous_expIntKernel.intervalIntegrable ε 1
    have hint2 : IntervalIntegrable (fun u => Real.log u * Real.exp (-u)) volume ε 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hε1.le]
      exact (Real.continuousOn_log.mono fun u hu => by show u ≠ 0; linarith [hu.1]).mul
        (Real.continuous_exp.comp continuous_neg).continuousOn
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.add hint2)
    rw [intervalIntegral.integral_add hint1 hint2] at hFTC
    simp only [Real.log_one, zero_mul, zero_sub] at hFTC
    linarith
  have hL : Tendsto (fun ε : ℝ => ∫ u in ε..1, expIntKernel u) (𝓝[>] 0) (𝓝 (expIntE 1)) := by
    have hcont : Continuous (fun ε : ℝ => ∫ u in ε..1, expIntKernel u) := by
      have : (fun ε : ℝ => ∫ u in ε..1, expIntKernel u) =
          fun ε => expIntE 1 - expIntE ε := by
        ext ε
        have h1 := continuous_expIntKernel.intervalIntegrable (μ := volume) 0 ε
        have h2 := continuous_expIntKernel.intervalIntegrable (μ := volume) ε 1
        have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
        unfold expIntE
        linarith
      rw [this]
      exact continuous_const.sub continuous_expIntE
    have h0 : (∫ u in (0 : ℝ)..1, expIntKernel u) = expIntE 1 := rfl
    rw [← h0]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun ε : ℝ => -(Real.log ε * (1 - Real.exp (-ε)))) (𝓝[>] 0) (𝓝 0) := by
    have hmul_log : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
      have h0 : (0 : ℝ) * Real.log 0 = 0 := by simp
      have hc : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝 0) (𝓝 0) := by
        simpa [h0] using (Real.continuous_mul_log.continuousAt (x := (0 : ℝ))).tendsto
      exact hc.mono_left nhdsWithin_le_nhds
    have hquot : Tendsto (fun ε : ℝ => (1 - Real.exp (-ε)) / ε) (𝓝[>] 0) (𝓝 1) := by
      have hderiv : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).neg.exp).const_sub 1
      have hsl := hderiv.tendsto_slope_zero
      refine (hsl.mono_left (nhdsWithin_mono 0 fun _ hx => ne_of_gt hx)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x _
      simp [div_eq_inv_mul]
    have hprod := (hmul_log.mul hquot).neg
    simp only [mul_one, neg_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    field_simp [hε.ne']
  have hI : Tendsto (fun ε : ℝ => ∫ u in ε..1, Real.log u * Real.exp (-u))
      (𝓝[>] 0) (𝓝 (∫ u in Set.Ioc (0 : ℝ) 1, Real.log u * Real.exp (-u))) := by
    have hrew : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫ u in ε..1, Real.log u * Real.exp (-u) =
          ∫ u in Set.Ioc (0 : ℝ) 1, Set.indicator (Set.Ioi ε)
            (fun u => Real.log u * Real.exp (-u)) u := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
      rw [intervalIntegral.integral_of_le hε.2.le]
      symm
      rw [setIntegral_indicator measurableSet_Ioi, Set.Ioc_inter_Ioi, max_eq_right hε.1.le]
    rw [tendsto_congr' hrew]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u => ‖Real.log u * Real.exp (-u)‖) ?_ ?_ hIoc_int.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε _
      exact (hIoc_int.aestronglyMeasurable.indicator measurableSet_Ioi)
    · filter_upwards [self_mem_nhdsWithin] with ε _
      filter_upwards with u
      exact norm_indicator_le_norm_self _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u ∈ Set.Ioi ε := by
        filter_upwards [Ioo_mem_nhdsGT hu.1] with ε hε
        exact hε.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with ε hε
      simp [Set.indicator_of_mem hε]
  have hR := hB.sub hI
  simp only [zero_sub] at hR
  have hR' : Tendsto (fun ε : ℝ => ∫ u in ε..1, expIntKernel u)
      (𝓝[>] 0) (𝓝 (- ∫ u in Set.Ioc (0 : ℝ) 1, Real.log u * Real.exp (-u))) := by
    refine hR.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact (hIBP ε hε.1 hε.2).symm
  exact tendsto_nhds_unique hL hR'

theorem tendsto_expIntE_sub_log :
    Tendsto (fun T : ℝ => expIntE T - Real.log T) atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hIoi1 : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi 1) :=
    integrableOn_log_mul_exp_neg.mono_set (Ioi_subset_Ioi zero_le_one)
  have hEq : ∀ T : ℝ, 1 ≤ T →
      expIntE T - Real.log T =
        expIntE 1 - Real.log T * Real.exp (-T) - ∫ u in (1 : ℝ)..T, Real.log u * Real.exp (-u) := by
    intro T hT
    have hsplit : expIntE T = expIntE 1 + ∫ u in (1 : ℝ)..T, expIntKernel u := by
      have h1 := continuous_expIntKernel.intervalIntegrable (μ := volume) 0 1
      have h2 := continuous_expIntKernel.intervalIntegrable (μ := volume) 1 T
      unfold expIntE
      exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    have hker : ∫ u in (1 : ℝ)..T, expIntKernel u =
        Real.log T - ∫ u in (1 : ℝ)..T, Real.exp (-u) / u := by
      have hcongr : EqOn expIntKernel (fun u => 1 / u - Real.exp (-u) / u) (uIcc 1 T) := by
        intro u hu
        rw [uIcc_of_le hT] at hu
        rw [expIntKernel_of_ne_zero (by linarith [hu.1])]
        ring
      have hi1 : IntervalIntegrable (fun u : ℝ => 1 / u) volume 1 T := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hT]
        exact continuousOn_const.div continuousOn_id fun u hu => by linarith [hu.1]
      have hi2 : IntervalIntegrable (fun u : ℝ => Real.exp (-u) / u) volume 1 T := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hT]
        exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
          fun u hu => by linarith [hu.1]
      have hlogT : ∫ u in (1 : ℝ)..T, (1 / u : ℝ) = Real.log T := by
        have hd : ∀ u ∈ uIcc 1 T, HasDerivAt Real.log (1 / u) u := fun u hu => by
          rw [uIcc_of_le hT] at hu
          simpa [one_div] using Real.hasDerivAt_log (by linarith [hu.1])
        simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi1
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hi1 hi2, hlogT]
    have hIBP : ∫ u in (1 : ℝ)..T, Real.exp (-u) / u =
        Real.log T * Real.exp (-T) + ∫ u in (1 : ℝ)..T, Real.log u * Real.exp (-u) := by
      have hderiv : ∀ u ∈ uIcc 1 T,
          HasDerivAt (fun x => Real.log x * Real.exp (-x))
            (Real.exp (-u) / u - Real.log u * Real.exp (-u)) u := by
        intro u hu
        rw [uIcc_of_le hT] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        have hlog := Real.hasDerivAt_log hu0.ne'
        have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u := by
          simpa using (hasDerivAt_id u).neg.exp
        convert hlog.mul hexp using 1
        field_simp [hu0.ne']
        ring
      have hi1 : IntervalIntegrable (fun u : ℝ => Real.exp (-u) / u) volume 1 T := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hT]
        exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
          fun u hu => by linarith [hu.1]
      have hi2 : IntervalIntegrable (fun u : ℝ => Real.log u * Real.exp (-u)) volume 1 T := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hT]
        exact (Real.continuousOn_log.mono fun u hu => by show u ≠ 0; linarith [hu.1]).mul
          (Real.continuous_exp.comp continuous_neg).continuousOn
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.sub hi2)
      rw [intervalIntegral.integral_sub hi1 hi2] at hFTC
      simp only [Real.log_one, zero_mul, sub_zero] at hFTC
      linarith
    linarith
  have h_prod_zero : Tendsto (fun T : ℝ => Real.log T * Real.exp (-T)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => T * Real.exp (-T)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact mul_nonneg (Real.log_nonneg hT) (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hlog : Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < T)]
      exact mul_le_mul_of_nonneg_right hlog (Real.exp_pos _).le
  have h_tail : Tendsto (fun T : ℝ => ∫ u in (1 : ℝ)..T, Real.log u * Real.exp (-u))
      atTop (𝓝 (∫ u in Set.Ioi (1 : ℝ), Real.log u * Real.exp (-u))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 hIoi1 tendsto_id
  have h_lim : Tendsto (fun T : ℝ =>
      expIntE 1 - Real.log T * Real.exp (-T) - ∫ u in (1 : ℝ)..T, Real.log u * Real.exp (-u))
      atTop (𝓝 (expIntE 1 - 0 - ∫ u in Set.Ioi (1 : ℝ), Real.log u * Real.exp (-u))) :=
    (tendsto_const_nhds.sub h_prod_zero).sub h_tail
  have h_val : expIntE 1 - 0 - ∫ u in Set.Ioi (1 : ℝ), Real.log u * Real.exp (-u) =
      Real.eulerMascheroniConstant := by
    rw [expIntE_one_eq, Real.eulerMascheroniConstant_eq_neg_integral_log]
    have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
    have hadd := MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrableOn_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self) hIoi1
    rw [hunion] at hadd
    linarith
  rw [h_val] at h_lim
  refine h_lim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  exact (hEq T hT).symm

end ExpInt

end

end BuchstabSwitching.External
