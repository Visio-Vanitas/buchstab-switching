import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Quadrature Second-Derivative Bounds for Linear Sieve Integrands

Formalizes the first and second derivatives and uniform second-derivative bounds for:
- `innerQuadIntegrand t = log (t - 1) / t` (`|d²/dt²| ≤ 13 / 10` on `[2, 4]`),
- `outerQuadIntegrand t = (1 / t) ∫_2^(t-1) (log (u - 1) / u) du` (`|d²/dt²| ≤ 3 / 10` on `[3, 5]`).
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

section QuadratureBounds

/-- Inner integrand `g(t) = log (t - 1) / t` used in `F(s)` on `[3, 5]` and `f(s)` on `[2, 6]`. -/
noncomputable def innerQuadIntegrand (t : ℝ) : ℝ := Real.log (t - 1) / t

/-- First derivative of `innerQuadIntegrand` on `(1, ∞)`. -/
noncomputable def innerQuadIntegrand_deriv (t : ℝ) : ℝ :=
  1 / (t * (t - 1)) - Real.log (t - 1) / t ^ 2

/-- Second derivative of `innerQuadIntegrand` on `(1, ∞)`. -/
noncomputable def innerQuadIntegrand_secondDeriv (t : ℝ) : ℝ :=
  2 * Real.log (t - 1) / t ^ 3 - (3 * t - 2) / (t ^ 2 * (t - 1) ^ 2)

theorem hasDerivAt_innerQuadIntegrand {t : ℝ} (ht : 1 < t) :
    HasDerivAt innerQuadIntegrand (innerQuadIntegrand_deriv t) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (t - 1)⁻¹ t := by
    have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
      simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
    simpa using hsub.log ht1
  have hdiv := hlog.div (hasDerivAt_id t) ht0
  convert hdiv using 1
  · rfl
  · unfold innerQuadIntegrand_deriv
    simp only [id_eq]
    field_simp

theorem hasDerivAt_innerQuadIntegrand_deriv {t : ℝ} (ht : 1 < t) :
    HasDerivAt innerQuadIntegrand_deriv (innerQuadIntegrand_secondDeriv t) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hterm1 : HasDerivAt (fun x : ℝ => 1 / (x * (x - 1))) (-(2 * t - 1) / (t ^ 2 * (t - 1) ^ 2)) t := by
    have hden : HasDerivAt (fun x : ℝ => x * (x - 1)) (2 * t - 1) t := by
      have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
        simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
      have hm := (hasDerivAt_id t).mul hsub
      convert hm using 1
      · rfl
      · simp only [id_eq]; ring
    have hinv := hden.inv (mul_ne_zero ht0 ht1)
    convert hinv using 1
    · ext x; simp [one_div]
    · field_simp
  have hterm2 : HasDerivAt (fun x : ℝ => Real.log (x - 1) / x ^ 2)
      (1 / (t ^ 2 * (t - 1)) - 2 * Real.log (t - 1) / t ^ 3) t := by
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (t - 1)⁻¹ t := by
      have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
        simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
      simpa using hsub.log ht1
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      convert (hasDerivAt_id t).pow 2 using 1
      · rfl
      · simp
    have hdiv := hlog.div hsq (pow_ne_zero 2 ht0)
    convert hdiv using 1
    field_simp
  have hsub := hterm1.sub hterm2
  convert hsub using 1
  · rfl
  · unfold innerQuadIntegrand_secondDeriv
    field_simp
    ring

theorem innerQuadIntegrand_nonneg {t : ℝ} (h2 : 2 ≤ t) : 0 ≤ innerQuadIntegrand t := by
  unfold innerQuadIntegrand
  exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)

theorem innerQuadIntegrand_le_half {t : ℝ} (h2 : 2 ≤ t) (_h4 : t ≤ 4) :
    innerQuadIntegrand t ≤ 1 / 2 := by
  unfold innerQuadIntegrand
  have ht0 : 0 < t := by linarith
  have hlog : Real.log (t - 1) ≤ t - 2 := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < t - 1)
    linarith
  rw [div_le_iff₀ ht0]
  linarith

theorem innerQuadIntegrand_deriv_pos {t : ℝ} (h2 : 2 ≤ t) (h4 : t ≤ 4) :
    0 < innerQuadIntegrand_deriv t := by
  unfold innerQuadIntegrand_deriv
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  let w : ℝ → ℝ := fun x => x / (x - 1) - Real.log (x - 1)
  have hw_deriv : ∀ x ∈ uIcc t 4, HasDerivAt w (-(1 / (x - 1) ^ 2 + 1 / (x - 1))) x := by
    intro x hx
    rw [uIcc_of_le h4] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (1 : ℝ)
    have hq : HasDerivAt (fun y : ℝ => y / (y - 1)) (-1 / (x - 1) ^ 2) x := by
      convert (hasDerivAt_id x).div hsub hx1 using 1
      · rfl
      · simp only [id_eq]; field_simp; ring
    have hl : HasDerivAt (fun y : ℝ => Real.log (y - 1)) (1 / (x - 1)) x := by
      simpa [one_div] using hsub.log hx1
    convert hq.sub hl using 1
    ring
  have hw_anti : w 4 ≤ w t := by
    have hint : IntervalIntegrable (fun x => -(1 / (x - 1) ^ 2 + 1 / (x - 1))) volume t 4 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le h4]
      refine ContinuousOn.neg ?_
      refine ContinuousOn.add ?_ ?_
      · exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2) fun x hx =>
          pow_ne_zero 2 (by show x - 1 ≠ 0; linarith [hx.1])
      · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun x hx =>
          by show x - 1 ≠ 0; linarith [hx.1]
    have hFTC := integral_eq_sub_of_hasDerivAt hw_deriv hint
    have hnonneg : 0 ≤ ∫ x in t..4, (1 / (x - 1) ^ 2 + 1 / (x - 1)) := by
      refine intervalIntegral.integral_nonneg h4 fun x hx => ?_
      have hx1 : 0 < x - 1 := by linarith [hx.1]
      positivity
    rw [intervalIntegral.integral_neg] at hFTC
    linarith
  have hw4 : 0 < w 4 := by
    dsimp [w]
    have hlog3 : Real.log 3 < 4 / 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have hexp : (27 : ℝ) < Real.exp 4 := by
        have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have hpow : (2.7 : ℝ) ^ 4 < (Real.exp 1) ^ 4 :=
          pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
        rw [← Real.exp_natCast_mul] at hpow
        norm_num at hpow
        linarith
      have hpow3 : (3 : ℝ) ^ 3 < (Real.exp (4 / 3 : ℝ)) ^ 3 := by
        rw [← Real.exp_natCast_mul]
        norm_num
        exact hexp
      nlinarith [Real.exp_pos (4 / 3 : ℝ), pow_pos (Real.exp_pos (4 / 3 : ℝ)) 2]
    norm_num
    linarith
  have hwt : 0 < w t := lt_of_lt_of_le hw4 hw_anti
  dsimp [w] at hwt
  have hdiff : t / (t - 1) - Real.log (t - 1) > 0 := hwt
  have hmul : 0 < (t / (t - 1) - Real.log (t - 1)) / t ^ 2 :=
    div_pos hdiff (pow_pos ht0 2)
  convert hmul using 1
  field_simp

theorem innerQuadIntegrand_deriv_le_half {t : ℝ} (h2 : 2 ≤ t) (_h4 : t ≤ 4) :
    innerQuadIntegrand_deriv t ≤ 1 / 2 := by
  unfold innerQuadIntegrand_deriv
  have hlog : 0 ≤ Real.log (t - 1) / t ^ 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) (sq_nonneg t)
  have h1 : 1 / (t * (t - 1)) ≤ 1 / 2 := by
    rw [one_div_le_one_div (by nlinarith) (by norm_num)]
    nlinarith
  linarith

theorem innerQuadIntegrand_strictMonoOn :
    StrictMonoOn innerQuadIntegrand (Set.Icc 2 4) := by
  intro a ha b hb hab
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt innerQuadIntegrand (innerQuadIntegrand_deriv t) t := by
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    exact hasDerivAt_innerQuadIntegrand (by linarith [ha.1, ht.1])
  have hcont_d : ContinuousOn innerQuadIntegrand_deriv (Set.Icc a b) := by
    refine ContinuousOn.sub ?_ ?_
    · exact continuousOn_const.div (continuousOn_id.mul (continuousOn_id.sub continuousOn_const))
        fun t ht => mul_ne_zero (by linarith [ha.1, ht.1]) (by show t - 1 ≠ 0; linarith [ha.1, ht.1])
    · exact (ContinuousOn.log (continuousOn_id.sub continuousOn_const) fun t ht =>
        by show t - 1 ≠ 0; linarith [ha.1, ht.1]).div (continuousOn_id.pow 2) fun t ht =>
          pow_ne_zero 2 (by linarith [ha.1, ht.1])
  have hint : IntervalIntegrable innerQuadIntegrand_deriv volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab.le]
    exact hcont_d
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hint
  have hpos : 0 < ∫ t in a..b, innerQuadIntegrand_deriv t := by
    refine integral_pos hab hcont_d ?_ ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    · intro t ht
      exact (innerQuadIntegrand_deriv_pos (by linarith [ha.1, ht.1]) (by linarith [hb.2, ht.2])).le
    · exact innerQuadIntegrand_deriv_pos (by linarith [ha.1]) (by linarith [hb.2])
  linarith

/-- Second-derivative bound `|d²/dt² (log (t - 1) / t)| ≤ 13 / 10` on `[2, 4]`
(in fact `≤ 1`) for the trapezoid rule error in `linear_sieve.py`. -/
theorem abs_innerQuadIntegrand_secondDeriv_le {t : ℝ} (h2 : 2 ≤ t) (_h4 : t ≤ 4) :
    |innerQuadIntegrand_secondDeriv t| ≤ 13 / 10 := by
  unfold innerQuadIntegrand_secondDeriv
  set A : ℝ := 2 * Real.log (t - 1) / t ^ 3
  set B : ℝ := (3 * t - 2) / (t ^ 2 * (t - 1) ^ 2)
  have hA0 : 0 ≤ A := div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) (by positivity)
  have hA_le : A ≤ 1 / 2 := by
    have hlog : Real.log (t - 1) ≤ t - 2 := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < t - 1)
      linarith
    have hpow : (8 : ℝ) ≤ t ^ 3 := by
      have h23 : (2 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
      norm_num at h23
      exact h23
    have hnum : 2 * Real.log (t - 1) ≤ 4 := by linarith
    calc A = 2 * Real.log (t - 1) / t ^ 3 := rfl
      _ ≤ 4 / 8 := div_le_div₀ (by norm_num) hnum (by norm_num) hpow
      _ = 1 / 2 := by norm_num
  have hB0 : 0 ≤ B := div_nonneg (by linarith) (by positivity)
  have hB_le : B ≤ 1 := by
    have ht1 : 0 < t - 1 := by linarith
    have hden_pos : 0 < t ^ 2 * (t - 1) ^ 2 := by positivity
    rw [div_le_one hden_pos]
    have hu : 0 ≤ t - 2 := by linarith
    have hid : t ^ 2 * (t - 1) ^ 2 - (3 * t - 2) =
        9 * (t - 2) + 13 * (t - 2) ^ 2 + 6 * (t - 2) ^ 3 + (t - 2) ^ 4 := by ring
    nlinarith [sq_nonneg (t - 2), pow_nonneg hu 3, pow_nonneg hu 4]
  rw [abs_le]
  constructor <;> linarith

theorem abs_second_deriv_log_sub_one_div_le {t : ℝ} (h2 : 2 ≤ t) (h4 : t ≤ 4) :
    |deriv (deriv (fun u : ℝ => Real.log (u - 1) / u)) t| ≤ 13 / 10 := by
  have h1 : ∀ᶠ u in 𝓝 t, deriv (fun x : ℝ => Real.log (x - 1) / x) u = innerQuadIntegrand_deriv u := by
    filter_upwards [Ioi_mem_nhds (by linarith : (1 : ℝ) < t)] with u hu
    exact (hasDerivAt_innerQuadIntegrand hu).deriv
  rw [Filter.EventuallyEq.deriv_eq h1, (hasDerivAt_innerQuadIntegrand_deriv (by linarith)).deriv]
  exact abs_innerQuadIntegrand_secondDeriv_le h2 h4

/-- Outer integrand `(1 / t) ∫_2^(t-1) (log (u - 1) / u) du` on `[3, 5]` in `linear_sieve.py`. -/
noncomputable def outerQuadIntegrand (t : ℝ) : ℝ :=
  (1 / t) * ∫ u in (2 : ℝ)..(t - 1), innerQuadIntegrand u

/-- First derivative of `outerQuadIntegrand` for `t > 2`. -/
noncomputable def outerQuadIntegrand_deriv (t : ℝ) : ℝ :=
  innerQuadIntegrand (t - 1) / t - (∫ u in (2 : ℝ)..(t - 1), innerQuadIntegrand u) / t ^ 2

/-- Second derivative of `outerQuadIntegrand` for `t > 2`. -/
noncomputable def outerQuadIntegrand_secondDeriv (t : ℝ) : ℝ :=
  innerQuadIntegrand_deriv (t - 1) / t - 2 * innerQuadIntegrand (t - 1) / t ^ 2 +
    2 * (∫ u in (2 : ℝ)..(t - 1), innerQuadIntegrand u) / t ^ 3

private theorem innerQuadIntegrand_continuousOn :
    ContinuousOn innerQuadIntegrand (Set.Ioi 1) := by
  refine ContinuousOn.div ?_ continuousOn_id fun u hu => by linarith [Set.mem_Ioi.mp hu]
  exact ContinuousOn.log (continuousOn_id.sub continuousOn_const) fun u hu => by
    linarith [Set.mem_Ioi.mp hu]

private theorem hasDerivAt_innerQuad_primitive {t : ℝ} (ht : 2 < t) :
    HasDerivAt (fun x : ℝ => ∫ u in (2 : ℝ)..(x - 1), innerQuadIntegrand u)
      (innerQuadIntegrand (t - 1)) t := by
  have ht1 : 1 < t - 1 := by linarith
  have hi : IntervalIntegrable innerQuadIntegrand volume 2 (t - 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine innerQuadIntegrand_continuousOn.mono fun u hu => ?_
    rw [Set.mem_uIcc] at hu
    rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith
  have hca : ContinuousAt innerQuadIntegrand (t - 1) :=
    innerQuadIntegrand_continuousOn.continuousAt (Ioi_mem_nhds ht1)
  have hmeas : StronglyMeasurableAtFilter innerQuadIntegrand (𝓝 (t - 1)) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi innerQuadIntegrand_continuousOn (t - 1) ht1
  have hI := intervalIntegral.integral_hasDerivAt_right hi hmeas hca
  have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
  convert hI.comp t hsub using 1
  · rfl
  · ring

theorem hasDerivAt_outerQuadIntegrand {t : ℝ} (ht : 2 < t) :
    HasDerivAt outerQuadIntegrand (outerQuadIntegrand_deriv t) t := by
  have ht0 : t ≠ 0 := by linarith
  have h1t : HasDerivAt (fun x : ℝ => 1 / x) (-1 / t ^ 2) t := by
    convert (hasDerivAt_id t).inv ht0 using 1
    · ext x; simp [one_div]
    · simp only [id_eq]
  have hI := hasDerivAt_innerQuad_primitive ht
  have hmul := h1t.mul hI
  convert hmul using 1
  · rfl
  · unfold outerQuadIntegrand_deriv
    ring

theorem hasDerivAt_outerQuadIntegrand_deriv {t : ℝ} (ht : 2 < t) :
    HasDerivAt outerQuadIntegrand_deriv (outerQuadIntegrand_secondDeriv t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
  have hg : HasDerivAt (fun x : ℝ => innerQuadIntegrand (x - 1))
      (innerQuadIntegrand_deriv (t - 1)) t := by
    convert (hasDerivAt_innerQuadIntegrand (by linarith : 1 < t - 1)).comp t hsub using 1
    · rfl
    · ring
  have hterm1 : HasDerivAt (fun x : ℝ => innerQuadIntegrand (x - 1) / x)
      ((innerQuadIntegrand_deriv (t - 1) * t - innerQuadIntegrand (t - 1)) / t ^ 2) t := by
    convert hg.div (hasDerivAt_id t) ht0 using 1
    · rfl
    · simp only [id_eq]; ring
  have hI := hasDerivAt_innerQuad_primitive ht
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1
    · rfl
    · simp only [id_eq]; ring
  have hterm2 : HasDerivAt (fun x : ℝ => (∫ u in (2 : ℝ)..(x - 1), innerQuadIntegrand u) / x ^ 2)
      ((innerQuadIntegrand (t - 1) * t ^ 2 -
        (∫ u in (2 : ℝ)..(t - 1), innerQuadIntegrand u) * (2 * t)) / (t ^ 2) ^ 2) t :=
    hI.div hsq (pow_ne_zero 2 ht0)
  have hdiff := hterm1.sub hterm2
  convert hdiff using 1
  · rfl
  · unfold outerQuadIntegrand_secondDeriv
    field_simp
    ring

/-- Outer integrand second-derivative bound `≤ 3 / 10` (in fact `≤ 1 / 6`) on `[3, 5]`
used in `linear_sieve.py`. -/
theorem abs_outerQuadIntegrand_secondDeriv_le {t : ℝ} (h3 : 3 ≤ t) (h5 : t ≤ 5) :
    |outerQuadIntegrand_secondDeriv t| ≤ 3 / 10 := by
  unfold outerQuadIntegrand_secondDeriv
  set Ival : ℝ := ∫ u in (2 : ℝ)..(t - 1), innerQuadIntegrand u
  set A : ℝ := innerQuadIntegrand_deriv (t - 1) / t
  set B : ℝ := 2 * innerQuadIntegrand (t - 1) / t ^ 2 - 2 * Ival / t ^ 3
  have ht1_2 : 2 ≤ t - 1 := by linarith
  have ht1_4 : t - 1 ≤ 4 := by linarith
  have ht0 : 0 < t := by linarith
  have hA0 : 0 ≤ A :=
    div_nonneg (innerQuadIntegrand_deriv_pos ht1_2 ht1_4).le ht0.le
  have hA_le : A ≤ 1 / 6 := by
    have h1 := innerQuadIntegrand_deriv_le_half ht1_2 ht1_4
    calc A = innerQuadIntegrand_deriv (t - 1) / t := rfl
      _ ≤ (1 / 2) / 3 := div_le_div₀ (by norm_num) h1 (by norm_num) h3
      _ = 1 / 6 := by norm_num
  have hI_nonneg : 0 ≤ Ival := by
    refine intervalIntegral.integral_nonneg ht1_2 fun u hu => ?_
    exact innerQuadIntegrand_nonneg (by linarith [hu.1])
  have hI_le : Ival ≤ t * innerQuadIntegrand (t - 1) := by
    have hi : IntervalIntegrable innerQuadIntegrand volume 2 (t - 1) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine innerQuadIntegrand_continuousOn.mono fun u hu => ?_
      rw [uIcc_of_le ht1_2] at hu
      simp only [Set.mem_Ioi]; linarith [hu.1]
    have hmono : Ival ≤ (t - 3) * innerQuadIntegrand (t - 1) := by
      have hc : (t - 3) * innerQuadIntegrand (t - 1) =
          ∫ _ in (2 : ℝ)..(t - 1), innerQuadIntegrand (t - 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      rw [hc]
      refine integral_mono_on ht1_2 hi intervalIntegrable_const fun u hu => ?_
      exact innerQuadIntegrand_strictMonoOn.monotoneOn ⟨hu.1, hu.2.trans ht1_4⟩ ⟨ht1_2, ht1_4⟩ hu.2
    have hnn := innerQuadIntegrand_nonneg ht1_2
    nlinarith
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have h1 : 2 * Ival / t ^ 3 ≤ 2 * (t * innerQuadIntegrand (t - 1)) / t ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hI_le (by norm_num)) (by positivity)
    have h2 : 2 * (t * innerQuadIntegrand (t - 1)) / t ^ 3 = 2 * innerQuadIntegrand (t - 1) / t ^ 2 := by
      field_simp
    linarith
  have hB_le : B ≤ 1 / 9 := by
    have h1 : 2 * innerQuadIntegrand (t - 1) / t ^ 2 ≤ 2 * (1 / 2) / 3 ^ 2 := by
      refine div_le_div₀ (by norm_num) ?_ (by norm_num) (by nlinarith)
      linarith [innerQuadIntegrand_le_half ht1_2 ht1_4]
    have h2 : 0 ≤ 2 * Ival / t ^ 3 := div_nonneg (mul_nonneg (by norm_num) hI_nonneg) (by positivity)
    dsimp [B]
    linarith
  have heq : innerQuadIntegrand_deriv (t - 1) / t - 2 * innerQuadIntegrand (t - 1) / t ^ 2 +
      2 * Ival / t ^ 3 = A - B := by
    dsimp [A, B]; ring
  rw [heq, abs_le]
  constructor <;> linarith

theorem abs_second_deriv_outerQuadIntegrand_le {t : ℝ} (h3 : 3 ≤ t) (h5 : t ≤ 5) :
    |deriv (deriv outerQuadIntegrand) t| ≤ 3 / 10 := by
  have h1 : ∀ᶠ x in 𝓝 t, deriv outerQuadIntegrand x = outerQuadIntegrand_deriv x := by
    filter_upwards [Ioi_mem_nhds (by linarith : (2 : ℝ) < t)] with x hx
    exact (hasDerivAt_outerQuadIntegrand hx).deriv
  rw [Filter.EventuallyEq.deriv_eq h1, (hasDerivAt_outerQuadIntegrand_deriv (by linarith)).deriv]
  exact abs_outerQuadIntegrand_secondDeriv_le h3 h5

end QuadratureBounds

end BuchstabSwitching
