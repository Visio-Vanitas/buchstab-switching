import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import BuchstabSwitchingK2.External.CitedPremisesK2

/-!
# Smooth Explicit-Formula Kernels & Critical-Line Mellin Bounds (`1 + 2`)

Constructs and certifies in Lean `v4.36.0` (zero `sorry`, zero custom `axiom`):

1. **General Admissible Kernel Mellin Theory**:
   - Any `External.SmoothedKernelAdmissible Φ δ` has an entire Mellin transform
     (`differentiable_mellin_of_admissible`), compact interval integral representation on `[δ, 1 - δ]`,
     two-fold integration-by-parts identity `s * (s + 1) * mellin Φ s = ∫_δ^{1-δ} t^(s+1) Φ''(t) dt`,
     and vertical `L¹` integrability (`verticalIntegrable_mellin_of_admissible`) on every line `σ > 0`.
2. **Mellin Inversion Uncertainty Barrier**:
   - Pointwise bound `sqrt_mul_abs_le_inv_two_pi_mellin_l1`: `√u * |Φ u| ≤ (1 / (2π)) ∫ ‖Φ̃(1/2 + it)‖ dt`.
   - Global mass bound `mass_le_two_sub_sqrt_mul_mellin_l1`.
3. **Explicit `C²` Polynomial Spline Kernel `polySplineKernel` (`δ = 1 / 25`, `∫_0^1 Φ = 1`)**:
   - Normalized Beta(4, 4) spline `Φ(u) = (875 / 368) * (1 - ((u - 1/2) / (23/50))^2)^3` on `[1/25, 24/25]`,
     with exact unit integral `∫_0^1 Φ = 1`, `Φ_max = 875 / 368`, and explicit 0-, 2-, and 3-fold
     integration-by-parts bounds on `mellin Φ s`.
-/

namespace BuchstabSwitchingK2.SmoothExplicitFormula

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

noncomputable section

/-! ### Part 1: General Mellin Properties of `SmoothedKernelAdmissible` Kernels -/

lemma continuous_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) : Continuous Φ :=
  hΦ.contDiff_two.continuous

lemma supp_lo_le_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) {u : ℝ} (hu : u ≤ δ) : Φ u = 0 := by
  rcases lt_or_eq_of_le hu with hlt | h_eq
  · exact hΦ.supp_lo u hlt
  · rw [h_eq]
    have hc : Continuous Φ := continuous_of_admissible hΦ
    have ht1 : Tendsto Φ (𝓝[<] δ) (𝓝 (Φ δ)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (0 : ℝ → ℝ) =ᶠ[𝓝[<] δ] Φ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hΦ.supp_lo x hx).symm
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr' hev)

lemma supp_hi_ge_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) {u : ℝ} (hu : 1 - δ ≤ u) : Φ u = 0 := by
  rcases lt_or_eq_of_le hu with hlt | h_eq
  · exact hΦ.supp_hi u hlt
  · rw [← h_eq]
    have hc : Continuous Φ := continuous_of_admissible hΦ
    have ht1 : Tendsto Φ (𝓝[>] (1 - δ)) (𝓝 (Φ (1 - δ))) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (0 : ℝ → ℝ) =ᶠ[𝓝[>] (1 - δ)] Φ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hΦ.supp_hi x hx).symm
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr' hev)

lemma isBigO_atTop_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) (a : ℝ) :
    (fun t : ℝ => (Φ t : ℂ)) =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 - δ)] with t ht
  rw [supp_hi_ge_of_admissible hΦ ht, Complex.ofReal_zero, norm_zero, zero_mul]

lemma isBigO_nhdsGT_zero_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) (b : ℝ) :
    (fun t : ℝ => (Φ t : ℂ)) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  have hmem : Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hΦ.delta_pos
  filter_upwards [hmem] with t ht
  rw [hΦ.supp_lo t ht.2, Complex.ofReal_zero, norm_zero, zero_mul]

lemma locallyIntegrableOn_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) :
    LocallyIntegrableOn (fun t : ℝ => (Φ t : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp (continuous_of_admissible hΦ)).locallyIntegrable.locallyIntegrableOn _

/-- Every admissible compactly supported smooth kernel has a convergent Mellin integral on all of `ℂ`. -/
theorem mellinConvergent_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) (s : ℂ) :
    MellinConvergent (fun t : ℝ => (Φ t : ℂ)) s :=
  mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_of_admissible hΦ)
    (isBigO_atTop_of_admissible hΦ (s.re + 1)) (by linarith)
    (isBigO_nhdsGT_zero_of_admissible hΦ (s.re - 1)) (by linarith)

/-- Every admissible compactly supported smooth kernel has an entire Mellin transform on `ℂ`. -/
theorem differentiable_mellin_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) :
    Differentiable ℂ (mellin (fun t : ℝ => (Φ t : ℂ))) := by
  intro s
  exact (mellin_hasDerivAt_of_isBigO_rpow (locallyIntegrableOn_of_admissible hΦ)
    (isBigO_atTop_of_admissible hΦ (s.re + 1)) (by linarith)
    (isBigO_nhdsGT_zero_of_admissible hΦ (s.re - 1)) (by linarith)).2.differentiableAt

/-- For an admissible kernel supported in `[δ, 1 - δ]`, `mellin` reduces to a compact interval integral. -/
theorem mellin_eq_intervalIntegral_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) (s : ℂ) :
    mellin (fun t : ℝ => (Φ t : ℂ)) s =
      ∫ t in δ..(1 - δ), (t : ℂ) ^ (s - 1) * (Φ t : ℂ) := by
  have hle : δ ≤ 1 - δ := by linarith [hΦ.delta_lt_half]
  have hconv : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Φ t : ℂ)) (Ioi 0) :=
    mellinConvergent_of_admissible hΦ s
  have hunion : Ioi (0 : ℝ) = Ioc 0 δ ∪ Ioc δ (1 - δ) ∪ Ioi (1 - δ) := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      rcases le_or_gt x δ with h1 | h1
      · exact Or.inl (Or.inl ⟨hx, h1⟩)
      · rcases le_or_gt x (1 - δ) with h2 | h2
        · exact Or.inl (Or.inr ⟨h1, h2⟩)
        · exact Or.inr h2
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | hx) <;> linarith [hΦ.delta_pos]
  have hdisj1 : Disjoint (Ioc (0 : ℝ) δ) (Ioc δ (1 - δ)) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj2 : Disjoint (Ioc (0 : ℝ) δ ∪ Ioc δ (1 - δ)) (Ioi (1 - δ)) := by
    refine Set.disjoint_left.mpr fun _ hx1 hx2 => ?_
    rcases hx1 with hx1 | hx1 <;> linarith [hx1.2, mem_Ioi.mp hx2]
  have hint_all : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Φ t : ℂ))
      (Ioc 0 δ ∪ Ioc δ (1 - δ) ∪ Ioi (1 - δ)) := hunion ▸ hconv
  have hint12 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Φ t : ℂ))
      (Ioc 0 δ ∪ Ioc δ (1 - δ)) := hint_all.mono_set Set.subset_union_left
  have hint3 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Φ t : ℂ)) (Ioi (1 - δ)) :=
    hint_all.mono_set Set.subset_union_right
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Φ t : ℂ)) (Ioc 0 δ) :=
    hint12.mono_set Set.subset_union_left
  have hint2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Φ t : ℂ)) (Ioc δ (1 - δ)) :=
    hint12.mono_set Set.subset_union_right
  rw [mellin, hunion, setIntegral_union hdisj2 measurableSet_Ioi hint12 hint3,
    setIntegral_union hdisj1 measurableSet_Ioc hint1 hint2]
  have hz1 : ∫ t in Ioc 0 δ, (t : ℂ) ^ (s - 1) • (Φ t : ℂ) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    rw [supp_lo_le_of_admissible hΦ ht.2, Complex.ofReal_zero, smul_zero]
  have hz3 : ∫ t in Ioi (1 - δ), (t : ℂ) ^ (s - 1) • (Φ t : ℂ) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    rw [hΦ.supp_hi t ht, Complex.ofReal_zero, smul_zero]
  rw [hz1, hz3, zero_add, add_zero, intervalIntegral.integral_of_le hle]
  simp only [smul_eq_mul]

/-- For an admissible kernel supported in `[δ, 1 - δ]`, `∫_0^1 Φ = ∫_δ^{1-δ} Φ`. -/
theorem integral_zero_one_eq_interval_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) :
    ∫ u in (0 : ℝ)..1, Φ u = ∫ u in δ..(1 - δ), Φ u := by
  have hc : Continuous Φ := continuous_of_admissible hΦ
  have h1 : (0 : ℝ) ≤ δ := hΦ.delta_pos.le
  have h2 : 1 - δ ≤ 1 := by linarith [hΦ.delta_pos]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 (1 - δ)) (hc.intervalIntegrable (1 - δ) 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 δ) (hc.intervalIntegrable δ (1 - δ))]
  have hz_lo : ∫ u in (0 : ℝ)..δ, Φ u = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_).trans
      intervalIntegral.integral_zero
    rw [Set.uIcc_of_le h1] at hu
    exact supp_lo_le_of_admissible hΦ hu.2
  have hz_hi : ∫ u in (1 - δ)..1, Φ u = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_).trans
      intervalIntegral.integral_zero
    rw [Set.uIcc_of_le h2] at hu
    exact supp_hi_ge_of_admissible hΦ hu.1
  rw [hz_lo, hz_hi, zero_add, add_zero]

lemma contDiff_one_deriv_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) :
    ContDiff ℝ 1 (deriv Φ) := by
  have h2 : ContDiff ℝ ((1 : ℕ) + 1) Φ := hΦ.contDiff_two
  exact (contDiff_succ_iff_deriv.mp h2).2.2

lemma deriv_eq_zero_at_endpoints_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) :
    deriv Φ δ = 0 ∧ deriv Φ (1 - δ) = 0 := by
  have hc1 : Continuous (deriv Φ) := (contDiff_one_deriv_of_admissible hΦ).continuous
  constructor
  · have hev : (0 : ℝ → ℝ) =ᶠ[𝓝[<] δ] deriv Φ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x < δ := hx
      have heq : Φ =ᶠ[𝓝 x] 0 := by
        filter_upwards [Iio_mem_nhds hx'] with y hy
        exact hΦ.supp_lo y hy
      simpa using heq.deriv_eq.symm
    have ht1 : Tendsto (deriv Φ) (𝓝[<] δ) (𝓝 (deriv Φ δ)) :=
      hc1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr' hev)
  · have hev : (0 : ℝ → ℝ) =ᶠ[𝓝[>] (1 - δ)] deriv Φ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 1 - δ < x := hx
      have heq : Φ =ᶠ[𝓝 x] 0 := by
        filter_upwards [Ioi_mem_nhds hx'] with y hy
        exact hΦ.supp_hi y hy
      simpa using heq.deriv_eq.symm
    have ht1 : Tendsto (deriv Φ) (𝓝[>] (1 - δ)) (𝓝 (deriv Φ (1 - δ))) :=
      hc1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique ht1 (tendsto_const_nhds.congr' hev)

lemma ibp_real_weight_cpow {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContDiff ℝ 1 f) (hfa : f a = 0) (hfb : f b = 0) {w : ℂ} (hw : w ≠ 0) :
    ∫ t in a..b, (t : ℂ) ^ (w - 1) * Complex.ofReal (f t) =
      -(1 / w) * ∫ t in a..b, (t : ℂ) ^ w * Complex.ofReal (deriv f t) := by
  have ht_pos : ∀ t ∈ Set.uIcc a b, 0 < t := fun t ht => by
    rw [Set.uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  let U : ℝ → ℂ := fun t => Complex.ofReal (f t)
  let U' : ℝ → ℂ := fun t => Complex.ofReal (deriv f t)
  let V : ℝ → ℂ := fun t => (t : ℂ) ^ w / w
  let V' : ℝ → ℂ := fun t => (t : ℂ) ^ (w - 1)
  have hU : ∀ t ∈ Set.uIcc a b, HasDerivAt U (U' t) t := fun t _ =>
    ((hf.differentiable one_ne_zero t).hasDerivAt).ofReal_comp
  have hV : ∀ t ∈ Set.uIcc a b, HasDerivAt V (V' t) t := fun t ht => by
    have ht0 : 0 < ((t : ℂ)).re := by simpa using ht_pos t ht
    have hcpow : HasDerivAt (fun z : ℂ => z ^ w) (w * (t : ℂ) ^ (w - 1)) (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).cpow_const (Or.inl ht0)
    have hd := (hcpow.comp_ofReal).div_const w
    refine hd.congr_deriv ?_
    dsimp only [V']
    field_simp [hw]
  have hU'_int : IntervalIntegrable U' volume a b :=
    (Complex.continuous_ofReal.comp (hf.continuous_deriv le_rfl)).intervalIntegrable a b
  have hV'_cont : ContinuousOn V' (Set.uIcc a b) := by
    intro t ht
    exact (continuousAt_ofReal_cpow_const t (w - 1) (Or.inr (ht_pos t ht).ne')).continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hU hV
    hU'_int hV'_cont.intervalIntegrable
  have hcomm1 : ∫ t in a..b, (t : ℂ) ^ (w - 1) * Complex.ofReal (f t) = ∫ t in a..b, U t * V' t :=
    intervalIntegral.integral_congr fun _ _ => mul_comm _ _
  rw [hcomm1, hibp]
  simp only [U, V, U', hfa, hfb, Complex.ofReal_zero, zero_mul, sub_zero, zero_sub]
  have hpull : ∫ t in a..b, Complex.ofReal (deriv f t) * ((t : ℂ) ^ w / w) =
      (1 / w) * ∫ t in a..b, (t : ℂ) ^ w * Complex.ofReal (deriv f t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun _ _ => ?_
    ring
  rw [hpull]
  ring

/-- Two-fold integration by parts for the Mellin transform of any admissible smooth kernel. -/
theorem mellin_mul_s_mul_add_one_eq_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    s * (s + 1) * mellin (fun t : ℝ => (Φ t : ℂ)) s =
      ∫ t in δ..(1 - δ), (t : ℂ) ^ (s + 1) * Complex.ofReal (deriv (deriv Φ) t) := by
  have hle : δ ≤ 1 - δ := by linarith [hΦ.delta_lt_half]
  have hc1 : ContDiff ℝ 1 Φ := hΦ.contDiff_two.of_le (by norm_num)
  have hc2 : ContDiff ℝ 1 (deriv Φ) := contDiff_one_deriv_of_admissible hΦ
  rcases deriv_eq_zero_at_endpoints_of_admissible hΦ with ⟨hd_lo, hd_hi⟩
  rw [mellin_eq_intervalIntegral_of_admissible hΦ s,
    ibp_real_weight_cpow hΦ.delta_pos hle hc1
      (supp_lo_le_of_admissible hΦ le_rfl) (supp_hi_ge_of_admissible hΦ le_rfl) hs0]
  have hstep2 := ibp_real_weight_cpow hΦ.delta_pos hle hc2 hd_lo hd_hi hs1
  have hexp : (s + 1) - 1 = s := by ring
  rw [hexp] at hstep2
  rw [hstep2]
  field_simp [hs0, hs1]

/-- Every `SmoothedKernelAdmissible` kernel has a vertically `L¹`-integrable Mellin transform
along every vertical line `Re(s) = σ > 0`. -/
theorem verticalIntegrable_mellin_of_admissible {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) {σ : ℝ} (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin (fun t : ℝ => (Φ t : ℂ))) σ := by
  have hle : δ ≤ 1 - δ := by linarith [hΦ.delta_lt_half]
  have hc_d2 : Continuous (deriv (deriv Φ)) :=
    (contDiff_one_deriv_of_admissible hΦ).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc δ (1 - δ), |deriv (deriv Φ) t| ≤ M := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc_d2.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun t ht => le_trans (by simpa using hC t ht) (le_max_left _ _)⟩
  have h1mδ_pos : 0 < 1 - δ := by linarith [hΦ.delta_lt_half]
  let B : ℝ := M * (1 - δ) ^ (σ + 1)
  have hB_nn : 0 ≤ B := mul_nonneg hM.1 (Real.rpow_nonneg h1mδ_pos.le _)
  have hcont_line : Continuous (fun y : ℝ => mellin (fun t : ℝ => (Φ t : ℂ)) ((σ : ℂ) + (y : ℂ) * I)) :=
    (differentiable_mellin_of_admissible hΦ).continuous.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hmaj_int : Integrable (fun y : ℝ => (B / σ ^ 2) * (1 + (σ⁻¹ * y) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hσ.ne')).const_mul (B / σ ^ 2)
  refine hmaj_int.mono' hcont_line.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  let s : ℂ := (σ : ℂ) + (y : ℂ) * I
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = y := by simp [s]
  have hs_sq : ‖s‖ ^ 2 = σ ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hs_re, hs_im]
    ring
  have hs_le : ‖s‖ ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, one_re, add_im, one_im, add_zero, hs_re, hs_im]
    nlinarith
  have hs_norm_sq : σ ^ 2 + y ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    calc σ ^ 2 + y ^ 2 = ‖s‖ * ‖s‖ := by linear_combination -hs_sq
      _ ≤ ‖s‖ * ‖s + 1‖ := mul_le_mul_of_nonneg_left hs_le (norm_nonneg _)
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs_re; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [hs_re] at hre
    linarith
  have hibp := mellin_mul_s_mul_add_one_eq_of_admissible hΦ (s := s) hs0 hs1
  have hint_bd : ‖∫ t in δ..(1 - δ), (t : ℂ) ^ (s + 1) * Complex.ofReal (deriv (deriv Φ) t)‖ ≤ B := by
    have hpt : ∀ t ∈ Set.uIoc δ (1 - δ),
        ‖(t : ℂ) ^ (s + 1) * Complex.ofReal (deriv (deriv Φ) t)‖ ≤ B := by
      intro t ht
      rw [Set.uIoc_of_le hle] at ht
      have ht_pos : 0 < t := lt_trans hΦ.delta_pos ht.1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, Complex.norm_real, Real.norm_eq_abs]
      have hre1 : (s + 1).re = σ + 1 := by simp [hs_re]
      rw [hre1]
      have hrp : t ^ (σ + 1) ≤ (1 - δ) ^ (σ + 1) :=
        Real.rpow_le_rpow ht_pos.le ht.2 (by linarith)
      calc t ^ (σ + 1) * |deriv (deriv Φ) t|
          ≤ (1 - δ) ^ (σ + 1) * M :=
            mul_le_mul hrp (hM.2 t ⟨ht.1.le, ht.2⟩) (abs_nonneg _) (Real.rpow_nonneg h1mδ_pos.le _)
        _ = B := by ring
    calc ‖∫ t in δ..(1 - δ), (t : ℂ) ^ (s + 1) * Complex.ofReal (deriv (deriv Φ) t)‖
        ≤ B * |(1 - δ) - δ| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ ≤ B * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hB_nn
        rw [abs_of_nonneg (by linarith)]
        linarith [hΦ.delta_pos]
      _ = B := mul_one B
  have hprod_bd : (σ ^ 2 + y ^ 2) * ‖mellin (fun t : ℝ => (Φ t : ℂ)) s‖ ≤ B := by
    calc (σ ^ 2 + y ^ 2) * ‖mellin (fun t : ℝ => (Φ t : ℂ)) s‖
        ≤ (‖s‖ * ‖s + 1‖) * ‖mellin (fun t : ℝ => (Φ t : ℂ)) s‖ :=
          mul_le_mul_of_nonneg_right hs_norm_sq (norm_nonneg _)
      _ = ‖s * (s + 1) * mellin (fun t : ℝ => (Φ t : ℂ)) s‖ := by rw [norm_mul, norm_mul]
      _ ≤ B := hibp ▸ hint_bd
  have hden_pos : 0 < σ ^ 2 + y ^ 2 := by positivity
  have hdiv : ‖mellin (fun t : ℝ => (Φ t : ℂ)) s‖ ≤ B / (σ ^ 2 + y ^ 2) :=
    (le_div_iff₀ hden_pos).mpr (by linarith)
  have hrew : B / (σ ^ 2 + y ^ 2) = (B / σ ^ 2) * (1 + (σ⁻¹ * y) ^ 2)⁻¹ := by
    field_simp [hσ.ne', hden_pos.ne']
  exact hdiv.trans_eq hrew

/-! ### Part 2: Universal Mellin Inversion Uncertainty Barrier -/

/-- **Pointwise Critical-Line Mellin Uncertainty Bound**: for any admissible smooth kernel `Φ` and
`u > 0`, `√u * |Φ u| ≤ (1 / (2π)) ∫_ℝ ‖Φ̃(1/2 + it)‖ dt`. -/
theorem sqrt_mul_abs_le_inv_two_pi_mellin_l1 {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) {u : ℝ} (hu : 0 < u) :
    Real.sqrt u * |Φ u| ≤
      (1 / (2 * Real.pi)) *
        ∫ y : ℝ, ‖mellin (fun t : ℝ => (Φ t : ℂ)) ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by
  let fC : ℝ → ℂ := fun t => (Φ t : ℂ)
  have hinv := mellinInv_mellin_eq (1 / 2 : ℝ) fC hu
    (mellinConvergent_of_admissible hΦ _)
    (verticalIntegrable_mellin_of_admissible hΦ (by norm_num))
    (Complex.continuous_ofReal.comp (continuous_of_admissible hΦ)).continuousAt
  have hnorm_eq : |Φ u| = ‖mellinInv (1 / 2 : ℝ) (mellin fC) u‖ := by
    rw [hinv]
    dsimp only [fC]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hpt_norm : ∀ y : ℝ,
      ‖(u : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) •
          mellin fC (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ =
        u ^ (-(1 / 2 : ℝ)) * ‖mellin fC ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by
    intro y
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp
  have hub : |Φ u| ≤ u ^ (-(1 / 2 : ℝ)) *
      ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖mellin fC ((1 / 2 : ℂ) + (y : ℂ) * I)‖) := by
    rw [hnorm_eq, mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
    have hle1 : ‖∫ y : ℝ, (u : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) •
        mellin fC (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        ∫ y : ℝ, ‖(u : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) •
          mellin fC (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ := norm_integral_le_integral_norm _
    have heq2 : (∫ y : ℝ, ‖(u : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) •
          mellin fC (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖) =
        u ^ (-(1 / 2 : ℝ)) * ∫ y : ℝ, ‖mellin fC ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by
      simp_rw [hpt_norm, integral_const_mul]
    have hmul := mul_le_mul_of_nonneg_left (hle1.trans_eq heq2)
      (by positivity : 0 ≤ 1 / (2 * Real.pi))
    linarith
  have hsqrt_pos : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hmul2 := mul_le_mul_of_nonneg_left hub hsqrt_pos
  have hcancel : Real.sqrt u * u ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hu]
    norm_num
  calc Real.sqrt u * |Φ u|
      ≤ Real.sqrt u * (u ^ (-(1 / 2 : ℝ)) *
          ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖mellin fC ((1 / 2 : ℂ) + (y : ℂ) * I)‖)) := hmul2
    _ = (Real.sqrt u * u ^ (-(1 / 2 : ℝ))) *
          ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖mellin fC ((1 / 2 : ℂ) + (y : ℂ) * I)‖) := by ring
    _ = (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖mellin fC ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by
          rw [hcancel, one_mul]

/-- **Global `L¹` Mellin Uncertainty Bound**: for any admissible smooth kernel `Φ` on `[δ, 1 - δ]`,
`∫_0^1 Φ(u) du ≤ 2 (√(1 - δ) - √δ) * (1 / (2π)) ∫_ℝ ‖Φ̃(1/2 + it)‖ dt`. -/
theorem mass_le_two_sub_sqrt_mul_mellin_l1 {Φ : ℝ → ℝ} {δ : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ δ) :
    ∫ u in (0 : ℝ)..1, Φ u ≤
      2 * (Real.sqrt (1 - δ) - Real.sqrt δ) *
        ((1 / (2 * Real.pi)) *
          ∫ y : ℝ, ‖mellin (fun t : ℝ => (Φ t : ℂ)) ((1 / 2 : ℂ) + (y : ℂ) * I)‖) := by
  set I_Φ : ℝ := (1 / (2 * Real.pi)) *
    ∫ y : ℝ, ‖mellin (fun t : ℝ => (Φ t : ℂ)) ((1 / 2 : ℂ) + (y : ℂ) * I)‖
  have hδ0 : 0 < δ := hΦ.delta_pos
  have hle : δ ≤ 1 - δ := by linarith [hΦ.delta_lt_half]
  rw [integral_zero_one_eq_interval_of_admissible hΦ]
  have hg_cont : ContinuousOn (fun u : ℝ => I_Φ * u ^ (-(1 / 2 : ℝ))) (Set.uIcc δ (1 - δ)) := by
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun u hu => ?_)
    rw [Set.uIcc_of_le hle] at hu
    exact Or.inl (lt_of_lt_of_le hδ0 hu.1).ne'
  have hmono : ∫ u in δ..(1 - δ), Φ u ≤ ∫ u in δ..(1 - δ), I_Φ * u ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_mono_on hle
      ((continuous_of_admissible hΦ).intervalIntegrable _ _) hg_cont.intervalIntegrable fun u hu => ?_
    have hu_pos : 0 < u := lt_of_lt_of_le hδ0 hu.1
    have hpt := sqrt_mul_abs_le_inv_two_pi_mellin_l1 hΦ hu_pos
    rw [abs_of_nonneg (hΦ.nonneg u)] at hpt
    have hsq_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
    have hdiv : Φ u ≤ I_Φ / Real.sqrt u := (le_div_iff₀ hsq_pos).mpr (by linarith)
    refine hdiv.trans_eq ?_
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hu_pos.le, div_eq_mul_inv]
  refine hmono.trans_eq ?_
  rw [intervalIntegral.integral_const_mul]
  have h0_not_mem : (0 : ℝ) ∉ Set.uIcc δ (1 - δ) := by
    rw [Set.uIcc_of_le hle]
    intro h0
    linarith [h0.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, h0_not_mem⟩)]
  have hexp : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hexp, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  ring

/-! ### Part 3: Explicit `C²` Polynomial Spline Kernel `polySplineKernel` (`∫_0^1 Φ = 1`) -/

section PolySplineKernel

/-- One-sided cubic `max(0, x)^3`, which is globally `C²` on `ℝ`. -/
def posCube (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ 3 else 0

private def posSq3 (x : ℝ) : ℝ :=
  if 0 ≤ x then 3 * x ^ 2 else 0

private lemma hasDerivAt_posCube (x : ℝ) : HasDerivAt posCube (posSq3 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : posCube =ᶠ[𝓝 x] 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hy' : y < 0 := hy
      simp [posCube, not_le.mpr hy']
    have hd : HasDerivAt (0 : ℝ → ℝ) 0 x := hasDerivAt_const x 0
    simpa [posSq3, not_le.mpr hx] using hd.congr_of_eventuallyEq heq
  · rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsLittleO.of_bound (fun ε hε => ?_)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (Real.sqrt_pos.mpr hε)] with h hh
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
    have hh2 : |h| ^ 2 ≤ ε := by
      have hsq := sq_lt_sq.mpr (by rwa [abs_of_pos (Real.sqrt_pos.mpr hε)] : |h| < |Real.sqrt ε|)
      rw [Real.sq_sqrt hε.le] at hsq
      rw [sq_abs]
      exact hsq.le
    have hpc0 : posCube 0 = 0 := by simp [posCube]
    have hps0 : posSq3 0 = 0 := by simp [posSq3]
    simp only [zero_add, hpc0, sub_zero, hps0, smul_zero, Real.norm_eq_abs]
    unfold posCube
    split_ifs with h0
    · rw [abs_pow]
      calc |h| ^ 3 = |h| ^ 2 * |h| := by ring
        _ ≤ ε * |h| := mul_le_mul_of_nonneg_right hh2 (abs_nonneg h)
    · simp [mul_nonneg hε.le (abs_nonneg h)]
  · have heq : posCube =ᶠ[𝓝 x] (fun y : ℝ => y ^ 3) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      have hy' : 0 < y := hy
      simp [posCube, le_of_lt hy']
    have hd : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      simpa using (hasDerivAt_pow 3 x)
    simpa [posSq3, le_of_lt hx] using hd.congr_of_eventuallyEq heq

private lemma hasDerivAt_posSq3 (x : ℝ) : HasDerivAt posSq3 (6 * max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : posSq3 =ᶠ[𝓝 x] 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hy' : y < 0 := hy
      simp [posSq3, not_le.mpr hy']
    have hd : HasDerivAt (0 : ℝ → ℝ) 0 x := hasDerivAt_const x 0
    simpa [max_eq_left (le_of_lt hx)] using hd.congr_of_eventuallyEq heq
  · rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsLittleO.of_bound (fun ε hε => ?_)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hε (by norm_num : (0 : ℝ) < 3))] with h hh
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
    have hps0 : posSq3 0 = 0 := by simp [posSq3]
    simp only [zero_add, hps0, sub_zero, max_self, mul_zero, smul_zero, Real.norm_eq_abs]
    unfold posSq3
    split_ifs with h0
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_pow]
      calc 3 * |h| ^ 2 = (3 * |h|) * |h| := by ring
        _ ≤ ε * |h| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg h)
    · simp [mul_nonneg hε.le (abs_nonneg h)]
  · have heq : posSq3 =ᶠ[𝓝 x] (fun y : ℝ => 3 * y ^ 2) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      have hy' : 0 < y := hy
      simp [posSq3, le_of_lt hy']
    have hd : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * x) x := by
      have h1 := (hasDerivAt_pow 2 x).const_mul 3
      refine h1.congr_deriv ?_
      ring
    simpa [max_eq_right (le_of_lt hx)] using hd.congr_of_eventuallyEq heq

lemma contDiff_two_posCube : ContDiff ℝ 2 posCube := by
  have hd1 : Differentiable ℝ posCube := fun x => (hasDerivAt_posCube x).differentiableAt
  have hderiv1 : deriv posCube = posSq3 := funext fun x => (hasDerivAt_posCube x).deriv
  have hd2 : Differentiable ℝ posSq3 := fun x => (hasDerivAt_posSq3 x).differentiableAt
  have hderiv2 : deriv posSq3 = fun x => 6 * max (0 : ℝ) x :=
    funext fun x => (hasDerivAt_posSq3 x).deriv
  have hc2 : ContDiff ℝ 1 posSq3 := by
    rw [contDiff_one_iff_deriv]
    refine ⟨hd2, ?_⟩
    rw [hderiv2]
    exact continuous_const.mul ((continuous_const : Continuous fun _ : ℝ => (0 : ℝ)).max continuous_id)
  have hgoal : ContDiff ℝ ((1 : ℕ) + 1) posCube := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨hd1, by simp, ?_⟩
    rwa [hderiv1]
  exact hgoal

/-- Unnormalized Beta(4, 4) spline on `[1/25, 24/25]`. -/
def polySplineRaw (u : ℝ) : ℝ :=
  posCube (u - 1 / 25) * posCube (24 / 25 - u) / (23 / 50 : ℝ) ^ 6

/-- Normalized `C²` polynomial spline kernel on `[1/25, 24/25]` with exact unit `L¹` mass `∫_0^1 Φ = 1`. -/
def polySplineKernel (u : ℝ) : ℝ :=
  (875 / 368 : ℝ) * polySplineRaw u

/-- Pure polynomial formula agreeing with `polySplineKernel` on the closed support `[1/25, 24/25]`. -/
def polySplinePoly (u : ℝ) : ℝ :=
  (875 / 368 : ℝ) * (1 - ((u - 1 / 2) / (23 / 50)) ^ 2) ^ 3

lemma polySplineKernel_eq_poly_of_mem {u : ℝ} (h1 : 1 / 25 ≤ u) (h2 : u ≤ 24 / 25) :
    polySplineKernel u = polySplinePoly u := by
  unfold polySplineKernel polySplineRaw polySplinePoly posCube
  have ha : 0 ≤ u - 1 / 25 := by linarith
  have hb : 0 ≤ 24 / 25 - u := by linarith
  simp only [ha, hb, ↓reduceIte]
  ring

theorem polySplineKernel_nonneg (u : ℝ) : 0 ≤ polySplineKernel u := by
  unfold polySplineKernel polySplineRaw posCube
  have h1 : 0 ≤ if 0 ≤ u - 1 / 25 then (u - 1 / 25) ^ 3 else 0 := by
    split_ifs with h
    · exact pow_nonneg h 3
    · exact le_rfl
  have h2 : 0 ≤ if 0 ≤ 24 / 25 - u then (24 / 25 - u) ^ 3 else 0 := by
    split_ifs with h
    · exact pow_nonneg h 3
    · exact le_rfl
  positivity

theorem polySplineKernel_supp_lo (u : ℝ) (hu : u ≤ 1 / 25) : polySplineKernel u = 0 := by
  unfold polySplineKernel polySplineRaw posCube
  rcases eq_or_lt_of_le hu with rfl | hlt
  · norm_num
  · have hnot : ¬ 0 ≤ u - 1 / 25 := by linarith
    simp only [hnot, ↓reduceIte]
    ring

theorem polySplineKernel_supp_hi (u : ℝ) (hu : 24 / 25 ≤ u) : polySplineKernel u = 0 := by
  unfold polySplineKernel polySplineRaw posCube
  rcases eq_or_lt_of_le hu with rfl | hlt
  · norm_num
  · have hnot : ¬ 0 ≤ 24 / 25 - u := by linarith
    simp only [hnot, ↓reduceIte]
    ring

theorem polySplineKernel_le (u : ℝ) : polySplineKernel u ≤ 875 / 368 := by
  by_cases hlo : u ≤ 1 / 25
  · rw [polySplineKernel_supp_lo u hlo]; norm_num
  by_cases hhi : 24 / 25 ≤ u
  · rw [polySplineKernel_supp_hi u hhi]; norm_num
  rw [polySplineKernel_eq_poly_of_mem (le_of_lt (not_le.mp hlo)) (le_of_lt (not_le.mp hhi))]
  unfold polySplinePoly
  have hv2 : ((u - 1 / 2) / (23 / 50)) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 23 / 50),
      div_le_one (by norm_num), abs_le]
    constructor <;> linarith
  have hbase_nn : 0 ≤ 1 - ((u - 1 / 2) / (23 / 50)) ^ 2 := by linarith
  have hbase_le : 1 - ((u - 1 / 2) / (23 / 50)) ^ 2 ≤ 1 := by
    linarith [sq_nonneg ((u - 1 / 2) / (23 / 50))]
  have hpow : (1 - ((u - 1 / 2) / (23 / 50)) ^ 2) ^ 3 ≤ 1 := by
    calc (1 - ((u - 1 / 2) / (23 / 50)) ^ 2) ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hbase_nn hbase_le 3
      _ = 1 := one_pow 3
  nlinarith

theorem polySplineKernel_contDiff_two : ContDiff ℝ 2 polySplineKernel := by
  unfold polySplineKernel polySplineRaw
  have hc1 : ContDiff ℝ 2 (fun u : ℝ => posCube (u - 1 / 25)) :=
    contDiff_two_posCube.comp (contDiff_id.sub contDiff_const)
  have hc2 : ContDiff ℝ 2 (fun u : ℝ => posCube (24 / 25 - u)) :=
    contDiff_two_posCube.comp (contDiff_const.sub contDiff_id)
  exact contDiff_const.mul ((hc1.mul hc2).div_const _)

/-- Exact rational evaluation `∫_0^1 polySplineKernel u du = 1`. -/
theorem integral_polySplineKernel : ∫ u in (0 : ℝ)..1, polySplineKernel u = 1 := by
  have hc : Continuous polySplineKernel := polySplineKernel_contDiff_two.continuous
  have hsplit : ∫ u in (0 : ℝ)..1, polySplineKernel u =
      (∫ u in (0 : ℝ)..(1 / 25), polySplineKernel u) +
        (∫ u in (1 / 25 : ℝ)..(24 / 25), polySplineKernel u) +
        (∫ u in (24 / 25 : ℝ)..1, polySplineKernel u) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 0 (24 / 25)) (hc.intervalIntegrable (24 / 25) 1),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 0 (1 / 25)) (hc.intervalIntegrable (1 / 25) (24 / 25))]
  have hz1 : ∫ u in (0 : ℝ)..(1 / 25), polySplineKernel u = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_).trans
      intervalIntegral.integral_zero
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact polySplineKernel_supp_lo u hu.2
  have hz3 : ∫ u in (24 / 25 : ℝ)..1, polySplineKernel u = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_).trans
      intervalIntegral.integral_zero
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact polySplineKernel_supp_hi u hu.1
  have hmid : ∫ u in (1 / 25 : ℝ)..(24 / 25), polySplineKernel u = 1 := by
    have hcongr : ∫ u in (1 / 25 : ℝ)..(24 / 25), polySplineKernel u =
        ∫ u in (1 / 25 : ℝ)..(24 / 25), polySplinePoly u := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu
      exact polySplineKernel_eq_poly_of_mem hu.1 hu.2
    rw [hcongr]
    let F : ℝ → ℝ := fun u =>
      (875 / 368 : ℝ) * (23 / 50 : ℝ) *
        (((u - 1 / 2) / (23 / 50)) - ((u - 1 / 2) / (23 / 50)) ^ 3 +
          (3 / 5 : ℝ) * ((u - 1 / 2) / (23 / 50)) ^ 5 -
          (1 / 7 : ℝ) * ((u - 1 / 2) / (23 / 50)) ^ 7)
    have hF : ∀ u ∈ Set.uIcc (1 / 25 : ℝ) (24 / 25), HasDerivAt F (polySplinePoly u) u := by
      intro u _
      have hv : HasDerivAt (fun x : ℝ => (x - 1 / 2) / (23 / 50)) (1 / (23 / 50)) u := by
        simpa using ((hasDerivAt_id u).sub_const (1 / 2 : ℝ)).div_const (23 / 50 : ℝ)
      let v : ℝ := (u - 1 / 2) / (23 / 50)
      have hG : HasDerivAt
          (fun w : ℝ => w - w ^ 3 + (3 / 5 : ℝ) * w ^ 5 - (1 / 7 : ℝ) * w ^ 7)
          ((1 - v ^ 2) ^ 3) v := by
        have hd := (((hasDerivAt_id v).fun_sub (hasDerivAt_pow 3 v)).fun_add
          ((hasDerivAt_pow 5 v).const_mul (3 / 5 : ℝ))).fun_sub
          ((hasDerivAt_pow 7 v).const_mul (1 / 7 : ℝ))
        refine hd.congr_deriv ?_
        ring
      have hcomp : HasDerivAt F
          (((875 / 368 : ℝ) * (23 / 50 : ℝ)) * ((1 - v ^ 2) ^ 3 * (1 / (23 / 50)))) u :=
        (hG.comp u hv).const_mul ((875 / 368 : ℝ) * (23 / 50 : ℝ))
      refine hcomp.congr_deriv ?_
      unfold polySplinePoly
      dsimp only [v]
      ring
    have hint : IntervalIntegrable polySplinePoly volume (1 / 25) (24 / 25) := by
      unfold polySplinePoly
      exact (by fun_prop : Continuous _).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
    dsimp only [F]
    norm_num
  rw [hsplit, hz1, hmid, hz3]
  ring

/-- Unconditional proof that `polySplineKernel` satisfies `External.SmoothedKernelAdmissible` at `δ = 1 / 25`. -/
theorem polySplineKernel_admissible :
    External.SmoothedKernelAdmissible polySplineKernel (1 / 25) where
  delta_pos := by norm_num
  delta_lt_half := by norm_num
  nonneg := polySplineKernel_nonneg
  supp_lo := fun u hu => polySplineKernel_supp_lo u hu.le
  supp_hi := fun u hu => polySplineKernel_supp_hi u (by linarith)
  contDiff_two := polySplineKernel_contDiff_two
  l1_pos := by rw [integral_polySplineKernel]; norm_num

/-- Shorthand for the Mellin transform of `polySplineKernel`. -/
def mellinPolySpline (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (polySplineKernel t : ℂ)) s

theorem differentiable_mellinPolySpline : Differentiable ℂ mellinPolySpline :=
  differentiable_mellin_of_admissible polySplineKernel_admissible

theorem mellinPolySpline_one : mellinPolySpline 1 = 1 := by
  unfold mellinPolySpline
  rw [mellin_eq_intervalIntegral_of_admissible polySplineKernel_admissible 1,
    show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num]
  have h1 : ∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ ((1 : ℂ) - 1) * (polySplineKernel t : ℂ) =
      ∫ t in (1 / 25 : ℝ)..(24 / 25), (polySplineKernel t : ℂ) :=
    intervalIntegral.integral_congr fun _ _ => by simp
  have h2 := integral_zero_one_eq_interval_of_admissible polySplineKernel_admissible
  rw [show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num] at h2
  rw [h1, intervalIntegral.integral_ofReal, ← h2,
    integral_polySplineKernel, Complex.ofReal_one]

/-- Pointwise bound on `mellinPolySpline` along the critical line `Re(s) = 1/2`. -/
theorem norm_mellinPolySpline_crit_le (y : ℝ) :
    ‖mellinPolySpline ((1 / 2 : ℂ) + (y : ℂ) * I)‖ ≤ 5 := by
  unfold mellinPolySpline
  rw [mellin_eq_intervalIntegral_of_admissible polySplineKernel_admissible,
    show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num]
  have hmono : ∀ t ∈ Set.uIoc (1 / 25 : ℝ) (24 / 25),
      ‖(t : ℂ) ^ (((1 / 2 : ℂ) + (y : ℂ) * I) - 1) * (polySplineKernel t : ℂ)‖ ≤
        5 * polySplineKernel t := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have ht_pos : 0 < t := lt_trans (by norm_num) ht.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos,
      Complex.norm_real, Real.norm_of_nonneg (polySplineKernel_nonneg t)]
    have hre : (((1 / 2 : ℂ) + (y : ℂ) * I) - 1).re = -(1 / 2 : ℝ) := by simp; norm_num
    rw [hre]
    have hrpow : t ^ (-(1 / 2 : ℝ)) ≤ 5 := by
      have h1 : (1 / 25 : ℝ) ^ (-(1 / 2 : ℝ)) = 5 := by
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
        norm_num
      rw [← h1]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) ht.1.le (by norm_num)
    exact mul_le_mul_of_nonneg_right hrpow (polySplineKernel_nonneg t)
  have hint : IntervalIntegrable (fun t : ℝ => 5 * polySplineKernel t) volume (1 / 25) (24 / 25) :=
    (continuous_const.mul polySplineKernel_contDiff_two.continuous).intervalIntegrable _ _
  have h2 := integral_zero_one_eq_interval_of_admissible polySplineKernel_admissible
  rw [show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num] at h2
  calc ‖∫ t in (1 / 25 : ℝ)..(24 / 25),
          (t : ℂ) ^ (((1 / 2 : ℂ) + (y : ℂ) * I) - 1) * (polySplineKernel t : ℂ)‖
      ≤ ∫ t in (1 / 25 : ℝ)..(24 / 25), 5 * polySplineKernel t :=
        intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
          (Eventually.of_forall fun t ht => hmono t (Set.Ioc_subset_uIoc ht)) hint
    _ = 5 * ∫ t in (1 / 25 : ℝ)..(24 / 25), polySplineKernel t :=
        intervalIntegral.integral_const_mul 5 _
    _ = 5 := by rw [← h2, integral_polySplineKernel, mul_one]

/-- Pointwise bound on `mellinPolySpline` across `Re(s) ≥ 1/4`. -/
theorem norm_mellinPolySpline_of_quarter_le_re {s : ℂ} (hs : 1 / 4 ≤ s.re) :
    ‖mellinPolySpline s‖ ≤ 12 := by
  unfold mellinPolySpline
  rw [mellin_eq_intervalIntegral_of_admissible polySplineKernel_admissible,
    show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num]
  have hmono : ∀ t ∈ Set.uIoc (1 / 25 : ℝ) (24 / 25),
      ‖(t : ℂ) ^ (s - 1) * (polySplineKernel t : ℂ)‖ ≤ 12 * polySplineKernel t := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have ht_pos : 0 < t := lt_trans (by norm_num) ht.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos,
      Complex.norm_real, Real.norm_of_nonneg (polySplineKernel_nonneg t)]
    have ht1 : t ≤ 1 := by linarith [ht.2]
    have hrpow1 : t ^ (s - 1).re ≤ t ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht_pos ht1 (by simp; linarith)
    have hrpow2 : t ^ (-(3 / 4 : ℝ)) ≤ (1 / 25 : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) ht.1.le (by norm_num)
    have h25 : (1 / 25 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 12 := by
      have hsq : ((1 / 25 : ℝ) ^ (-(3 / 4 : ℝ))) ^ 2 = 125 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        have he : -(3 / 4 : ℝ) * (2 : ℕ) = -(3 / 2 : ℝ) := by norm_num
        rw [he, show (1 / 25 : ℝ) = (5 : ℝ) ^ (-2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 25) (-(3 / 4 : ℝ))]
    exact mul_le_mul_of_nonneg_right ((hrpow1.trans hrpow2).trans h25) (polySplineKernel_nonneg t)
  have hint : IntervalIntegrable (fun t : ℝ => 12 * polySplineKernel t) volume (1 / 25) (24 / 25) :=
    (continuous_const.mul polySplineKernel_contDiff_two.continuous).intervalIntegrable _ _
  have h2 := integral_zero_one_eq_interval_of_admissible polySplineKernel_admissible
  rw [show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num] at h2
  calc ‖∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ (s - 1) * (polySplineKernel t : ℂ)‖
      ≤ ∫ t in (1 / 25 : ℝ)..(24 / 25), 12 * polySplineKernel t :=
        intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
          (Eventually.of_forall fun t ht => hmono t (Set.Ioc_subset_uIoc ht)) hint
    _ = 12 * ∫ t in (1 / 25 : ℝ)..(24 / 25), polySplineKernel t :=
        intervalIntegral.integral_const_mul 12 _
    _ = 12 := by rw [← h2, integral_polySplineKernel, mul_one]

private def polySplineD1 (u : ℝ) : ℝ :=
  ((875 / 368 : ℝ) * (-6 / (23 / 50))) * (((u - 1 / 2) / (23 / 50)) *
    (1 - ((u - 1 / 2) / (23 / 50)) ^ 2) ^ 2)

private def polySplineD2 (u : ℝ) : ℝ :=
  ((875 / 368 : ℝ) * (-6 / (23 / 50) ^ 2)) *
    ((1 - ((u - 1 / 2) / (23 / 50)) ^ 2) * (1 - 5 * ((u - 1 / 2) / (23 / 50)) ^ 2))

private def polySplineD3 (u : ℝ) : ℝ :=
  ((875 / 368 : ℝ) * (24 / (23 / 50) ^ 3)) * (((u - 1 / 2) / (23 / 50)) *
    (3 - 5 * ((u - 1 / 2) / (23 / 50)) ^ 2))

private lemma hasDerivAt_polySplinePoly (u : ℝ) : HasDerivAt polySplinePoly (polySplineD1 u) u := by
  have hv : HasDerivAt (fun x : ℝ => (x - 1 / 2) / (23 / 50)) (1 / (23 / 50)) u := by
    simpa using ((hasDerivAt_id u).sub_const (1 / 2 : ℝ)).div_const (23 / 50 : ℝ)
  let v : ℝ := (u - 1 / 2) / (23 / 50)
  have hG : HasDerivAt (fun w : ℝ => (1 - w ^ 2) ^ 3) (-6 * v * (1 - v ^ 2) ^ 2) v := by
    have hd := ((hasDerivAt_const v (1 : ℝ)).fun_sub (hasDerivAt_pow 2 v)).fun_pow 3
    refine hd.congr_deriv ?_
    ring
  have hcomp : HasDerivAt polySplinePoly
      ((875 / 368 : ℝ) * (-6 * v * (1 - v ^ 2) ^ 2 * (1 / (23 / 50)))) u :=
    (hG.comp u hv).const_mul (875 / 368 : ℝ)
  refine hcomp.congr_deriv ?_
  unfold polySplineD1
  dsimp only [v]
  ring

private lemma hasDerivAt_polySplineD1 (u : ℝ) : HasDerivAt polySplineD1 (polySplineD2 u) u := by
  have hv : HasDerivAt (fun x : ℝ => (x - 1 / 2) / (23 / 50)) (1 / (23 / 50)) u := by
    simpa using ((hasDerivAt_id u).sub_const (1 / 2 : ℝ)).div_const (23 / 50 : ℝ)
  let v : ℝ := (u - 1 / 2) / (23 / 50)
  have hG : HasDerivAt (fun w : ℝ => w * (1 - w ^ 2) ^ 2) ((1 - v ^ 2) * (1 - 5 * v ^ 2)) v := by
    have hd := (hasDerivAt_id v).fun_mul
      (((hasDerivAt_const v (1 : ℝ)).fun_sub (hasDerivAt_pow 2 v)).fun_pow 2)
    refine hd.congr_deriv ?_
    simp only [id]
    ring
  have hcomp : HasDerivAt polySplineD1
      (((875 / 368 : ℝ) * (-6 / (23 / 50))) * ((1 - v ^ 2) * (1 - 5 * v ^ 2) * (1 / (23 / 50)))) u :=
    (hG.comp u hv).const_mul ((875 / 368 : ℝ) * (-6 / (23 / 50)))
  refine hcomp.congr_deriv ?_
  unfold polySplineD2
  dsimp only [v]
  ring

private lemma hasDerivAt_polySplineD2 (u : ℝ) : HasDerivAt polySplineD2 (polySplineD3 u) u := by
  have hv : HasDerivAt (fun x : ℝ => (x - 1 / 2) / (23 / 50)) (1 / (23 / 50)) u := by
    simpa using ((hasDerivAt_id u).sub_const (1 / 2 : ℝ)).div_const (23 / 50 : ℝ)
  let v : ℝ := (u - 1 / 2) / (23 / 50)
  have hG : HasDerivAt (fun w : ℝ => (1 - w ^ 2) * (1 - 5 * w ^ 2)) (-4 * v * (3 - 5 * v ^ 2)) v := by
    have hd := ((hasDerivAt_const v (1 : ℝ)).fun_sub (hasDerivAt_pow 2 v)).fun_mul
      ((hasDerivAt_const v (1 : ℝ)).fun_sub ((hasDerivAt_pow 2 v).const_mul 5))
    refine hd.congr_deriv ?_
    ring
  have hcomp : HasDerivAt polySplineD2
      (((875 / 368 : ℝ) * (-6 / (23 / 50) ^ 2)) * (-4 * v * (3 - 5 * v ^ 2) * (1 / (23 / 50)))) u :=
    (hG.comp u hv).const_mul ((875 / 368 : ℝ) * (-6 / (23 / 50) ^ 2))
  refine hcomp.congr_deriv ?_
  unfold polySplineD3
  dsimp only [v]
  ring

/-- Explicit 2-fold integration-by-parts bound `‖s * (s + 1) * mellinPolySpline s‖ ≤ 63` on `Re(s) > 0`. -/
theorem norm_mul_two_mellinPolySpline_le {s : ℂ} (hs : 0 < s.re) :
    ‖s * (s + 1) * mellinPolySpline s‖ ≤ 63 := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; linarith
  have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc0 : ContDiff ℝ 1 polySplinePoly := by unfold polySplinePoly; fun_prop
  have hc1 : ContDiff ℝ 1 polySplineD1 := by unfold polySplineD1; fun_prop
  have hd0 : deriv polySplinePoly = polySplineD1 := funext fun x => (hasDerivAt_polySplinePoly x).deriv
  have hd1 : deriv polySplineD1 = polySplineD2 := funext fun x => (hasDerivAt_polySplineD1 x).deriv
  have hm : mellinPolySpline s =
      ∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ (s - 1) * Complex.ofReal (polySplinePoly t) := by
    unfold mellinPolySpline
    rw [mellin_eq_intervalIntegral_of_admissible polySplineKernel_admissible,
      show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    rw [polySplineKernel_eq_poly_of_mem ht.1 ht.2]
  have hibp1 := ibp_real_weight_cpow (by norm_num) (by norm_num : (1 / 25 : ℝ) ≤ 24 / 25) hc0
    (by unfold polySplinePoly; norm_num) (by unfold polySplinePoly; norm_num) hs0
  rw [hd0] at hibp1
  have hibp2 := ibp_real_weight_cpow (by norm_num) (by norm_num : (1 / 25 : ℝ) ≤ 24 / 25) hc1
    (by unfold polySplineD1; norm_num) (by unfold polySplineD1; norm_num) hs1
  rw [show (s + 1) - 1 = s by ring, hd1] at hibp2
  have hid : s * (s + 1) * mellinPolySpline s =
      ∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ (s + 1) * Complex.ofReal (polySplineD2 t) := by
    rw [hm, hibp1, hibp2]
    field_simp [hs0, hs1]
  rw [hid]
  have hpt : ∀ t ∈ Set.uIoc (1 / 25 : ℝ) (24 / 25),
      ‖(t : ℂ) ^ (s + 1) * Complex.ofReal (polySplineD2 t)‖ ≤ 68 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have ht_pos : 0 < t := lt_trans (by norm_num) ht.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, Complex.norm_real, Real.norm_eq_abs]
    have hrp : t ^ (s + 1).re ≤ 1 :=
      Real.rpow_le_one ht_pos.le (by linarith [ht.2]) (by simp; linarith)
    let v : ℝ := (t - 1 / 2) / (23 / 50)
    have hv2 : 0 ≤ v ^ 2 ∧ v ^ 2 ≤ 1 := by
      refine ⟨sq_nonneg v, ?_⟩
      rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 23 / 50),
        div_le_one (by norm_num), abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hd2_abs : |polySplineD2 t| ≤ 68 := by
      change |((875 / 368 : ℝ) * (-6 / (23 / 50) ^ 2)) * ((1 - v ^ 2) * (1 - 5 * v ^ 2))| ≤ 68
      rw [abs_le]
      constructor <;> nlinarith [hv2.1, hv2.2, sq_nonneg (v ^ 2 - 3 / 5)]
    calc t ^ (s + 1).re * |polySplineD2 t| ≤ 1 * 68 :=
          mul_le_mul hrp hd2_abs (abs_nonneg _) zero_le_one
      _ = 68 := one_mul 68
  calc ‖∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ (s + 1) * Complex.ofReal (polySplineD2 t)‖
      ≤ 68 * |(24 / 25 : ℝ) - 1 / 25| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ ≤ 63 := by norm_num

/-- Explicit 3-fold integration-by-parts bound `‖s * (s + 1) * (s + 2) * mellinPolySpline s‖ ≤ 1621`
on `Re(s) > 0` (giving `O(|t|⁻³)` vertical decay). -/
theorem norm_mul_three_mellinPolySpline_le {s : ℂ} (hs : 0 < s.re) :
    ‖s * (s + 1) * (s + 2) * mellinPolySpline s‖ ≤ 1621 := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; linarith
  have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s + 2 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc0 : ContDiff ℝ 1 polySplinePoly := by unfold polySplinePoly; fun_prop
  have hc1 : ContDiff ℝ 1 polySplineD1 := by unfold polySplineD1; fun_prop
  have hc2 : ContDiff ℝ 1 polySplineD2 := by unfold polySplineD2; fun_prop
  have hd0 : deriv polySplinePoly = polySplineD1 := funext fun x => (hasDerivAt_polySplinePoly x).deriv
  have hd1 : deriv polySplineD1 = polySplineD2 := funext fun x => (hasDerivAt_polySplineD1 x).deriv
  have hd2 : deriv polySplineD2 = polySplineD3 := funext fun x => (hasDerivAt_polySplineD2 x).deriv
  have hm : mellinPolySpline s =
      ∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ (s - 1) * Complex.ofReal (polySplinePoly t) := by
    unfold mellinPolySpline
    rw [mellin_eq_intervalIntegral_of_admissible polySplineKernel_admissible,
      show (1 : ℝ) - 1 / 25 = 24 / 25 by norm_num]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    rw [polySplineKernel_eq_poly_of_mem ht.1 ht.2]
  have hibp1 := ibp_real_weight_cpow (by norm_num) (by norm_num : (1 / 25 : ℝ) ≤ 24 / 25) hc0
    (by unfold polySplinePoly; norm_num) (by unfold polySplinePoly; norm_num) hs0
  rw [hd0] at hibp1
  have hibp2 := ibp_real_weight_cpow (by norm_num) (by norm_num : (1 / 25 : ℝ) ≤ 24 / 25) hc1
    (by unfold polySplineD1; norm_num) (by unfold polySplineD1; norm_num) hs1
  rw [show (s + 1) - 1 = s by ring, hd1] at hibp2
  have hibp3 := ibp_real_weight_cpow (by norm_num) (by norm_num : (1 / 25 : ℝ) ≤ 24 / 25) hc2
    (by unfold polySplineD2; norm_num) (by unfold polySplineD2; norm_num) hs2
  rw [show (s + 2) - 1 = s + 1 by ring, hd2] at hibp3
  have hid : s * (s + 1) * (s + 2) * mellinPolySpline s =
      -(∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ (s + 2) * Complex.ofReal (polySplineD3 t)) := by
    rw [hm, hibp1, hibp2, hibp3]
    field_simp [hs0, hs1, hs2]
  rw [hid, norm_neg]
  have hpt : ∀ t ∈ Set.uIoc (1 / 25 : ℝ) (24 / 25),
      ‖(t : ℂ) ^ (s + 2) * Complex.ofReal (polySplineD3 t)‖ ≤ 1761 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have ht_pos : 0 < t := lt_trans (by norm_num) ht.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, Complex.norm_real, Real.norm_eq_abs]
    have hrp : t ^ (s + 2).re ≤ 1 :=
      Real.rpow_le_one ht_pos.le (by linarith [ht.2]) (by simp; linarith)
    let v : ℝ := (t - 1 / 2) / (23 / 50)
    have hv_abs : |v| ≤ 1 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 23 / 50), div_le_one (by norm_num), abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hv2 : 0 ≤ v ^ 2 ∧ v ^ 2 ≤ 1 := by
      refine ⟨sq_nonneg v, ?_⟩
      have habs := abs_le.mp hv_abs
      nlinarith
    have h35 : |3 - 5 * v ^ 2| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [hv2.1, hv2.2]
    have hd3_abs : |polySplineD3 t| ≤ 1761 := by
      have habs_prod : |v * (3 - 5 * v ^ 2)| ≤ 3 := by
        rw [abs_mul]
        calc |v| * |3 - 5 * v ^ 2| ≤ 1 * 3 :=
              mul_le_mul hv_abs h35 (abs_nonneg _) zero_le_one
          _ = 3 := one_mul 3
      have hc_le : |(875 / 368 : ℝ) * (24 / (23 / 50) ^ 3)| ≤ 587 := by norm_num
      change |((875 / 368 : ℝ) * (24 / (23 / 50) ^ 3)) * (v * (3 - 5 * v ^ 2))| ≤ 1761
      rw [abs_mul]
      calc |(875 / 368 : ℝ) * (24 / (23 / 50) ^ 3)| * |v * (3 - 5 * v ^ 2)|
          ≤ 587 * 3 := mul_le_mul hc_le habs_prod (abs_nonneg _) (by norm_num)
        _ = 1761 := by norm_num
    calc t ^ (s + 2).re * |polySplineD3 t| ≤ 1 * 1761 :=
          mul_le_mul hrp hd3_abs (abs_nonneg _) zero_le_one
      _ = 1761 := one_mul 1761
  calc ‖∫ t in (1 / 25 : ℝ)..(24 / 25), (t : ℂ) ^ (s + 2) * Complex.ofReal (polySplineD3 t)‖
      ≤ 1761 * |(24 / 25 : ℝ) - 1 / 25| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ ≤ 1621 := by norm_num

end PolySplineKernel

end
end BuchstabSwitchingK2.SmoothExplicitFormula
