import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Rectangle Residue Theorem for Logarithmic Derivatives of Arbitrary Multiplicity

Self-contained Lean `v4.36.0` proof (zero `sorry`, zero custom `axiom`) of:

1. Local principal-part decomposition `logDeriv_eq_order_div_add_analytic` for zeros of arbitrary
   finite multiplicity `analyticOrderNatAt f p`, and `neg_logDeriv_riemannZeta_near_one` for the
   simple pole of `riemannZeta` at `s = 1`.
2. Holomorphic weight multiplication via `dslope` (`neg_mul_eq_residue_div_add_analytic` and
   `pos_mul_eq_residue_div_add_analytic`), reducing every zero/pole of `-(f'/f) * W` to a pure
   simple pole `r_p / (s - p)` plus a locally analytic remainder.
3. Cauchy's rectangle residue theorem `residue_rectangle_simple_poles` and vertical contour-shift
   rearrangement `contour_vertical_shift_identity`.
-/

namespace BuchstabSwitchingK2.SmoothExplicitFormula

open Complex MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

/-! ### Part 1: Logarithmic Derivative Principal Parts & `dslope` Weight Multiplication -/

/-- At any point `p` where `f` is analytic and not identically zero in a neighborhood, `f'/f` equals
`(analyticOrderNatAt f p) / (s - p)` plus an analytic function on `𝓝[≠] p`. -/
theorem logDeriv_eq_order_div_add_analytic
    (f : ℂ → ℂ) (p : ℂ) (hf : AnalyticAt ℂ f p) (hne : ¬ ∀ᶠ s in 𝓝 p, f s = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p, f s ≠ 0 ∧
      deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  have htop : analyticOrderAt f p ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    exact hne
  let n : ℕ := analyticOrderNatAt f p
  have hord : analyticOrderAt f p = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt htop).symm
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hord
  have heq : f =ᶠ[𝓝[≠] p] fun s => (s - p) ^ n * g s := by
    filter_upwards [nhdsWithin_le_nhds hfg] with s hs
    simpa only [smul_eq_mul] using hs
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  filter_upwards [heq, logDeriv_congr_nhdsNE heq, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg0),
    nhdsWithin_le_nhds hg.eventually_analyticAt] with s hs hlog hsp hgne hga
  have hsub : s - p ≠ 0 := sub_ne_zero.mpr hsp
  refine ⟨by rw [hs]; exact mul_ne_zero (pow_ne_zero n hsub) hgne, ?_⟩
  change logDeriv f s = _
  rw [hlog, logDeriv_fun_mul (f := fun z : ℂ => (z - p) ^ n) (g := g) s
      (pow_ne_zero n hsub) hgne ((differentiableAt_id.sub_const p).pow n) hga.differentiableAt,
    logDeriv_fun_pow (f := fun z : ℂ => z - p) (differentiableAt_id.sub_const p) n]
  simp [n, logDeriv_apply, div_eq_mul_inv]

/-- Near `s = 1`, `-ζ'(s) / ζ(s) = 1 / (s - 1) + g₁(s)` with `g₁` analytic at `1`. -/
theorem neg_logDeriv_riemannZeta_near_one :
    ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ 1 ∧ ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      -(deriv riemannZeta s / riemannZeta s) = (1 : ℂ) / (s - 1) + g₁ s := by
  have han1 : AnalyticAt ℂ riemannZeta₁ 1 := differentiable_riemannZeta₁.analyticAt 1
  have hne1 : riemannZeta₁ 1 ≠ 0 := by simp
  refine ⟨fun s => -(deriv riemannZeta₁ s / riemannZeta₁ s), (han1.deriv.div han1 hne1).neg, ?_⟩
  have heq : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)] fun s => (s - 1)⁻¹ * riemannZeta₁ s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact riemannZeta_eq_inv_sub_mul hs
  filter_upwards [logDeriv_congr_nhdsNE heq, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (han1.continuousAt.eventually_ne hne1)] with s hlog hs1 hzne
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  change -logDeriv riemannZeta s = _
  rw [hlog, logDeriv_fun_mul (f := fun z : ℂ => (z - 1)⁻¹) (g := riemannZeta₁) s
      (inv_ne_zero hsub) hzne ((differentiableAt_id.sub_const 1).inv hsub)
      (differentiable_riemannZeta₁ s)]
  have hinv_ld : logDeriv (fun z : ℂ => (z - 1)⁻¹) s = -(1 / (s - 1)) := by
    have hd : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-(1 / (s - 1) ^ 2)) s := by
      have h1 : HasDerivAt (fun z : ℂ => z - 1) 1 s := by
        simpa using (hasDerivAt_id s).fun_sub (hasDerivAt_const s (1 : ℂ))
      refine (h1.fun_inv hsub).congr_deriv ?_
      ring
    rw [logDeriv_apply, hd.deriv]
    field_simp [hsub]
  rw [hinv_ld, logDeriv_apply]
  ring

/-- Multiplying a simple principal part `k / (s - p) + g s` by `-W s` yields residue `-(k * W p)`. -/
theorem neg_mul_eq_residue_div_add_analytic
    {φ g W : ℂ → ℂ} {p k : ℂ}
    (hg : AnalyticAt ℂ g p) (hW : AnalyticAt ℂ W p)
    (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G p ∧
      ∀ᶠ s in 𝓝[≠] p, -φ s * W s = -(k * W p) / (s - p) + G s := by
  refine ⟨fun s => -(k * dslope W p s) - g s * W s,
    ((analyticAt_const.mul (hW.dslope p)).neg).sub (hg.mul hW), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  rw [hs, dslope_of_ne _ hsp, slope_def_field]
  field_simp [sub_ne_zero.mpr hsp]
  ring

/-- Multiplying a simple principal part `k / (s - p) + g s` by `+W s` yields residue `k * W p`. -/
theorem pos_mul_eq_residue_div_add_analytic
    {φ g W : ℂ → ℂ} {p k : ℂ}
    (hg : AnalyticAt ℂ g p) (hW : AnalyticAt ℂ W p)
    (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G p ∧
      ∀ᶠ s in 𝓝[≠] p, φ s * W s = (k * W p) / (s - p) + G s := by
  refine ⟨fun s => k * dslope W p s + g s * W s,
    (analyticAt_const.mul (hW.dslope p)).add (hg.mul hW), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  rw [hs, dslope_of_ne _ hsp, slope_def_field]
  field_simp [sub_ne_zero.mpr hsp]
  ring

/-! ### Part 2: Counterclockwise Rectangle Boundary Integral & Simple-Pole Residue Formula -/

/-- Counterclockwise boundary integral around `[a, b] × [c, d]`. -/
def rectBdInt (a b c d : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f (x + c * I)) - (∫ x : ℝ in a..b, f (x + d * I))
    + I * (∫ y : ℝ in c..d, f (b + y * I)) - I * (∫ y : ℝ in c..d, f (a + y * I))

private def RectSidesIn (a b c d : ℝ) (B : Set ℂ) : Prop :=
  (∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) ∧
  (∀ x ∈ Set.uIcc a b, (x : ℂ) + d * I ∈ B) ∧
  (∀ y ∈ Set.uIcc c d, (b : ℂ) + y * I ∈ B) ∧
  (∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B)

private lemma rect_int_hor {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b :=
  (hf.comp (Complex.continuous_ofReal.add continuous_const).continuousOn h).intervalIntegrable

private lemma rect_int_ver {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d :=
  (hf.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn h).intervalIntegrable

private lemma rectBdInt_add {a b c d : ℝ} {B : Set ℂ} (h : RectSidesIn a b c d B) {f g : ℂ → ℂ}
    (hf : ContinuousOn f B) (hg : ContinuousOn g B) :
    rectBdInt a b c d (fun s => f s + g s) = rectBdInt a b c d f + rectBdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [rectBdInt]
  rw [intervalIntegral.integral_add (rect_int_hor hf h1) (rect_int_hor hg h1),
    intervalIntegral.integral_add (rect_int_hor hf h2) (rect_int_hor hg h2),
    intervalIntegral.integral_add (rect_int_ver hf h3) (rect_int_ver hg h3),
    intervalIntegral.integral_add (rect_int_ver hf h4) (rect_int_ver hg h4)]
  ring

private lemma rectBdInt_sum {a b c d : ℝ} {B : Set ℂ} (h : RectSidesIn a b c d B)
    {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, ContinuousOn (f i) B) :
    rectBdInt a b c d (fun s => ∑ i ∈ S, f i s) = ∑ i ∈ S, rectBdInt a b c d (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectBdInt]
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [rectBdInt_add h (hf i (Finset.mem_insert_self _ _))
      (continuousOn_finsetSum _ fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

private lemma rectBdInt_congr {a b c d : ℝ} {B : Set ℂ} (h : RectSidesIn a b c d B) {f g : ℂ → ℂ}
    (hfg : ∀ s ∈ B, f s = g s) : rectBdInt a b c d f = rectBdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [rectBdInt]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => g (x + c * I)) fun x hx => hfg _ (h1 x hx),
    intervalIntegral.integral_congr (g := fun x : ℝ => g (x + d * I)) fun x hx => hfg _ (h2 x hx),
    intervalIntegral.integral_congr (g := fun y : ℝ => g (b + y * I)) fun y hy => hfg _ (h3 y hy),
    intervalIntegral.integral_congr (g := fun y : ℝ => g (a + y * I)) fun y hy => hfg _ (h4 y hy)]

private lemma rect_ftc_hor {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    ∫ x : ℝ in a..b, f (x + c * I) = F (b + c * I) - F (a + c * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + c * I))
    (fun x hx => ?_) (rect_int_hor hf h)
  exact (HasDerivAt.comp_add_const (x : ℂ) (c * I) (hF _ (h x hx))).comp_ofReal

private lemma rect_ftc_ver {F f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B)
    (hF : ∀ s ∈ B, HasDerivAt F (f s) s) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    I * ∫ y : ℝ in c..d, f (a + y * I) = F (a + d * I) - F (a + c * I) := by
  rw [mul_comm, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => F (a + y * I))
    (fun y hy => ?_) ((rect_int_ver hf h).mul_const I)
  have h0 : HasDerivAt (fun t : ℂ => (a : ℂ) + t * I) I (y : ℂ) := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (a : ℂ)
  exact (HasDerivAt.comp (y : ℂ) (hF _ (h y hy)) h0).comp_ofReal

private lemma rectBdInt_inv {a b c d : ℝ} {p : ℂ}
    (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im) (h4 : p.im < d) (k : ℂ) :
    rectBdInt a b c d (fun s => k / (s - p)) = 2 * Real.pi * I * k := by
  have hc : ∀ B : Set ℂ, (∀ s ∈ B, s - p ≠ 0) → ContinuousOn (fun s => k / (s - p)) B :=
    fun B hB => ContinuousOn.div₀ continuousOn_const (continuousOn_id.sub continuousOn_const) hB
  have hc1 := hc {s | s - p ∈ slitPlane} fun _ hs => slitPlane_ne_zero hs
  have hc2 := hc {s | -(s - p) ∈ slitPlane} fun _ hs => neg_ne_zero.1 (slitPlane_ne_zero hs)
  have hd1 : ∀ s ∈ {s | s - p ∈ slitPlane},
      HasDerivAt (fun s => k * log (s - p)) (k / (s - p)) s := fun s hs => by
    have hs' : s - p ∈ slitPlane := hs
    have hsub : HasDerivAt (fun z : ℂ => z - p) 1 s := by
      simpa using (hasDerivAt_id s).fun_sub (hasDerivAt_const s p)
    have hlog : HasDerivAt (fun z : ℂ => log (z - p)) (1 / (s - p)) s := hsub.clog hs'
    exact (hlog.const_mul k).congr_deriv (by ring)
  have hd2 : ∀ s ∈ {s | -(s - p) ∈ slitPlane},
      HasDerivAt (fun s => k * log (-(s - p))) (k / (s - p)) s := fun s hs => by
    have hs' : -(s - p) ∈ slitPlane := hs
    have hsub : HasDerivAt (fun z : ℂ => -(z - p)) (-1) s := by
      simpa using ((hasDerivAt_id s).fun_sub (hasDerivAt_const s p)).fun_neg
    have hlog : HasDerivAt (fun z : ℂ => log (-(z - p))) ((-1) / -(s - p)) s := hsub.clog hs'
    refine (hlog.const_mul k).congr_deriv ?_
    rw [neg_div_neg_eq]
    ring
  have hs_c : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ {s | s - p ∈ slitPlane} := by
    intro x _; change ((x : ℂ) + c * I - p) ∈ slitPlane
    rw [mem_slitPlane_iff]; exact Or.inr (by simp; linarith)
  have hs_d : ∀ x ∈ Set.uIcc a b, (x : ℂ) + d * I ∈ {s | s - p ∈ slitPlane} := by
    intro x _; change ((x : ℂ) + d * I - p) ∈ slitPlane
    rw [mem_slitPlane_iff]; exact Or.inr (by simp; linarith)
  have hs_b : ∀ y ∈ Set.uIcc c d, (b : ℂ) + y * I ∈ {s | s - p ∈ slitPlane} := by
    intro y _; change ((b : ℂ) + y * I - p) ∈ slitPlane
    rw [mem_slitPlane_iff]; exact Or.inl (by simp; linarith)
  have hs_a : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ {s | -(s - p) ∈ slitPlane} := by
    intro y _; change (-((a : ℂ) + y * I - p)) ∈ slitPlane
    rw [mem_slitPlane_iff]; exact Or.inl (by simp; linarith)
  simp only [rectBdInt]
  rw [rect_ftc_hor hc1 hd1 hs_c, rect_ftc_hor hc1 hd1 hs_d,
    rect_ftc_ver hc1 hd1 hs_b, rect_ftc_ver hc2 hd2 hs_a]
  let z_ad : ℂ := (a : ℂ) + (d : ℂ) * I - p
  let z_ac : ℂ := (a : ℂ) + (c : ℂ) * I - p
  have him_d : 0 < z_ad.im := by simp [z_ad]; linarith
  have him_c : z_ac.im < 0 := by simp [z_ac]; linarith
  have e1 : log (-z_ad) = log z_ad - (Real.pi : ℂ) * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos him_d]
    push_cast; ring
  have e2 : log (-z_ac) = log z_ac + (Real.pi : ℂ) * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg him_c]
    push_cast; ring
  change (k * log ((b : ℂ) + (c : ℂ) * I - p) - k * log z_ac) -
      (k * log ((b : ℂ) + (d : ℂ) * I - p) - k * log z_ad) +
      (k * log ((b : ℂ) + (d : ℂ) * I - p) - k * log ((b : ℂ) + (c : ℂ) * I - p)) -
      (k * log (-z_ad) - k * log (-z_ac)) = 2 * (Real.pi : ℂ) * I * k
  rw [e1, e2]
  ring

/-- **Cauchy's Rectangle Residue Theorem for Simple Principal Parts**: if `f` is holomorphic on
`[x0, x1] × [y0, y1] \ S` and at each `p ∈ S` strictly inside the open rectangle admits
`f s = r p / (s - p) + g_p s` with `g_p` analytic at `p`, then
`rectBdInt x0 x1 y0 y1 f = 2πi * ∑ p ∈ S, r p`. -/
theorem residue_rectangle_simple_poles
    (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) (S : Finset ℂ) (r : ℂ → ℂ)
    (hx : x0 < x1) (hy : y0 < y1)
    (hS : ∀ p ∈ S, x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1)
    (hf : DifferentiableOn ℂ f ((Set.Icc x0 x1 ×ℂ Set.Icc y0 y1) \ S))
    (hp : ∀ p ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ s in 𝓝[≠] p, f s = r p / (s - p) + g s) :
    rectBdInt x0 x1 y0 y1 f = 2 * Real.pi * I * ∑ p ∈ S, r p := by
  classical
  choose! g hg hfg using hp
  set R : Set ℂ := Set.Icc x0 x1 ×ℂ Set.Icc y0 y1 with hR
  let P : ℂ → ℂ → ℂ := fun p s => r p / (s - p)
  have hP : ∀ p s, s ≠ p → DifferentiableAt ℂ (P p) s := fun p s hs =>
    (((hasDerivAt_const s (r p)).fun_div
      ((hasDerivAt_id s).fun_sub (hasDerivAt_const s p)) (sub_ne_zero.mpr hs)).differentiableAt)
  let h : ℂ → ℂ := fun s =>
    if s ∈ S then g s s - ∑ q ∈ S.erase s, P q s else f s - ∑ q ∈ S, P q s
  have hopen : ∀ T : Finset ℂ, ∀ s ∉ T, ∀ᶠ t in 𝓝 s, t ∉ T := fun T s hs =>
    T.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
  have hh : DifferentiableOn ℂ h R := by
    intro s hs
    by_cases hsS : s ∈ S
    · have hd : DifferentiableAt ℂ (fun t => g s t - ∑ q ∈ S.erase s, P q t) s :=
        (hg s hsS).differentiableAt.fun_sub
          (DifferentiableAt.fun_sum fun q hq => hP q s (Finset.ne_of_mem_erase hq).symm)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      have e1 := eventually_nhdsWithin_iff.1 (hfg s hsS)
      filter_upwards [e1, hopen (S.erase s) s (Finset.notMem_erase s S)] with t ht1 ht2
      by_cases hts : t = s
      · subst hts; simp only [h, hsS, ↓reduceIte]
      · have htS : t ∉ S := fun ht => ht2 (Finset.mem_erase.mpr ⟨hts, ht⟩)
        simp only [h, htS, ↓reduceIte, P]
        rw [ht1 hts, ← Finset.add_sum_erase S _ hsS]
        ring
    · have hd : DifferentiableWithinAt ℂ (fun t => f t - ∑ q ∈ S, P q t) R s := by
        refine DifferentiableWithinAt.fun_sub ?_
          (DifferentiableAt.fun_sum fun q hq => hP q s fun e => hsS (e ▸ hq)).differentiableWithinAt
        exact (hf s ⟨hs, hsS⟩).mono_of_mem_nhdsWithin (inter_mem_nhdsWithin R (hopen S s hsS))
      refine hd.congr_of_eventuallyEq ?_ (by simp only [h, hsS, ↓reduceIte])
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen S s hsS)] with t ht
      have ht' : t ∉ S := ht
      simp only [h, ht', ↓reduceIte]
  have hB : RectSidesIn x0 x1 y0 y1 (R \ S) := by
    rw [RectSidesIn, Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le]
    refine ⟨fun x hxm => ⟨?_, fun hm => ?_⟩, fun x hxm => ⟨?_, fun hm => ?_⟩,
      fun y hym => ⟨?_, fun hm => ?_⟩, fun y hym => ⟨?_, fun hm => ?_⟩⟩
    · simp only [hR, mem_reProdIm, Set.mem_Icc, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      exact ⟨hxm, ⟨le_rfl, hy.le⟩⟩
    · have hpS := (hS _ hm).2.2.1
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at hpS
      linarith
    · simp only [hR, mem_reProdIm, Set.mem_Icc, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      exact ⟨hxm, ⟨hy.le, le_rfl⟩⟩
    · have hpS := (hS _ hm).2.2.2
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at hpS
      linarith
    · simp only [hR, mem_reProdIm, Set.mem_Icc, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      exact ⟨⟨hx.le, le_rfl⟩, hym⟩
    · have hpS := (hS _ hm).2.1
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero] at hpS
      linarith
    · simp only [hR, mem_reProdIm, Set.mem_Icc, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      exact ⟨⟨le_rfl, hx.le⟩, hym⟩
    · have hpS := (hS _ hm).1
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero] at hpS
      linarith
  have hPc : ∀ p ∈ S, ContinuousOn (P p) (R \ S) := fun p hp s hs =>
    (hP p s fun e => hs.2 (e ▸ hp)).continuousAt.continuousWithinAt
  have hR_eq : Set.uIcc (⟨x0, y0⟩ : ℂ).re (⟨x1, y1⟩ : ℂ).re ×ℂ
      Set.uIcc (⟨x0, y0⟩ : ℂ).im (⟨x1, y1⟩ : ℂ).im = R := by
    change Set.uIcc x0 x1 ×ℂ Set.uIcc y0 y1 = Set.Icc x0 x1 ×ℂ Set.Icc y0 y1
    rw [Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le]
  have h0 : rectBdInt x0 x1 y0 y1 h = 0 := by
    have hh' : DifferentiableOn ℂ h
        (Set.uIcc (⟨x0, y0⟩ : ℂ).re (⟨x1, y1⟩ : ℂ).re ×ℂ
          Set.uIcc (⟨x0, y0⟩ : ℂ).im (⟨x1, y1⟩ : ℂ).im) := hR_eq.symm ▸ hh
    have hz := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h ⟨x0, y0⟩ ⟨x1, y1⟩ hh'
    dsimp only [rectBdInt]
    simpa only [smul_eq_mul] using hz
  rw [rectBdInt_congr hB (g := fun s => h s + ∑ q ∈ S, P q s) (fun s hs => by
      have ht' : s ∉ S := hs.2
      simp only [h, ht', ↓reduceIte]
      exact (sub_add_cancel _ _).symm),
    rectBdInt_add hB (hh.continuousOn.mono Set.sdiff_subset) (continuousOn_finsetSum _ hPc),
    h0, zero_add, rectBdInt_sum hB S hPc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hS p hp
  exact rectBdInt_inv h1 h2 h3 h4 (r p)

/-- Algebraic rearrangement converting `rectBdInt x0 x1 y0 y1 f = 2πi * R` into an identity for
the right vertical line integral `(1 / (2π)) ∫_{y0}^{y1} f(x1 + y I) dy`. -/
theorem contour_vertical_shift_identity (x0 x1 y0 y1 : ℝ) (f : ℂ → ℂ) (R : ℂ)
    (hid : rectBdInt x0 x1 y0 y1 f = 2 * Real.pi * I * R) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ y : ℝ in y0..y1, f (x1 + y * I)) =
      R + (1 / (2 * (Real.pi : ℂ))) * (∫ y : ℝ in y0..y1, f (x0 + y * I)) +
        (I / (2 * (Real.pi : ℂ))) *
          ((∫ x : ℝ in x0..x1, f (x + y0 * I)) - (∫ x : ℝ in x0..x1, f (x + y1 * I))) := by
  unfold rectBdInt at hid
  set H0 : ℂ := ∫ x : ℝ in x0..x1, f (x + y0 * I)
  set H1 : ℂ := ∫ x : ℝ in x0..x1, f (x + y1 * I)
  set V1 : ℂ := ∫ y : ℝ in y0..y1, f (x1 + y * I)
  set V0 : ℂ := ∫ y : ℝ in y0..y1, f (x0 + y * I)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2πI : 2 * (Real.pi : ℂ) * I ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
  have h1 : (2 * (Real.pi : ℂ) * I) * (1 / (2 * (Real.pi : ℂ))) = I := by field_simp [hπ]
  have h2 : (2 * (Real.pi : ℂ) * I) * (I / (2 * (Real.pi : ℂ))) = -1 := by
    calc (2 * (Real.pi : ℂ) * I) * (I / (2 * (Real.pi : ℂ)))
        = I ^ 2 * ((2 * (Real.pi : ℂ)) / (2 * (Real.pi : ℂ))) := by ring
      _ = -1 := by rw [Complex.I_sq, div_self (mul_ne_zero two_ne_zero hπ), mul_one]
  apply mul_left_cancel₀ h2πI
  calc (2 * (Real.pi : ℂ) * I) * ((1 / (2 * (Real.pi : ℂ))) * V1)
      = ((2 * (Real.pi : ℂ) * I) * (1 / (2 * (Real.pi : ℂ)))) * V1 := by ring
    _ = I * V1 := by rw [h1]
    _ = (2 * (Real.pi : ℂ) * I) * R + I * V0 + (-1) * (H0 - H1) := by linear_combination hid
    _ = (2 * (Real.pi : ℂ) * I) * R +
          ((2 * (Real.pi : ℂ) * I) * (1 / (2 * (Real.pi : ℂ)))) * V0 +
          ((2 * (Real.pi : ℂ) * I) * (I / (2 * (Real.pi : ℂ)))) * (H0 - H1) := by rw [h1, h2]
    _ = (2 * (Real.pi : ℂ) * I) *
          (R + (1 / (2 * (Real.pi : ℂ))) * V0 + (I / (2 * (Real.pi : ℂ))) * (H0 - H1)) := by ring

end
end BuchstabSwitchingK2.SmoothExplicitFormula
