import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import BuchstabSwitchingK2.External.CitedPremisesK2

/-!
# Right-Half-Plane Blaschke–Landau Disk Bounds & Good Contour Heights (`1 + 2`)

Self-contained complex-analytic zero-density and logarithmic-derivative bounds inside the open
right half-plane `Re(s) ≥ 1 / 16 > 0` in Lean `v4.36.0` (zero `sorry`, zero custom `axiom`):

1. **Blaschke + Borel–Carathéodory Disk Lemma (`blaschke_borel_disk`)**:
   - Factors all zeros of a holomorphic function `f` in `closedBall z₀ r₁` (`0 < r₀ ≤ r₁ < R`) using
     exact Blaschke denominators `R^2 - conj(ρ - z₀) * (z - z₀)`, obtaining both the sharp Blaschke
     zero-multiplicity bound `(∑_{ρ ∈ Z₀} m_ρ) * log(R / r₀) ≤ log M` and a single-disk
     Borel–Carathéodory bound on `f'/f(s) - ∑_{ρ ∈ Z₁} m_ρ / (s - ρ)` across `closedBall z₀ r_eval`
     for ANY `r_eval < r₁ < R`.
2. **Right-Half-Plane `L`-Function & `riemannZeta₁` Bounds (`Re(s) ≥ 1 / 16`)**:
   - Elementary telescoping lower bound `1 / 4 ≤ ‖LFunction χ (2 + t * I)‖` and
     `1 / 4 ≤ ‖riemannZeta₁ (2 + t * I)‖`;
   - Partial-summation upper bound `‖LFunction χ z‖ ≤ 68 * q * (1 + ‖z‖)` (`χ ≠ 1`, `1 / 16 ≤ z.re`);
   - Euler–Maclaurin upper bound `‖riemannZeta₁ z‖ ≤ 36 * (1 + ‖z‖) ^ 2` (`1 / 16 ≤ z.re`).
3. **Unit-Strip Critical-Line Zero Counts, Left-Edge (`σ = 1 / 4`) GRH Bounds, & Symmetric Good
   Horizontal Shift Heights `T' ∈ [T, T + 1]`**.
-/

namespace BuchstabSwitchingK2.SmoothExplicitFormula

open Complex Set Filter Topology Metric MeasureTheory
open scoped BigOperators Classical

noncomputable section

/-! ### Part 1: Zero Factorization & Blaschke–Borel–Carathéodory Disk Theorem -/

section BlaschkeBorelDisk

private lemma exists_factorization_of_sum_order (z₀ : ℂ) (R r₁ : ℝ) (hr : r₁ < R) :
    ∀ N : ℕ, ∀ (f : ℂ → ℂ) (Z : Finset ℂ), DifferentiableOn ℂ f (closedBall z₀ R) →
      (∀ ρ ∈ Z, ρ ∈ closedBall z₀ r₁) →
      (∀ z ∈ closedBall z₀ r₁, f z = 0 → z ∈ Z) →
      (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∑ ρ ∈ Z, analyticOrderNatAt f ρ = N →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (closedBall z₀ R) ∧
        (∀ z ∈ closedBall z₀ r₁, h z ≠ 0) ∧
        ∀ z ∈ closedBall z₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
  classical
  intro N
  induction N with
  | zero =>
    intro f Z hf _ hzero htop hsum
    have h0 : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = 0 := Finset.sum_eq_zero_iff.mp hsum
    refine ⟨f, hf, fun z hz hfz => ?_, fun z _ => by
      rw [Finset.prod_eq_one fun ρ hρ => by rw [h0 ρ hρ, pow_zero], one_mul]⟩
    have hzZ := hzero z hz hfz
    have hord : analyticOrderAt f z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt (htop z hzZ)]; simp [h0 z hzZ]
    have hball := closedBall_mem_nhds_of_mem (closedBall_subset_ball hr hz)
    exact ((hf.analyticAt hball).analyticOrderAt_eq_zero.mp hord) hfz
  | succ n ih =>
    intro f Z hf hZ hzero htop hsum
    obtain ⟨ρ₀, hρ₀Z, hρ₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by rw [hsum]; exact Nat.succ_ne_zero n)
    have hρ₀B := hZ ρ₀ hρ₀Z
    have hρ₀N := closedBall_mem_nhds_of_mem (closedBall_subset_ball hr hρ₀B)
    have hfρ₀ : f ρ₀ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hρ₀
    let g : ℂ → ℂ := dslope f ρ₀
    have hfg : ∀ z, f z = (z - ρ₀) * g z := fun z => by
      have h := sub_smul_dslope f ρ₀ z
      rw [hfρ₀, sub_zero, smul_eq_mul] at h
      exact h.symm
    have hgd : DifferentiableOn ℂ g (closedBall z₀ R) :=
      (Complex.differentiableOn_dslope hρ₀N).mpr hf
    have keyN : ∀ ρ ∈ Z,
        analyticOrderNatAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ ∧
          analyticOrderAt g ρ ≠ ⊤ := fun ρ hρ => by
      have hga := hgd.analyticAt (closedBall_mem_nhds_of_mem (closedBall_subset_ball hr (hZ ρ hρ)))
      have hla : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ := analyticAt_id.sub analyticAt_const
      have hk : analyticOrderAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderAt g ρ := by
        rw [show f = (fun z : ℂ => z - ρ₀) * g from funext hfg, analyticOrderAt_mul hla hga]
        congr 1
        split_ifs with hρρ₀
        · subst hρρ₀; exact analyticOrderAt_id_sub_const_self
        · exact analyticOrderAt_id_sub_const_of_ne hρρ₀
      have ht := htop ρ hρ
      have hgt : analyticOrderAt g ρ ≠ ⊤ := fun h => ht (by rw [hk, h]; simp)
      refine ⟨?_, hgt⟩
      have h1 : ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) =
          (((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ : ℕ) : ℕ∞) := by
        rw [Nat.cast_analyticOrderNatAt ht, hk, Nat.cast_add, Nat.cast_analyticOrderNatAt hgt]
        split_ifs <;> simp
      exact_mod_cast h1
    have hsumg : ∑ ρ ∈ Z, analyticOrderNatAt g ρ = n := by
      have hs := Finset.sum_congr rfl fun ρ hρ => (keyN ρ hρ).1
      rw [hs, Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
      simp only [hρ₀Z, ↓reduceIte] at hsum
      lia
    obtain ⟨h, hhd, hh0, hhf⟩ := ih g Z hgd hZ
      (fun z hz h0 => hzero z hz (by rw [hfg z, h0, mul_zero]))
      (fun ρ hρ => (keyN ρ hρ).2) hsumg
    refine ⟨h, hhd, hh0, fun z hz => ?_⟩
    have hone : ∏ ρ ∈ Z, (z - ρ) ^ (if ρ = ρ₀ then 1 else 0) = z - ρ₀ := by
      rw [Finset.prod_eq_single ρ₀ (fun _ _ hb => by simp [hb]) (fun h => absurd hρ₀Z h)]
      simp
    have hprod : ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ =
        (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
      rw [← hone, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun ρ hρ => by rw [(keyN ρ hρ).1, pow_add]
    rw [hfg z, hhf z hz, hprod, mul_assoc]

/-- Finite zero factorization of a holomorphic function `f` on `closedBall z₀ R` across any strictly
smaller closed sub-ball `closedBall z₀ r₁` (`0 < r₁ < R`). -/
theorem zeroFactorization_on_ball (f : ℂ → ℂ) (z₀ : ℂ) (R r₁ : ℝ)
    (hr₁ : 0 < r₁) (hr : r₁ < R)
    (hf : DifferentiableOn ℂ f (closedBall z₀ R)) (hf0 : f z₀ ≠ 0) :
    ∃ (Z : Finset ℂ) (h : ℂ → ℂ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall z₀ r₁ ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt f ρ) ∧
      DifferentiableOn ℂ h (closedBall z₀ R) ∧
      (∀ z ∈ closedBall z₀ r₁, h z ≠ 0) ∧
      ∀ z ∈ closedBall z₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
  have hU : AnalyticOnNhd ℂ f (ball z₀ R) :=
    (hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball
  have hnotzero : ∀ x ∈ ball z₀ R, ¬ (∀ᶠ w in 𝓝 x, f w = 0) := fun x hx hev =>
    hf0 (hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball z₀ R).isPreconnected hx hev
      (mem_ball_self (hr₁.trans hr)))
  have hisol : ∀ x ∈ ball z₀ R, ∀ᶠ w in 𝓝[≠] x, f w ≠ 0 := fun x hx =>
    (hU x hx).eventually_eq_zero_or_eventually_ne_zero.resolve_left (hnotzero x hx)
  have htop : ∀ x ∈ ball z₀ R, analyticOrderAt f x ≠ ⊤ := fun x hx h =>
    hnotzero x hx (analyticOrderAt_eq_top.mp h)
  have hScpt : IsCompact (closedBall z₀ r₁ ∩ f ⁻¹' {0}) :=
    (isCompact_closedBall z₀ r₁).of_isClosed_subset
      ((hf.continuousOn.mono (closedBall_subset_closedBall hr.le)).preimage_isClosed_of_isClosed
        isClosed_closedBall isClosed_singleton) Set.inter_subset_left
  have hSdisc : DiscreteTopology (closedBall z₀ r₁ ∩ f ⁻¹' {0} : Set ℂ) :=
    discreteTopology_subtype_iff.mpr fun x hx => Filter.inf_principal_eq_bot.mpr <| by
      filter_upwards [hisol x (closedBall_subset_ball hr hx.1)] with w hw hwS using hw hwS.2
  have hfin : (closedBall z₀ r₁ ∩ f ⁻¹' {0}).Finite := hScpt.finite ⟨hSdisc⟩
  have hmem : ∀ ρ : ℂ, ρ ∈ hfin.toFinset ↔ (ρ ∈ closedBall z₀ r₁ ∧ f ρ = 0) := fun ρ =>
    Set.Finite.mem_toFinset hfin
  obtain ⟨h, hhd, hh0, hhf⟩ := exists_factorization_of_sum_order z₀ R r₁ hr _ f hfin.toFinset hf
    (fun ρ hρ => ((hmem ρ).mp hρ).1) (fun z hz hfz => (hmem z).mpr ⟨hz, hfz⟩)
    (fun ρ hρ => htop ρ (closedBall_subset_ball hr ((hmem ρ).mp hρ).1)) rfl
  refine ⟨hfin.toFinset, h, hmem, fun ρ hρ => ?_, hhd, hh0, hhf⟩
  obtain ⟨hB, hfρ⟩ := (hmem ρ).mp hρ
  have hball := closedBall_subset_ball hr hB
  exact Nat.one_le_iff_ne_zero.mpr fun h0 =>
    ((hU ρ hball).analyticOrderAt_eq_zero.mp
      (by rw [← Nat.cast_analyticOrderNatAt (htop ρ hball)]; simp [h0])) hfρ

private lemma exists_holomorphic_log_on_ball {f : ℂ → ℂ} {z₀ : ℂ} {r₁ : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ r₁)) (hne : ∀ z ∈ ball z₀ r₁, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ r₁, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ r₁, f z = f z₀ * Complex.exp (g z) := by
  obtain ⟨g, hg₀, hg⟩ := ((hf.deriv isOpen_ball).div hf hne).isExactOn_ball.with_val_at z₀ 0
  refine ⟨g, hg₀, hg, ?_⟩
  have hd : DifferentiableOn ℂ g (ball z₀ r₁) :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hf hd.cexp isOpen_ball isPreconnected_ball
    (fun _ _ => Complex.exp_ne_zero _) hne).mp fun z hz => by
      simp [logDeriv_apply, (hg z hz).cexp.deriv]
  intro z hz
  have hcenter := hc (mem_ball_self (pos_of_mem_ball hz))
  have hfc : f z₀ = c := by simpa [hg₀] using hcenter
  simpa [hfc] using hc hz

/-- Borel–Carathéodory + Cauchy derivative bound on `closedBall z₀ r_eval` inside a zero-free
ball `closedBall z₀ r₁` (`0 ≤ r_eval < r₁`). -/
theorem borelCaratheodory_logDeriv_on_subball (h : ℂ → ℂ) (z₀ : ℂ) (r₁ r_eval M : ℝ)
    (hr_eval_nn : 0 ≤ r_eval) (hlt : r_eval < r₁) (hM : 1 ≤ M)
    (hh : DifferentiableOn ℂ h (closedBall z₀ r₁))
    (hne : ∀ z ∈ closedBall z₀ r₁, h z ≠ 0)
    (hbd : ∀ z ∈ closedBall z₀ r₁, ‖h z‖ ≤ M * ‖h z₀‖) :
    ∀ z ∈ closedBall z₀ r_eval,
      ‖deriv h z / h z‖ ≤ (4 * (r_eval + r₁) / (r₁ - r_eval) ^ 2) * Real.log M := by
  have hr₁ : 0 < r₁ := lt_of_le_of_lt hr_eval_nn hlt
  intro z hz
  obtain ⟨g, hg0, hgd, hgf⟩ := exists_holomorphic_log_on_ball (hh.mono ball_subset_closedBall)
    fun w hw => hne w (ball_subset_closedBall hw)
  have hh0_pos : 0 < ‖h z₀‖ := norm_pos_iff.mpr (hne z₀ (mem_closedBall_self hr₁.le))
  have hre : ∀ w ∈ ball z₀ r₁, (g w).re ≤ Real.log M := fun w hw => by
    have h1 := hbd w (ball_subset_closedBall hw)
    rw [hgf w hw, norm_mul, Complex.norm_exp] at h1
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le zero_lt_one hM)).mpr
      ((mul_le_mul_iff_right₀ hh0_pos).mp (by simpa only [mul_comm M] using h1))
  have hshift : ∀ v ∈ ball (0 : ℂ) r₁, z₀ + v ∈ ball z₀ r₁ := fun v hv => by
    simpa [mem_ball, dist_eq_norm] using hv
  set r_mid : ℝ := (r_eval + r₁) / 2
  set δ : ℝ := (r₁ - r_eval) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmain : ∀ A : ℝ, Real.log M < A →
      ‖deriv h z / h z‖ ≤ (4 * (r_eval + r₁) / (r₁ - r_eval) ^ 2) * A := fun A hA => by
    have hA0 : 0 < A := (Real.log_nonneg hM).trans_lt hA
    have hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 r₁) := fun v hv =>
      ((hgd _ (hshift v hv)).differentiableAt.comp v
        (differentiableAt_id.const_add z₀)).differentiableWithinAt
    have hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 r₁) {w | w.re ≤ A} :=
      fun v hv => (hre _ (hshift v hv)).trans hA.le
    have hbc : ∀ w ∈ closedBall z₀ r_mid, ‖g w‖ ≤ (2 * r_mid / (r₁ - r_mid)) * A := fun w hw => by
      obtain ⟨u, rfl⟩ : ∃ u, w = z₀ + u := ⟨w - z₀, by ring⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hw
      have hB := Complex.borelCaratheodory_zero hA0 hhd hhm hr₁
        (mem_ball_zero_iff.mpr (by dsimp [r_mid] at hw ⊢; linarith)) (by simpa using hg0)
      have hsub_pos : 0 < r₁ - ‖u‖ := by dsimp [r_mid] at hw; linarith
      have hrmid_pos : 0 < r₁ - r_mid := by dsimp [r_mid]; linarith
      refine hB.trans ?_
      rw [div_le_iff₀ hsub_pos]
      have h1 : 2 * ‖u‖ * A ≤ (2 * r_mid / (r₁ - r_mid) * A) * (r₁ - ‖u‖) := by
        have h2 : 2 * ‖u‖ * A * (r₁ - r_mid) ≤ 2 * r_mid * A * (r₁ - ‖u‖) := by
          nlinarith [norm_nonneg u, mul_nonneg hA0.le (sub_nonneg.mpr hw)]
        have h3 := (le_div_iff₀ hrmid_pos).mpr h2
        calc 2 * ‖u‖ * A ≤ (2 * r_mid * A * (r₁ - ‖u‖)) / (r₁ - r_mid) := h3
          _ = (2 * r_mid / (r₁ - r_mid) * A) * (r₁ - ‖u‖) := by ring
      linarith
    have hsub : closedBall z δ ⊆ ball z₀ r₁ := fun w hw => by
      have hd_wz : dist w z ≤ δ := mem_closedBall.mp hw
      have hd_zz0 : dist z z₀ ≤ r_eval := mem_closedBall.mp hz
      have htri := dist_triangle w z z₀
      rw [mem_ball]
      dsimp [δ] at hd_wz
      linarith
    have hdiff : DiffContOnCl ℂ g (ball z δ) := DifferentiableOn.diffContOnCl <| by
      rw [closure_ball z hδ.ne']
      exact fun w hw => (hgd w (hsub hw)).differentiableAt.differentiableWithinAt
    have hC : ∀ w ∈ sphere z δ, ‖g w‖ ≤ (2 * r_mid / (r₁ - r_mid)) * A := fun w hw => by
      refine hbc w ?_
      rw [mem_closedBall]
      have hd_wz : dist w z = δ := mem_sphere.mp hw
      have hd_zz0 : dist z z₀ ≤ r_eval := mem_closedBall.mp hz
      have htri := dist_triangle w z z₀
      dsimp [r_mid, δ] at hd_wz ⊢
      linarith
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdiff hC
    rw [(hgd z (hsub (mem_closedBall_self hδ.le))).deriv] at hder
    refine hder.trans_eq ?_
    dsimp [r_mid, δ]
    have hrm1 : r₁ - (r_eval + r₁) / 2 = (r₁ - r_eval) / 2 := by ring
    have hne_sub : r₁ - r_eval ≠ 0 := by linarith
    rw [hrm1]
    field_simp [hne_sub]
    ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set K : ℝ := 4 * (r_eval + r₁) / (r₁ - r_eval) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  have h := hmain (Real.log M + ε / K) (lt_add_of_pos_right _ (div_pos hε hK))
  refine h.trans_eq ?_
  field_simp [hK.ne']

private def blaschkeDenom (z₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ :=
  (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - z₀) * (z - z₀)

private lemma norm_blaschkeDenom_on_sphere {z₀ ρ w : ℂ} {R : ℝ}
    (hR : 0 < R) (hw : w ∈ sphere z₀ R) :
    ‖blaschkeDenom z₀ R ρ w / (R : ℂ)‖ = ‖w - ρ‖ := by
  set u : ℂ := w - z₀
  set a : ℂ := ρ - z₀
  have hu : ‖u‖ = R := by simpa [u, mem_sphere, dist_eq_norm] using hw
  have hu_conj : u * starRingEnd ℂ u = (R : ℂ) ^ 2 := by
    rw [Complex.mul_conj', ← hu]
  have hnum : ‖blaschkeDenom z₀ R ρ w‖ = R * ‖w - ρ‖ := by
    unfold blaschkeDenom
    change ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * u‖ = R * ‖w - ρ‖
    have hwa : u - a = w - ρ := by dsimp [u, a]; ring
    calc ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * u‖
        = ‖u * starRingEnd ℂ u - starRingEnd ℂ a * u‖ := by rw [hu_conj]
      _ = ‖u * starRingEnd ℂ (u - a)‖ := by congr 1; rw [map_sub (starRingEnd ℂ) u a]; ring
      _ = ‖u‖ * ‖starRingEnd ℂ (u - a)‖ := norm_mul _ _
      _ = R * ‖w - ρ‖ := by rw [hu, Complex.norm_conj, hwa]
  rw [norm_div, hnum, Complex.norm_real, Real.norm_of_nonneg hR.le,
    mul_div_cancel_left₀ _ hR.ne']

private lemma norm_blaschkeDenom_ge {z₀ ρ z : ℂ} {R r₁ r_lim : ℝ}
    (hρ : ρ ∈ closedBall z₀ r₁) (hz : z ∈ closedBall z₀ r_lim)
    (hr₁_nn : 0 ≤ r₁) :
    R ^ 2 - r₁ * r_lim ≤ ‖blaschkeDenom z₀ R ρ z‖ := by
  have h1 : ‖starRingEnd ℂ (ρ - z₀) * (z - z₀)‖ ≤ r₁ * r_lim := by
    rw [norm_mul, Complex.norm_conj]
    have ha : ‖ρ - z₀‖ ≤ r₁ := by simpa [mem_closedBall, dist_eq_norm] using hρ
    have hb : ‖z - z₀‖ ≤ r_lim := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact mul_le_mul ha hb (norm_nonneg _) hr₁_nn
  have h2 : ‖(R : ℂ) ^ 2‖ - ‖starRingEnd ℂ (ρ - z₀) * (z - z₀)‖ ≤ ‖blaschkeDenom z₀ R ρ z‖ :=
    norm_sub_norm_le _ _
  have hR2 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  linarith

private lemma differentiableAt_finset_prod {ι : Type*} (S : Finset ι) (g : ι → ℂ → ℂ) (z : ℂ)
    (hd : ∀ i ∈ S, DifferentiableAt ℂ (g i) z) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ S, g i w) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hfun : (fun w => ∏ i ∈ insert a S, g i w) = fun w => g a w * ∏ i ∈ S, g i w :=
      funext fun _ => Finset.prod_insert ha
    rw [hfun]
    exact (hd a (Finset.mem_insert_self a S)).mul
      (ih fun i hi => hd i (Finset.mem_insert_of_mem hi))

private lemma one_le_prod_real {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ S, 1 ≤ g i) : 1 ≤ ∏ i ∈ S, g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hg a (Finset.mem_insert_self a S)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    nlinarith

private lemma logDeriv_finset_prod_pow {ι : Type*} (S : Finset ι) (g : ι → ℂ → ℂ) (m : ι → ℕ)
    (z : ℂ) (hd : ∀ i ∈ S, DifferentiableAt ℂ (g i) z) (hne : ∀ i ∈ S, g i z ≠ 0) :
    logDeriv (fun w => ∏ i ∈ S, g i w ^ m i) z =
      ∑ i ∈ S, (m i : ℂ) * logDeriv (g i) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ha_mem : a ∈ insert a S := Finset.mem_insert_self a S
    have hS_sub : ∀ i ∈ S, i ∈ insert a S := fun i hi => Finset.mem_insert_of_mem hi
    have hp1 : g a z ^ m a ≠ 0 := pow_ne_zero _ (hne a ha_mem)
    have hp2 : (∏ i ∈ S, g i z ^ m i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hne i (hS_sub i hi))
    have hd1 : DifferentiableAt ℂ (fun w => g a w ^ m a) z := (hd a ha_mem).pow (m a)
    have hd2 : DifferentiableAt ℂ (fun w => ∏ i ∈ S, g i w ^ m i) z :=
      differentiableAt_finset_prod S _ z fun i hi => (hd i (hS_sub i hi)).pow (m i)
    have hfun : (fun w => ∏ i ∈ insert a S, g i w ^ m i) =
        fun w => g a w ^ m a * ∏ i ∈ S, g i w ^ m i :=
      funext fun w => Finset.prod_insert ha
    rw [hfun, logDeriv_fun_mul z hp1 hp2 hd1 hd2,
      logDeriv_fun_pow (hd a ha_mem) (m a),
      ih (fun i hi => hd i (hS_sub i hi)) (fun i hi => hne i (hS_sub i hi)),
      Finset.sum_insert ha]

/-- **Single-Disk Blaschke + Borel–Carathéodory Theorem**. -/
theorem blaschke_borel_disk (f : ℂ → ℂ) (z₀ : ℂ) (R r₁ r₀ r_eval M : ℝ)
    (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁) (hr₁R : r₁ < R)
    (hr_eval_nn : 0 ≤ r_eval) (hr_eval₁ : r_eval < r₁) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (closedBall z₀ R)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ Z₁ : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z₁ ↔ (ρ ∈ closedBall z₀ r₁ ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z₁, 1 ≤ analyticOrderNatAt f ρ) ∧
      (∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall z₀ r₀), (analyticOrderNatAt f ρ : ℝ)) *
        Real.log (R / r₀) ≤ Real.log M ∧
      (∑ ρ ∈ Z₁, (analyticOrderNatAt f ρ : ℝ)) * Real.log (R / r₁) ≤ Real.log M ∧
      ∀ s ∈ closedBall z₀ r_eval, f s ≠ 0 →
        ‖deriv f s / f s - ∑ ρ ∈ Z₁, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
          (4 * (r_eval + r₁) / (r₁ - r_eval) ^ 2 +
            (r₁ / (R ^ 2 - r₁ * r_eval)) / Real.log (R / r₁)) * Real.log M := by
  classical
  have hr₁ : 0 < r₁ := lt_of_lt_of_le hr₀ hr₀₁
  have hR : 0 < R := lt_trans hr₁ hr₁R
  obtain ⟨Z₁, h, hZ₁, hm_pos, hhd, hh0, hfac⟩ :=
    zeroFactorization_on_ball f z₀ R r₁ hr₁ hr₁R hf hfz₀
  let m : ℂ → ℕ := analyticOrderNatAt f
  let qFactor : ℂ → ℂ → ℂ := fun ρ z => blaschkeDenom z₀ R ρ z / (R : ℂ)
  let hB : ℂ → ℂ := fun z => (∏ ρ ∈ Z₁, qFactor ρ z ^ m ρ) * h z
  have hq_diff : ∀ ρ : ℂ, Differentiable ℂ (qFactor ρ) := fun ρ => by
    unfold qFactor blaschkeDenom
    fun_prop
  have hhB_diff : DifferentiableOn ℂ hB (closedBall z₀ R) := by
    refine DifferentiableOn.mul ?_ hhd
    intro z _
    exact (differentiableAt_finset_prod Z₁ _ z fun ρ _ => ((hq_diff ρ) z).pow (m ρ)).differentiableWithinAt
  have hq_ne_r1 : ∀ ρ ∈ Z₁, ∀ z ∈ closedBall z₀ r₁, qFactor ρ z ≠ 0 := by
    intro ρ hρ z hz h0
    have hden0 : blaschkeDenom z₀ R ρ z = 0 :=
      (div_eq_zero_iff.mp h0).resolve_right (ofReal_ne_zero.mpr hR.ne')
    have hge := norm_blaschkeDenom_ge (R := R) ((hZ₁ ρ).mp hρ).1 hz hr₁.le
    rw [hden0, norm_zero] at hge
    nlinarith
  have hhB_ne_r1 : ∀ z ∈ closedBall z₀ r₁, hB z ≠ 0 := fun z hz =>
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hq_ne_r1 ρ hρ z hz)) (hh0 z hz)
  have hρ_ne_z0 : ∀ ρ ∈ Z₁, 0 < ‖z₀ - ρ‖ := fun ρ hρ => by
    rw [norm_pos_iff, sub_ne_zero]
    intro heq
    exact hfz₀ (heq ▸ ((hZ₁ ρ).mp hρ).2)
  have hhB_z0 : ‖hB z₀‖ = (∏ ρ ∈ Z₁, R ^ m ρ) * ‖h z₀‖ := by
    dsimp only [hB, qFactor, blaschkeDenom]
    rw [norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [sub_self, mul_zero, sub_zero, norm_pow, norm_div, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hR.le]
    congr 1
    field_simp [hR.ne']
  have hf_z0 : ‖f z₀‖ = (∏ ρ ∈ Z₁, ‖z₀ - ρ‖ ^ m ρ) * ‖h z₀‖ := by
    rw [hfac z₀ (mem_closedBall_self hR.le), norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun ρ _ => norm_pow _ _
  have hRprod_pos : 0 < ∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ :=
    Finset.prod_pos fun ρ hρ => pow_pos (div_pos hR (hρ_ne_z0 ρ hρ)) _
  have hcl : closure (ball z₀ R) = closedBall z₀ R := closure_ball z₀ hR.ne'
  have hfr : frontier (ball z₀ R) = sphere z₀ R := frontier_ball z₀ hR.ne'
  have hmax : ∀ z ∈ closedBall z₀ R,
      ‖hB z‖ * (∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ) ≤ M * ‖hB z₀‖ := by
    have hd : DiffContOnCl ℂ hB (ball z₀ R) :=
      DifferentiableOn.diffContOnCl (by rw [hcl]; exact hhB_diff)
    intro z hz
    have hc : ‖hB z‖ ≤ (M * ‖hB z₀‖) / (∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ) := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ (by rw [hcl]; exact hz)
      intro w hw
      rw [hfr] at hw
      have hwc : w ∈ closedBall z₀ R := sphere_subset_closedBall hw
      have hb_eq : ‖hB w‖ = ‖f w‖ := by
        dsimp only [hB]
        rw [hfac w hwc, norm_mul, norm_mul, norm_prod, norm_prod]
        congr 1
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [norm_pow, norm_pow, norm_blaschkeDenom_on_sphere hR hw]
      rw [hb_eq, le_div_iff₀ hRprod_pos]
      have h1 := hbound w hwc
      have hratio : (∏ ρ ∈ Z₁, ‖z₀ - ρ‖ ^ m ρ) * (∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ) =
          ∏ ρ ∈ Z₁, R ^ m ρ := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun ρ hρ => ?_
        rw [← mul_pow, mul_div_cancel₀ _ (hρ_ne_z0 ρ hρ).ne']
      calc ‖f w‖ * (∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ)
          ≤ (M * ‖f z₀‖) * (∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ) :=
            mul_le_mul_of_nonneg_right h1 hRprod_pos.le
        _ = M * (((∏ ρ ∈ Z₁, ‖z₀ - ρ‖ ^ m ρ) * (∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ)) * ‖h z₀‖) := by
            rw [hf_z0]; ring
        _ = M * ‖hB z₀‖ := by rw [hratio, hhB_z0]
    exact (le_div_iff₀ hRprod_pos).mp hc
  have hhB_z0_pos : 0 < ‖hB z₀‖ :=
    norm_pos_iff.mpr (hhB_ne_r1 z₀ (mem_closedBall_self hr₁.le))
  have hprod_le_M : (∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ) ≤ M := by
    have hz0 := hmax z₀ (mem_closedBall_self hR.le)
    exact le_of_mul_le_mul_left (by linarith) hhB_z0_pos
  have hterm_ge_one : ∀ ρ ∈ Z₁, 1 ≤ (R / ‖z₀ - ρ‖) ^ m ρ := by
    intro ρ hρ
    refine one_le_pow₀ ?_
    rw [one_le_div (hρ_ne_z0 ρ hρ), norm_sub_rev, ← dist_eq_norm]
    exact (mem_closedBall.mp ((hZ₁ ρ).mp hρ).1).trans hr₁R.le
  have hcount_r1 : (∑ ρ ∈ Z₁, (m ρ : ℝ)) * Real.log (R / r₁) ≤ Real.log M := by
    have hpow : (R / r₁) ^ (∑ ρ ∈ Z₁, m ρ) ≤ ∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ρ hρ => ?_
      refine pow_le_pow_left₀ (by positivity) ?_ _
      refine div_le_div_of_nonneg_left hR.le (hρ_ne_z0 ρ hρ) ?_
      rw [norm_sub_rev, ← dist_eq_norm]
      exact mem_closedBall.mp ((hZ₁ ρ).mp hρ).1
    have hlog := Real.log_le_log (by positivity) (hpow.trans hprod_le_M)
    rwa [Real.log_pow, Nat.cast_sum] at hlog
  have hcount_r0 : (∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall z₀ r₀), (m ρ : ℝ)) *
      Real.log (R / r₀) ≤ Real.log M := by
    let Z₀ := Z₁.filter (fun ρ => ρ ∈ closedBall z₀ r₀)
    have hpow1 : (R / r₀) ^ (∑ ρ ∈ Z₀, m ρ) ≤ ∏ ρ ∈ Z₀, (R / ‖z₀ - ρ‖) ^ m ρ := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ρ hρ => ?_
      refine pow_le_pow_left₀ (by positivity) ?_ _
      refine div_le_div_of_nonneg_left hR.le (hρ_ne_z0 ρ (Finset.mem_filter.mp hρ).1) ?_
      rw [norm_sub_rev, ← dist_eq_norm]
      exact mem_closedBall.mp (Finset.mem_filter.mp hρ).2
    have hpow2 : (∏ ρ ∈ Z₀, (R / ‖z₀ - ρ‖) ^ m ρ) ≤ ∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ := by
      rw [← Finset.prod_sdiff (Finset.filter_subset (fun ρ => ρ ∈ closedBall z₀ r₀) Z₁)]
      have h1 : 1 ≤ ∏ ρ ∈ Z₁ \ Z₀, (R / ‖z₀ - ρ‖) ^ m ρ :=
        one_le_prod_real _ _ fun ρ hρ => hterm_ge_one ρ (Finset.sdiff_subset hρ)
      have h2 : 0 ≤ ∏ ρ ∈ Z₀, (R / ‖z₀ - ρ‖) ^ m ρ :=
        Finset.prod_nonneg fun ρ hρ => pow_nonneg (div_nonneg hR.le (norm_nonneg _)) _
      nlinarith
    have hlog := Real.log_le_log (by positivity) ((hpow1.trans hpow2).trans hprod_le_M)
    rwa [Real.log_pow, Nat.cast_sum] at hlog
  have hprod_ge_one : 1 ≤ ∏ ρ ∈ Z₁, (R / ‖z₀ - ρ‖) ^ m ρ :=
    one_le_prod_real _ _ hterm_ge_one
  have hhB_bd_r1 : ∀ z ∈ closedBall z₀ r₁, ‖hB z‖ ≤ M * ‖hB z₀‖ := fun z hz =>
    (le_mul_of_one_le_right (norm_nonneg _) hprod_ge_one).trans
      (hmax z (closedBall_subset_closedBall hr₁R.le hz))
  have hbc := borelCaratheodory_logDeriv_on_subball hB z₀ r₁ r_eval M
    hr_eval_nn hr_eval₁ hM (hhB_diff.mono (closedBall_subset_closedBall hr₁R.le))
    hhB_ne_r1 hhB_bd_r1
  refine ⟨Z₁, hZ₁, hm_pos, hcount_r0, hcount_r1, fun s hs hfs => ?_⟩
  have hs_r1 : s ∈ closedBall z₀ r₁ := closedBall_subset_closedBall hr_eval₁.le hs
  have hs_bR : s ∈ ball z₀ R := closedBall_subset_ball hr₁R hs_r1
  have hfeq_loc : (fun w => f w * ∏ ρ ∈ Z₁, qFactor ρ w ^ m ρ) =ᶠ[𝓝 s]
      (fun w => (∏ ρ ∈ Z₁, (w - ρ) ^ m ρ) * hB w) := by
    filter_upwards [isOpen_ball.mem_nhds hs_bR] with w hw
    dsimp only [hB]
    rw [hfac w (ball_subset_closedBall hw)]
    ring
  have hs_ne_ρ : ∀ ρ ∈ Z₁, s - ρ ≠ 0 := fun ρ hρ he =>
    hfs (sub_eq_zero.mp he ▸ ((hZ₁ ρ).mp hρ).2)
  have hq_prod_ne : (∏ ρ ∈ Z₁, qFactor ρ s ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hq_ne_r1 ρ hρ s hs_r1)
  have hlin_prod_ne : (∏ ρ ∈ Z₁, (s - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hs_ne_ρ ρ hρ)
  have hf_diff_s : DifferentiableAt ℂ f s :=
    hf.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hs_bR) ball_subset_closedBall)
  have hhB_diff_s : DifferentiableAt ℂ hB s :=
    hhB_diff.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hs_bR) ball_subset_closedBall)
  have hld_at : logDeriv (fun w => f w * ∏ ρ ∈ Z₁, qFactor ρ w ^ m ρ) s =
      logDeriv (fun w => (∏ ρ ∈ Z₁, (w - ρ) ^ m ρ) * hB w) s := by
    simp only [logDeriv_apply, hfeq_loc.deriv_eq, hfeq_loc.eq_of_nhds]
  rw [logDeriv_fun_mul s hfs hq_prod_ne hf_diff_s
      (differentiableAt_finset_prod Z₁ (fun ρ w => qFactor ρ w ^ m ρ) s
        fun ρ _ => ((hq_diff ρ) s).pow (m ρ)),
    logDeriv_fun_mul s hlin_prod_ne (hhB_ne_r1 s hs_r1)
      (differentiableAt_finset_prod Z₁ (fun ρ w => (w - ρ) ^ m ρ) s
        fun ρ _ => ((differentiableAt_id.sub_const ρ).pow (m ρ))) hhB_diff_s,
    logDeriv_finset_prod_pow Z₁ qFactor m s (fun ρ _ => (hq_diff ρ) s) (fun ρ hρ => hq_ne_r1 ρ hρ s hs_r1),
    logDeriv_finset_prod_pow Z₁ (fun ρ w => w - ρ) m s
      (fun ρ _ => differentiableAt_id.sub_const ρ) hs_ne_ρ] at hld_at
  have hld_lin : ∑ ρ ∈ Z₁, (m ρ : ℂ) * logDeriv (fun w => w - ρ) s =
      ∑ ρ ∈ Z₁, (m ρ : ℂ) / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hd : HasDerivAt (fun w : ℂ => w - ρ) 1 s :=
      ((hasDerivAt_id s).fun_sub (hasDerivAt_const s ρ)).congr_deriv (sub_zero 1)
    rw [logDeriv_apply, hd.deriv, mul_one_div]
  have hld_q : ∀ ρ ∈ Z₁,
      logDeriv (qFactor ρ) s = -starRingEnd ℂ (ρ - z₀) / blaschkeDenom z₀ R ρ s := by
    intro ρ hρ
    have hd : HasDerivAt (qFactor ρ) (-starRingEnd ℂ (ρ - z₀) / (R : ℂ)) s := by
      unfold qFactor blaschkeDenom
      have h1 : HasDerivAt (fun w : ℂ => w - z₀) 1 s :=
        ((hasDerivAt_id s).fun_sub (hasDerivAt_const s z₀)).congr_deriv (sub_zero 1)
      have h2 := ((hasDerivAt_const s ((R : ℂ) ^ 2)).fun_sub
        (h1.const_mul (starRingEnd ℂ (ρ - z₀)))).div_const (R : ℂ)
      refine h2.congr_deriv ?_
      ring
    have hden_ne : blaschkeDenom z₀ R ρ s ≠ 0 := fun h0 =>
      hq_ne_r1 ρ hρ s hs_r1 (by unfold qFactor; rw [h0, zero_div])
    have hR_ne : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
    rw [logDeriv_apply, hd.deriv]
    unfold qFactor
    field_simp [hden_ne, hR_ne]
  rw [hld_lin] at hld_at
  have hsplit : deriv f s / f s - ∑ ρ ∈ Z₁, (m ρ : ℂ) / (s - ρ) =
      deriv hB s / hB s - ∑ ρ ∈ Z₁, (m ρ : ℂ) * logDeriv (qFactor ρ) s := by
    simp only [logDeriv_apply] at hld_at ⊢
    linear_combination hld_at
  rw [hsplit]
  have hden_pos : 0 < R ^ 2 - r₁ * r_eval := by
    have h1 : r₁ * r_eval < r₁ * r₁ := mul_lt_mul_of_pos_left hr_eval₁ hr₁
    have h2 : r₁ * r₁ < R * R := mul_lt_mul'' hr₁R hr₁R hr₁.le hr₁.le
    nlinarith
  have hq_sum_le : ‖∑ ρ ∈ Z₁, (m ρ : ℂ) * logDeriv (qFactor ρ) s‖ ≤
      ((r₁ / (R ^ 2 - r₁ * r_eval)) / Real.log (R / r₁)) * Real.log M := by
    have hlog_pos : 0 < Real.log (R / r₁) :=
      Real.log_pos ((one_lt_div hr₁).mpr hr₁R)
    have hcnt_div : (∑ ρ ∈ Z₁, (m ρ : ℝ)) ≤ Real.log M / Real.log (R / r₁) :=
      (le_div_iff₀ hlog_pos).mpr hcount_r1
    calc ‖∑ ρ ∈ Z₁, (m ρ : ℂ) * logDeriv (qFactor ρ) s‖
        ≤ ∑ ρ ∈ Z₁, ‖(m ρ : ℂ) * logDeriv (qFactor ρ) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z₁, (m ρ : ℝ) * (r₁ / (R ^ 2 - r₁ * r_eval)) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [hld_q ρ hρ, norm_mul, Complex.norm_natCast, norm_div, norm_neg, Complex.norm_conj]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hnum_le : ‖ρ - z₀‖ ≤ r₁ := by
            simpa [mem_closedBall, dist_eq_norm] using ((hZ₁ ρ).mp hρ).1
          have hden_ge := norm_blaschkeDenom_ge (R := R) ((hZ₁ ρ).mp hρ).1 hs hr₁.le
          exact div_le_div₀ hr₁.le hnum_le hden_pos hden_ge
      _ = (∑ ρ ∈ Z₁, (m ρ : ℝ)) * (r₁ / (R ^ 2 - r₁ * r_eval)) := (Finset.sum_mul ..).symm
      _ ≤ (Real.log M / Real.log (R / r₁)) * (r₁ / (R ^ 2 - r₁ * r_eval)) :=
          mul_le_mul_of_nonneg_right hcnt_div (by positivity)
      _ = ((r₁ / (R ^ 2 - r₁ * r_eval)) / Real.log (R / r₁)) * Real.log M := by ring
  calc ‖deriv hB s / hB s - ∑ ρ ∈ Z₁, (m ρ : ℂ) * logDeriv (qFactor ρ) s‖
      ≤ ‖deriv hB s / hB s‖ + ‖∑ ρ ∈ Z₁, (m ρ : ℂ) * logDeriv (qFactor ρ) s‖ := norm_sub_le _ _
    _ ≤ (4 * (r_eval + r₁) / (r₁ - r_eval) ^ 2) * Real.log M +
          ((r₁ / (R ^ 2 - r₁ * r_eval)) / Real.log (R / r₁)) * Real.log M :=
        add_le_add (hbc s hs) hq_sum_le
    _ = (4 * (r_eval + r₁) / (r₁ - r_eval) ^ 2 +
          (r₁ / (R ^ 2 - r₁ * r_eval)) / Real.log (R / r₁)) * Real.log M := by ring

end BlaschkeBorelDisk

/-! ### Part 2: Right-Half-Plane Polynomial Growth & `σ = 2` Lower Bounds -/

section RightHalfPlaneGrowth

private lemma cpow_sub_eq_integral_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - (y : ℂ) ^ (-s) = s * ∫ t in x..y, (t : ℂ) ^ (-s - 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc x y := Set.notMem_uIcc_of_lt hx (hx.trans_le hxy)
  have hr : (-s - 1) ≠ -1 := fun h => hs (by linear_combination -h)
  have hs' : -s ≠ 0 := neg_ne_zero.mpr hs
  rw [integral_cpow (Or.inr ⟨hr, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e, mul_div_assoc', eq_div_iff hs']
  ring

private lemma norm_cpow_sub_le_rpow_diff {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      (‖s‖ / s.re) * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  rw [cpow_sub_eq_integral_of_pos hx (by linarith) hs0, norm_mul]
  have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := Set.notMem_uIcc_of_lt hx (by linarith)
  have hint_norm : ‖∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1)‖ ≤ ∫ t in x..(x + 1), t ^ (-s.re - 1) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun t ht => ?_) ?_
    · have ht0 : 0 < t := lt_trans hx ht.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp
    · refine (continuousOn_id.rpow_const fun t ht => Or.inl ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact (lt_of_lt_of_le hx ht.1).ne'
  have hint_eq : ∫ t in x..(x + 1), t ^ (-s.re - 1) = (x ^ (-s.re) - (x + 1) ^ (-s.re)) / s.re := by
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have e : -s.re - 1 + 1 = -s.re := by ring
    rw [e, div_neg, ← neg_div, neg_sub]
  calc ‖s‖ * ‖∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1)‖
      ≤ ‖s‖ * ((x ^ (-s.re) - (x + 1) ^ (-s.re)) / s.re) :=
        mul_le_mul_of_nonneg_left (hint_norm.trans_eq hint_eq) (norm_nonneg _)
    _ = (‖s‖ / s.re) * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by ring

private lemma norm_cpow_sub_le_rpow_point {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxa : x ≤ a + 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have hxpos : 0 < x := lt_of_lt_of_le ha hax
  rw [cpow_sub_eq_integral_of_pos hxpos hxa hs0, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hC : ∀ t ∈ Set.uIoc x (a + 1), ‖(t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) := by
    intro t ht
    rw [Set.uIoc_of_le hxa] at ht
    have hta : a ≤ t := le_trans hax ht.1.le
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha hta)]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos ha hta (by linarith)
  calc ‖∫ t in x..(a + 1), (t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) * |a + 1 - x| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ ≤ a ^ (-s.re - 1) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ha.le _)
        rw [abs_of_nonneg (by linarith)]; linarith
    _ = a ^ (-s.re - 1) := mul_one _

private lemma norm_character_sum_Icc_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have hmod0 : ∑ n ∈ Finset.range q, χ (n : ZMod q) = 0 := by
    have hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun a b hab => Fin.ext ?_, by simp [ZMod.card]⟩
      have h1 := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h1
    rw [Finset.sum_range, Fintype.sum_bijective _ hbij (fun i => χ ((i : ℕ) : ZMod q)) χ (fun _ => rfl)]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  have hrange : ∀ K : ℕ, ‖∑ n ∈ Finset.range K, χ (n : ZMod q)‖ ≤ (q : ℝ) := by
    intro K
    induction K using Nat.strong_induction_on with
    | _ K ih =>
      by_cases hK : K < q
      · calc ‖∑ n ∈ Finset.range K, χ (n : ZMod q)‖
            ≤ ∑ n ∈ Finset.range K, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum fun n _ => χ.norm_le_one _
          _ = K := by simp
          _ ≤ q := by exact_mod_cast hK.le
      · obtain ⟨K', rfl⟩ : ∃ K', K = q + K' := ⟨K - q, by lia⟩
        rw [Finset.sum_range_add, hmod0, zero_add]
        simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
        exact ih K' (by have := NeZero.pos q; lia)
  have hsplit : ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) =
      (∑ n ∈ Finset.range (M + 1), χ (n : ZMod q)) - χ ((0 : ℕ) : ZMod q) := by
    have hI : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; lia
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M), zero_add, hI]
    ring
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add (hrange (M + 1)) (χ.norm_le_one _))

/-- Explicit polynomial upper bound `‖LFunction χ s‖ ≤ 68 * q * (1 + ‖s‖)` on `Re(s) ≥ 1 / 16`
for every non-principal character `χ ≠ 1` modulo `q`. -/
theorem norm_LFunction_le_of_sixteenth_le_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 68 * (q : ℝ) * (1 + ‖s‖) := by
  let Ap : ℕ → ℂ := fun n => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)
  let dterm : ℂ → ℕ → ℂ := fun w n => Ap n * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))
  let G : ℂ → ℂ := fun w => ∑' n : ℕ, dterm w n
  let B : ℝ := (q : ℝ) + 1
  have hB : ∀ M : ℕ, ‖Ap M‖ ≤ B := norm_character_sum_Icc_le χ hχ
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hdterm_zero : ∀ w : ℂ, dterm w 0 = 0 := fun w => by simp [dterm, Ap]
  have hdterm_le : ∀ {w : ℂ}, 0 < w.re → ∀ n : ℕ,
      ‖dterm w n‖ ≤ B * (‖w‖ * (n : ℝ) ^ (-w.re - 1)) := by
    intro w hw n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hdterm_zero, norm_zero]
      exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · have hx : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have key := norm_cpow_sub_le_rpow_point hx le_rfl (by linarith) hw
      have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [← hcast, Complex.ofReal_natCast] at key
      dsimp only [dterm]
      rw [norm_mul]
      exact mul_le_mul (hB n) key (norm_nonneg _) hB0
  have hsummable : ∀ {w : ℂ}, 0 < w.re → Summable (dterm w) := by
    intro w hw
    refine (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hdterm_le hw) ?_).of_norm
    exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left ‖w‖).mul_left B
  have hpart_id : ∀ (w : ℂ) (M : ℕ),
      ∑ n ∈ Finset.range (M + 1), dterm w n + Ap M * ((M : ℂ) + 1) ^ (-w) =
        ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) * (n : ℂ) ^ (-w) := by
    intro w M
    induction M with
    | zero => simp [hdterm_zero, Ap]
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by lia), ← ih]
      dsimp only [dterm, Ap]
      rw [Finset.sum_Icc_succ_top (by lia)]
      push_cast
      ring
  have hG_diff : DifferentiableOn ℂ G {w : ℂ | 0 < w.re} := by
    intro s0 hs0
    have hs0' : 0 < s0.re := hs0
    let U : Set ℂ := {w : ℂ | s0.re / 2 < w.re} ∩ ball 0 (‖s0‖ + 1)
    have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball
    have hs0U : s0 ∈ U := ⟨by show s0.re / 2 < s0.re; linarith, by simp⟩
    have hdiff : DifferentiableOn ℂ (fun w => ∑' n, dterm w n) U := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1)))
        (((Real.summable_nat_rpow.mpr (by linarith)).mul_left _).mul_left _) ?_ hUo ?_
      · intro n w hw
        have hw0 : w ≠ 0 := fun h => by
          have h1 : s0.re / 2 < w.re := hw.1
          rw [h, zero_re] at h1
          linarith
        refine DifferentiableAt.differentiableWithinAt ?_
        dsimp only [dterm]
        exact ((differentiableAt_id.neg.const_cpow (Or.inr (neg_ne_zero.mpr hw0))).sub
          (differentiableAt_id.neg.const_cpow (Or.inr (neg_ne_zero.mpr hw0)))).const_mul _
      · intro n w hw
        have h1 : s0.re / 2 < w.re := hw.1
        have h2 : ‖w‖ < ‖s0‖ + 1 := by simpa using hw.2
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [hdterm_zero, norm_zero]
          exact mul_nonneg hB0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        · refine (hdterm_le (by linarith) n).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ hB0
          exact mul_le_mul h2.le
            (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (by linarith))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
    exact (hdiff.differentiableAt (hUo.mem_nhds hs0U)).differentiableWithinAt
  have hL_eq_G : ∀ {w : ℂ}, 0 < w.re → DirichletCharacter.LFunction χ w = G w := by
    intro w hw
    have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 0 < z.re} :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
    have hG_an : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} := hG_diff.analyticOnNhd hU
    have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] G := by
      have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [ho.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
      rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
      have hsumL := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz
      have ht1 := (hsumL.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
      have ht_d := ((hsummable (by linarith : 0 < z.re)).hasSum.tendsto_sum_nat).comp
        (tendsto_add_atTop_nat 1)
      have ht_rem : Tendsto (fun M : ℕ => Ap M * ((M : ℂ) + 1) ^ (-z)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hg : Tendsto (fun M : ℕ => B * ((M : ℝ) + 1) ^ (-z.re)) atTop (𝓝 0) := by
          simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < z.re)).comp
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).const_mul B
        refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hg
        have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
        have hcast : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hM, Complex.neg_re]
        exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg hM.le _)
      have ht2 := (ht_d.add ht_rem).congr (hpart_id z)
      rw [add_zero] at ht2
      refine tendsto_nhds_unique (ht1.congr fun M => ?_) ht2
      dsimp only [Function.comp_apply]
      have hIcc_range : ∑ n ∈ Finset.range (M + 1), LSeries.term (χ ·) z n =
          ∑ n ∈ Finset.Icc 1 M, LSeries.term (χ ·) z n := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M),
          LSeries.term_zero, zero_add]
        have hI : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; lia
        rw [hI]
      rw [hIcc_range]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; lia
      rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
    exact hL_an.eqOn_of_preconnected_of_eventuallyEq hG_an
      (convex_halfSpace_re_gt 0).isPreconnected (show (0 : ℝ) < (2 : ℂ).re by norm_num) hev hw
  have hs_pos : 0 < s.re := by linarith
  rw [hL_eq_G hs_pos]
  have hsplitG : G s = (∑ n ∈ Finset.range 2, dterm s n) + ∑' i : ℕ, dterm s (i + 2) :=
    ((hsummable hs_pos).sum_add_tsum_nat_add 2).symm
  have h1_id := hpart_id s 1
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow, mul_one] at h1_id
  have hrewG : G s = χ (1 : ZMod q) + (∑' i : ℕ, dterm s (i + 2) - Ap 1 * ((1 : ℂ) + 1) ^ (-s)) := by
    have h1_eq : ∑ n ∈ Finset.range 2, dterm s n = χ (1 : ZMod q) - Ap 1 * ((1 : ℂ) + 1) ^ (-s) :=
      eq_sub_of_add_eq h1_id
    rw [hsplitG, h1_eq]
    ring
  rw [hrewG]
  have htail : ‖∑' i : ℕ, dterm s (i + 2)‖ ≤ B * (‖s‖ / s.re) := by
    let maj : ℕ → ℝ := fun i => B * ((‖s‖ / s.re) *
      ((((i + 2 : ℕ) : ℝ)) ^ (-s.re) - (((i + 1 + 2 : ℕ) : ℝ)) ^ (-s.re)))
    have hterm_maj : ∀ i : ℕ, ‖dterm s (i + 2)‖ ≤ maj i := by
      intro i
      dsimp only [dterm, maj]
      rw [norm_mul]
      have hx : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
      have key := norm_cpow_sub_le_rpow_diff hx hs_pos
      have hcast1 : (((i + 2 : ℕ) : ℂ) + 1) = ((((i + 2 : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      have hcast2 : (((i + 2 : ℕ) : ℝ) + 1) = ((i + 1 + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [← hcast1, Complex.ofReal_natCast, hcast2] at key
      exact mul_le_mul (hB (i + 2)) key (norm_nonneg _) hB0
    have hmaj_nn : ∀ i : ℕ, 0 ≤ maj i := by
      intro i
      dsimp only [maj]
      refine mul_nonneg hB0 (mul_nonneg (div_nonneg (norm_nonneg _) hs_pos.le) (sub_nonneg.mpr ?_))
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (by lia : i + 2 ≤ i + 1 + 2))
        (by linarith)
    have hpart_maj : ∀ n : ℕ, ∑ i ∈ Finset.range n, maj i ≤ B * (‖s‖ / s.re) := by
      intro n
      dsimp only [maj]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub']
      have h2_le : (((0 + 2 : ℕ) : ℝ)) ^ (-s.re) ≤ 1 := by
        rw [Nat.zero_add, Nat.cast_ofNat]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      have hend_nn : 0 ≤ (((n + 2 : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
      have hc_nn : 0 ≤ B * (‖s‖ / s.re) := mul_nonneg hB0 (div_nonneg (norm_nonneg _) hs_pos.le)
      calc B * ((‖s‖ / s.re) * ((((0 + 2 : ℕ) : ℝ)) ^ (-s.re) - (((n + 2 : ℕ) : ℝ)) ^ (-s.re)))
          = (B * (‖s‖ / s.re)) * ((((0 + 2 : ℕ) : ℝ)) ^ (-s.re) - (((n + 2 : ℕ) : ℝ)) ^ (-s.re)) := by ring
        _ ≤ (B * (‖s‖ / s.re)) * 1 := mul_le_mul_of_nonneg_left (by linarith) hc_nn
        _ = B * (‖s‖ / s.re) := mul_one _
    have hsf := summable_of_sum_range_le hmaj_nn hpart_maj
    have hsn := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_maj hsf
    exact (norm_tsum_le_tsum_norm hsn).trans
      ((Summable.tsum_le_tsum hterm_maj hsn hsf).trans (Real.tsum_le_of_sum_range_le hmaj_nn hpart_maj))
  have hAp1 : ‖Ap 1 * ((1 : ℂ) + 1) ^ (-s)‖ ≤ B := by
    have hcast : ((1 : ℂ) + 1) = ((2 : ℝ) : ℂ) := by norm_num
    rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re]
    have h2_le : (2 : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    calc ‖Ap 1‖ * (2 : ℝ) ^ (-s.re) ≤ B * 1 :=
          mul_le_mul (hB 1) h2_le (Real.rpow_nonneg (by norm_num) _) hB0
      _ = B := mul_one B
  have hdiv : ‖s‖ / s.re ≤ 16 * ‖s‖ := by
    rw [div_le_iff₀ hs_pos]
    nlinarith [norm_nonneg s]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  have hnorm_tot : ‖χ (1 : ZMod q) + (∑' i : ℕ, dterm s (i + 2) - Ap 1 * ((1 : ℂ) + 1) ^ (-s))‖ ≤
      1 + B * (16 * ‖s‖) + B := by
    have ht1 := norm_add_le (χ (1 : ZMod q))
      (∑' i : ℕ, dterm s (i + 2) - Ap 1 * ((1 : ℂ) + 1) ^ (-s))
    have ht2 := norm_sub_le (∑' i : ℕ, dterm s (i + 2)) (Ap 1 * ((1 : ℂ) + 1) ^ (-s))
    have hc1 := χ.norm_le_one (1 : ZMod q)
    nlinarith
  refine hnorm_tot.trans ?_
  dsimp [B]
  nlinarith [norm_nonneg s]

/-- Explicit Euler–Maclaurin upper bound `‖riemannZeta₁ s‖ ≤ 36 * (1 + ‖s‖) ^ 2` on `Re(s) ≥ 1 / 16`. -/
theorem norm_riemannZeta₁_le_of_sixteenth_le_re {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ 36 * (1 + ‖s‖) ^ 2 := by
  let eint : ℂ → ℕ → ℂ := fun w k =>
    ∫ x in ((k + 1 : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ) + 1),
      ((x : ℂ) ^ (-w) - ((((k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (-w))
  let Fk : ℂ → ℕ → ℂ := fun w k =>
    (((k + 1 : ℕ) : ℂ) ^ (1 - w) - ((k + 2 : ℕ) : ℂ) ^ (1 - w)) -
      (w - 1) * ((k + 2 : ℕ) : ℂ) ^ (-w)
  have hFk_eq : ∀ (w : ℂ) (k : ℕ), Fk w k = (w - 1) * eint w k := by
    intro w k
    by_cases hw1 : w = 1
    · subst hw1; simp [Fk, eint]
    set a : ℝ := ((k + 1 : ℕ) : ℝ)
    have ha : 0 < a := by positivity
    have h0 : (0 : ℝ) ∉ Set.uIcc a (a + 1) := Set.notMem_uIcc_of_lt ha (by linarith)
    have hr : -w ≠ -1 := fun h => hw1 (by linear_combination -h)
    have hint1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-w)) volume a (a + 1) :=
      intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
    dsimp only [Fk, eint]
    change (((k + 1 : ℕ) : ℂ) ^ (1 - w) - ((k + 2 : ℕ) : ℂ) ^ (1 - w)) -
        (w - 1) * ((k + 2 : ℕ) : ℂ) ^ (-w) =
      (w - 1) * ∫ x in a..(a + 1), ((x : ℂ) ^ (-w) - ((a + 1 : ℝ) : ℂ) ^ (-w))
    rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const,
      integral_cpow (Or.inr ⟨hr, h0⟩), intervalIntegral.integral_const, Complex.real_smul]
    have hca : (a : ℂ) = ((k + 1 : ℕ) : ℂ) := Complex.ofReal_natCast (k + 1)
    have hcb : ((a + 1 : ℝ) : ℂ) = ((k + 2 : ℕ) : ℂ) := by simp [a]; ring
    have hexp : -w + 1 = 1 - w := by ring
    have h1mw : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
    have hlen : ((a + 1 - a : ℝ) : ℂ) = 1 := by push_cast; ring
    rw [hexp, hca, hcb, hlen]
    set A : ℂ := ((k + 1 : ℕ) : ℂ) ^ (1 - w)
    set B : ℂ := ((k + 2 : ℕ) : ℂ) ^ (1 - w)
    set C : ℂ := ((k + 2 : ℕ) : ℂ) ^ (-w)
    field_simp [h1mw]
    ring
  have hFk_norm : ∀ {w : ℂ}, 0 < w.re → ∀ k : ℕ,
      ‖Fk w k‖ ≤ ‖w - 1‖ * ‖w‖ * ((k + 1 : ℕ) : ℝ) ^ (-w.re - 1) := by
    intro w hw k
    rw [hFk_eq w k, norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    set a : ℝ := ((k + 1 : ℕ) : ℝ)
    have ha : 0 < a := by positivity
    have hC : ∀ x ∈ Set.uIoc a (a + 1),
        ‖(x : ℂ) ^ (-w) - ((a + 1 : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith)] at hx
      exact norm_cpow_sub_le_rpow_point ha hx.1.le hx.2 hw
    calc ‖eint w k‖ ≤ ‖w‖ * a ^ (-w.re - 1) * |a + 1 - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hC
      _ = ‖w‖ * a ^ (-w.re - 1) := by rw [show a + 1 - a = 1 by ring, abs_one, mul_one]
  have hFk_sum : ∀ {w : ℂ}, 0 < w.re → Summable (fun k : ℕ => Fk w k) := by
    intro w hw
    refine (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hFk_norm hw) ?_).of_norm
    exact (((Real.summable_nat_rpow.mpr (by linarith)).comp_injective
      (fun _ _ h => Nat.succ.inj h)).mul_left (‖w - 1‖ * ‖w‖))
  let Gz : ℂ → ℂ := fun w => w - ∑' k : ℕ, Fk w k
  have hGz_diff : DifferentiableOn ℂ Gz {w : ℂ | 0 < w.re} := by
    intro s0 hs0
    have hs0' : 0 < s0.re := hs0
    let U : Set ℂ := {w : ℂ | s0.re / 2 < w.re} ∩ ball 0 (‖s0‖ + 1)
    have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball
    have hs0U : s0 ∈ U := ⟨by show s0.re / 2 < s0.re; linarith, by simp⟩
    have htsum_diff : DifferentiableOn ℂ (fun w => ∑' k : ℕ, Fk w k) U := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k : ℕ => ((‖s0‖ + 2) * (‖s0‖ + 1)) * ((k + 1 : ℕ) : ℝ) ^ (-(s0.re / 2) - 1))
        (((Real.summable_nat_rpow.mpr (by linarith)).comp_injective
          (fun _ _ h => Nat.succ.inj h)).mul_left _) ?_ hUo ?_
      · intro k w _
        refine DifferentiableAt.differentiableWithinAt ?_
        dsimp only [Fk]
        have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        have hk2 : ((k + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
        exact (((differentiableAt_const (1 : ℂ)).fun_sub differentiableAt_id).const_cpow (Or.inl hk1)
          |>.fun_sub (((differentiableAt_const (1 : ℂ)).fun_sub differentiableAt_id).const_cpow (Or.inl hk2)))
          |>.fun_sub ((differentiableAt_id.sub_const 1).fun_mul
            (differentiableAt_id.fun_neg.const_cpow (Or.inl hk2)))
      · intro k w hw
        have h1 : s0.re / 2 < w.re := hw.1
        have h2 : ‖w‖ < ‖s0‖ + 1 := by simpa using hw.2
        have hw1_le : ‖w - 1‖ ≤ ‖s0‖ + 2 := by
          have := norm_sub_le w 1
          rw [norm_one] at this
          linarith
        refine (hFk_norm (by linarith) k).trans ?_
        have hprod_w : ‖w - 1‖ * ‖w‖ ≤ (‖s0‖ + 2) * (‖s0‖ + 1) :=
          mul_le_mul hw1_le h2.le (norm_nonneg _) (by positivity)
        exact mul_le_mul hprod_w
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos k) (by linarith))
          (Real.rpow_nonneg (by positivity) _) (by positivity)
    exact (differentiableWithinAt_id.fun_sub
      (htsum_diff.differentiableAt (hUo.mem_nhds hs0U)).differentiableWithinAt)
  have hzeta_eq_Gz : ∀ {w : ℂ}, 0 < w.re → riemannZeta₁ w = Gz w := by
    intro w hw
    have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h1_an : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
      differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU
    have h2_an : AnalyticOnNhd ℂ Gz {z : ℂ | 0 < z.re} := hGz_diff.analyticOnNhd hU
    have hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] Gz := by
      have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [ho.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
      have hz_ne1 : z ≠ 1 := fun h => by rw [h, one_re] at hz; exact lt_irrefl 1 hz
      have hzeta1 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
        rw [riemannZeta_eq_inv_sub_mul hz_ne1, mul_inv_cancel_left₀ (sub_ne_zero.mpr hz_ne1)]
      rw [hzeta1, zeta_eq_tsum_one_div_nat_add_one_cpow hz]
      have hsum_z : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ z) := by
        have hs' := Real.summable_nat_rpow.mpr (show -z.re < -1 by linarith)
        refine (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
          (hs'.comp_injective (fun _ _ h => Nat.succ.inj h))).of_norm
        have hn_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hc : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
        dsimp only [Function.comp_apply]
        rw [norm_div, norm_one, hc, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hn_pos, Real.rpow_neg hn_pos.le, one_div]
      have ht_z := ((hsum_z.hasSum.tendsto_sum_nat).const_mul (z - 1)).comp (tendsto_add_atTop_nat 1)
      have ht_F := (tendsto_const_nhds (x := z)).sub
        ((hFk_sum (by linarith : 0 < z.re)).hasSum.tendsto_sum_nat)
      have hpart_z : ∀ M : ℕ,
          (z - ∑ k ∈ Finset.range M, Fk z k) - ((M + 1 : ℕ) : ℂ) ^ (1 - z) =
            (z - 1) * ∑ n ∈ Finset.range (M + 1), 1 / ((n : ℂ) + 1) ^ z := by
        intro M
        induction M with
        | zero =>
          simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add, Nat.cast_one,
            one_cpow, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, div_one, mul_one]
        | succ M ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ _ (M + 1)]
          have hc1 : ((M + 1 + 1 : ℕ) : ℂ) = ((M + 2 : ℕ) : ℂ) := rfl
          have hc2 : (((M + 1 : ℕ) : ℂ) + 1) = ((M + 2 : ℕ) : ℂ) := by push_cast; ring
          rw [hc1, hc2, one_div, ← Complex.cpow_neg]
          dsimp only [Fk]
          linear_combination ih
      have ht_rem : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℂ) ^ (1 - z)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hg : Tendsto (fun M : ℕ => (((M : ℝ) + 1) ^ (-(z.re - 1)))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop (by linarith : 0 < z.re - 1)).comp
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hg
        have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hM]
        have hre : (1 - z).re = -(z.re - 1) := by simp
        have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        rw [hre, hcast]
      have ht_lhs := (ht_F.sub ht_rem).congr hpart_z
      rw [sub_zero] at ht_lhs
      exact tendsto_nhds_unique ht_z ht_lhs
    exact h1_an.eqOn_of_preconnected_of_eventuallyEq h2_an
      (convex_halfSpace_re_gt 0).isPreconnected (show (0 : ℝ) < (2 : ℂ).re by norm_num) hev hw
  have hs_pos : 0 < s.re := by linarith
  rw [hzeta_eq_Gz hs_pos]
  dsimp only [Gz]
  have hsum_rpow : ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ)) ≤ 17 := by
    let g : ℕ → ℝ := fun k =>
      if k = 0 then 1 else 16 * ((k : ℝ) ^ (-(1 / 16 : ℝ)) - ((k + 1 : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)))
    have hg_nn : ∀ k : ℕ, 0 ≤ g k := by
      intro k
      dsimp only [g]
      split_ifs with hk0
      · norm_num
      · refine mul_nonneg (by norm_num) (sub_nonneg.mpr ?_)
        exact Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0))
          (by exact_mod_cast Nat.le_succ k) (by norm_num)
    have hle_g : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ)) ≤ g k := by
      intro k
      rcases eq_or_ne k 0 with rfl | hk0
      · simp [g]
      · dsimp only [g]
        simp only [hk0, ↓reduceIte]
        have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
        have h0 : (0 : ℝ) ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
          Set.notMem_uIcc_of_lt hk_pos (by exact_mod_cast (by lia : 0 < k + 1))
        have hint_eq : ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), t ^ (-(17 / 16 : ℝ)) =
            16 * ((k : ℝ) ^ (-(1 / 16 : ℝ)) - ((k + 1 : ℕ) : ℝ) ^ (-(1 / 16 : ℝ))) := by
          rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
          have he : -(17 / 16 : ℝ) + 1 = -(1 / 16 : ℝ) := by norm_num
          rw [he]
          ring
        rw [← hint_eq]
        have hconst : ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ)) =
            ∫ _t in (k : ℝ)..((k + 1 : ℕ) : ℝ), ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          push_cast; ring
        rw [hconst]
        refine intervalIntegral.integral_mono_on (by exact_mod_cast Nat.le_succ k)
          intervalIntegrable_const ?_ fun t ht => ?_
        · refine (continuousOn_id.rpow_const fun t ht => Or.inl ?_).intervalIntegrable
          rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ k)] at ht
          exact (lt_of_lt_of_le hk_pos ht.1).ne'
        · exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hk_pos ht.1) ht.2 (by norm_num)
    have hpart_g : ∀ N : ℕ, ∑ k ∈ Finset.range N, g k ≤ 17 := by
      intro N
      rcases eq_or_ne N 0 with rfl | hN0
      · simp
      · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by lia⟩
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M)]
        have hIco : ∑ k ∈ Finset.Ico 1 (M + 1), g k =
            ∑ j ∈ Finset.range M, 16 * (((j + 1 : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) -
              (((j + 1 + 1 : ℕ) : ℝ)) ^ (-(1 / 16 : ℝ))) := by
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [g]
          have hj1 : 1 + j ≠ 0 := by lia
          simp only [hj1, ↓reduceIte]
          rw [Nat.add_comm 1 j]
        rw [hIco, ← Finset.mul_sum, Finset.sum_range_sub']
        dsimp only [g]
        simp only [↓reduceIte, zero_add, Nat.cast_one, Real.one_rpow]
        have hnn : 0 ≤ (((M + 1 : ℕ) : ℝ)) ^ (-(1 / 16 : ℝ)) := Real.rpow_nonneg (by positivity) _
        linarith
    have hsg := summable_of_sum_range_le hg_nn hpart_g
    have hsf : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ))) :=
      Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (by positivity) _) hle_g hsg
    exact (Summable.tsum_le_tsum hle_g hsf hsg).trans (Real.tsum_le_of_sum_range_le hg_nn hpart_g)
  have htsum_Fk : ‖∑' k : ℕ, Fk s k‖ ≤ 17 * (‖s - 1‖ * ‖s‖) := by
    have hterm : ∀ k : ℕ, ‖Fk s k‖ ≤ (‖s - 1‖ * ‖s‖) * ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ)) := by
      intro k
      refine (hFk_norm hs_pos k).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos k) (by linarith)
    have hsr : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ))) :=
      (Real.summable_nat_rpow.mpr (by norm_num)).comp_injective (fun _ _ h => Nat.succ.inj h)
    have hsn := (hFk_sum hs_pos).norm
    calc ‖∑' k : ℕ, Fk s k‖ ≤ ∑' k : ℕ, ‖Fk s k‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k : ℕ, (‖s - 1‖ * ‖s‖) * ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ)) :=
          Summable.tsum_le_tsum hterm hsn (hsr.mul_left _)
      _ = (‖s - 1‖ * ‖s‖) * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(17 / 16 : ℝ)) := tsum_mul_left
      _ ≤ (‖s - 1‖ * ‖s‖) * 17 := mul_le_mul_of_nonneg_left hsum_rpow (by positivity)
      _ = 17 * (‖s - 1‖ * ‖s‖) := by ring
  have hs1_le : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    have := norm_sub_le s 1
    rw [norm_one] at this
    linarith
  calc ‖s - ∑' k : ℕ, Fk s k‖ ≤ ‖s‖ + ‖∑' k : ℕ, Fk s k‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + 17 * (‖s - 1‖ * ‖s‖) := by linarith [htsum_Fk]
    _ ≤ ‖s‖ + 17 * ((1 + ‖s‖) * ‖s‖) := by gcongr
    _ ≤ 36 * (1 + ‖s‖) ^ 2 := by nlinarith [norm_nonneg s]

private lemma tsum_inv_sq_from_two_le_three_quarters :
    ∑' k : ℕ, (1 / ((k + 2 : ℕ) : ℝ) ^ 2) ≤ 3 / 4 := by
  let g : ℕ → ℝ := fun k =>
    if k = 0 then 1 / 4 else 1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)
  have hg_nn : ∀ k : ℕ, 0 ≤ g k := by
    intro k
    dsimp only [g]
    split_ifs with hk0
    · norm_num
    · refine sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) ?_)
      exact_mod_cast (by lia : k + 1 ≤ k + 2)
  have hle : ∀ k : ℕ, 1 / ((k + 2 : ℕ) : ℝ) ^ 2 ≤ g k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk0
    · norm_num [g]
    · dsimp only [g]
      simp only [hk0, ↓reduceIte]
      have h1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have h2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
      have hsub : 1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ) =
          1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
        field_simp
        push_cast
        ring
      rw [hsub]
      refine one_div_le_one_div_of_le (mul_pos h1 h2) ?_
      push_cast
      nlinarith
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, g k ≤ 3 / 4 := by
    intro N
    rcases eq_or_ne N 0 with rfl | hN0
    · simp; norm_num
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by lia⟩
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M)]
      have hIco : ∑ k ∈ Finset.Ico 1 (M + 1), g k =
          ∑ j ∈ Finset.range M, (1 / ((j + 2 : ℕ) : ℝ) - 1 / ((j + 1 + 2 : ℕ) : ℝ)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [g]
        have hj1 : 1 + j ≠ 0 := by lia
        simp only [hj1, ↓reduceIte]
        congr 2 <;> lia
      rw [hIco, Finset.sum_range_sub']
      dsimp only [g]
      simp only [↓reduceIte, zero_add]
      have hnn : 0 ≤ 1 / (((M + 2 : ℕ) : ℝ)) := by positivity
      push_cast at hnn ⊢
      linarith
  have hsg := summable_of_sum_range_le hg_nn hpart
  have hsf := Summable.of_nonneg_of_le (fun _ => by positivity) hle hsg
  exact (Summable.tsum_le_tsum hle hsf hsg).trans (Real.tsum_le_of_sum_range_le hg_nn hpart)

/-- Elementary telescoping lower bound `1 / 4 ≤ ‖LFunction χ (2 + t * I)‖` for all `χ` and `t : ℝ`. -/
theorem quarter_le_norm_LFunction_two_add_im {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ ((2 : ℂ) + (t : ℂ) * I)‖ := by
  set c : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hre : c.re = 2 := by simp [c]
  have hre1 : 1 < c.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hre1]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hre1
  have hsplit := (hsum.sum_add_tsum_nat_add 2).symm
  change 1 / 4 ≤ ‖∑' n : ℕ, LSeries.term (χ ·) c n‖
  rw [hsplit, Finset.sum_range_succ, Finset.sum_range_one, LSeries.term_zero, zero_add,
    LSeries.term_of_ne_zero one_ne_zero]
  simp only [Nat.cast_one, one_cpow, div_one, map_one]
  have htail : ‖∑' k : ℕ, LSeries.term (χ ·) c (k + 2)‖ ≤ 3 / 4 := by
    have hterm : ∀ k : ℕ, ‖LSeries.term (χ ·) c (k + 2)‖ ≤ 1 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
      intro k
      rw [LSeries.term_of_ne_zero (by lia), norm_div, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre, Real.rpow_two]
      exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
    have hsn := (hsum.comp_injective (fun _ _ h => Nat.succ.inj (Nat.succ.inj h))).norm
    have hsg : Summable (fun k : ℕ => 1 / ((k + 2 : ℕ) : ℝ) ^ 2) := by
      have hs' := Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)
      refine Summable.congr (hs'.comp_injective (fun _ _ h => Nat.succ.inj (Nat.succ.inj h))) fun k => ?_
      have hp : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
      rw [Function.comp_apply, Real.rpow_neg hp.le, Real.rpow_two, one_div]
    exact (norm_tsum_le_tsum_norm hsn).trans
      ((Summable.tsum_le_tsum hterm hsn hsg).trans tsum_inv_sq_from_two_le_three_quarters)
  have htri := norm_sub_norm_le (1 : ℂ) (-∑' k : ℕ, LSeries.term (χ ·) c (k + 2))
  rw [sub_neg_eq_add, norm_one, norm_neg] at htri
  linarith

/-- Elementary telescoping lower bound `1 / 4 ≤ ‖riemannZeta₁ (2 + t * I)‖` for all `t : ℝ`. -/
theorem quarter_le_norm_riemannZeta₁_two_add_im (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta₁ ((2 : ℂ) + (t : ℂ) * I)‖ := by
  set c : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hc_re : c.re = 2 := by simp [c]
  have hc_ne1 : c ≠ 1 := fun h => by rw [h, one_re] at hc_re; norm_num at hc_re
  have hzeta1 : riemannZeta₁ c = (c - 1) * riemannZeta c := by
    rw [riemannZeta_eq_inv_sub_mul hc_ne1, mul_inv_cancel_left₀ (sub_ne_zero.mpr hc_ne1)]
  have hL1 := quarter_le_norm_LFunction_two_add_im (1 : DirichletCharacter ℂ 1) t
  rw [DirichletCharacter.LFunction_modOne_eq] at hL1
  have hc1_ge : 1 ≤ ‖c - 1‖ := by
    have := Complex.re_le_norm (c - 1)
    rw [sub_re, hc_re, one_re] at this
    linarith
  rw [hzeta1, norm_mul]
  calc (1 / 4 : ℝ) = 1 * (1 / 4) := by ring
    _ ≤ ‖c - 1‖ * ‖riemannZeta c‖ := mul_le_mul hc1_ge hL1 (by norm_num) (norm_nonneg _)

end RightHalfPlaneGrowth

/-! ### Part 3: Concrete Strip Zero Counts, Left-Edge GRH Bounds & Good Shift Heights -/

section ConcreteStripAndHeights

private lemma one_sixth_le_log_thirty_one_twenty_sixths :
    (1 / 6 : ℝ) ≤ Real.log (31 / 26) := by
  have hexp : Real.exp 1 ≤ (31 / 26 : ℝ) ^ (6 : ℕ) := by
    have h1 := Real.exp_one_lt_d9
    norm_num at h1 ⊢
    linarith
  have hlog := Real.log_le_log (Real.exp_pos 1) hexp
  rw [Real.log_exp, Real.log_pow] at hlog
  norm_num at hlog
  linarith

private lemma one_sixteenth_le_log_thirty_one_twenty_ninths :
    (1 / 16 : ℝ) ≤ Real.log (31 / 29) := by
  have hexp : Real.exp 1 ≤ (31 / 29 : ℝ) ^ (16 : ℕ) := by
    have h1 := Real.exp_one_lt_d9
    norm_num at h1 ⊢
    linarith
  have hlog := Real.log_le_log (Real.exp_pos 1) hexp
  rw [Real.log_exp, Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-- Concrete single-disk Blaschke–Landau expansion for `LFunction χ` (`χ ≠ 1`) centered at `2 + t*I`
covering the entire horizontal strip `Re(s) ∈ [1 / 4, 2]`. -/
theorem local_expansion_LFunction_at_height {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ∃ Z₁ : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z₁ ↔
        (ρ ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (29 / 16) ∧
          DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z₁, 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ∧
      (∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (13 / 8)),
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
        6 * (Real.log (q : ℝ) + Real.log (680 * (|t| + 2))) ∧
      (∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
        16 * (Real.log (q : ℝ) + Real.log (680 * (|t| + 2))) ∧
      ∀ s ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (7 / 4),
        DirichletCharacter.LFunction χ s ≠ 0 →
          ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
              ∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ ≤
            3750 * (Real.log (q : ℝ) + Real.log (680 * (|t| + 2))) := by
  set z₀ : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  set M : ℝ := 680 * (q : ℝ) * (|t| + 2)
  have hM1 : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t]
  have hlow := quarter_le_norm_LFunction_two_add_im χ t
  have hfz₀ : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hlow)
  have hbound : ∀ z ∈ closedBall z₀ (31 / 16),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre : 1 / 16 ≤ z.re := by
      have h1 := (Complex.abs_re_le_norm (z - z₀)).trans (by simpa [mem_closedBall, dist_eq_norm] using hz)
      have h2 : z₀.re = 2 := by simp [z₀]
      rw [sub_re, h2, abs_le] at h1
      linarith
    have hzn : 1 + ‖z‖ ≤ (5 / 2) * (|t| + 2) := by
      have h1 : ‖z - z₀‖ ≤ 31 / 16 := by simpa [mem_closedBall, dist_eq_norm] using hz
      have h2 : ‖z₀‖ ≤ 2 + |t| := (norm_add_le _ _).trans (by simp)
      have h4 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      linarith [abs_nonneg t]
    have hg := norm_LFunction_le_of_sixteenth_le_re χ hχ hre
    have h4low : 1 ≤ 4 * ‖DirichletCharacter.LFunction χ z₀‖ := by linarith
    calc ‖DirichletCharacter.LFunction χ z‖
        ≤ 68 * (q : ℝ) * (1 + ‖z‖) := hg
      _ ≤ 68 * (q : ℝ) * ((5 / 2) * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left hzn (by positivity)
      _ = (170 * (q : ℝ) * (|t| + 2)) * 1 := by ring
      _ ≤ (170 * (q : ℝ) * (|t| + 2)) * (4 * ‖DirichletCharacter.LFunction χ z₀‖) :=
          mul_le_mul_of_nonneg_left h4low (by positivity)
      _ = M * ‖DirichletCharacter.LFunction χ z₀‖ := by dsimp [M]; ring
  obtain ⟨Z₁, hZ₁, hm_pos, hc0, hc1, hder⟩ :=
    blaschke_borel_disk (DirichletCharacter.LFunction χ) z₀ (31 / 16) (29 / 16) (13 / 8) (7 / 4) M
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM1
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn hfz₀ hbound
  have hlogM_eq : Real.log M = Real.log (q : ℝ) + Real.log (680 * (|t| + 2)) := by
    have heq : M = (q : ℝ) * (680 * (|t| + 2)) := by dsimp [M]; ring
    rw [heq, Real.log_mul (by positivity) (by positivity)]
  have hlogM_nn : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hrat0 : (31 / 16 : ℝ) / (13 / 8) = 31 / 26 := by norm_num
  have hrat1 : (31 / 16 : ℝ) / (29 / 16) = 31 / 29 := by norm_num
  rw [hrat0] at hc0
  rw [hrat1] at hc1 hder
  have hl26 := one_sixth_le_log_thirty_one_twenty_sixths
  have hl29 := one_sixteenth_le_log_thirty_one_twenty_ninths
  refine ⟨Z₁, hZ₁, hm_pos, ?_, ?_, fun s hs hfs => ?_⟩
  · have hsum_nn : 0 ≤ ∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall z₀ (13 / 8)),
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hl26 hsum_nn
    rw [← hlogM_eq]
    linarith
  · have hsum_nn : 0 ≤ ∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hl29 hsum_nn
    rw [← hlogM_eq]
    linarith
  · refine (hder s hs hfs).trans ?_
    rw [← hlogM_eq]
    refine mul_le_mul_of_nonneg_right ?_ hlogM_nn
    have hdiv_le : ((29 / 16 : ℝ) / ((31 / 16) ^ 2 - (29 / 16) * (7 / 4))) /
        Real.log (31 / 29) ≤ 64 := by
      have hnum : (29 / 16 : ℝ) / ((31 / 16) ^ 2 - (29 / 16) * (7 / 4)) = 464 / 149 := by norm_num
      rw [hnum, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl29)]
      linarith
    have hmain_const : (4 : ℝ) * (7 / 4 + 29 / 16) / (29 / 16 - 7 / 4) ^ 2 = 3648 := by norm_num
    linarith

/-- Concrete single-disk Blaschke–Landau expansion for `riemannZeta` (via `riemannZeta₁`) centered at
`2 + t*I` covering `Re(s) ∈ [1 / 4, 2]`. -/
theorem local_expansion_zeta_at_height (t : ℝ) :
    ∃ Z₁ : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z₁ ↔
        (ρ ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (29 / 16) ∧ ρ ≠ 1 ∧ riemannZeta ρ = 0)) ∧
      (∀ ρ ∈ Z₁, 1 ≤ analyticOrderNatAt riemannZeta ρ) ∧
      (∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (13 / 8)),
          (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        6 * Real.log (1440 * (|t| + 2) ^ 2) ∧
      (∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        16 * Real.log (1440 * (|t| + 2) ^ 2) ∧
      ∀ s ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (7 / 4),
        s ≠ 1 → riemannZeta s ≠ 0 →
          ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
              ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
            3750 * Real.log (1440 * (|t| + 2) ^ 2) := by
  set z₀ : ℂ := (2 : ℂ) + (t : ℂ) * I
  set M : ℝ := 1440 * (|t| + 2) ^ 2
  have hM1 : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t]
  have hlow := quarter_le_norm_riemannZeta₁_two_add_im t
  have hfz₀ : riemannZeta₁ z₀ ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hlow)
  have hbound : ∀ z ∈ closedBall z₀ (31 / 16),
      ‖riemannZeta₁ z‖ ≤ M * ‖riemannZeta₁ z₀‖ := by
    intro z hz
    have hre : 1 / 16 ≤ z.re := by
      have h1 := (Complex.abs_re_le_norm (z - z₀)).trans (by simpa [mem_closedBall, dist_eq_norm] using hz)
      have h2 : z₀.re = 2 := by simp [z₀]
      rw [sub_re, h2, abs_le] at h1
      linarith
    have hzn : 1 + ‖z‖ ≤ (5 / 2) * (|t| + 2) := by
      have h1 : ‖z - z₀‖ ≤ 31 / 16 := by simpa [mem_closedBall, dist_eq_norm] using hz
      have h2 : ‖z₀‖ ≤ 2 + |t| := (norm_add_le _ _).trans (by simp)
      have h4 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      linarith [abs_nonneg t]
    have hg := norm_riemannZeta₁_le_of_sixteenth_le_re hre
    have hsq : (1 + ‖z‖) ^ 2 ≤ ((5 / 2) * (|t| + 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hzn 2
    have h4low : 1 ≤ 4 * ‖riemannZeta₁ z₀‖ := by linarith
    calc ‖riemannZeta₁ z‖ ≤ 36 * (1 + ‖z‖) ^ 2 := hg
      _ ≤ 36 * ((5 / 2) * (|t| + 2)) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = (225 * (|t| + 2) ^ 2) * 1 := by ring
      _ ≤ (360 * (|t| + 2) ^ 2) * (4 * ‖riemannZeta₁ z₀‖) := by
          nlinarith [norm_nonneg (riemannZeta₁ z₀)]
      _ = M * ‖riemannZeta₁ z₀‖ := by dsimp [M]; ring
  obtain ⟨Z₁, hZ₁, hm_pos, hc0, hc1, hder⟩ :=
    blaschke_borel_disk riemannZeta₁ z₀ (31 / 16) (29 / 16) (13 / 8) (7 / 4) M
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM1
      differentiable_riemannZeta₁.differentiableOn hfz₀ hbound
  have hzeta1_eq : ∀ {w : ℂ}, w ≠ 1 → riemannZeta₁ w = (w - 1) * riemannZeta w := fun hw => by
    rw [riemannZeta_eq_inv_sub_mul hw, mul_inv_cancel_left₀ (sub_ne_zero.mpr hw)]
  have hord_eq : ∀ {w : ℂ}, w ≠ 1 →
      analyticOrderNatAt riemannZeta₁ w = analyticOrderNatAt riemannZeta w := by
    intro w hw
    unfold analyticOrderNatAt
    have hev : riemannZeta₁ =ᶠ[𝓝 w] (fun z => z - 1) * riemannZeta := by
      filter_upwards [isOpen_ne.mem_nhds hw] with z hz
      exact hzeta1_eq hz
    have ha1 : AnalyticAt ℂ (fun z : ℂ => z - 1) w := analyticAt_id.sub analyticAt_const
    have ha2 : AnalyticAt ℂ riemannZeta w := analyticOn_riemannZeta w hw
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul ha1 ha2,
      ha1.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hw), zero_add]
  have hne1_of_Z1 : ∀ ρ ∈ Z₁, ρ ≠ 1 := by
    intro ρ hρ h1
    have hz0 := ((hZ₁ ρ).mp hρ).2
    rw [h1, riemannZeta₁_one] at hz0
    exact one_ne_zero hz0
  have hZ1_iff : ∀ ρ : ℂ, ρ ∈ Z₁ ↔ (ρ ∈ closedBall z₀ (29 / 16) ∧ ρ ≠ 1 ∧ riemannZeta ρ = 0) := by
    intro ρ
    rw [hZ₁]
    constructor
    · rintro ⟨hb, hz⟩
      have hne1 : ρ ≠ 1 := fun h => by rw [h, riemannZeta₁_one] at hz; exact one_ne_zero hz
      rw [hzeta1_eq hne1, mul_eq_zero] at hz
      exact ⟨hb, hne1, hz.resolve_left (sub_ne_zero.mpr hne1)⟩
    · rintro ⟨hb, hne1, hz⟩
      refine ⟨hb, ?_⟩
      rw [hzeta1_eq hne1, hz, mul_zero]
  have hl26 := one_sixth_le_log_thirty_one_twenty_sixths
  have hl29 := one_sixteenth_le_log_thirty_one_twenty_ninths
  have hlogM_nn : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hrat0 : (31 / 16 : ℝ) / (13 / 8) = 31 / 26 := by norm_num
  have hrat1 : (31 / 16 : ℝ) / (29 / 16) = 31 / 29 := by norm_num
  rw [hrat0] at hc0
  rw [hrat1] at hc1 hder
  refine ⟨Z₁, hZ1_iff, fun ρ hρ => hord_eq (hne1_of_Z1 ρ hρ) ▸ hm_pos ρ hρ, ?_, ?_, ?_⟩
  · have heq_sum : ∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall z₀ (13 / 8)),
        (analyticOrderNatAt riemannZeta ρ : ℝ) =
      ∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall z₀ (13 / 8)),
        (analyticOrderNatAt riemannZeta₁ ρ : ℝ) :=
      Finset.sum_congr rfl fun ρ hρ => by rw [hord_eq (hne1_of_Z1 ρ (Finset.mem_filter.mp hρ).1)]
    rw [heq_sum]
    have hnn : 0 ≤ ∑ ρ ∈ Z₁.filter (fun ρ => ρ ∈ closedBall z₀ (13 / 8)),
        (analyticOrderNatAt riemannZeta₁ ρ : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hl26 hnn
    linarith
  · have heq_sum : ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℝ) =
        ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta₁ ρ : ℝ) :=
      Finset.sum_congr rfl fun ρ hρ => by rw [hord_eq (hne1_of_Z1 ρ hρ)]
    rw [heq_sum]
    have hnn : 0 ≤ ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta₁ ρ : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hl29 hnn
    linarith
  · intro s hs hs1 hzs
    have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hz1_ne : riemannZeta₁ s ≠ 0 := by
      rw [hzeta1_eq hs1]
      exact mul_ne_zero hs_sub hzs
    have hld_id : deriv riemannZeta₁ s / riemannZeta₁ s =
        deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
      rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1, riemannZeta_eq_inv_sub_mul hs1]
      field_simp [hs_sub, hz1_ne]
      ring
    have hsum_id : ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ) =
        ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta₁ ρ : ℂ) / (s - ρ) :=
      Finset.sum_congr rfl fun ρ hρ => by rw [hord_eq (hne1_of_Z1 ρ hρ)]
    rw [← hld_id, hsum_id]
    refine (hder s hs hz1_ne).trans (mul_le_mul_of_nonneg_right ?_ hlogM_nn)
    have hdiv_le : ((29 / 16 : ℝ) / ((31 / 16) ^ 2 - (29 / 16) * (7 / 4))) /
        Real.log (31 / 29) ≤ 64 := by
      have hnum : (29 / 16 : ℝ) / ((31 / 16) ^ 2 - (29 / 16) * (7 / 4)) = 464 / 149 := by norm_num
      rw [hnum, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl29)]
      linarith
    have hmain_const : (4 : ℝ) * (7 / 4 + 29 / 16) / (29 / 16 - 7 / 4) ^ 2 = 3648 := by norm_num
    linarith

/-- Under GRH for `χ`, along the left vertical line `Re(s) = 1 / 4`, `LFunction χ (1 / 4 + t * I) ≠ 0`
and `‖L'/L(1 / 4 + t * I, χ)‖ ≤ 3814 * (log q + log(680 * (|t| + 2)))`. -/
theorem norm_logDeriv_LFunction_quarter_le_of_grh {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hLine : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2)
    (t : ℝ) :
    DirichletCharacter.LFunction χ ((1 / 4 : ℂ) + (t : ℂ) * I) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((1 / 4 : ℂ) + (t : ℂ) * I) /
          DirichletCharacter.LFunction χ ((1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
        3814 * (Real.log (q : ℝ) + Real.log (680 * (|t| + 2))) := by
  set s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I
  have hs_re : s.re = 1 / 4 := by simp [s]
  have hs_ne0 : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro h0
    have hhalf := hLine s (by linarith) (by linarith) h0
    linarith
  refine ⟨hs_ne0, ?_⟩
  obtain ⟨Z₁, hZ₁, _, _, hc1, hder⟩ := local_expansion_LFunction_at_height χ hχ t
  have hs_mem : s ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (7 / 4) := by
    rw [mem_closedBall, dist_eq_norm]
    have hdiff : s - ((2 : ℂ) + (t : ℂ) * I) = -(7 / 4 : ℂ) := by dsimp [s]; ring
    rw [hdiff]
    norm_num
  have hmain := hder s hs_mem hs_ne0
  have hsum_le : ‖∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ ≤
      64 * (Real.log (q : ℝ) + Real.log (680 * (|t| + 2))) := by
    calc ‖∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z₁, ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z₁, 4 * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rcases (hZ₁ ρ).mp hρ with ⟨hρ_ball, hρ_zero⟩
          have hρ_re_pos : 0 < ρ.re := by
            have h1 := (Complex.abs_re_le_norm (ρ - ((2 : ℂ) + (t : ℂ) * I))).trans
              (by simpa [mem_closedBall, dist_eq_norm] using hρ_ball)
            rw [sub_re, abs_le] at h1
            simp at h1
            linarith
          have hρ_re_lt1 : ρ.re < 1 := by
            by_contra hge1
            exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
              (not_lt.mp hge1) hρ_zero
          have hρ_half : ρ.re = 1 / 2 := hLine ρ hρ_re_pos hρ_re_lt1 hρ_zero
          have hdist : 1 / 4 ≤ ‖s - ρ‖ := by
            have h1 := Complex.abs_re_le_norm (s - ρ)
            rw [sub_re, hs_re, hρ_half] at h1
            norm_num at h1
            exact h1
          rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
          have hm_nn : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
            Nat.cast_nonneg _
          nlinarith
      _ = 4 * ∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
          (Finset.mul_sum ..).symm
      _ ≤ 4 * (16 * (Real.log (q : ℝ) + Real.log (680 * (|t| + 2)))) :=
          mul_le_mul_of_nonneg_left hc1 (by norm_num)
      _ = 64 * (Real.log (q : ℝ) + Real.log (680 * (|t| + 2))) := by ring
  have htri : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ := by
    simpa using norm_add_le
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
      (∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
  linarith

/-- Under `RiemannZetaZerosOnLine`, along `Re(s) = 1 / 4`, `riemannZeta (1 / 4 + t * I) ≠ 0` and
`‖ζ'/ζ(1 / 4 + t * I)‖ ≤ 3814 * log(1440 * (|t| + 2)^2) + 4 / 3`. -/
theorem norm_logDeriv_zeta_quarter_le_of_grh
    (hRH : CitedPremises.RiemannZetaZerosOnLine) (t : ℝ) :
    riemannZeta ((1 / 4 : ℂ) + (t : ℂ) * I) ≠ 0 ∧
      ‖deriv riemannZeta ((1 / 4 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
        3814 * Real.log (1440 * (|t| + 2) ^ 2) + 4 / 3 := by
  set s : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I
  have hs_re : s.re = 1 / 4 := by simp [s]
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, one_re] at hs_re; norm_num at hs_re
  have hnot_triv : ∀ z : ℂ, 0 < z.re → ¬∃ n : ℕ, z = -2 * ((n : ℂ) + 1) := by
    intro z hz ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs_ne0 : riemannZeta s ≠ 0 := by
    intro h0
    have hhalf := hRH s h0 (hnot_triv s (by linarith)) hs_ne1
    linarith
  refine ⟨hs_ne0, ?_⟩
  obtain ⟨Z₁, hZ₁, _, _, hc1, hder⟩ := local_expansion_zeta_at_height t
  have hs_mem : s ∈ closedBall ((2 : ℂ) + (t : ℂ) * I) (7 / 4) := by
    rw [mem_closedBall, dist_eq_norm]
    have hdiff : s - ((2 : ℂ) + (t : ℂ) * I) = -(7 / 4 : ℂ) := by dsimp [s]; ring
    rw [hdiff]
    norm_num
  have hmain := hder s hs_mem hs_ne1 hs_ne0
  have hsum_le : ‖∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
      64 * Real.log (1440 * (|t| + 2) ^ 2) := by
    calc ‖∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z₁, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z₁, 4 * (analyticOrderNatAt riemannZeta ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rcases (hZ₁ ρ).mp hρ with ⟨hρ_ball, hρ_ne1, hρ_zero⟩
          have hρ_re_pos : 0 < ρ.re := by
            have h1 := (Complex.abs_re_le_norm (ρ - ((2 : ℂ) + (t : ℂ) * I))).trans
              (by simpa [mem_closedBall, dist_eq_norm] using hρ_ball)
            rw [sub_re, abs_le] at h1
            simp at h1
            linarith
          have hρ_half : ρ.re = 1 / 2 := hRH ρ hρ_zero (hnot_triv ρ hρ_re_pos) hρ_ne1
          have hdist : 1 / 4 ≤ ‖s - ρ‖ := by
            have h1 := Complex.abs_re_le_norm (s - ρ)
            rw [sub_re, hs_re, hρ_half] at h1
            norm_num at h1
            exact h1
          rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
          have hm_nn : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
          nlinarith
      _ = 4 * ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℝ) := (Finset.mul_sum ..).symm
      _ ≤ 4 * (16 * Real.log (1440 * (|t| + 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left hc1 (by norm_num)
      _ = 64 * Real.log (1440 * (|t| + 2) ^ 2) := by ring
  have hpole_le : ‖(1 : ℂ) / (s - 1)‖ ≤ 4 / 3 := by
    have h1 : 3 / 4 ≤ ‖s - 1‖ := by
      have hre := Complex.abs_re_le_norm (s - 1)
      rw [sub_re, hs_re, one_re] at hre
      norm_num at hre
      exact hre
    rw [norm_div, norm_one]
    exact (div_le_div_iff₀ (by linarith) (by norm_num)).mpr (by linarith)
  have hsplit : deriv riemannZeta s / riemannZeta s =
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)) +
        (∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)) - 1 / (s - 1) := by ring
  rw [hsplit]
  have htri1 := norm_sub_le
    ((deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
        ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)) +
      (∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)))
    (1 / (s - 1))
  have htri2 := norm_add_le
    (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
      ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
    (∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
  linarith

/-- Pigeonhole height-selection lemma on `[T, T + 1]` avoiding any finite set `S : Finset ℝ`. -/
theorem exists_far_from_finset (S : Finset ℝ) (T : ℝ) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      ∀ x ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |x - T'| := by
  classical
  by_contra hcon
  push Not at hcon
  have hn : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have key : ∀ k ∈ Finset.range (S.card + 1), ∃ x ∈ S,
      |x - (T + (k : ℝ) / ((S.card : ℝ) + 1))| < 1 / (2 * ((S.card : ℝ) + 1)) := by
    intro k hk
    have hk' : (k : ℝ) ≤ S.card := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    apply hcon
    · have : 0 ≤ (k : ℝ) / ((S.card : ℝ) + 1) := by positivity
      linarith
    · have : (k : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by rw [div_le_one hn]; linarith
      linarith
  choose! g hgS hg using key
  obtain ⟨a, ha, b, hb, hab, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (S.card + 1)) (t := S)
      (by simp) (fun k hk => hgS k hk)
  have h1 := hg a ha
  have h2 := hg b hb
  rw [heq] at h1
  have hclose : |(a : ℝ) / ((S.card : ℝ) + 1) - (b : ℝ) / ((S.card : ℝ) + 1)|
      < 1 / ((S.card : ℝ) + 1) := by
    calc |(a : ℝ) / ((S.card : ℝ) + 1) - (b : ℝ) / ((S.card : ℝ) + 1)|
        = |(g b - (T + (b : ℝ) / ((S.card : ℝ) + 1))) -
            (g b - (T + (a : ℝ) / ((S.card : ℝ) + 1)))| := by congr 1; ring
      _ ≤ |g b - (T + (b : ℝ) / ((S.card : ℝ) + 1))| +
            |g b - (T + (a : ℝ) / ((S.card : ℝ) + 1))| := abs_sub _ _
      _ < 1 / (2 * ((S.card : ℝ) + 1)) + 1 / (2 * ((S.card : ℝ) + 1)) := add_lt_add h2 h1
      _ = 1 / ((S.card : ℝ) + 1) := by field_simp; ring
  rw [← sub_div, abs_div, abs_of_pos hn, div_lt_div_iff_of_pos_right hn] at hclose
  have hsep : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    rcases lt_or_gt_of_ne hab with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  linarith

private lemma closedBall_cover_of_crit_zero {y₀ y : ℝ} {w : ℂ}
    (h1 : y₀ ≤ y) (h2 : y ≤ y₀ + 1) (hw_re : w.re = 1 / 2)
    (h5 : w ∈ closedBall ((2 : ℂ) + (y : ℂ) * I) (29 / 16)) :
    w ∈ closedBall ((2 : ℂ) + (y₀ : ℂ) * I) (29 / 16) ∨
      w ∈ closedBall ((2 : ℂ) + ((y₀ + 1 : ℝ) : ℂ) * I) (29 / 16) := by
  have hnorm_iff : ∀ η : ℝ,
      w ∈ closedBall ((2 : ℂ) + (η : ℂ) * I) (29 / 16) ↔
        (w.re - 2) ^ 2 + (w.im - η) ^ 2 ≤ (29 / 16) ^ 2 := by
    intro η
    have heq : Complex.normSq (w - ((2 : ℂ) + (η : ℂ) * I)) = (w.re - 2) ^ 2 + (w.im - η) ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [sub_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, sub_im, add_im, im_ofNat, mul_im, zero_add]
      ring
    rw [mem_closedBall, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (by norm_num),
      Complex.sq_norm, heq]
  rw [hnorm_iff, hw_re] at h5
  rw [hnorm_iff, hnorm_iff, hw_re]
  by_cases hv : w.im ≤ y₀ + 1 / 2
  · left
    by_cases hv' : y₀ ≤ w.im
    · nlinarith [mul_nonneg (sub_nonneg.mpr hv') (sub_nonneg.mpr hv)]
    · push Not at hv'
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ y + y₀ - 2 * w.im by linarith)]
  · right
    push Not at hv
    by_cases hv' : w.im ≤ y₀ + 1
    · nlinarith [mul_nonneg (show 0 ≤ w.im - y₀ - 1 / 2 by linarith) (sub_nonneg.mpr hv')]
    · push Not at hv'
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ 2 * w.im - y - y₀ - 1 by linarith)]

/-- Under GRH for `χ` (`χ ≠ 1`), for every `T ≥ 2` there exists a symmetric good horizontal shift
height `T' ∈ [T, T + 1]` on which `LFunction χ (x ± T' * I) ≠ 0` and
`‖L'/L(x ± T' * I, χ)‖ ≤ 3000 * (log q + log(680 * (T + 3))) ^ 2` across all `x ∈ [1 / 4, 3 / 2]`. -/
theorem exists_good_shift_height_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hLine : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2)
    {T : ℝ} (hT : 2 ≤ T) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      ∀ (x y : ℝ), 1 / 4 ≤ x → x ≤ 3 / 2 → (y = T' ∨ y = -T') →
        DirichletCharacter.LFunction χ ((x : ℂ) + (y : ℂ) * I) ≠ 0 ∧
          ‖deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + (y : ℂ) * I) /
              DirichletCharacter.LFunction χ ((x : ℂ) + (y : ℂ) * I)‖ ≤
            3000 * (Real.log (q : ℝ) + Real.log (680 * (T + 3))) ^ 2 := by
  classical
  obtain ⟨Z_p0, hZp0, hmp0, _, hcp0, _⟩ := local_expansion_LFunction_at_height χ hχ T
  obtain ⟨Z_p1, hZp1, hmp1, _, hcp1, _⟩ := local_expansion_LFunction_at_height χ hχ (T + 1)
  obtain ⟨Z_n0, hZn0, hmn0, _, hcn0, _⟩ := local_expansion_LFunction_at_height χ hχ (-T)
  obtain ⟨Z_n1, hZn1, hmn1, _, hcn1, _⟩ := local_expansion_LFunction_at_height χ hχ (-(T + 1))
  let L_max : ℝ := Real.log (q : ℝ) + Real.log (680 * (T + 3))
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  have hL_ge6 : 6 ≤ L_max := by
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    have h680 : Real.exp 6 ≤ 680 * (T + 3) := by
      have he1 := Real.exp_one_lt_d9
      have he6 : Real.exp 6 = (Real.exp 1) ^ (6 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [he6]
      have hp : (Real.exp 1) ^ (6 : ℕ) ≤ (2.72 : ℝ) ^ (6 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 6
      norm_num at hp
      linarith
    have hl2 : 6 ≤ Real.log (680 * (T + 3)) :=
      (Real.le_log_iff_exp_le (by positivity)).mpr h680
    dsimp [L_max]; linarith
  have hcard_le : ∀ (Z : Finset ℂ) (η : ℝ), |η| ≤ T + 1 →
      (∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) →
      (∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
        16 * (Real.log (q : ℝ) + Real.log (680 * (|η| + 2))) →
      (Z.card : ℝ) ≤ 16 * L_max := by
    intro Z η hη hm hc
    have h1 : (Z.card : ℝ) ≤ ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact Finset.sum_le_sum fun ρ hρ => by exact_mod_cast hm ρ hρ
    have hlog_mono : Real.log (680 * (|η| + 2)) ≤ Real.log (680 * (T + 3)) :=
      Real.log_le_log (by positivity) (by linarith)
    dsimp [L_max]; linarith
  let Z_all : Finset ℂ := (Z_p0 ∪ Z_p1) ∪ (Z_n0 ∪ Z_n1)
  let S_sym : Finset ℝ := Z_all.image (fun ρ => |ρ.im|)
  have hS_card : (S_sym.card : ℝ) + 1 ≤ 65 * L_max := by
    have hc_img : S_sym.card ≤ Z_all.card := Finset.card_image_le
    have hc_u : Z_all.card ≤ Z_p0.card + Z_p1.card + Z_n0.card + Z_n1.card := by
      have u1 := Finset.card_union_le (Z_p0 ∪ Z_p1) (Z_n0 ∪ Z_n1)
      have u2 := Finset.card_union_le Z_p0 Z_p1
      have u3 := Finset.card_union_le Z_n0 Z_n1
      dsimp [Z_all] at u1 ⊢; lia
    have h1 : (S_sym.card : ℝ) ≤
        (Z_p0.card : ℝ) + (Z_p1.card : ℝ) + (Z_n0.card : ℝ) + (Z_n1.card : ℝ) := by
      exact_mod_cast hc_img.trans hc_u
    have b0 := hcard_le Z_p0 T (by rw [abs_of_nonneg (by linarith)]; linarith) hmp0 hcp0
    have b1 := hcard_le Z_p1 (T + 1) (by rw [abs_of_nonneg (by linarith)]) hmp1 hcp1
    have bn0 := hcard_le Z_n0 (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)]; linarith) hmn0 hcn0
    have bn1 := hcard_le Z_n1 (-(T + 1)) (by rw [abs_neg, abs_of_nonneg (by linarith)]) hmn1 hcn1
    linarith
  obtain ⟨T', hT1, hT2, hfar⟩ := exists_far_from_finset S_sym T
  refine ⟨T', hT1, hT2, fun x y hx1 hx2 hy => ?_⟩
  have hy_abs : |y| = T' := by
    rcases hy with rfl | rfl
    · exact abs_of_nonneg (by linarith)
    · rw [abs_neg, abs_of_nonneg (by linarith)]
  have hcrit_of_ball : ∀ (η : ℝ) (ρ : ℂ),
      ρ ∈ closedBall ((2 : ℂ) + (η : ℂ) * I) (29 / 16) →
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re = 1 / 2 := by
    intro η ρ hb hz
    have hre_pos : 0 < ρ.re := by
      have h1 := (Complex.abs_re_le_norm (ρ - ((2 : ℂ) + (η : ℂ) * I))).trans
        (by simpa [mem_closedBall, dist_eq_norm] using hb)
      rw [sub_re, abs_le] at h1; simp at h1; linarith
    have hre_lt1 : ρ.re < 1 := by
      by_contra hge1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp hge1) hz
    exact hLine ρ hre_pos hre_lt1 hz
  have hmem_Zall : ∀ ρ : ℂ, ρ ∈ closedBall ((2 : ℂ) + (y : ℂ) * I) (29 / 16) →
      DirichletCharacter.LFunction χ ρ = 0 → ρ ∈ Z_all := by
    intro ρ hb hz
    have hhalf := hcrit_of_ball y ρ hb hz
    rcases hy with rfl | rfl
    · rcases closedBall_cover_of_crit_zero hT1 hT2 hhalf hb with hcov | hcov
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((hZp0 ρ).mpr ⟨hcov, hz⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((hZp1 ρ).mpr ⟨hcov, hz⟩))
    · have hcov_neg := closedBall_cover_of_crit_zero (y₀ := -(T + 1)) (y := -T')
        (by linarith) (by linarith) hhalf hb
      have hshift_eq : ((-(T + 1) + 1 : ℝ) : ℂ) = ((-T : ℝ) : ℂ) := by push_cast; ring
      rcases hcov_neg with hcov | hcov
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ ((hZn1 ρ).mpr ⟨hcov, hz⟩))
      · rw [hshift_eq] at hcov
        exact Finset.mem_union_right _ (Finset.mem_union_left _ ((hZn0 ρ).mpr ⟨hcov, hz⟩))
  have hgap : ∀ ρ ∈ Z_all, 1 / (130 * L_max) ≤ |ρ.im - y| := by
    intro ρ hρ
    have hmem_S : |ρ.im| ∈ S_sym := Finset.mem_image_of_mem _ hρ
    have hf := hfar |ρ.im| hmem_S
    have hpos_S : 0 < 2 * ((S_sym.card : ℝ) + 1) := by
      have : (0 : ℝ) ≤ S_sym.card := Nat.cast_nonneg _
      linarith
    have hden_le : 1 / (130 * L_max) ≤ 1 / (2 * ((S_sym.card : ℝ) + 1)) :=
      one_div_le_one_div_of_le hpos_S (by linarith)
    have hgap0 : 1 / (130 * L_max) ≤ |(|ρ.im| - T')| := hden_le.trans hf
    have hsmall : 1 / (130 * L_max) ≤ 2 := by
      have : (1 : ℝ) ≤ 130 * L_max := by linarith
      exact (div_le_one (by linarith)).mpr this |>.trans (by norm_num)
    rcases hy with hy_eq | hy_eq <;> rw [hy_eq]
    · rcases le_or_gt 0 ρ.im with him | him
      · rwa [abs_of_nonneg him] at hgap0
      · have : 2 ≤ |ρ.im - T'| := by rw [abs_of_neg (by linarith)]; linarith
        exact hsmall.trans this
    · rcases le_or_gt ρ.im 0 with him | him
      · rw [abs_of_nonpos him] at hgap0
        have heq : |ρ.im - -T'| = |-ρ.im - T'| := by
          rw [← abs_neg]; congr 1; ring
        rwa [heq]
      · have : 2 ≤ |ρ.im - -T'| := by rw [abs_of_pos (by linarith)]; linarith
        exact hsmall.trans this
  set s : ℂ := (x : ℂ) + (y : ℂ) * I
  have hs_mem : s ∈ closedBall ((2 : ℂ) + (y : ℂ) * I) (7 / 4) := by
    rw [mem_closedBall, dist_eq_norm]
    have hdiff : s - ((2 : ℂ) + (y : ℂ) * I) = ((x - 2 : ℝ) : ℂ) := by
      dsimp [s]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hs_ne0 : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro h0
    have hs_29 : s ∈ closedBall ((2 : ℂ) + (y : ℂ) * I) (29 / 16) :=
      closedBall_subset_closedBall (by norm_num) hs_mem
    have hs_Zall := hmem_Zall s hs_29 h0
    have hg := hgap s hs_Zall
    have him_s : s.im = y := by simp [s]
    rw [him_s, sub_self, abs_zero] at hg
    have hpos : 0 < 1 / (130 * L_max) := by positivity
    linarith
  refine ⟨hs_ne0, ?_⟩
  obtain ⟨Z₁, hZ₁, _, _, hc1, hder⟩ := local_expansion_LFunction_at_height χ hχ y
  have hmain := hder s hs_mem hs_ne0
  have hLy_le : Real.log (q : ℝ) + Real.log (680 * (|y| + 2)) ≤ L_max := by
    dsimp [L_max]
    have hmono : Real.log (680 * (|y| + 2)) ≤ Real.log (680 * (T + 3)) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hsum_le : ‖∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ ≤
      2080 * L_max ^ 2 := by
    calc ‖∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z₁, ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z₁, (130 * L_max) *
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rcases (hZ₁ ρ).mp hρ with ⟨hρ_ball, hρ_zero⟩
          have hρ_Zall := hmem_Zall ρ hρ_ball hρ_zero
          have hdist : 1 / (130 * L_max) ≤ ‖s - ρ‖ := by
            have h1 := Complex.abs_im_le_norm (s - ρ)
            have him_s : s.im = y := by simp [s]
            rw [sub_im, him_s, abs_sub_comm] at h1
            exact (hgap ρ hρ_Zall).trans h1
          have hpos_d : 0 < 1 / (130 * L_max) := by positivity
          rw [norm_div, Complex.norm_natCast, div_le_iff₀ (lt_of_lt_of_le hpos_d hdist)]
          have hm_nn : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
            Nat.cast_nonneg _
          have hmul := mul_le_mul_of_nonneg_left hdist
            (show 0 ≤ (130 * L_max) * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              by positivity)
          have hcancel : ((130 * L_max) *
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) *
                (1 / (130 * L_max)) =
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
            field_simp [(show (0 : ℝ) < L_max by linarith).ne']
          linarith
      _ = (130 * L_max) *
            ∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
          (Finset.mul_sum ..).symm
      _ ≤ (130 * L_max) * (16 * L_max) :=
          mul_le_mul_of_nonneg_left (hc1.trans (by linarith)) (by positivity)
      _ = 2080 * L_max ^ 2 := by ring
  have hmain_sq : 3750 * (Real.log (q : ℝ) + Real.log (680 * (|y| + 2))) ≤ 625 * L_max ^ 2 := by
    nlinarith [hLy_le, hL_ge6]
  have htri := norm_add_le
    (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
      ∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
    (∑ ρ ∈ Z₁, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
  rw [sub_add_cancel] at htri
  nlinarith

/-- Under `RiemannZetaZerosOnLine`, for every `T ≥ 2` there exists a symmetric good horizontal shift
height `T' ∈ [T, T + 1]` on which `riemannZeta (x ± T' * I) ≠ 0` and
`‖ζ'/ζ(x ± T' * I)‖ ≤ 3000 * log(1440 * (T + 3)^2) ^ 2` across all `x ∈ [1 / 4, 3 / 2]`. -/
theorem exists_good_shift_height_zeta
    (hRH : CitedPremises.RiemannZetaZerosOnLine) {T : ℝ} (hT : 2 ≤ T) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      ∀ (x y : ℝ), 1 / 4 ≤ x → x ≤ 3 / 2 → (y = T' ∨ y = -T') →
        riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 ∧
          ‖deriv riemannZeta ((x : ℂ) + (y : ℂ) * I) /
              riemannZeta ((x : ℂ) + (y : ℂ) * I)‖ ≤
            3000 * Real.log (1440 * (T + 3) ^ 2) ^ 2 := by
  classical
  obtain ⟨Z_p0, hZp0, hmp0, _, hcp0, _⟩ := local_expansion_zeta_at_height T
  obtain ⟨Z_p1, hZp1, hmp1, _, hcp1, _⟩ := local_expansion_zeta_at_height (T + 1)
  obtain ⟨Z_n0, hZn0, hmn0, _, hcn0, _⟩ := local_expansion_zeta_at_height (-T)
  obtain ⟨Z_n1, hZn1, hmn1, _, hcn1, _⟩ := local_expansion_zeta_at_height (-(T + 1))
  let L_max : ℝ := Real.log (1440 * (T + 3) ^ 2)
  have hL_ge7 : 7 ≤ L_max := by
    have h1440 : Real.exp 7 ≤ 1440 * (T + 3) ^ 2 := by
      have he1 := Real.exp_one_lt_d9
      have he7 : Real.exp 7 = (Real.exp 1) ^ (7 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [he7]
      have hp : (Real.exp 1) ^ (7 : ℕ) ≤ (2.72 : ℝ) ^ (7 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 7
      norm_num at hp
      nlinarith
    exact (Real.le_log_iff_exp_le (by positivity)).mpr h1440
  have hcard_le : ∀ (Z : Finset ℂ) (η : ℝ), |η| ≤ T + 1 →
      (∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt riemannZeta ρ) →
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        16 * Real.log (1440 * (|η| + 2) ^ 2) →
      (Z.card : ℝ) ≤ 16 * L_max := by
    intro Z η hη hm hc
    have h1 : (Z.card : ℝ) ≤ ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact Finset.sum_le_sum fun ρ hρ => by exact_mod_cast hm ρ hρ
    have hsq : (|η| + 2) ^ 2 ≤ (T + 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hlog_mono : Real.log (1440 * (|η| + 2) ^ 2) ≤ L_max :=
      Real.log_le_log (by positivity) (by nlinarith)
    linarith
  let Z_all : Finset ℂ := (Z_p0 ∪ Z_p1) ∪ (Z_n0 ∪ Z_n1)
  let S_sym : Finset ℝ := Z_all.image (fun ρ => |ρ.im|)
  have hS_card : (S_sym.card : ℝ) + 1 ≤ 65 * L_max := by
    have hc_img : S_sym.card ≤ Z_all.card := Finset.card_image_le
    have hc_u : Z_all.card ≤ Z_p0.card + Z_p1.card + Z_n0.card + Z_n1.card := by
      have u1 := Finset.card_union_le (Z_p0 ∪ Z_p1) (Z_n0 ∪ Z_n1)
      have u2 := Finset.card_union_le Z_p0 Z_p1
      have u3 := Finset.card_union_le Z_n0 Z_n1
      dsimp [Z_all] at u1 ⊢; lia
    have h1 : (S_sym.card : ℝ) ≤
        (Z_p0.card : ℝ) + (Z_p1.card : ℝ) + (Z_n0.card : ℝ) + (Z_n1.card : ℝ) := by
      exact_mod_cast hc_img.trans hc_u
    have b0 := hcard_le Z_p0 T (by rw [abs_of_nonneg (by linarith)]; linarith) hmp0 hcp0
    have b1 := hcard_le Z_p1 (T + 1) (by rw [abs_of_nonneg (by linarith)]) hmp1 hcp1
    have bn0 := hcard_le Z_n0 (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)]; linarith) hmn0 hcn0
    have bn1 := hcard_le Z_n1 (-(T + 1)) (by rw [abs_neg, abs_of_nonneg (by linarith)]) hmn1 hcn1
    linarith
  obtain ⟨T', hT1, hT2, hfar⟩ := exists_far_from_finset S_sym T
  refine ⟨T', hT1, hT2, fun x y hx1 hx2 hy => ?_⟩
  have hy_abs : |y| = T' := by
    rcases hy with rfl | rfl
    · exact abs_of_nonneg (by linarith)
    · rw [abs_neg, abs_of_nonneg (by linarith)]
  have hnot_triv : ∀ z : ℂ, 0 < z.re → ¬∃ n : ℕ, z = -2 * ((n : ℂ) + 1) := by
    intro z hz ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcrit_of_ball : ∀ (η : ℝ) (ρ : ℂ),
      ρ ∈ closedBall ((2 : ℂ) + (η : ℂ) * I) (29 / 16) →
      ρ ≠ 1 → riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
    intro η ρ hb hne1 hz
    have hre_pos : 0 < ρ.re := by
      have h1 := (Complex.abs_re_le_norm (ρ - ((2 : ℂ) + (η : ℂ) * I))).trans
        (by simpa [mem_closedBall, dist_eq_norm] using hb)
      rw [sub_re, abs_le] at h1; simp at h1; linarith
    exact hRH ρ hz (hnot_triv ρ hre_pos) hne1
  have hmem_Zall : ∀ ρ : ℂ, ρ ∈ closedBall ((2 : ℂ) + (y : ℂ) * I) (29 / 16) →
      ρ ≠ 1 → riemannZeta ρ = 0 → ρ ∈ Z_all := by
    intro ρ hb hne1 hz
    have hhalf := hcrit_of_ball y ρ hb hne1 hz
    rcases hy with rfl | rfl
    · rcases closedBall_cover_of_crit_zero hT1 hT2 hhalf hb with hcov | hcov
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((hZp0 ρ).mpr ⟨hcov, hne1, hz⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((hZp1 ρ).mpr ⟨hcov, hne1, hz⟩))
    · have hcov_neg := closedBall_cover_of_crit_zero (y₀ := -(T + 1)) (y := -T')
        (by linarith) (by linarith) hhalf hb
      have hshift_eq : ((-(T + 1) + 1 : ℝ) : ℂ) = ((-T : ℝ) : ℂ) := by push_cast; ring
      rcases hcov_neg with hcov | hcov
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ ((hZn1 ρ).mpr ⟨hcov, hne1, hz⟩))
      · rw [hshift_eq] at hcov
        exact Finset.mem_union_right _ (Finset.mem_union_left _ ((hZn0 ρ).mpr ⟨hcov, hne1, hz⟩))
  have hgap : ∀ ρ ∈ Z_all, 1 / (130 * L_max) ≤ |ρ.im - y| := by
    intro ρ hρ
    have hmem_S : |ρ.im| ∈ S_sym := Finset.mem_image_of_mem _ hρ
    have hf := hfar |ρ.im| hmem_S
    have hpos_S : 0 < 2 * ((S_sym.card : ℝ) + 1) := by
      have : (0 : ℝ) ≤ S_sym.card := Nat.cast_nonneg _
      linarith
    have hden_le : 1 / (130 * L_max) ≤ 1 / (2 * ((S_sym.card : ℝ) + 1)) :=
      one_div_le_one_div_of_le hpos_S (by linarith)
    have hgap0 : 1 / (130 * L_max) ≤ |(|ρ.im| - T')| := hden_le.trans hf
    have hsmall : 1 / (130 * L_max) ≤ 2 := by
      have : (1 : ℝ) ≤ 130 * L_max := by linarith
      exact (div_le_one (by linarith)).mpr this |>.trans (by norm_num)
    rcases hy with hy_eq | hy_eq <;> rw [hy_eq]
    · rcases le_or_gt 0 ρ.im with him | him
      · rwa [abs_of_nonneg him] at hgap0
      · have : 2 ≤ |ρ.im - T'| := by rw [abs_of_neg (by linarith)]; linarith
        exact hsmall.trans this
    · rcases le_or_gt ρ.im 0 with him | him
      · rw [abs_of_nonpos him] at hgap0
        have heq : |ρ.im - -T'| = |-ρ.im - T'| := by
          rw [← abs_neg]; congr 1; ring
        rwa [heq]
      · have : 2 ≤ |ρ.im - -T'| := by rw [abs_of_pos (by linarith)]; linarith
        exact hsmall.trans this
  set s : ℂ := (x : ℂ) + (y : ℂ) * I
  have hs_ne1 : s ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    simp [s] at him
    rw [him, abs_zero] at hy_abs
    linarith
  have hs_mem : s ∈ closedBall ((2 : ℂ) + (y : ℂ) * I) (7 / 4) := by
    rw [mem_closedBall, dist_eq_norm]
    have hdiff : s - ((2 : ℂ) + (y : ℂ) * I) = ((x - 2 : ℝ) : ℂ) := by
      dsimp [s]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hs_ne0 : riemannZeta s ≠ 0 := by
    intro h0
    have hs_29 : s ∈ closedBall ((2 : ℂ) + (y : ℂ) * I) (29 / 16) :=
      closedBall_subset_closedBall (by norm_num) hs_mem
    have hs_Zall := hmem_Zall s hs_29 hs_ne1 h0
    have hg := hgap s hs_Zall
    have him_s : s.im = y := by simp [s]
    rw [him_s, sub_self, abs_zero] at hg
    have hpos : 0 < 1 / (130 * L_max) := by positivity
    linarith
  refine ⟨hs_ne0, ?_⟩
  obtain ⟨Z₁, hZ₁, _, _, hc1, hder⟩ := local_expansion_zeta_at_height y
  have hmain := hder s hs_mem hs_ne1 hs_ne0
  have hLy_le : Real.log (1440 * (|y| + 2) ^ 2) ≤ L_max := by
    dsimp [L_max]
    have hsq : (|y| + 2) ^ 2 ≤ (T + 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hsum_le : ‖∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
      2080 * L_max ^ 2 := by
    calc ‖∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z₁, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z₁, (130 * L_max) * (analyticOrderNatAt riemannZeta ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rcases (hZ₁ ρ).mp hρ with ⟨hρ_ball, hρ_ne1, hρ_zero⟩
          have hρ_Zall := hmem_Zall ρ hρ_ball hρ_ne1 hρ_zero
          have hdist : 1 / (130 * L_max) ≤ ‖s - ρ‖ := by
            have h1 := Complex.abs_im_le_norm (s - ρ)
            have him_s : s.im = y := by simp [s]
            rw [sub_im, him_s, abs_sub_comm] at h1
            exact (hgap ρ hρ_Zall).trans h1
          have hpos_d : 0 < 1 / (130 * L_max) := by positivity
          rw [norm_div, Complex.norm_natCast, div_le_iff₀ (lt_of_lt_of_le hpos_d hdist)]
          have hmul := mul_le_mul_of_nonneg_left hdist
            (show 0 ≤ (130 * L_max) * (analyticOrderNatAt riemannZeta ρ : ℝ) by positivity)
          have hcancel : ((130 * L_max) * (analyticOrderNatAt riemannZeta ρ : ℝ)) *
                (1 / (130 * L_max)) =
              (analyticOrderNatAt riemannZeta ρ : ℝ) := by
            field_simp [(show (0 : ℝ) < L_max by linarith).ne']
          linarith
      _ = (130 * L_max) * ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℝ) :=
          (Finset.mul_sum ..).symm
      _ ≤ (130 * L_max) * (16 * L_max) :=
          mul_le_mul_of_nonneg_left (hc1.trans (by linarith)) (by positivity)
      _ = 2080 * L_max ^ 2 := by ring
  have hpole_le : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / 2 := by
    have h1 : 2 ≤ ‖s - 1‖ := by
      have him := Complex.abs_im_le_norm (s - 1)
      have him_s : s.im = y := by simp [s]
      rw [sub_im, him_s, one_im, sub_zero, hy_abs] at him
      linarith
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) h1
  have hsplit : deriv riemannZeta s / riemannZeta s =
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)) +
        (∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)) - 1 / (s - 1) := by ring
  rw [hsplit]
  have htri1 := norm_sub_le
    ((deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
        ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)) +
      (∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)))
    (1 / (s - 1))
  have htri2 := norm_add_le
    (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
      ∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
    (∑ ρ ∈ Z₁, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
  nlinarith [hLy_le, hL_ge7]

end ConcreteStripAndHeights

end
end BuchstabSwitchingK2.SmoothExplicitFormula
