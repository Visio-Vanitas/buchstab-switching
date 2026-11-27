import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import BuchstabSwitchingK2.External.SmoothExplicitFormula.MellinDirichletIdentity
import BuchstabSwitchingK2.External.SmoothExplicitFormula.RectangleResidueMultiplicity
import BuchstabSwitchingK2.External.SmoothExplicitFormula.RightHalfPlaneLandau

/-!
# End-to-End Complex-Analytic Proof of `SmoothExplicitFormulaLiteraturePremise` (`1 + 2`)

Eliminates `SmoothExplicitFormulaLiteraturePremise` as an external literature assumption for
`polySplineKernel` (`δ = 1 / 25`, `∫_0^1 Φ = 1`, `Φ_max = 875 / 368`) by proving in Lean `v4.36.0`
(zero `sorry`, zero custom `axiom`, zero `native_decide`):

1. `polySplineKernel_principalSmoothPNT`:
   `CitedPremises.PrincipalSmoothPNTPremise polySplineKernel 1 46935000`
2. `polySplineKernel_primitiveSmoothEF`:
   `CitedPremises.PrimitiveSmoothExplicitFormulaPremise polySplineKernel 1 688 37805000`
3. `polySplineKernel_smoothExplicitFormula`:
   `CitedPremises.SmoothExplicitFormulaLiteraturePremise polySplineKernel 1 688 84741000`

via right-half-plane contour shifting (`σ₀ = 3 / 2 → σ₁ = 1 / 4 > 0`) on `[1 / 4, 3 / 2] × [-T_M, T_M]`
along symmetric good horizontal heights `T_M ∈ [M, M + 1]`, single-disk Blaschke + Borel–Carathéodory
strip zero-density bounds, 2-fold and 3-fold integration-by-parts Mellin decay, and passage to the
limit `M → ∞`.
-/

namespace BuchstabSwitchingK2.SmoothExplicitFormula

open Complex Set Filter Topology Metric MeasureTheory ArithmeticFunction
open scoped BigOperators LSeries.notation

noncomputable section

/-! ### Part 1: Elementary Logarithmic, Power, Finset & Mellin Decay Helpers -/

private lemma log_680_le_ten : Real.log 680 ≤ 10 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (680 : ℝ) ≤ Real.exp 10 := by
    have hpow : (680 : ℝ) ≤ (Real.exp 1) ^ (10 : ℕ) :=
      le_trans (by norm_num : (680 : ℝ) ≤ 2 ^ 10) (pow_le_pow_left₀ (by norm_num) h2 10)
    rwa [← Real.exp_nat_mul, show (10 : ℕ) * (1 : ℝ) = 10 by norm_num] at hpow
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr hp

private lemma log_1440_le_eleven : Real.log 1440 ≤ 11 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (1440 : ℝ) ≤ Real.exp 11 := by
    have hpow : (1440 : ℝ) ≤ (Real.exp 1) ^ (11 : ℕ) :=
      le_trans (by norm_num : (1440 : ℝ) ≤ 2 ^ 11) (pow_le_pow_left₀ (by norm_num) h2 11)
    rwa [← Real.exp_nat_mul, show (11 : ℕ) * (1 : ℝ) = 11 by norm_num] at hpow
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr hp

private lemma log_680_height_le (t : ℝ) :
    Real.log (680 * (|t| + 2)) ≤ |t| + 11 := by
  rw [Real.log_mul (by norm_num) (by positivity)]
  have h1 : Real.log (|t| + 2) ≤ |t| + 1 := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < |t| + 2 by positivity)]
  linarith [log_680_le_ten]

private lemma log_1440_height_sq_le (t : ℝ) :
    Real.log (1440 * (|t| + 2) ^ 2) ≤ 2 * |t| + 13 := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h1 : Real.log (|t| + 2) ≤ |t| + 1 := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < |t| + 2 by positivity)]
  norm_num
  linarith [log_1440_le_eleven]

private lemma norm_mellinPolySpline_le_div_sq {σ y : ℝ} (hσ : 0 < σ) (hy : y ≠ 0) :
    ‖mellinPolySpline ((σ : ℂ) + (y : ℂ) * I)‖ ≤ 63 / y ^ 2 := by
  set s : ℂ := (σ : ℂ) + (y : ℂ) * I
  have hs : 0 < s.re := by simp [s, hσ]
  have hy_pos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have h0 : |y| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
  have h1 : |y| ≤ ‖s + 1‖ := by simpa [s] using Complex.abs_im_le_norm (s + 1)
  have hprod : y ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, ← sq_abs]
    nlinarith [abs_nonneg y]
  rw [le_div_iff₀ hy_pos]
  calc ‖mellinPolySpline s‖ * y ^ 2
      ≤ ‖mellinPolySpline s‖ * ‖s * (s + 1)‖ :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖s * (s + 1) * mellinPolySpline s‖ := by rw [mul_comm, ← norm_mul]
    _ ≤ 63 := norm_mul_two_mellinPolySpline_le hs

private lemma norm_mellinPolySpline_le_div_cube {σ y : ℝ} (hσ : 0 < σ) (hy : y ≠ 0) :
    ‖mellinPolySpline ((σ : ℂ) + (y : ℂ) * I)‖ ≤ 1621 / |y| ^ 3 := by
  set s : ℂ := (σ : ℂ) + (y : ℂ) * I
  have hs : 0 < s.re := by simp [s, hσ]
  have hy_abs : 0 < |y| := abs_pos.mpr hy
  have hy3 : 0 < |y| ^ 3 := pow_pos hy_abs 3
  have h0 : |y| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
  have h1 : |y| ≤ ‖s + 1‖ := by simpa [s] using Complex.abs_im_le_norm (s + 1)
  have h2 : |y| ≤ ‖s + 2‖ := by simpa [s] using Complex.abs_im_le_norm (s + 2)
  have hprod12 : |y| ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    nlinarith [hy_abs.le]
  have hprod : |y| ^ 3 ≤ ‖s * (s + 1) * (s + 2)‖ := by
    rw [norm_mul]
    calc |y| ^ 3 = |y| ^ 2 * |y| := by ring
      _ ≤ ‖s * (s + 1)‖ * ‖s + 2‖ :=
        mul_le_mul hprod12 h2 hy_abs.le (norm_nonneg _)
  rw [le_div_iff₀ hy3]
  calc ‖mellinPolySpline s‖ * |y| ^ 3
      ≤ ‖mellinPolySpline s‖ * ‖s * (s + 1) * (s + 2)‖ :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖s * (s + 1) * (s + 2) * mellinPolySpline s‖ := by rw [mul_comm, ← norm_mul]
    _ ≤ 1621 := norm_mul_three_mellinPolySpline_le hs

private lemma rpow_quarter_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    x ^ (1 / 4 : ℝ) ≤ Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

private lemma rpow_quarter_mul_log_le_two_sqrt {x : ℝ} {q : ℕ} [NeZero q]
    (hx : 1 ≤ x) (hq : (q : ℝ) ≤ Real.sqrt x) :
    x ^ (1 / 4 : ℝ) * Real.log (q : ℝ) ≤ 2 * Real.sqrt x := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hx4_pos : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx_pos _
  have hlog_le : Real.log (q : ℝ) ≤ 2 * x ^ (1 / 4 : ℝ) := by
    have h1 : Real.log (q : ℝ) ≤ Real.log (Real.sqrt x) :=
      Real.log_le_log hq_pos hq
    have hsqrt_eq : Real.sqrt x = (x ^ (1 / 4 : ℝ)) ^ (2 : ℕ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
      norm_num
    rw [hsqrt_eq, Real.log_pow] at h1
    have h2 : Real.log (x ^ (1 / 4 : ℝ)) ≤ x ^ (1 / 4 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hx4_pos
    norm_num at h1
    linarith
  have hsq : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = Real.sqrt x := by
    rw [← Real.rpow_add hx_pos, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  calc x ^ (1 / 4 : ℝ) * Real.log (q : ℝ)
      ≤ x ^ (1 / 4 : ℝ) * (2 * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_le hx4_pos.le
    _ = 2 * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by ring
    _ = 2 * Real.sqrt x := by rw [hsq]

private lemma inv_two_pi_le_quarter : 1 / (2 * Real.pi) ≤ (1 / 4 : ℝ) := by
  have hpi := Real.two_le_pi
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

private lemma sum_union_le_real {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ (∑ x ∈ s₁, f x) + ∑ x ∈ s₂, f x := by
  induction s₁ using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.insert_union, Finset.sum_insert ha]
    by_cases ha2 : a ∈ s ∪ s₂
    · rw [Finset.insert_eq_of_mem ha2]
      linarith [hf a]
    · rw [Finset.sum_insert ha2]
      linarith

private lemma sum_biUnion_le_real {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    linarith [sum_union_le_real (t a) (s.biUnion t) f hf]

private lemma sum_range_inv_sq_from_two_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / ((k + 2 : ℕ) : ℝ) ^ 2) ≤ 3 / 4 := by
  let g : ℕ → ℝ := fun k =>
    if k = 0 then 1 / 4 else 1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)
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
        field_simp; push_cast; ring
      rw [hsub]
      refine one_div_le_one_div_of_le (mul_pos h1 h2) ?_
      push_cast; nlinarith
  refine (Finset.sum_le_sum fun k _ => hle k).trans ?_
  rcases eq_or_ne K 0 with rfl | hK0
  · simp; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by lia⟩
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos m)]
    have hIco : ∑ k ∈ Finset.Ico 1 (m + 1), g k =
        ∑ j ∈ Finset.range m, (1 / ((j + 2 : ℕ) : ℝ) - 1 / ((j + 1 + 2 : ℕ) : ℝ)) := by
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
    have hnn : 0 ≤ 1 / (((m + 2 : ℕ) : ℝ)) := by positivity
    push_cast at hnn ⊢
    linarith

/-! ### Part 2: Holomorphic Weight `mellinPolySpline s * x ^ s` & `Re(s) = 3 / 2` Integrability -/

private def weightPoly (x : ℝ) (s : ℂ) : ℂ :=
  mellinPolySpline s * (x : ℂ) ^ s

private lemma differentiable_weightPoly {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (weightPoly x) := by
  intro s
  exact (differentiable_mellinPolySpline s).fun_mul
    (differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne')))

private lemma analyticAt_weightPoly {x : ℝ} (hx : 0 < x) (p : ℂ) :
    AnalyticAt ℂ (weightPoly x) p :=
  (differentiable_weightPoly hx).differentiableOn.analyticOnNhd isOpen_univ p (Set.mem_univ p)

private lemma norm_weightPoly {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖weightPoly x s‖ = ‖mellinPolySpline s‖ * x ^ s.re := by
  rw [weightPoly, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

private lemma weightPoly_one (x : ℝ) : weightPoly x 1 = (x : ℂ) := by
  rw [weightPoly, mellinPolySpline_one, one_mul, cpow_one]

private lemma integrable_LSeries_weightPoly (a : ℕ → ℂ) (hsum : LSeriesSummable a (3 / 2 : ℂ))
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ =>
      LSeries a ((3 / 2 : ℂ) + (y : ℂ) * I) * weightPoly x ((3 / 2 : ℂ) + (y : ℂ) * I)) := by
  let sLine : ℝ → ℂ := fun y => (3 / 2 : ℂ) + (y : ℂ) * I
  have hs_cont : Continuous sLine :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hsum_norm : Summable (fun n : ℕ => ‖LSeries.term a (3 / 2 : ℂ) n‖) := hsum.norm
  have hterm_norm : ∀ (n : ℕ) (y : ℝ),
      ‖LSeries.term a (sLine y) n‖ = ‖LSeries.term a (3 / 2 : ℂ) n‖ := by
    intro n y
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · simp only [LSeries.term_of_ne_zero hn0, norm_div]
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
      simp [sLine]
  have hL_cont : Continuous (fun y : ℝ => LSeries a (sLine y)) := by
    refine continuous_tsum (fun n => ?_) hsum_norm (fun n y => (hterm_norm n y).le)
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]; exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn0]
      refine continuous_const.div (hs_cont.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn0))) fun y => ?_
      rw [Ne, cpow_eq_zero_iff, not_and_or, Nat.cast_eq_zero]
      exact Or.inl hn0
  have hw_cont : Continuous (fun y : ℝ => weightPoly x (sLine y)) :=
    (differentiable_weightPoly hx).continuous.comp hs_cont
  have hvi : Integrable (fun y : ℝ => ‖mellinPolySpline (sLine y)‖) := by
    have h1 := (verticalIntegrable_mellin_of_admissible polySplineKernel_admissible
      (show (0 : ℝ) < 3 / 2 by norm_num)).norm
    convert h1 using 1
    ext y
    have heq : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = sLine y := by push_cast; rfl
    rw [heq]; rfl
  let C : ℝ := ∑' n : ℕ, ‖LSeries.term a (3 / 2 : ℂ) n‖
  refine Integrable.mono' ((hvi.const_mul (C * x ^ (3 / 2 : ℝ))))
    (hL_cont.mul hw_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hL_le : ‖LSeries a (sLine y)‖ ≤ C := by
    have hs_y : Summable (fun n : ℕ => ‖LSeries.term a (sLine y) n‖) := by
      simpa only [hterm_norm] using hsum_norm
    calc ‖LSeries a (sLine y)‖ ≤ ∑' n : ℕ, ‖LSeries.term a (sLine y) n‖ :=
          norm_tsum_le_tsum_norm hs_y
      _ = C := by simp_rw [hterm_norm]; rfl
  rw [norm_mul, norm_weightPoly hx]
  have hre : (sLine y).re = 3 / 2 := by simp [sLine]
  rw [hre]
  calc ‖LSeries a (sLine y)‖ * (‖mellinPolySpline (sLine y)‖ * x ^ (3 / 2 : ℝ))
      ≤ C * (‖mellinPolySpline (sLine y)‖ * x ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hL_le (by positivity)
    _ = (C * x ^ (3 / 2 : ℝ)) * ‖mellinPolySpline (sLine y)‖ := by ring

/-! ### Part 3: Unit-Strip Critical-Line Zero Covering & Residue Helpers -/

private lemma mem_closedBall_strip_of_crit_zero {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ρ ∈ closedBall ((2 : ℂ) + (((Int.floor ρ.im : ℝ) + 1 / 2 : ℝ) : ℂ) * I) (13 / 8) := by
  set η : ℝ := (Int.floor ρ.im : ℝ) + 1 / 2
  have hlo : (Int.floor ρ.im : ℝ) ≤ ρ.im := Int.floor_le ρ.im
  have hhi : ρ.im ≤ (Int.floor ρ.im : ℝ) + 1 := (Int.lt_floor_add_one ρ.im).le
  have heq : Complex.normSq (ρ - ((2 : ℂ) + (η : ℂ) * I)) = (ρ.re - 2) ^ 2 + (ρ.im - η) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [sub_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, sub_im, add_im, im_ofNat, mul_im, zero_add]
    ring
  rw [mem_closedBall, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (by norm_num),
    Complex.sq_norm, heq, hre]
  have him_sq : (ρ.im - η) ^ 2 ≤ (1 / 2) ^ 2 := by
    dsimp only [η]
    nlinarith
  nlinarith

private lemma floor_im_mem_Icc {γ T' : ℝ} {M : ℕ} (hT2 : T' ≤ (M : ℝ) + 1)
    (hlo : -T' < γ) (hhi : γ < T') :
    Int.floor γ ∈ Finset.Icc (-(M : ℤ) - 1) (M : ℤ) := by
  rw [Finset.mem_Icc]
  constructor
  · by_contra hlt
    push Not at hlt
    have hle : Int.floor γ + 1 ≤ -(M : ℤ) - 1 := by lia
    have hreal : (Int.floor γ : ℝ) + 1 ≤ -(M : ℝ) - 1 := by exact_mod_cast hle
    linarith [Int.lt_floor_add_one γ]
  · by_contra hgt
    push Not at hgt
    have hge : (M : ℤ) + 1 ≤ Int.floor γ := by lia
    have hreal : (M : ℝ) + 1 ≤ (Int.floor γ : ℝ) := by exact_mod_cast hge
    linarith [Int.floor_le γ]

private lemma sum_Icc_int_split {M : ℕ} (hM : 2 ≤ M) (g : ℤ → ℝ) (_hg_nn : ∀ n : ℤ, 0 ≤ g n) :
    ∑ n ∈ Finset.Icc (-(M : ℤ) - 1) (M : ℤ), g n ≤
      (g (-2) + g (-1) + g 0 + g 1) +
        (∑ k ∈ Finset.range (M - 1), g ((k + 2 : ℕ) : ℤ)) +
        (∑ k ∈ Finset.range (M - 1), g (-((k + 3 : ℕ) : ℤ))) := by
  set K : ℕ := M - 1
  have h1M : 1 ≤ M := by linarith
  have h1K : 1 ≤ K := Nat.le_sub_of_add_le hM
  have hMK : M = K + 1 := (Nat.sub_add_cancel h1M).symm
  have hMz : (M : ℤ) = (K : ℤ) + 1 := by exact_mod_cast hMK
  let idx : ℕ → ℤ := fun m => (m : ℤ) - ((K : ℤ) + 2)
  have hbij : ∑ m ∈ Finset.range ((K + 4) + K), g (idx m) =
      ∑ n ∈ Finset.Icc (-(M : ℤ) - 1) (M : ℤ), g n := by
    refine Finset.sum_bij (fun m _ => idx m) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro m hm
      have hmlt : (m : ℤ) < (((K + 4) + K : ℕ) : ℤ) := by
        exact_mod_cast Finset.mem_range.mp hm
      have hm0 : (0 : ℤ) ≤ (m : ℤ) := Nat.cast_nonneg m
      rw [Finset.mem_Icc]
      dsimp only [idx]
      push_cast at hmlt
      constructor <;> linarith
    · intro m₁ _ m₂ _ heq
      dsimp only [idx] at heq
      exact Nat.cast_injective (R := ℤ) (by linarith)
    · intro n hn
      rw [Finset.mem_Icc] at hn
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n + ((K : ℤ) + 2) by linarith)
      have hmlt_z : (m : ℤ) < (((K + 4) + K : ℕ) : ℤ) := by push_cast; linarith
      have hmlt : m < (K + 4) + K := by exact_mod_cast hmlt_z
      exact ⟨m, Finset.mem_range.mpr hmlt, by dsimp only [idx]; linarith⟩
  rw [← hbij, Finset.sum_range_add, Finset.sum_range_add]
  have hmid : ∑ j ∈ Finset.range 4, g (idx (K + j)) = g (-2) + g (-1) + g 0 + g 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 : idx (K + 0) = -2 := by dsimp only [idx]; push_cast; ring
    have e1 : idx (K + 1) = -1 := by dsimp only [idx]; push_cast; ring
    have e2 : idx (K + 2) = 0 := by dsimp only [idx]; push_cast; ring
    have e3 : idx (K + 3) = 1 := by dsimp only [idx]; push_cast; ring
    rw [e0, e1, e2, e3]
  have hpos : ∑ k ∈ Finset.range K, g (idx ((K + 4) + k)) =
      ∑ k ∈ Finset.range K, g ((k + 2 : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; dsimp only [idx]; push_cast; ring
  have hneg : ∑ m ∈ Finset.range K, g (idx m) =
      ∑ k ∈ Finset.range K, g (-((k + 3 : ℕ) : ℤ)) := by
    refine Finset.sum_bij (fun m _ => K - 1 - m) ?_ ?_ ?_ ?_
    · intro m hm
      have hlt := Finset.mem_range.mp hm
      exact Finset.mem_range.mpr (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.sub_lt (lt_of_lt_of_le zero_lt_one h1K) zero_lt_one))
    · intro m₁ hm₁ m₂ hm₂ heq
      have hle₁ := Nat.le_sub_one_of_lt (Finset.mem_range.mp hm₁)
      have hle₂ := Nat.le_sub_one_of_lt (Finset.mem_range.mp hm₂)
      have h1 := congrArg (fun t => K - 1 - t) heq
      simpa only [Nat.sub_sub_self hle₁, Nat.sub_sub_self hle₂] using h1
    · intro k hk
      have hle := Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)
      refine ⟨K - 1 - k, Finset.mem_range.mpr (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.sub_lt (lt_of_lt_of_le zero_lt_one h1K) zero_lt_one)), Nat.sub_sub_self hle⟩
    · intro m hm
      have hle := Nat.le_sub_one_of_lt (Finset.mem_range.mp hm)
      congr 1
      dsimp only [idx]
      push_cast
      rw [Nat.cast_sub hle, Nat.cast_sub h1K, Nat.cast_one]
      ring
  rw [hmid, hpos, hneg]
  linarith

/-! ### Part 4: Modular Zero-Sum, Left-Edge & Horizontal-Edge Bounds -/

private lemma integral_rpow_neg_two_le_one {T' : ℝ} (hT : 2 ≤ T') :
    ∫ y : ℝ in (1 : ℝ)..T', y ^ (-2 : ℝ) ≤ 1 := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) T' := Set.notMem_uIcc_of_lt zero_lt_one (by linarith)
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
  have he : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [he, Real.one_rpow]
  have hpos : 0 ≤ T' ^ (-1 : ℝ) := Real.rpow_nonneg (by linarith) _
  linarith

private lemma intervalIntegral_even_split_bound {g : ℝ → ℝ} {T' C_mid C_tail : ℝ}
    (hT : 2 ≤ T') (hg_cont : Continuous g) (hC_tail_nn : 0 ≤ C_tail)
    (hmid : ∀ y : ℝ, |y| ≤ 1 → g y ≤ C_mid)
    (htail : ∀ y : ℝ, 1 ≤ |y| → g y ≤ C_tail * |y| ^ (-2 : ℝ)) :
    ∫ y : ℝ in -T'..T', g y ≤ 2 * C_mid + 2 * C_tail := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg_cont.intervalIntegrable a b
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (hint (-T') (-1)) (hint (-1) T')
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hint (-1) 1) (hint 1 T')
  rw [← hsplit1, ← hsplit2]
  have hb_mid : ∫ y : ℝ in (-1 : ℝ)..1, g y ≤ 2 * C_mid := by
    have hm := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
      (hint (-1) 1) intervalIntegrable_const fun y hy =>
        hmid y (abs_le.mpr ⟨hy.1, hy.2⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    linarith
  have htail_int : IntervalIntegrable (fun y : ℝ => C_tail * y ^ (-2 : ℝ)) volume 1 T' := by
    refine ((continuousOn_id.rpow_const fun y hy => Or.inl ?_).const_mul C_tail).intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)] at hy
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hy.1)
  have hr := integral_rpow_neg_two_le_one hT
  have hcr : C_tail * ∫ y : ℝ in (1 : ℝ)..T', y ^ (-2 : ℝ) ≤ C_tail := by
    have hm1 := mul_le_mul_of_nonneg_left hr hC_tail_nn
    linarith
  have hb_pos : ∫ y : ℝ in (1 : ℝ)..T', g y ≤ C_tail := by
    have hm := intervalIntegral.integral_mono_on (by linarith : (1 : ℝ) ≤ T')
      (hint 1 T') htail_int fun y hy => by
        have habs : |y| = y := abs_of_pos (lt_of_lt_of_le zero_lt_one hy.1)
        simpa [habs] using htail y (by rw [habs]; exact hy.1)
    rw [intervalIntegral.integral_const_mul] at hm
    exact hm.trans hcr
  have hb_neg : ∫ y : ℝ in -T'..(-1 : ℝ), g y ≤ C_tail := by
    have hcomp : ∫ y : ℝ in -T'..(-1 : ℝ), g y = ∫ y : ℝ in (1 : ℝ)..T', g (-y) := by
      simp
    rw [hcomp]
    have hm := intervalIntegral.integral_mono_on (by linarith : (1 : ℝ) ≤ T')
      ((hg_cont.comp continuous_neg).intervalIntegrable 1 T') htail_int fun y hy => by
        have habs : |-y| = y := by rw [abs_neg, abs_of_pos (lt_of_lt_of_le zero_lt_one hy.1)]
        simpa [habs] using htail (-y) (by rw [habs]; exact hy.1)
    rw [intervalIntegral.integral_const_mul] at hm
    exact hm.trans hcr
  linarith

private lemma left_edge_bound_LFunction {f : ℕ} [NeZero f]
    (ψ : DirichletCharacter ℂ f) (hψ_ne1 : ψ ≠ 1)
    (hLine : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction ψ s = 0 → s.re = 1 / 2)
    {x T' : ℝ} (hx : 1 ≤ x) (hf_sqrt : (f : ℝ) ≤ Real.sqrt x) (hT : 2 ≤ T') :
    ‖(1 / (2 * (Real.pi : ℂ))) *
        ∫ y : ℝ in -T'..T',
          (-(deriv (DirichletCharacter.LFunction ψ) ((1 / 4 : ℂ) + (y : ℂ) * I) /
              DirichletCharacter.LFunction ψ ((1 / 4 : ℂ) + (y : ℂ) * I))) *
            weightPoly x ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
      37700000 * Real.sqrt x := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast NeZero.one_le
  have hlogf_nn : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf1
  let FL : ℂ → ℂ := fun s =>
    (-(deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s)) * weightPoly x s
  let sLine : ℝ → ℂ := fun y => (1 / 4 : ℂ) + (y : ℂ) * I
  have hline_cont : Continuous sLine :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hg_cont : Continuous (fun y : ℝ => ‖FL ((1 / 4 : ℂ) + (y : ℂ) * I)‖) := by
    refine Continuous.norm (continuous_iff_continuousAt.mpr fun y => ?_)
    have hs_ne0 := (norm_logDeriv_LFunction_quarter_le_of_grh ψ hψ_ne1 hLine y).1
    have hanL : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) (sLine y) :=
      (DirichletCharacter.differentiable_LFunction hψ_ne1).differentiableOn.analyticOnNhd
        isOpen_univ (sLine y) (Set.mem_univ _)
    have hd_FL : DifferentiableAt ℂ FL (sLine y) :=
      ((hanL.deriv.differentiableAt.fun_div hanL.differentiableAt hs_ne0).fun_neg).fun_mul
        (differentiable_weightPoly hx_pos (sLine y))
    exact ContinuousAt.comp (g := FL) (f := sLine) hd_FL.continuousAt hline_cont.continuousAt
  have hmid_pt : ∀ y : ℝ, |y| ≤ 1 →
      ‖FL ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
        (45768 * Real.log (f : ℝ) + 549216) * x ^ (1 / 4 : ℝ) := by
    intro y hy
    set s : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I
    have hld := (norm_logDeriv_LFunction_quarter_le_of_grh ψ hψ_ne1 hLine y).2
    have hlog : Real.log (680 * (|y| + 2)) ≤ 12 := by linarith [log_680_height_le y]
    have hm12 : ‖mellinPolySpline s‖ ≤ 12 :=
      norm_mellinPolySpline_of_quarter_le_re (by simp [s])
    dsimp only [FL]
    rw [norm_mul, norm_neg, norm_weightPoly hx_pos, show s.re = 1 / 4 by simp [s]]
    have hp1 : ‖deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s‖ *
        ‖mellinPolySpline s‖ ≤ 45768 * Real.log (f : ℝ) + 549216 := by
      have hld' : ‖deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s‖ ≤
          3814 * (Real.log (f : ℝ) + 12) := by linarith
      calc ‖deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s‖ *
            ‖mellinPolySpline s‖
          ≤ (3814 * (Real.log (f : ℝ) + 12)) * 12 :=
            mul_le_mul hld' hm12 (norm_nonneg _) (by positivity)
        _ = 45768 * Real.log (f : ℝ) + 549216 := by ring
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg hx_pos.le _)
  have htail_pt : ∀ y : ℝ, 1 ≤ |y| →
      ‖FL ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
        ((240282 * Real.log (f : ℝ) + 74189928) * x ^ (1 / 4 : ℝ)) * |y| ^ (-2 : ℝ) := by
    intro y hy
    have hy_ne : y ≠ 0 := fun h0 => by rw [h0, abs_zero] at hy; linarith
    have hy_pos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
    set s : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I
    have hs_eq : s = ((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I := by simp [s]
    have hld := (norm_logDeriv_LFunction_quarter_le_of_grh ψ hψ_ne1 hLine y).2
    have hlog : Real.log (680 * (|y| + 2)) ≤ 12 * |y| := by linarith [log_680_height_le y]
    have hm2 : ‖mellinPolySpline s‖ ≤ 63 / |y| ^ 2 := by
      rw [hs_eq, sq_abs]; exact norm_mellinPolySpline_le_div_sq (by norm_num) hy_ne
    have hm3 : ‖mellinPolySpline s‖ ≤ 1621 / |y| ^ 3 := by
      rw [hs_eq]; exact norm_mellinPolySpline_le_div_cube (by norm_num) hy_ne
    have hld' : ‖deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s‖ ≤
        3814 * Real.log (f : ℝ) + 45768 * |y| := by linarith
    have hprod_min : ‖deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s‖ *
        ‖mellinPolySpline s‖ ≤
        (3814 * Real.log (f : ℝ)) * (63 / |y| ^ 2) + (45768 * |y|) * (1621 / |y| ^ 3) := by
      have b1 := mul_le_mul hld' hm2 (norm_nonneg _) (by positivity)
      have b2 := mul_le_mul hld' hm3 (norm_nonneg _) (by positivity)
      rcases le_total (63 / |y| ^ 2) (1621 / |y| ^ 3) with hle | hle
      · nlinarith [hy_pos]
      · nlinarith [hlogf_nn]
    have hrpow_eq : 1 / |y| ^ 2 = |y| ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hy_pos.le, Real.rpow_two, one_div]
    have halg : (3814 * Real.log (f : ℝ)) * (63 / |y| ^ 2) + (45768 * |y|) * (1621 / |y| ^ 3) =
        (240282 * Real.log (f : ℝ) + 74189928) * |y| ^ (-2 : ℝ) := by
      rw [← hrpow_eq]; field_simp [hy_pos.ne']; ring
    dsimp only [FL]
    rw [norm_mul, norm_neg, norm_weightPoly hx_pos, show s.re = 1 / 4 by simp [s]]
    calc ‖deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s‖ *
          (‖mellinPolySpline s‖ * x ^ (1 / 4 : ℝ))
        = (‖deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s‖ *
            ‖mellinPolySpline s‖) * x ^ (1 / 4 : ℝ) := by ring
      _ ≤ ((240282 * Real.log (f : ℝ) + 74189928) * |y| ^ (-2 : ℝ)) * x ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (hprod_min.trans_eq halg) (by positivity)
      _ = ((240282 * Real.log (f : ℝ) + 74189928) * x ^ (1 / 4 : ℝ)) * |y| ^ (-2 : ℝ) := by ring
  have hint_bd := intervalIntegral_even_split_bound hT hg_cont (by positivity) hmid_pt htail_pt
  have hnorm_v0 : ‖∫ y : ℝ in -T'..T', FL ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
      (572100 * Real.log (f : ℝ) + 149478288) * x ^ (1 / 4 : ℝ) := by
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun y : ℝ =>
      FL ((1 / 4 : ℂ) + (y : ℂ) * I)) (by linarith : -T' ≤ T')
    linarith
  have hpref : ‖(1 / (2 * (Real.pi : ℂ)))‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    exact inv_two_pi_le_quarter
  change ‖(1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FL ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤ _
  rw [norm_mul]
  have h1 := mul_le_mul hpref hnorm_v0 (norm_nonneg _) (by norm_num)
  have h1_rw : (1 / 4 : ℝ) * ((572100 * Real.log (f : ℝ) + 149478288) * x ^ (1 / 4 : ℝ)) =
      143025 * (x ^ (1 / 4 : ℝ) * Real.log (f : ℝ)) + 37369572 * x ^ (1 / 4 : ℝ) := by ring
  have hqx := rpow_quarter_mul_log_le_two_sqrt hx hf_sqrt
  have hx4 := rpow_quarter_le_sqrt hx
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  linarith

private lemma left_edge_bound_zeta (hRH : CitedPremises.RiemannZetaZerosOnLine)
    {x T' : ℝ} (hx : 1 ≤ x) (hT : 2 ≤ T') :
    ‖(1 / (2 * (Real.pi : ℂ))) *
        ∫ y : ℝ in -T'..T',
          (-(deriv riemannZeta ((1 / 4 : ℂ) + (y : ℂ) * I) /
              riemannZeta ((1 / 4 : ℂ) + (y : ℂ) * I))) *
            weightPoly x ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
      46800000 * Real.sqrt x := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let FZ : ℂ → ℂ := fun s => (-(deriv riemannZeta s / riemannZeta s)) * weightPoly x s
  let sLine : ℝ → ℂ := fun y => (1 / 4 : ℂ) + (y : ℂ) * I
  have hline_cont : Continuous sLine :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hg_cont : Continuous (fun y : ℝ => ‖FZ ((1 / 4 : ℂ) + (y : ℂ) * I)‖) := by
    refine Continuous.norm (continuous_iff_continuousAt.mpr fun y => ?_)
    have hs_ne1 : sLine y ≠ 1 := fun h1 => by
      have hre := congrArg Complex.re h1; simp [sLine] at hre
    have hs_ne0 := (norm_logDeriv_zeta_quarter_le_of_grh hRH y).1
    have hanz : AnalyticAt ℂ riemannZeta (sLine y) := analyticOn_riemannZeta (sLine y) hs_ne1
    have hd_FZ : DifferentiableAt ℂ FZ (sLine y) :=
      ((hanz.deriv.differentiableAt.fun_div hanz.differentiableAt hs_ne0).fun_neg).fun_mul
        (differentiable_weightPoly hx_pos (sLine y))
    exact ContinuousAt.comp (g := FZ) (f := sLine) hd_FZ.continuousAt hline_cont.continuousAt
  have hmid_pt : ∀ y : ℝ, |y| ≤ 1 →
      ‖FZ ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤ 686544 * x ^ (1 / 4 : ℝ) := by
    intro y hy
    set s : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I
    have hld := (norm_logDeriv_zeta_quarter_le_of_grh hRH y).2
    have hlog : Real.log (1440 * (|y| + 2) ^ 2) ≤ 15 := by linarith [log_1440_height_sq_le y]
    have hm12 : ‖mellinPolySpline s‖ ≤ 12 :=
      norm_mellinPolySpline_of_quarter_le_re (by simp [s])
    dsimp only [FZ]
    rw [norm_mul, norm_neg, norm_weightPoly hx_pos, show s.re = 1 / 4 by simp [s]]
    have hp1 : ‖deriv riemannZeta s / riemannZeta s‖ * ‖mellinPolySpline s‖ ≤ 686544 := by
      have hld' : ‖deriv riemannZeta s / riemannZeta s‖ ≤ 57212 := by linarith
      calc ‖deriv riemannZeta s / riemannZeta s‖ * ‖mellinPolySpline s‖
          ≤ 57212 * 12 := mul_le_mul hld' hm12 (norm_nonneg _) (by norm_num)
        _ = 686544 := by norm_num
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg hx_pos.le _)
  have htail_pt : ∀ y : ℝ, 1 ≤ |y| →
      ‖FZ ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤ (92740652 * x ^ (1 / 4 : ℝ)) * |y| ^ (-2 : ℝ) := by
    intro y hy
    have hy_ne : y ≠ 0 := fun h0 => by rw [h0, abs_zero] at hy; linarith
    have hy_pos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
    set s : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I
    have hs_eq : s = ((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I := by simp [s]
    have hld := (norm_logDeriv_zeta_quarter_le_of_grh hRH y).2
    have hlog := log_1440_height_sq_le y
    have hld' : ‖deriv riemannZeta s / riemannZeta s‖ ≤ 57212 * |y| := by linarith
    have hm3 : ‖mellinPolySpline s‖ ≤ 1621 / |y| ^ 3 := by
      rw [hs_eq]; exact norm_mellinPolySpline_le_div_cube (by norm_num) hy_ne
    have hrpow_eq : 1 / |y| ^ 2 = |y| ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hy_pos.le, Real.rpow_two, one_div]
    have hprod : ‖deriv riemannZeta s / riemannZeta s‖ * ‖mellinPolySpline s‖ ≤
        92740652 * |y| ^ (-2 : ℝ) := by
      calc ‖deriv riemannZeta s / riemannZeta s‖ * ‖mellinPolySpline s‖
          ≤ (57212 * |y|) * (1621 / |y| ^ 3) :=
            mul_le_mul hld' hm3 (norm_nonneg _) (by positivity)
        _ = 92740652 * (1 / |y| ^ 2) := by field_simp [hy_pos.ne']; ring
        _ = 92740652 * |y| ^ (-2 : ℝ) := by rw [hrpow_eq]
    dsimp only [FZ]
    rw [norm_mul, norm_neg, norm_weightPoly hx_pos, show s.re = 1 / 4 by simp [s]]
    calc ‖deriv riemannZeta s / riemannZeta s‖ * (‖mellinPolySpline s‖ * x ^ (1 / 4 : ℝ))
        = (‖deriv riemannZeta s / riemannZeta s‖ * ‖mellinPolySpline s‖) * x ^ (1 / 4 : ℝ) := by ring
      _ ≤ (92740652 * |y| ^ (-2 : ℝ)) * x ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = (92740652 * x ^ (1 / 4 : ℝ)) * |y| ^ (-2 : ℝ) := by ring
  have hint_bd := intervalIntegral_even_split_bound hT hg_cont (by positivity) hmid_pt htail_pt
  have hnorm_v0 : ‖∫ y : ℝ in -T'..T', FZ ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
      186854392 * x ^ (1 / 4 : ℝ) := by
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun y : ℝ =>
      FZ ((1 / 4 : ℂ) + (y : ℂ) * I)) (by linarith : -T' ≤ T')
    linarith
  have hpref : ‖(1 / (2 * (Real.pi : ℂ)))‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    exact inv_two_pi_le_quarter
  change ‖(1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FZ ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤ _
  rw [norm_mul]
  have h1 := mul_le_mul hpref hnorm_v0 (norm_nonneg _) (by norm_num)
  have hx4 := rpow_quarter_le_sqrt hx
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  linarith

private lemma horiz_diff_bound_of_logDeriv (φ : ℂ → ℂ) (B_log : ℝ) {x T' : ℝ} {M : ℕ}
    (hx : 1 ≤ x) (hM : 2 ≤ M) (hTM1 : (M : ℝ) ≤ T')
    (hhor : ∀ (xr yr : ℝ), 1 / 4 ≤ xr → xr ≤ 3 / 2 → (yr = T' ∨ yr = -T') →
      ‖φ ((xr : ℂ) + (yr : ℂ) * I)‖ ≤ 3000 * B_log ^ 2) :
    ‖(I / (2 * (Real.pi : ℂ))) *
        ((∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2),
            (-φ ((xr : ℂ) + ((-T' : ℝ) : ℂ) * I)) * weightPoly x ((xr : ℂ) + ((-T' : ℝ) : ℂ) * I)) -
          (∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2),
            (-φ ((xr : ℂ) + (T' : ℂ) * I)) * weightPoly x ((xr : ℂ) + (T' : ℂ) * I)))‖ ≤
      ((5 / 4 : ℝ) * 3000 * 1621 * x ^ (3 / 2 : ℝ) / Real.pi) * (B_log ^ 2 / (M : ℝ) ^ 3) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by lia : 0 < M)
  have hT_pos : 0 < T' := lt_of_lt_of_le hM_pos hTM1
  have hside : ∀ yr : ℝ, (yr = T' ∨ yr = -T') →
      ‖∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2),
          (-φ ((xr : ℂ) + (yr : ℂ) * I)) * weightPoly x ((xr : ℂ) + (yr : ℂ) * I)‖ ≤
        ((5 / 4 : ℝ) * 3000 * 1621 * x ^ (3 / 2 : ℝ)) * (B_log ^ 2 / (M : ℝ) ^ 3) := by
    intro yr hyr
    have hyr_abs : |yr| = T' := by
      rcases hyr with rfl | rfl
      · exact abs_of_pos hT_pos
      · rw [abs_neg, abs_of_pos hT_pos]
    have hyr_ne : yr ≠ 0 := fun h0 => by rw [h0, abs_zero] at hyr_abs; linarith
    have hpt : ∀ xr ∈ Set.uIoc (1 / 4 : ℝ) (3 / 2),
        ‖(-φ ((xr : ℂ) + (yr : ℂ) * I)) * weightPoly x ((xr : ℂ) + (yr : ℂ) * I)‖ ≤
          (3000 * 1621 * x ^ (3 / 2 : ℝ)) * (B_log ^ 2 / (M : ℝ) ^ 3) := by
      intro xr hxr
      rw [Set.uIoc_of_le (by norm_num)] at hxr
      have hld := hhor xr yr hxr.1.le hxr.2 hyr
      have hm3 : ‖mellinPolySpline ((xr : ℂ) + (yr : ℂ) * I)‖ ≤ 1621 / (M : ℝ) ^ 3 := by
        refine (norm_mellinPolySpline_le_div_cube (by linarith [hxr.1]) hyr_ne).trans ?_
        rw [hyr_abs]
        exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hM_pos 3)
          (pow_le_pow_left₀ hM_pos.le hTM1 3)
      have hxr_pow : x ^ xr ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hxr.2
      rw [norm_mul, norm_neg, norm_weightPoly hx_pos, show ((xr : ℂ) + (yr : ℂ) * I).re = xr by simp]
      calc ‖φ ((xr : ℂ) + (yr : ℂ) * I)‖ * (‖mellinPolySpline ((xr : ℂ) + (yr : ℂ) * I)‖ * x ^ xr)
          ≤ (3000 * B_log ^ 2) * ((1621 / (M : ℝ) ^ 3) * x ^ (3 / 2 : ℝ)) :=
            mul_le_mul hld (mul_le_mul hm3 hxr_pow (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = (3000 * 1621 * x ^ (3 / 2 : ℝ)) * (B_log ^ 2 / (M : ℝ) ^ 3) := by ring
    calc ‖∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2),
            (-φ ((xr : ℂ) + (yr : ℂ) * I)) * weightPoly x ((xr : ℂ) + (yr : ℂ) * I)‖
        ≤ ((3000 * 1621 * x ^ (3 / 2 : ℝ)) * (B_log ^ 2 / (M : ℝ) ^ 3)) * |(3 / 2 : ℝ) - 1 / 4| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = ((5 / 4 : ℝ) * 3000 * 1621 * x ^ (3 / 2 : ℝ)) * (B_log ^ 2 / (M : ℝ) ^ 3) := by
          norm_num; ring
  have hnI : ‖I / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_I, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hnI]
  have hsub_le := (norm_sub_le _ _).trans
    (add_le_add (hside (-T') (Or.inr rfl)) (hside T' (Or.inl rfl)))
  have hmul := mul_le_mul_of_nonneg_left hsub_le (show 0 ≤ 1 / (2 * Real.pi) by positivity)
  refine hmul.trans_eq ?_
  field_simp [Real.pi_pos.ne']
  ring

private lemma tendsto_quadratic_div_cube_zero (A B : ℝ) :
    Tendsto (fun M : ℕ => (A + B * (M : ℝ)) ^ 2 / (M : ℝ) ^ 3) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfun : (fun M : ℕ => A ^ 2 * ((M : ℝ)⁻¹) ^ 3 + 2 * A * B * ((M : ℝ)⁻¹) ^ 2 + B ^ 2 * (M : ℝ)⁻¹)
      =ᶠ[atTop] (fun M : ℕ => (A + B * (M : ℝ)) ^ 2 / (M : ℝ) ^ 3) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with M hM
    have hM_ne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    field_simp [hM_ne]
    ring
  have ht : Tendsto (fun M : ℕ =>
      A ^ 2 * ((M : ℝ)⁻¹) ^ 3 + 2 * A * B * ((M : ℝ)⁻¹) ^ 2 + B ^ 2 * (M : ℝ)⁻¹) atTop (𝓝 0) := by
    have p1 : Tendsto (fun M : ℕ => A ^ 2 * ((M : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
      simpa using (h1.pow 3).const_mul (A ^ 2)
    have p2 : Tendsto (fun M : ℕ => 2 * A * B * ((M : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using (h1.pow 2).const_mul (2 * A * B)
    have p3 : Tendsto (fun M : ℕ => B ^ 2 * (M : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using h1.const_mul (B ^ 2)
    simpa using (p1.add p2).add p3
  exact ht.congr' hfun

private lemma zero_sum_bound_LFunction {f M : ℕ} [NeZero f]
    (ψ : DirichletCharacter ℂ f)
    {x T' : ℝ} (hx : 0 < x) (hM : 2 ≤ M) (hTM2 : T' ≤ (M : ℝ) + 1)
    (Z_strip : ℤ → Finset ℂ) (S_zeros : Finset ℂ)
    (hZ_mem : ∀ (n : ℤ) (ρ : ℂ),
      ρ ∈ closedBall ((2 : ℂ) + (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * I) (13 / 8) →
      DirichletCharacter.LFunction ψ ρ = 0 → ρ ∈ Z_strip n)
    (hZ_cnt : ∀ n : ℤ,
      (∑ ρ ∈ Z_strip n, (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℝ)) ≤
        6 * (Real.log (f : ℝ) + Real.log (680 * (|(n : ℝ) + 1 / 2| + 2))))
    (hS_info : ∀ p ∈ S_zeros, p.re = 1 / 2 ∧ -T' < p.im ∧ p.im < T' ∧
      DirichletCharacter.LFunction ψ p = 0) :
    ‖∑ p ∈ S_zeros, -((analyticOrderNatAt (DirichletCharacter.LFunction ψ) p : ℂ) * weightPoly x p)‖ ≤
      (688 * Real.log (f : ℝ) + 104000) * Real.sqrt x := by
  classical
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast NeZero.one_le
  have hlogf_nn : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf1
  let ord : ℂ → ℝ := fun p => (analyticOrderNatAt (DirichletCharacter.LFunction ψ) p : ℝ)
  let f_zero : ℂ → ℝ := fun p => ord p * ‖mellinPolySpline p‖
  have hf_nn : ∀ p : ℂ, 0 ≤ f_zero p := fun p => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hbiU_sub : S_zeros ⊆ (Finset.Icc (-(M : ℤ) - 1) (M : ℤ)).biUnion
      (fun n => S_zeros.filter (fun p => Int.floor p.im = n)) := by
    intro p hp
    rcases hS_info p hp with ⟨_, him1, him2, _⟩
    exact Finset.mem_biUnion.mpr ⟨Int.floor p.im, floor_im_mem_Icc hTM2 him1 him2,
      Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  let g_strip : ℤ → ℝ := fun n => ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), f_zero p
  have hg_nn : ∀ n : ℤ, 0 ≤ g_strip n := fun n => Finset.sum_nonneg fun p _ => hf_nn p
  have hsum_strips : ∑ p ∈ S_zeros, f_zero p ≤
      ∑ n ∈ Finset.Icc (-(M : ℤ) - 1) (M : ℤ), g_strip n :=
    (Finset.sum_le_sum_of_subset_of_nonneg hbiU_sub fun p _ _ => hf_nn p).trans
      (sum_biUnion_le_real _ _ f_zero hf_nn)
  have hsub_Z : ∀ n : ℤ, S_zeros.filter (fun p => Int.floor p.im = n) ⊆ Z_strip n := by
    intro n p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hfl⟩
    rcases hS_info p hpS with ⟨hhalf, _, _, hz⟩
    rw [← hfl]
    exact hZ_mem _ p (mem_closedBall_strip_of_crit_zero hhalf) hz
  have hg_mid : ∀ n : ℤ, |(n : ℝ) + 1 / 2| ≤ 3 / 2 →
      g_strip n ≤ 30 * Real.log (f : ℝ) + 375 := by
    intro n hn_abs
    have h1 : g_strip n ≤ ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), 5 * ord p := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpS := (Finset.mem_filter.mp hp).1
      have hpeq : p = (1 / 2 : ℂ) + (p.im : ℂ) * I := by
        have h := Complex.re_add_im p; rw [(hS_info p hpS).1] at h; simpa using h.symm
      have hm5 : ‖mellinPolySpline p‖ ≤ 5 := by rw [hpeq]; exact norm_mellinPolySpline_crit_le p.im
      dsimp only [f_zero]
      have ho_nn : 0 ≤ ord p := Nat.cast_nonneg _
      nlinarith
    have h2 : ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), 5 * ord p ≤
        5 * ∑ p ∈ Z_strip n, ord p := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (hsub_Z n) fun _ _ _ => Nat.cast_nonneg _)
        (by norm_num)
    have h3 : ∑ p ∈ Z_strip n, ord p ≤
        6 * (Real.log (f : ℝ) + Real.log (680 * (|(n : ℝ) + 1 / 2| + 2))) := hZ_cnt n
    have hlog_le : Real.log (680 * (|(n : ℝ) + 1 / 2| + 2)) ≤ 25 / 2 := by
      linarith [log_680_height_le ((n : ℝ) + 1 / 2)]
    linarith
  have hg_tail : ∀ (n : ℤ) (k : ℕ),
      (n = ((k + 2 : ℕ) : ℤ) ∨ n = -((k + 3 : ℕ) : ℤ)) →
      g_strip n ≤ (378 * Real.log (f : ℝ) + 68082) * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := by
    intro n k hnk
    set mR : ℝ := ((k + 2 : ℕ) : ℝ)
    have hm2 : 2 ≤ mR := by dsimp [mR]; exact_mod_cast Nat.le_add_left 2 k
    have hm_pos : 0 < mR := by linarith
    have htc_abs : |(n : ℝ) + 1 / 2| = mR + 1 / 2 := by
      rcases hnk with hnk_eq | hnk_eq
      · have heq : (n : ℝ) + 1 / 2 = mR + 1 / 2 := by rw [hnk_eq]; dsimp [mR]; push_cast; ring
        rw [heq, abs_of_pos (by linarith)]
      · have heq : (n : ℝ) + 1 / 2 = -(mR + 1 / 2) := by rw [hnk_eq]; dsimp [mR]; push_cast; ring
        rw [heq, abs_neg, abs_of_pos (by linarith)]
    have hpt_mellin : ∀ p ∈ S_zeros.filter (fun p => Int.floor p.im = n),
        ‖mellinPolySpline p‖ ≤ 63 / mR ^ 2 ∧ ‖mellinPolySpline p‖ ≤ 1621 / mR ^ 3 := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hfl⟩
      have hm_le_im : mR ≤ |p.im| := by
        have hlo : (n : ℝ) ≤ p.im := hfl ▸ Int.floor_le p.im
        have hhi : p.im < (n : ℝ) + 1 := hfl ▸ Int.lt_floor_add_one p.im
        rcases hnk with hnk_eq | hnk_eq
        · have hlo' : mR ≤ p.im := by rw [hnk_eq] at hlo; dsimp [mR]; exact_mod_cast hlo
          exact hlo'.trans (le_abs_self p.im)
        · have hhi' : p.im < -mR := by
            rw [hnk_eq] at hhi; dsimp [mR] at hhi ⊢; push_cast at hhi ⊢; linarith
          rw [abs_of_neg (by linarith)]; linarith
      have hp_im_ne : p.im ≠ 0 := fun h0 => by rw [h0, abs_zero] at hm_le_im; linarith
      have hpeq : p = ((1 / 2 : ℝ) : ℂ) + (p.im : ℂ) * I := by
        have h := Complex.re_add_im p; rw [(hS_info p hpS).1] at h; push_cast; simpa using h.symm
      rw [hpeq]
      refine ⟨(norm_mellinPolySpline_le_div_sq (by norm_num) hp_im_ne).trans ?_,
        (norm_mellinPolySpline_le_div_cube (by norm_num) hp_im_ne).trans ?_⟩
      · rw [← sq_abs]
        exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hm_pos 2)
          (pow_le_pow_left₀ hm_pos.le hm_le_im 2)
      · exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hm_pos 3)
          (pow_le_pow_left₀ hm_pos.le hm_le_im 3)
    have hcnt : ∑ p ∈ Z_strip n, ord p ≤
        6 * (Real.log (f : ℝ) + Real.log (680 * (|(n : ℝ) + 1 / 2| + 2))) := hZ_cnt n
    have hlog_lin : Real.log (680 * (|(n : ℝ) + 1 / 2| + 2)) ≤ 7 * mR := by
      have h1 := log_680_height_le ((n : ℝ) + 1 / 2)
      linarith [h1, htc_abs, hm2]
    have hcnt' : (∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p) ≤
        6 * Real.log (f : ℝ) + 42 * mR := by
      have hs_le : (∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p) ≤
          ∑ p ∈ Z_strip n, ord p :=
        Finset.sum_le_sum_of_subset_of_nonneg (hsub_Z n) fun _ _ _ => Nat.cast_nonneg _
      linarith
    have hb63 : g_strip n ≤ (63 / mR ^ 2) * (6 * Real.log (f : ℝ) + 42 * mR) := by
      calc g_strip n ≤ ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p * (63 / mR ^ 2) :=
          Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (hpt_mellin p hp).1 (Nat.cast_nonneg _)
        _ = (63 / mR ^ 2) * ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p := by
            rw [← Finset.sum_mul, mul_comm]
        _ ≤ (63 / mR ^ 2) * (6 * Real.log (f : ℝ) + 42 * mR) :=
            mul_le_mul_of_nonneg_left hcnt' (by positivity)
    have hb1621 : g_strip n ≤ (1621 / mR ^ 3) * (6 * Real.log (f : ℝ) + 42 * mR) := by
      calc g_strip n ≤ ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p * (1621 / mR ^ 3) :=
          Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (hpt_mellin p hp).2 (Nat.cast_nonneg _)
        _ = (1621 / mR ^ 3) * ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p := by
            rw [← Finset.sum_mul, mul_comm]
        _ ≤ (1621 / mR ^ 3) * (6 * Real.log (f : ℝ) + 42 * mR) :=
            mul_le_mul_of_nonneg_left hcnt' (by positivity)
    have hmin_trick : g_strip n ≤
        (63 / mR ^ 2) * (6 * Real.log (f : ℝ)) + (1621 / mR ^ 3) * (42 * mR) := by
      rcases le_total (63 / mR ^ 2) (1621 / mR ^ 3) with hle | hle
      · nlinarith [hm_pos]
      · nlinarith [hlogf_nn]
    have hsimp_rhs : (63 / mR ^ 2) * (6 * Real.log (f : ℝ)) + (1621 / mR ^ 3) * (42 * mR) =
        (378 * Real.log (f : ℝ) + 68082) * (1 / mR ^ 2) := by
      field_simp [hm_pos.ne']; ring
    linarith
  have hsplit := sum_Icc_int_split hM g_strip hg_nn
  have hm_n2 := hg_mid (-2) (by norm_num)
  have hm_n1 := hg_mid (-1) (by norm_num)
  have hm_0 := hg_mid 0 (by norm_num)
  have hm_1 := hg_mid 1 (by norm_num)
  have hpos_sum : ∑ k ∈ Finset.range (M - 1), g_strip ((k + 2 : ℕ) : ℤ) ≤
      284 * Real.log (f : ℝ) + 51062 := by
    calc ∑ k ∈ Finset.range (M - 1), g_strip ((k + 2 : ℕ) : ℤ)
        ≤ ∑ k ∈ Finset.range (M - 1),
            (378 * Real.log (f : ℝ) + 68082) * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun k _ => hg_tail _ k (Or.inl rfl)
      _ = (378 * Real.log (f : ℝ) + 68082) *
            ∑ k ∈ Finset.range (M - 1), (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := (Finset.mul_sum ..).symm
      _ ≤ (378 * Real.log (f : ℝ) + 68082) * (3 / 4) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_from_two_le _) (by positivity)
      _ ≤ 284 * Real.log (f : ℝ) + 51062 := by linarith
  have hneg_sum : ∑ k ∈ Finset.range (M - 1), g_strip (-((k + 3 : ℕ) : ℤ)) ≤
      284 * Real.log (f : ℝ) + 51062 := by
    calc ∑ k ∈ Finset.range (M - 1), g_strip (-((k + 3 : ℕ) : ℤ))
        ≤ ∑ k ∈ Finset.range (M - 1),
            (378 * Real.log (f : ℝ) + 68082) * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun k _ => hg_tail _ k (Or.inr rfl)
      _ = (378 * Real.log (f : ℝ) + 68082) *
            ∑ k ∈ Finset.range (M - 1), (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := (Finset.mul_sum ..).symm
      _ ≤ (378 * Real.log (f : ℝ) + 68082) * (3 / 4) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_from_two_le _) (by positivity)
      _ ≤ 284 * Real.log (f : ℝ) + 51062 := by linarith
  have htot_f : ∑ p ∈ S_zeros, f_zero p ≤ 688 * Real.log (f : ℝ) + 104000 := by linarith
  calc ‖∑ p ∈ S_zeros, -((analyticOrderNatAt (DirichletCharacter.LFunction ψ) p : ℂ) * weightPoly x p)‖
      ≤ ∑ p ∈ S_zeros, ‖-((analyticOrderNatAt (DirichletCharacter.LFunction ψ) p : ℂ) * weightPoly x p)‖ :=
        norm_sum_le _ _
    _ = (∑ p ∈ S_zeros, f_zero p) * Real.sqrt x := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [norm_neg, norm_mul, Complex.norm_natCast, norm_weightPoly hx,
          (hS_info p hp).1, ← Real.sqrt_eq_rpow]
        dsimp only [f_zero, ord]; ring
    _ ≤ (688 * Real.log (f : ℝ) + 104000) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right htot_f (Real.sqrt_nonneg x)

private lemma zero_sum_bound_zeta {M : ℕ}
    {x T' : ℝ} (hx : 0 < x) (hM : 2 ≤ M) (hTM2 : T' ≤ (M : ℝ) + 1)
    (Z_strip : ℤ → Finset ℂ) (S_zeros : Finset ℂ)
    (hZ_mem : ∀ (n : ℤ) (ρ : ℂ),
      ρ ∈ closedBall ((2 : ℂ) + (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * I) (13 / 8) →
      ρ ≠ 1 → riemannZeta ρ = 0 → ρ ∈ Z_strip n)
    (hZ_cnt : ∀ n : ℤ,
      (∑ ρ ∈ Z_strip n, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        6 * Real.log (1440 * (|(n : ℝ) + 1 / 2| + 2) ^ 2))
    (hS_info : ∀ p ∈ S_zeros, p.re = 1 / 2 ∧ -T' < p.im ∧ p.im < T' ∧
      p ≠ 1 ∧ riemannZeta p = 0) :
    ‖∑ p ∈ S_zeros, -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p)‖ ≤
      134000 * Real.sqrt x := by
  classical
  let ord : ℂ → ℝ := fun p => (analyticOrderNatAt riemannZeta p : ℝ)
  let f_zero : ℂ → ℝ := fun p => ord p * ‖mellinPolySpline p‖
  have hf_nn : ∀ p : ℂ, 0 ≤ f_zero p := fun p => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hbiU_sub : S_zeros ⊆ (Finset.Icc (-(M : ℤ) - 1) (M : ℤ)).biUnion
      (fun n => S_zeros.filter (fun p => Int.floor p.im = n)) := by
    intro p hp
    rcases hS_info p hp with ⟨_, him1, him2, _, _⟩
    exact Finset.mem_biUnion.mpr ⟨Int.floor p.im, floor_im_mem_Icc hTM2 him1 him2,
      Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  let g_strip : ℤ → ℝ := fun n => ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), f_zero p
  have hg_nn : ∀ n : ℤ, 0 ≤ g_strip n := fun n => Finset.sum_nonneg fun p _ => hf_nn p
  have hsum_strips : ∑ p ∈ S_zeros, f_zero p ≤
      ∑ n ∈ Finset.Icc (-(M : ℤ) - 1) (M : ℤ), g_strip n :=
    (Finset.sum_le_sum_of_subset_of_nonneg hbiU_sub fun p _ _ => hf_nn p).trans
      (sum_biUnion_le_real _ _ f_zero hf_nn)
  have hsub_Z : ∀ n : ℤ, S_zeros.filter (fun p => Int.floor p.im = n) ⊆ Z_strip n := by
    intro n p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hfl⟩
    rcases hS_info p hpS with ⟨hhalf, _, _, hne1, hz⟩
    rw [← hfl]
    exact hZ_mem _ p (mem_closedBall_strip_of_crit_zero hhalf) hne1 hz
  have hg_mid : ∀ n : ℤ, |(n : ℝ) + 1 / 2| ≤ 3 / 2 → g_strip n ≤ 480 := by
    intro n hn_abs
    have h1 : g_strip n ≤ ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), 5 * ord p := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpS := (Finset.mem_filter.mp hp).1
      have hpeq : p = (1 / 2 : ℂ) + (p.im : ℂ) * I := by
        have h := Complex.re_add_im p; rw [(hS_info p hpS).1] at h; simpa using h.symm
      have hm5 : ‖mellinPolySpline p‖ ≤ 5 := by rw [hpeq]; exact norm_mellinPolySpline_crit_le p.im
      dsimp only [f_zero]
      have ho_nn : 0 ≤ ord p := Nat.cast_nonneg _
      nlinarith
    have h2 : ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), 5 * ord p ≤
        5 * ∑ p ∈ Z_strip n, ord p := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (hsub_Z n) fun _ _ _ => Nat.cast_nonneg _)
        (by norm_num)
    have h3 : ∑ p ∈ Z_strip n, ord p ≤
        6 * Real.log (1440 * (|(n : ℝ) + 1 / 2| + 2) ^ 2) := hZ_cnt n
    have hlog_le : Real.log (1440 * (|(n : ℝ) + 1 / 2| + 2) ^ 2) ≤ 16 := by
      linarith [log_1440_height_sq_le ((n : ℝ) + 1 / 2)]
    linarith
  have hg_tail : ∀ (n : ℤ) (k : ℕ),
      (n = ((k + 2 : ℕ) : ℤ) ∨ n = -((k + 3 : ℕ) : ℤ)) →
      g_strip n ≤ 87534 * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := by
    intro n k hnk
    set mR : ℝ := ((k + 2 : ℕ) : ℝ)
    have hm2 : 2 ≤ mR := by dsimp [mR]; exact_mod_cast Nat.le_add_left 2 k
    have hm_pos : 0 < mR := by linarith
    have htc_abs : |(n : ℝ) + 1 / 2| = mR + 1 / 2 := by
      rcases hnk with hnk_eq | hnk_eq
      · have heq : (n : ℝ) + 1 / 2 = mR + 1 / 2 := by rw [hnk_eq]; dsimp [mR]; push_cast; ring
        rw [heq, abs_of_pos (by linarith)]
      · have heq : (n : ℝ) + 1 / 2 = -(mR + 1 / 2) := by rw [hnk_eq]; dsimp [mR]; push_cast; ring
        rw [heq, abs_neg, abs_of_pos (by linarith)]
    have hpt_m3 : ∀ p ∈ S_zeros.filter (fun p => Int.floor p.im = n),
        ‖mellinPolySpline p‖ ≤ 1621 / mR ^ 3 := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hfl⟩
      have hm_le_im : mR ≤ |p.im| := by
        have hlo : (n : ℝ) ≤ p.im := hfl ▸ Int.floor_le p.im
        have hhi : p.im < (n : ℝ) + 1 := hfl ▸ Int.lt_floor_add_one p.im
        rcases hnk with hnk_eq | hnk_eq
        · have hlo' : mR ≤ p.im := by rw [hnk_eq] at hlo; dsimp [mR]; exact_mod_cast hlo
          exact hlo'.trans (le_abs_self p.im)
        · have hhi' : p.im < -mR := by
            rw [hnk_eq] at hhi; dsimp [mR] at hhi ⊢; push_cast at hhi ⊢; linarith
          rw [abs_of_neg (by linarith)]; linarith
      have hp_im_ne : p.im ≠ 0 := fun h0 => by rw [h0, abs_zero] at hm_le_im; linarith
      have hpeq : p = ((1 / 2 : ℝ) : ℂ) + (p.im : ℂ) * I := by
        have h := Complex.re_add_im p; rw [(hS_info p hpS).1] at h; push_cast; simpa using h.symm
      rw [hpeq]
      refine (norm_mellinPolySpline_le_div_cube (by norm_num) hp_im_ne).trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hm_pos 3)
        (pow_le_pow_left₀ hm_pos.le hm_le_im 3)
    have hcnt : ∑ p ∈ Z_strip n, ord p ≤
        6 * Real.log (1440 * (|(n : ℝ) + 1 / 2| + 2) ^ 2) := hZ_cnt n
    have hlog_lin : Real.log (1440 * (|(n : ℝ) + 1 / 2| + 2) ^ 2) ≤ 9 * mR := by
      have h1 := log_1440_height_sq_le ((n : ℝ) + 1 / 2)
      linarith [h1, htc_abs, hm2]
    have hcnt' : (∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p) ≤ 54 * mR := by
      have hs_le : (∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p) ≤
          ∑ p ∈ Z_strip n, ord p :=
        Finset.sum_le_sum_of_subset_of_nonneg (hsub_Z n) fun _ _ _ => Nat.cast_nonneg _
      linarith
    calc g_strip n ≤ ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p * (1621 / mR ^ 3) :=
        Finset.sum_le_sum fun p hp =>
          mul_le_mul_of_nonneg_left (hpt_m3 p hp) (Nat.cast_nonneg _)
      _ = (1621 / mR ^ 3) * ∑ p ∈ S_zeros.filter (fun p => Int.floor p.im = n), ord p := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (1621 / mR ^ 3) * (54 * mR) :=
          mul_le_mul_of_nonneg_left hcnt' (by positivity)
      _ = 87534 * (1 / mR ^ 2) := by field_simp [hm_pos.ne']; ring
  have hsplit := sum_Icc_int_split hM g_strip hg_nn
  have hm_n2 := hg_mid (-2) (by norm_num)
  have hm_n1 := hg_mid (-1) (by norm_num)
  have hm_0 := hg_mid 0 (by norm_num)
  have hm_1 := hg_mid 1 (by norm_num)
  have hpos_sum : ∑ k ∈ Finset.range (M - 1), g_strip ((k + 2 : ℕ) : ℤ) ≤ 65651 := by
    calc ∑ k ∈ Finset.range (M - 1), g_strip ((k + 2 : ℕ) : ℤ)
        ≤ ∑ k ∈ Finset.range (M - 1), 87534 * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun k _ => hg_tail _ k (Or.inl rfl)
      _ = 87534 * ∑ k ∈ Finset.range (M - 1), (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := (Finset.mul_sum ..).symm
      _ ≤ 87534 * (3 / 4) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_from_two_le _) (by norm_num)
      _ ≤ 65651 := by norm_num
  have hneg_sum : ∑ k ∈ Finset.range (M - 1), g_strip (-((k + 3 : ℕ) : ℤ)) ≤ 65651 := by
    calc ∑ k ∈ Finset.range (M - 1), g_strip (-((k + 3 : ℕ) : ℤ))
        ≤ ∑ k ∈ Finset.range (M - 1), 87534 * (1 / ((k + 2 : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun k _ => hg_tail _ k (Or.inr rfl)
      _ = 87534 * ∑ k ∈ Finset.range (M - 1), (1 / ((k + 2 : ℕ) : ℝ) ^ 2) := (Finset.mul_sum ..).symm
      _ ≤ 87534 * (3 / 4) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_from_two_le _) (by norm_num)
      _ ≤ 65651 := by norm_num
  have htot_f : ∑ p ∈ S_zeros, f_zero p ≤ 134000 := by linarith
  calc ‖∑ p ∈ S_zeros, -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p)‖
      ≤ ∑ p ∈ S_zeros, ‖-((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p)‖ :=
        norm_sum_le _ _
    _ = (∑ p ∈ S_zeros, f_zero p) * Real.sqrt x := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [norm_neg, norm_mul, Complex.norm_natCast, norm_weightPoly hx,
          (hS_info p hp).1, ← Real.sqrt_eq_rpow]
        dsimp only [f_zero, ord]; ring
    _ ≤ 134000 * Real.sqrt x := mul_le_mul_of_nonneg_right htot_f (Real.sqrt_nonneg x)

/-! ### Part 5: Primitive-Character Smooth Explicit Formula Proof -/

/-- Complex-analytic proof of `PrimitiveSmoothExplicitFormulaPremise polySplineKernel 1 688 37805000`
directly from `PrimitiveDirichletLZerosOnLine` (zero external explicit-formula premise). -/
theorem polySplineKernel_primitiveSmoothEF :
    CitedPremises.PrimitiveSmoothExplicitFormulaPremise polySplineKernel 1 688 37805000 := by
  classical
  intro hPrimLine x hx f _ ψ hprim hψ_ne1 hf_sqrt
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast (NeZero.one_le : 1 ≤ f)
  have hlogf_nn : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf1
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hLine : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction ψ s = 0 → s.re = 1 / 2 :=
    fun s hs0 hs1 hz => hPrimLine f ψ hprim s hs0 hs1 hz
  let FL : ℂ → ℂ := fun s =>
    (-(deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s)) * weightPoly x s
  have hpsi_bound : ‖smoothedPsiChar polySplineKernel x ψ‖ ≤
      (688 * Real.log (f : ℝ) + 37804000) * Real.sqrt x := by
    have hgood : ∀ M : ℕ, 2 ≤ M → ∃ T' : ℝ, (M : ℝ) ≤ T' ∧ T' ≤ (M : ℝ) + 1 ∧
        ∀ (xr yr : ℝ), 1 / 4 ≤ xr → xr ≤ 3 / 2 → (yr = T' ∨ yr = -T') →
          DirichletCharacter.LFunction ψ ((xr : ℂ) + (yr : ℂ) * I) ≠ 0 ∧
            ‖deriv (DirichletCharacter.LFunction ψ) ((xr : ℂ) + (yr : ℂ) * I) /
                DirichletCharacter.LFunction ψ ((xr : ℂ) + (yr : ℂ) * I)‖ ≤
              3000 * (Real.log (f : ℝ) + Real.log (680 * ((M : ℝ) + 3))) ^ 2 :=
      fun M hM => exists_good_shift_height_LFunction ψ hψ_ne1 hLine (by exact_mod_cast hM)
    let Tseq : ℕ → ℝ := fun M =>
      if hM : 2 ≤ M then Classical.choose (hgood M hM) else (M : ℝ)
    have hTseq_ge : ∀ M : ℕ, (M : ℝ) ≤ Tseq M := fun M => by
      dsimp only [Tseq]
      split_ifs with hM
      · exact (Classical.choose_spec (hgood M hM)).1
      · exact le_rfl
    have hTseq_top : Tendsto Tseq atTop atTop :=
      tendsto_atTop_mono hTseq_ge tendsto_natCast_atTop_atTop
    have hTseq_bot : Tendsto (fun M : ℕ => -Tseq M) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hTseq_top
    have hFL_int : Integrable (fun y : ℝ => FL ((3 / 2 : ℂ) + (y : ℂ) * I)) := by
      have h1 := integrable_LSeries_weightPoly (↗ψ * ↗Λ)
        (DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ (by norm_num)) hx_pos
      refine h1.congr (Eventually.of_forall fun y => ?_)
      set s : ℂ := (3 / 2 : ℂ) + (y : ℂ) * I
      have hre : 1 < s.re := by simp [s]; norm_num
      have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hre
      rw [← DirichletCharacter.LFunction_eq_LSeries ψ hre,
        ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries ψ hre] at hL
      dsimp only [FL]
      rw [hL, neg_div]
    have htend_V1 : Tendsto (fun M : ℕ =>
        ‖(1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -Tseq M..Tseq M, FL ((3 / 2 : ℂ) + (y : ℂ) * I)‖)
        atTop (𝓝 ‖smoothedPsiChar polySplineKernel x ψ‖) := by
      have hv := smoothedPsiChar_eq_vertical_integral polySplineKernel_admissible ψ hx_pos
      have heq_int : ∫ y : ℝ, FL ((3 / 2 : ℂ) + (y : ℂ) * I) =
          ∫ y : ℝ, (-(deriv (DirichletCharacter.LFunction ψ) ((3 / 2 : ℂ) + (y : ℂ) * I) /
              DirichletCharacter.LFunction ψ ((3 / 2 : ℂ) + (y : ℂ) * I))) *
            mellin (fun t : ℝ => (polySplineKernel t : ℂ)) ((3 / 2 : ℂ) + (y : ℂ) * I) *
            (x : ℂ) ^ ((3 / 2 : ℂ) + (y : ℂ) * I) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only [FL, weightPoly, mellinPolySpline]
        ring
      have ht := ((intervalIntegral_tendsto_integral hFL_int hTseq_bot hTseq_top).const_mul
        (1 / (2 * (Real.pi : ℂ)))).norm
      rwa [heq_int, ← hv] at ht
    let errSeq : ℕ → ℝ := fun M =>
      ((5 / 4 : ℝ) * 3000 * 1621 * x ^ (3 / 2 : ℝ) / Real.pi) *
        (((Real.log (f : ℝ) + 14) + 1 * (M : ℝ)) ^ 2 / (M : ℝ) ^ 3)
    have htend_rhs : Tendsto (fun M : ℕ =>
        (688 * Real.log (f : ℝ) + 37804000) * Real.sqrt x + errSeq M) atTop
        (𝓝 ((688 * Real.log (f : ℝ) + 37804000) * Real.sqrt x)) := by
      simpa [errSeq] using tendsto_const_nhds.add
        ((tendsto_quadratic_div_cube_zero (Real.log (f : ℝ) + 14) 1).const_mul
          ((5 / 4 : ℝ) * 3000 * 1621 * x ^ (3 / 2 : ℝ) / Real.pi))
    refine le_of_tendsto_of_tendsto htend_V1 htend_rhs ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with M hM
    have hspec : (M : ℝ) ≤ Tseq M ∧ Tseq M ≤ (M : ℝ) + 1 ∧
        ∀ (xr yr : ℝ), 1 / 4 ≤ xr → xr ≤ 3 / 2 → (yr = Tseq M ∨ yr = -Tseq M) →
          DirichletCharacter.LFunction ψ ((xr : ℂ) + (yr : ℂ) * I) ≠ 0 ∧
            ‖deriv (DirichletCharacter.LFunction ψ) ((xr : ℂ) + (yr : ℂ) * I) /
                DirichletCharacter.LFunction ψ ((xr : ℂ) + (yr : ℂ) * I)‖ ≤
              3000 * (Real.log (f : ℝ) + Real.log (680 * ((M : ℝ) + 3))) ^ 2 := by
      dsimp only [Tseq]; simp only [hM, ↓reduceDIte]; exact Classical.choose_spec (hgood M hM)
    rcases hspec with ⟨hTM1, hTM2, hTM_hor⟩
    set T' : ℝ := Tseq M
    have hT'_ge2 : 2 ≤ T' := le_trans (by exact_mod_cast hM) hTM1
    let stripSpec := fun n : ℤ => local_expansion_LFunction_at_height ψ hψ_ne1 ((n : ℝ) + 1 / 2)
    let Z_strip : ℤ → Finset ℂ := fun n =>
      (Classical.choose (stripSpec n)).filter
        (fun ρ => ρ ∈ closedBall ((2 : ℂ) + (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * I) (13 / 8))
    have hZ_strip_mem : ∀ (n : ℤ) (ρ : ℂ),
        ρ ∈ closedBall ((2 : ℂ) + (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * I) (13 / 8) →
        DirichletCharacter.LFunction ψ ρ = 0 → ρ ∈ Z_strip n := by
      intro n ρ hb hz
      refine Finset.mem_filter.mpr ⟨?_, hb⟩
      exact ((Classical.choose_spec (stripSpec n)).1 ρ).mpr
        ⟨closedBall_subset_closedBall (by norm_num) hb, hz⟩
    have hZ_strip_cnt : ∀ n : ℤ,
        (∑ ρ ∈ Z_strip n, (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℝ)) ≤
          6 * (Real.log (f : ℝ) + Real.log (680 * (|(n : ℝ) + 1 / 2| + 2))) :=
      fun n => (Classical.choose_spec (stripSpec n)).2.2.1
    let S_zeros : Finset ℂ :=
      ((Finset.Icc (-(M : ℤ) - 1) (M : ℤ)).biUnion Z_strip).filter
        (fun ρ => 1 / 4 < ρ.re ∧ ρ.re < 3 / 2 ∧ -T' < ρ.im ∧ ρ.im < T' ∧
          DirichletCharacter.LFunction ψ ρ = 0)
    have hS_iff : ∀ ρ : ℂ, ρ ∈ S_zeros ↔
        (1 / 4 < ρ.re ∧ ρ.re < 3 / 2 ∧ -T' < ρ.im ∧ ρ.im < T' ∧
          DirichletCharacter.LFunction ψ ρ = 0) := by
      intro ρ
      simp only [S_zeros, Finset.mem_filter]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      rcases h with ⟨hre1, _, him1, him2, hz⟩
      have hre_lt1 : ρ.re < 1 := by
        by_contra hge1
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ_ne1) (not_lt.mp hge1) hz
      have hhalf : ρ.re = 1 / 2 := hLine ρ (by linarith) hre_lt1 hz
      exact Finset.mem_biUnion.mpr ⟨Int.floor ρ.im, floor_im_mem_Icc hTM2 him1 him2,
        hZ_strip_mem (Int.floor ρ.im) ρ (mem_closedBall_strip_of_crit_zero hhalf) hz⟩
    let res : ℂ → ℂ := fun p =>
      -((analyticOrderNatAt (DirichletCharacter.LFunction ψ) p : ℂ) * weightPoly x p)
    have hrect_ne0 : ∀ s ∈ (Set.Icc (1 / 4 : ℝ) (3 / 2) ×ℂ Set.Icc (-T') T') \ (S_zeros : Set ℂ),
        DirichletCharacter.LFunction ψ s ≠ 0 := by
      rintro s ⟨hsR, hsS⟩ h0
      rw [mem_reProdIm, Set.mem_Icc, Set.mem_Icc] at hsR
      rcases hsR with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
      rcases eq_or_lt_of_le hx1 with hxeq1 | hxlt1
      · have hq := (norm_logDeriv_LFunction_quarter_le_of_grh ψ hψ_ne1 hLine s.im).1
        have hs14 : ((1 / 4 : ℂ) + (s.im : ℂ) * I) = s := by
          apply Complex.ext <;> simp [← hxeq1]
        rw [hs14] at hq; exact hq h0
      · rcases eq_or_lt_of_le hx2 with hxeq2 | hxlt2
        · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ_ne1) (by linarith) h0
        · rcases eq_or_lt_of_le hy1 with hyeq1 | hylt1
          · have hh := (hTM_hor s.re (-T') hx1 hx2 (Or.inr rfl)).1
            have hs_bot : ((s.re : ℂ) + ((-T' : ℝ) : ℂ) * I) = s := by
              apply Complex.ext <;> simp [← hyeq1]
            rw [hs_bot] at hh; exact hh h0
          · rcases eq_or_lt_of_le hy2 with hyeq2 | hylt2
            · have hh := (hTM_hor s.re T' hx1 hx2 (Or.inl rfl)).1
              have hs_top : ((s.re : ℂ) + (T' : ℂ) * I) = s := by
                apply Complex.ext <;> simp [hyeq2]
              rw [hs_top] at hh; exact hh h0
            · exact hsS ((hS_iff s).mpr ⟨hxlt1, hxlt2, hylt1, hylt2, h0⟩)
    have hFL_diff : DifferentiableOn ℂ FL
        ((Set.Icc (1 / 4 : ℝ) (3 / 2) ×ℂ Set.Icc (-T') T') \ (S_zeros : Set ℂ)) := by
      intro s hs
      have hne0 := hrect_ne0 s hs
      have hanL : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) s :=
        (DirichletCharacter.differentiable_LFunction hψ_ne1).differentiableOn.analyticOnNhd
          isOpen_univ s (Set.mem_univ s)
      have hd_quot : DifferentiableAt ℂ
          (fun z => -(deriv (DirichletCharacter.LFunction ψ) z / DirichletCharacter.LFunction ψ z)) s :=
        (hanL.deriv.differentiableAt.fun_div hanL.differentiableAt hne0).fun_neg
      exact (hd_quot.fun_mul (differentiable_weightPoly hx_pos s)).differentiableWithinAt
    have hpoles : ∀ p ∈ S_zeros, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
        ∀ᶠ s in 𝓝[≠] p, FL s = res p / (s - p) + g s := by
      intro p hp
      have hp_re : 0 < p.re := by linarith [((hS_iff p).mp hp).1]
      have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hanL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) {z : ℂ | 0 < z.re} :=
        (DirichletCharacter.differentiable_LFunction hψ_ne1).differentiableOn.analyticOnNhd hU
      have hnot_zero : ¬ ∀ᶠ z in 𝓝 p, DirichletCharacter.LFunction ψ z = 0 := by
        intro hev
        have hp_mem : p ∈ {z : ℂ | 0 < z.re} := hp_re
        have h2_mem : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by change (0 : ℝ) < (2 : ℂ).re; norm_num
        have hzero2 := hanL.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_halfSpace_re_gt 0).isPreconnected hp_mem hev h2_mem
        have hlow := quarter_le_norm_LFunction_two_add_im ψ 0
        simp only [ofReal_zero, zero_mul, add_zero] at hlow
        rw [hzero2, Pi.zero_apply, norm_zero] at hlow
        linarith
      obtain ⟨g₀, hg₀, hld⟩ := logDeriv_eq_order_div_add_analytic _ p (hanL p hp_re) hnot_zero
      exact neg_mul_eq_residue_div_add_analytic hg₀ (analyticAt_weightPoly hx_pos p)
        (hld.mono fun _ hs => hs.2)
    have hres_eq := residue_rectangle_simple_poles FL (1 / 4) (3 / 2) (-T') T' S_zeros res
      (by norm_num) (by linarith)
      (fun p hp => by rcases (hS_iff p).mp hp with ⟨h1, h2, h3, h4, _⟩; exact ⟨h1, h2, h3, h4⟩)
      hFL_diff hpoles
    have hshift := contour_vertical_shift_identity (1 / 4) (3 / 2) (-T') T' FL
      (∑ p ∈ S_zeros, res p) hres_eq
    have hR_bound : ‖∑ p ∈ S_zeros, res p‖ ≤ (688 * Real.log (f : ℝ) + 104000) * Real.sqrt x := by
      refine zero_sum_bound_LFunction ψ hx_pos hM hTM2 Z_strip S_zeros hZ_strip_mem hZ_strip_cnt
        fun p hp => ?_
      rcases (hS_iff p).mp hp with ⟨h1, _, him1, him2, hz⟩
      have hlt1 : p.re < 1 := by
        by_contra hge1
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ_ne1) (not_lt.mp hge1) hz
      exact ⟨hLine p (by linarith) hlt1 hz, him1, him2, hz⟩
    have hV0_bound : ‖(1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FL ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
        37700000 * Real.sqrt x := by
      have h := left_edge_bound_LFunction ψ hψ_ne1 hLine hx hf_sqrt hT'_ge2
      simpa only [FL] using h
    have hH_tot : ‖(I / (2 * (Real.pi : ℂ))) *
        ((∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FL ((xr : ℂ) + ((-T' : ℝ) : ℂ) * I)) -
          (∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FL ((xr : ℂ) + (T' : ℂ) * I)))‖ ≤ errSeq M := by
      have hLmax_le : Real.log (f : ℝ) + Real.log (680 * ((M : ℝ) + 3)) ≤
          (Real.log (f : ℝ) + 14) + 1 * (M : ℝ) := by
        have h1 := log_680_height_le ((M : ℝ) + 1)
        rw [abs_of_pos (by exact_mod_cast (by lia : 0 < M + 1))] at h1
        have h2 : (M : ℝ) + 1 + 2 = (M : ℝ) + 3 := by ring
        rw [h2] at h1; linarith
      dsimp only [FL, errSeq]
      refine horiz_diff_bound_of_logDeriv
        (fun s => deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s)
        ((Real.log (f : ℝ) + 14) + 1 * (M : ℝ)) hx hM hTM1 fun xr yr hx1 hx2 hyr => ?_
      have hlog_nn : 0 ≤ Real.log (f : ℝ) + Real.log (680 * ((M : ℝ) + 3)) :=
        add_nonneg hlogf_nn (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M]))
      refine ((hTM_hor xr yr hx1 hx2 hyr).2).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact pow_le_pow_left₀ hlog_nn hLmax_le 2
    have h14_cast : (((1 / 4 : ℝ) : ℂ)) = (1 / 4 : ℂ) := by norm_num
    have h32_cast : (((3 / 2 : ℝ) : ℂ)) = (3 / 2 : ℂ) := by norm_num
    rw [h14_cast, h32_cast] at hshift
    rw [hshift]
    have htri1 := norm_add_le
      ((∑ p ∈ S_zeros, res p) +
        (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FL ((1 / 4 : ℂ) + (y : ℂ) * I))
      ((I / (2 * (Real.pi : ℂ))) *
        ((∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FL ((xr : ℂ) + ((-T' : ℝ) : ℂ) * I)) -
          (∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FL ((xr : ℂ) + (T' : ℂ) * I))))
    have htri2 := norm_add_le (∑ p ∈ S_zeros, res p)
      ((1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FL ((1 / 4 : ℂ) + (y : ℂ) * I))
    linarith
  have hdiff := norm_smoothedThetaChar_sub_psi_le polySplineKernel_nonneg polySplineKernel_le
    (by norm_num) x ψ
  have htri := norm_add_le (smoothedPsiChar polySplineKernel x ψ)
    (CitedPremises.smoothedThetaChar polySplineKernel x ψ - smoothedPsiChar polySplineKernel x ψ)
  rw [add_sub_cancel] at htri
  have h43 : 18 * (875 / 368 : ℝ) ≤ 43 := by norm_num
  nlinarith

/-! ### Part 6: Principal Smooth Prime Number Theorem Proof -/

/-- Complex-analytic proof of `PrincipalSmoothPNTPremise polySplineKernel 1 46935000`
directly from `RiemannZetaZerosOnLine` (zero external explicit-formula premise). -/
theorem polySplineKernel_principalSmoothPNT :
    CitedPremises.PrincipalSmoothPNTPremise polySplineKernel 1 46935000 := by
  classical
  intro hRH x hx
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsqrt_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  let FZ : ℂ → ℂ := fun s => (-(deriv riemannZeta s / riemannZeta s)) * weightPoly x s
  have hpsi_bound : |smoothedPsiAll polySplineKernel x - x| ≤ 46934000 * Real.sqrt x := by
    have hgood : ∀ M : ℕ, 2 ≤ M → ∃ T' : ℝ, (M : ℝ) ≤ T' ∧ T' ≤ (M : ℝ) + 1 ∧
        ∀ (xr yr : ℝ), 1 / 4 ≤ xr → xr ≤ 3 / 2 → (yr = T' ∨ yr = -T') →
          riemannZeta ((xr : ℂ) + (yr : ℂ) * I) ≠ 0 ∧
            ‖deriv riemannZeta ((xr : ℂ) + (yr : ℂ) * I) /
                riemannZeta ((xr : ℂ) + (yr : ℂ) * I)‖ ≤
              3000 * Real.log (1440 * ((M : ℝ) + 3) ^ 2) ^ 2 :=
      fun M hM => exists_good_shift_height_zeta hRH (by exact_mod_cast hM)
    let Tseq : ℕ → ℝ := fun M =>
      if hM : 2 ≤ M then Classical.choose (hgood M hM) else (M : ℝ)
    have hTseq_ge : ∀ M : ℕ, (M : ℝ) ≤ Tseq M := fun M => by
      dsimp only [Tseq]
      split_ifs with hM
      · exact (Classical.choose_spec (hgood M hM)).1
      · exact le_rfl
    have hTseq_top : Tendsto Tseq atTop atTop :=
      tendsto_atTop_mono hTseq_ge tendsto_natCast_atTop_atTop
    have hTseq_bot : Tendsto (fun M : ℕ => -Tseq M) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hTseq_top
    have hFZ_int : Integrable (fun y : ℝ => FZ ((3 / 2 : ℂ) + (y : ℂ) * I)) := by
      have h1 := integrable_LSeries_weightPoly (↗Λ)
        (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)) hx_pos
      refine h1.congr (Eventually.of_forall fun y => ?_)
      have hre : 1 < ((3 / 2 : ℂ) + (y : ℂ) * I).re := by simp; norm_num
      have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
      dsimp only [FZ]
      change LSeries (↗Λ) ((3 / 2 : ℂ) + (y : ℂ) * I) * _ = _
      rw [hL, neg_div]
    have htend_V1 : Tendsto (fun M : ℕ =>
        ‖(1 / (2 * (Real.pi : ℂ))) *
            (∫ y : ℝ in -Tseq M..Tseq M, FZ ((3 / 2 : ℂ) + (y : ℂ) * I)) - (x : ℂ)‖)
        atTop (𝓝 |smoothedPsiAll polySplineKernel x - x|) := by
      have hv := smoothedPsiAll_eq_vertical_integral polySplineKernel_admissible hx_pos
      have heq_int : ∫ y : ℝ, FZ ((3 / 2 : ℂ) + (y : ℂ) * I) =
          ∫ y : ℝ, (-(deriv riemannZeta ((3 / 2 : ℂ) + (y : ℂ) * I) /
              riemannZeta ((3 / 2 : ℂ) + (y : ℂ) * I))) *
            mellin (fun t : ℝ => (polySplineKernel t : ℂ)) ((3 / 2 : ℂ) + (y : ℂ) * I) *
            (x : ℂ) ^ ((3 / 2 : ℂ) + (y : ℂ) * I) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only [FZ, weightPoly, mellinPolySpline]
        ring
      have ht := (((intervalIntegral_tendsto_integral hFZ_int hTseq_bot hTseq_top).const_mul
        (1 / (2 * (Real.pi : ℂ)))).sub_const (x : ℂ)).norm
      rw [heq_int, ← hv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at ht
      exact ht
    let errSeq : ℕ → ℝ := fun M =>
      ((5 / 4 : ℝ) * 3000 * 1621 * x ^ (3 / 2 : ℝ) / Real.pi) *
        ((19 + 2 * (M : ℝ)) ^ 2 / (M : ℝ) ^ 3)
    have htend_rhs : Tendsto (fun M : ℕ => 46934000 * Real.sqrt x + errSeq M) atTop
        (𝓝 (46934000 * Real.sqrt x)) := by
      simpa [errSeq] using tendsto_const_nhds.add
        ((tendsto_quadratic_div_cube_zero 19 2).const_mul
          ((5 / 4 : ℝ) * 3000 * 1621 * x ^ (3 / 2 : ℝ) / Real.pi))
    refine le_of_tendsto_of_tendsto htend_V1 htend_rhs ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with M hM
    have hspec : (M : ℝ) ≤ Tseq M ∧ Tseq M ≤ (M : ℝ) + 1 ∧
        ∀ (xr yr : ℝ), 1 / 4 ≤ xr → xr ≤ 3 / 2 → (yr = Tseq M ∨ yr = -Tseq M) →
          riemannZeta ((xr : ℂ) + (yr : ℂ) * I) ≠ 0 ∧
            ‖deriv riemannZeta ((xr : ℂ) + (yr : ℂ) * I) /
                riemannZeta ((xr : ℂ) + (yr : ℂ) * I)‖ ≤
              3000 * Real.log (1440 * ((M : ℝ) + 3) ^ 2) ^ 2 := by
      dsimp only [Tseq]; simp only [hM, ↓reduceDIte]; exact Classical.choose_spec (hgood M hM)
    rcases hspec with ⟨hTM1, hTM2, hTM_hor⟩
    set T' : ℝ := Tseq M
    have hT'_ge2 : 2 ≤ T' := le_trans (by exact_mod_cast hM) hTM1
    have hnot_triv : ∀ z : ℂ, 0 < z.re → ¬∃ n : ℕ, z = -2 * ((n : ℂ) + 1) := by
      intro z hz ⟨n, hn⟩
      have hre := congrArg Complex.re hn; simp at hre
      linarith [Nat.cast_nonneg (α := ℝ) n]
    let stripSpec := fun n : ℤ => local_expansion_zeta_at_height ((n : ℝ) + 1 / 2)
    let Z_strip : ℤ → Finset ℂ := fun n =>
      (Classical.choose (stripSpec n)).filter
        (fun ρ => ρ ∈ closedBall ((2 : ℂ) + (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * I) (13 / 8))
    have hZ_strip_mem : ∀ (n : ℤ) (ρ : ℂ),
        ρ ∈ closedBall ((2 : ℂ) + (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * I) (13 / 8) →
        ρ ≠ 1 → riemannZeta ρ = 0 → ρ ∈ Z_strip n := by
      intro n ρ hb hne1 hz
      refine Finset.mem_filter.mpr ⟨?_, hb⟩
      exact ((Classical.choose_spec (stripSpec n)).1 ρ).mpr
        ⟨closedBall_subset_closedBall (by norm_num) hb, hne1, hz⟩
    have hZ_strip_cnt : ∀ n : ℤ,
        (∑ ρ ∈ Z_strip n, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
          6 * Real.log (1440 * (|(n : ℝ) + 1 / 2| + 2) ^ 2) :=
      fun n => (Classical.choose_spec (stripSpec n)).2.2.1
    let S_zeros : Finset ℂ :=
      ((Finset.Icc (-(M : ℤ) - 1) (M : ℤ)).biUnion Z_strip).filter
        (fun ρ => 1 / 4 < ρ.re ∧ ρ.re < 3 / 2 ∧ -T' < ρ.im ∧ ρ.im < T' ∧
          ρ ≠ 1 ∧ riemannZeta ρ = 0)
    have hS_iff : ∀ ρ : ℂ, ρ ∈ S_zeros ↔
        (1 / 4 < ρ.re ∧ ρ.re < 3 / 2 ∧ -T' < ρ.im ∧ ρ.im < T' ∧ ρ ≠ 1 ∧ riemannZeta ρ = 0) := by
      intro ρ
      simp only [S_zeros, Finset.mem_filter]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      rcases h with ⟨hre1, _, him1, him2, hne1, hz⟩
      have hhalf : ρ.re = 1 / 2 := hRH ρ hz (hnot_triv ρ (by linarith)) hne1
      exact Finset.mem_biUnion.mpr ⟨Int.floor ρ.im, floor_im_mem_Icc hTM2 him1 him2,
        hZ_strip_mem (Int.floor ρ.im) ρ (mem_closedBall_strip_of_crit_zero hhalf) hne1 hz⟩
    have h1_notMem : (1 : ℂ) ∉ S_zeros := fun h => ((hS_iff 1).mp h).2.2.2.2.1 rfl
    let S_poles : Finset ℂ := insert (1 : ℂ) S_zeros
    let res : ℂ → ℂ := fun p =>
      if p = 1 then (x : ℂ) else -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p)
    have hrect_regular : ∀ s ∈ (Set.Icc (1 / 4 : ℝ) (3 / 2) ×ℂ Set.Icc (-T') T') \ (S_poles : Set ℂ),
        s ≠ 1 ∧ riemannZeta s ≠ 0 := by
      rintro s ⟨hsR, hsP⟩
      have hs1 : s ≠ 1 := fun h1 => hsP (by rw [h1]; exact Finset.mem_insert_self 1 S_zeros)
      refine ⟨hs1, fun h0 => ?_⟩
      have hsZ : s ∉ S_zeros := fun hz => hsP (Finset.mem_insert_of_mem hz)
      rw [mem_reProdIm, Set.mem_Icc, Set.mem_Icc] at hsR
      rcases hsR with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
      rcases eq_or_lt_of_le hx1 with hxeq1 | hxlt1
      · have hq := (norm_logDeriv_zeta_quarter_le_of_grh hRH s.im).1
        have hs14 : ((1 / 4 : ℂ) + (s.im : ℂ) * I) = s := by
          apply Complex.ext <;> simp [← hxeq1]
        rw [hs14] at hq; exact hq h0
      · rcases eq_or_lt_of_le hx2 with hxeq2 | hxlt2
        · exact riemannZeta_ne_zero_of_one_lt_re (by linarith) h0
        · rcases eq_or_lt_of_le hy1 with hyeq1 | hylt1
          · have hh := (hTM_hor s.re (-T') hx1 hx2 (Or.inr rfl)).1
            have hs_bot : ((s.re : ℂ) + ((-T' : ℝ) : ℂ) * I) = s := by
              apply Complex.ext <;> simp [← hyeq1]
            rw [hs_bot] at hh; exact hh h0
          · rcases eq_or_lt_of_le hy2 with hyeq2 | hylt2
            · have hh := (hTM_hor s.re T' hx1 hx2 (Or.inl rfl)).1
              have hs_top : ((s.re : ℂ) + (T' : ℂ) * I) = s := by
                apply Complex.ext <;> simp [hyeq2]
              rw [hs_top] at hh; exact hh h0
            · exact hsZ ((hS_iff s).mpr ⟨hxlt1, hxlt2, hylt1, hylt2, hs1, h0⟩)
    have hFZ_diff : DifferentiableOn ℂ FZ
        ((Set.Icc (1 / 4 : ℝ) (3 / 2) ×ℂ Set.Icc (-T') T') \ (S_poles : Set ℂ)) := by
      intro s hs
      rcases hrect_regular s hs with ⟨hs1, hne0⟩
      have hanz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
      have hd_quot : DifferentiableAt ℂ (fun z => -(deriv riemannZeta z / riemannZeta z)) s :=
        (hanz.deriv.differentiableAt.fun_div hanz.differentiableAt hne0).fun_neg
      exact (hd_quot.fun_mul (differentiable_weightPoly hx_pos s)).differentiableWithinAt
    have hpoles : ∀ p ∈ S_poles, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
        ∀ᶠ s in 𝓝[≠] p, FZ s = res p / (s - p) + g s := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpZ
      · obtain ⟨g₁, hg₁, hpole1⟩ := neg_logDeriv_riemannZeta_near_one
        obtain ⟨G, hG, hev⟩ := pos_mul_eq_residue_div_add_analytic hg₁
          (analyticAt_weightPoly hx_pos 1) hpole1
        refine ⟨G, hG, hev.mono fun s hs => ?_⟩
        dsimp only [FZ, res]; simp only [↓reduceIte]
        rw [one_mul, weightPoly_one] at hs; exact hs
      · have hp_ne1 : p ≠ 1 := ((hS_iff p).mp hpZ).2.2.2.2.1
        have hnot_zero : ¬ ∀ᶠ z in 𝓝 p, riemannZeta z = 0 := by
          intro hev
          have hev1 : riemannZeta₁ =ᶠ[𝓝 p] 0 := by
            filter_upwards [hev, isOpen_ne.mem_nhds hp_ne1] with z hz hz1
            have h1 := riemannZeta_eq_inv_sub_mul hz1
            rw [hz, eq_comm, mul_eq_zero] at h1
            exact h1.resolve_left (inv_ne_zero (sub_ne_zero.mpr hz1))
          have han1 : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
            differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ
          have h01 := han1.eqOn_zero_of_preconnected_of_eventuallyEq_zero
            convex_univ.isPreconnected (Set.mem_univ p) hev1 (Set.mem_univ (1 : ℂ))
          rw [riemannZeta₁_one, Pi.zero_apply] at h01
          exact one_ne_zero h01
        obtain ⟨g₀, hg₀, hld⟩ := logDeriv_eq_order_div_add_analytic _ p
          (analyticOn_riemannZeta p hp_ne1) hnot_zero
        obtain ⟨G, hG, hev⟩ := neg_mul_eq_residue_div_add_analytic hg₀
          (analyticAt_weightPoly hx_pos p) (hld.mono fun _ hs => hs.2)
        refine ⟨G, hG, hev.mono fun s hs => ?_⟩
        dsimp only [FZ, res]; simp only [hp_ne1, ↓reduceIte]; exact hs
    have hres_eq := residue_rectangle_simple_poles FZ (1 / 4) (3 / 2) (-T') T' S_poles res
      (by norm_num) (by linarith)
      (fun p hp => by
        rcases Finset.mem_insert.mp hp with rfl | hpZ
        · simp only [one_re, one_im]; refine ⟨by norm_num, by norm_num, by linarith, by linarith⟩
        · rcases (hS_iff p).mp hpZ with ⟨h1, h2, h3, h4, _, _⟩; exact ⟨h1, h2, h3, h4⟩)
      hFZ_diff hpoles
    have hshift := contour_vertical_shift_identity (1 / 4) (3 / 2) (-T') T' FZ
      (∑ p ∈ S_poles, res p) hres_eq
    have hres_split : ∑ p ∈ S_poles, res p =
        (x : ℂ) + ∑ p ∈ S_zeros, -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p) := by
      dsimp only [S_poles]
      rw [Finset.sum_insert h1_notMem]
      congr 1
      · simp only [res, ↓reduceIte]
      · refine Finset.sum_congr rfl fun p hp => ?_
        have hne1 : p ≠ 1 := ((hS_iff p).mp hp).2.2.2.2.1
        simp only [res, hne1, ↓reduceIte]
    have hR_bound :
        ‖∑ p ∈ S_zeros, -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p)‖ ≤
          134000 * Real.sqrt x := by
      refine zero_sum_bound_zeta hx_pos hM hTM2 Z_strip S_zeros hZ_strip_mem hZ_strip_cnt
        fun p hp => ?_
      rcases (hS_iff p).mp hp with ⟨h1, _, him1, him2, hne1, hz⟩
      exact ⟨hRH p hz (hnot_triv p (by linarith)) hne1, him1, him2, hne1, hz⟩
    have hV0_bound : ‖(1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FZ ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
        46800000 * Real.sqrt x := by
      have h := left_edge_bound_zeta hRH hx hT'_ge2
      simpa only [FZ] using h
    have hH_tot : ‖(I / (2 * (Real.pi : ℂ))) *
        ((∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FZ ((xr : ℂ) + ((-T' : ℝ) : ℂ) * I)) -
          (∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FZ ((xr : ℂ) + (T' : ℂ) * I)))‖ ≤ errSeq M := by
      have hLmax_le : Real.log (1440 * ((M : ℝ) + 3) ^ 2) ≤ 19 + 2 * (M : ℝ) := by
        have h1 := log_1440_height_sq_le ((M : ℝ) + 1)
        rw [abs_of_pos (by exact_mod_cast (by lia : 0 < M + 1))] at h1
        have h2 : (M : ℝ) + 1 + 2 = (M : ℝ) + 3 := by ring
        rw [h2] at h1; linarith
      dsimp only [FZ, errSeq]
      refine horiz_diff_bound_of_logDeriv
        (fun s => deriv riemannZeta s / riemannZeta s)
        (19 + 2 * (M : ℝ)) hx hM hTM1 fun xr yr hx1 hx2 hyr => ?_
      have hlog_nn : 0 ≤ Real.log (1440 * ((M : ℝ) + 3) ^ 2) :=
        Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) M])
      refine ((hTM_hor xr yr hx1 hx2 hyr).2).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      exact pow_le_pow_left₀ hlog_nn hLmax_le 2
    have h14_cast : (((1 / 4 : ℝ) : ℂ)) = (1 / 4 : ℂ) := by norm_num
    have h32_cast : (((3 / 2 : ℝ) : ℂ)) = (3 / 2 : ℂ) := by norm_num
    rw [h14_cast, h32_cast] at hshift
    have hshift_sub :
        (1 / (2 * (Real.pi : ℂ))) * (∫ y : ℝ in -T'..T', FZ ((3 / 2 : ℂ) + (y : ℂ) * I)) - (x : ℂ) =
          (∑ p ∈ S_zeros, -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p)) +
            (1 / (2 * (Real.pi : ℂ))) * (∫ y : ℝ in -T'..T', FZ ((1 / 4 : ℂ) + (y : ℂ) * I)) +
            (I / (2 * (Real.pi : ℂ))) *
              ((∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FZ ((xr : ℂ) + ((-T' : ℝ) : ℂ) * I)) -
                (∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FZ ((xr : ℂ) + (T' : ℂ) * I))) := by
      rw [hshift, hres_split]; ring
    rw [hshift_sub]
    have htri1 := norm_add_le
      ((∑ p ∈ S_zeros, -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p)) +
        (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FZ ((1 / 4 : ℂ) + (y : ℂ) * I))
      ((I / (2 * (Real.pi : ℂ))) *
        ((∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FZ ((xr : ℂ) + ((-T' : ℝ) : ℂ) * I)) -
          (∫ xr : ℝ in (1 / 4 : ℝ)..(3 / 2), FZ ((xr : ℂ) + (T' : ℂ) * I))))
    have htri2 := norm_add_le
      (∑ p ∈ S_zeros, -((analyticOrderNatAt riemannZeta p : ℂ) * weightPoly x p))
      ((1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ in -T'..T', FZ ((1 / 4 : ℂ) + (y : ℂ) * I))
    linarith
  rw [integral_polySplineKernel, one_mul]
  have hdiff := abs_smoothedThetaAll_sub_psi_le polySplineKernel_nonneg polySplineKernel_le
    (by norm_num) x
  have htri : |CitedPremises.smoothedThetaAll polySplineKernel x - x| ≤
      |CitedPremises.smoothedThetaAll polySplineKernel x - smoothedPsiAll polySplineKernel x| +
        |smoothedPsiAll polySplineKernel x - x| :=
    abs_sub_le _ _ _
  have h43 : 18 * (875 / 368 : ℝ) ≤ 43 := by norm_num
  nlinarith

/-! ### Part 7: Full Unconditional Proof of `SmoothExplicitFormulaLiteraturePremise` -/

/-- **Main Theorem (Literature-Premise-Free Smoothed Explicit Formula in Lean `v4.36.0`)**:
`polySplineKernel` unconditionally satisfies `CitedPremises.SmoothExplicitFormulaLiteraturePremise`
with `X₀ = 1`, `κ₁ = 688`, and `κ₀ = 84741000` (deriving smoothed prime-in-AP remainder bounds
solely from `CitedPremises.UpstreamGRHPremise`). -/
theorem polySplineKernel_smoothExplicitFormula :
    CitedPremises.SmoothExplicitFormulaLiteraturePremise polySplineKernel 1 688 84741000 := by
  have hraw := CitedPremises.smoothExplicitFormula_of_primitiveBounds
    (Φ := polySplineKernel) (X₀ := 1) (Φ_max := 875 / 368)
    (κ₁ := 688) (κ_zeta := 46935000) (κ_prim := 37805000)
    le_rfl polySplineKernel_nonneg polySplineKernel_le (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    polySplineKernel_principalSmoothPNT polySplineKernel_primitiveSmoothEF
  intro hGRH x hx d a hd hd_sqrt hcop
  refine (hraw hGRH x hx d a hd hd_sqrt hcop).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg x)
  norm_num

end
end BuchstabSwitchingK2.SmoothExplicitFormula
