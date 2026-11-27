import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import BuchstabSwitchingK2.External.SmoothExplicitFormula.KernelMellinDecay

/-!
# Mellin–Dirichlet Vertical Line Identity & Prime-Power Reduction (`1 + 2`)

Proves in Lean `v4.36.0` (zero `sorry`, zero custom `axiom`):

1. **Prime vs Prime-Power Chebyshev Reduction**:
   - `abs_smoothedThetaAll_sub_psi_le`:
     `|CitedPremises.smoothedThetaAll Φ x - smoothedPsiAll Φ x| ≤ 18 * Φ_max * √x`
   - `norm_smoothedThetaChar_sub_psi_le`:
     `‖CitedPremises.smoothedThetaChar Φ x χ - smoothedPsiChar Φ x χ‖ ≤ 18 * Φ_max * √x`
2. **Exact Vertical Mellin–Dirichlet Integral Representation at `σ = 3 / 2`**:
   - Unified Fubini–Mellin identity `sum_Icc_eq_vertical_integral_LSeries` for any `LSeriesSummable`
     sequence `a : ℕ → ℂ` at `σ = 3 / 2`;
   - Specializations `smoothedPsiAll_eq_vertical_integral` (`-ζ'/ζ`) and
     `smoothedPsiChar_eq_vertical_integral` (`-L'/L`).
-/

namespace BuchstabSwitchingK2.SmoothExplicitFormula

open MeasureTheory Set Filter Complex ArithmeticFunction
open scoped BigOperators Chebyshev LSeries.notation

noncomputable section

/-! ### Part 1: Smoothed von Mangoldt Sums & Prime-Power Reduction -/

/-- Smoothed von Mangoldt sum `∑_{1 ≤ n ≤ ⌊x⌋} Λ(n) Φ(n / x)`. -/
def smoothedPsiAll (Φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n) * Φ ((n : ℝ) / x)

/-- Character-twisted smoothed von Mangoldt sum `∑_{1 ≤ n ≤ ⌊x⌋} Λ(n) Φ(n / x) χ(n)`. -/
def smoothedPsiChar (Φ : ℝ → ℝ) (x : ℝ) {d : ℕ} (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), (((Λ n) * Φ ((n : ℝ) / x) : ℝ) : ℂ) * χ n

private lemma sum_not_prime_vonMangoldt_le (x : ℝ) :
    ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime), Λ n ≤ 18 * Real.sqrt x := by
  rcases lt_or_ge x 1 with hx | hx
  · have hf0 : Nat.floor x = 0 := Nat.floor_eq_zero.mpr hx
    rw [hf0]
    simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.filter_empty, Finset.sum_empty]
    positivity
  · have hset : (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime) =
        (Finset.Ioc 0 (Nat.floor x)).filter (fun n => ¬ n.Prime) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      lia
    rw [hset, ← Chebyshev.psi_sub_theta_eq_sum_not_prime x]
    have hlog4 : Real.log 4 ≤ 2 := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [h4, Real.log_pow]
      have h2 := Real.log_two_lt_d9
      norm_num at h2 ⊢
      linarith
    have hterm : ∀ k : ℕ, 2 ≤ k → Chebyshev.psi (x ^ (1 / (k : ℝ))) ≤ 6 * Real.sqrt x := by
      intro k hk
      have hx0 : 0 ≤ x := by linarith
      have hrp_nn : 0 ≤ x ^ (1 / (k : ℝ)) := Real.rpow_nonneg hx0 _
      have h1 := Chebyshev.psi_le_const_mul_self hrp_nn
      have hexp : x ^ (1 / (k : ℝ)) ≤ Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
        refine Real.rpow_le_rpow_of_exponent_le hx ?_
        have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by lia : 0 < k)
        have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        exact one_div_le_one_div_of_le (by norm_num) hk2
      calc Chebyshev.psi (x ^ (1 / (k : ℝ)))
          ≤ (Real.log 4 + 4) * x ^ (1 / (k : ℝ)) := h1
        _ ≤ 6 * Real.sqrt x := by
            refine mul_le_mul (by linarith) hexp hrp_nn (by norm_num)
    have h2 := hterm 2 le_rfl
    have h3 := hterm 3 (by norm_num)
    have h5 := hterm 5 (by norm_num)
    simp only [one_div, Nat.cast_ofNat] at h2 h3 h5
    linarith [Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x]

private lemma filter_prime_range_eq_Icc (N : ℕ) :
    (Finset.range (N + 1)).filter Nat.Prime = (Finset.Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hlt, hpr⟩
    exact ⟨⟨hpr.pos, Nat.lt_succ_iff.mp hlt⟩, hpr⟩
  · rintro ⟨⟨_, hle⟩, hpr⟩
    exact ⟨Nat.lt_succ_iff.mpr hle, hpr⟩

/-- Replacing primes by prime powers in `smoothedThetaAll` changes it by at most `18 * Φ_max * √x`. -/
theorem abs_smoothedThetaAll_sub_psi_le {Φ : ℝ → ℝ} {Φ_max : ℝ}
    (hΦ_nn : ∀ u : ℝ, 0 ≤ Φ u) (hΦ_ub : ∀ u : ℝ, Φ u ≤ Φ_max) (hΦ_max_nn : 0 ≤ Φ_max)
    (x : ℝ) :
    |CitedPremises.smoothedThetaAll Φ x - smoothedPsiAll Φ x| ≤
      18 * Φ_max * Real.sqrt x := by
  rw [abs_sub_comm]
  unfold smoothedPsiAll CitedPremises.smoothedThetaAll
  rw [filter_prime_range_eq_Icc]
  have hprime_eq :
      ∑ p ∈ (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime, Real.log (p : ℝ) * Φ ((p : ℝ) / x) =
        ∑ p ∈ (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime, (Λ p) * Φ ((p : ℝ) / x) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [hprime_eq]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 (Nat.floor x)) Nat.Prime (fun n => (Λ n) * Φ ((n : ℝ) / x))
  have hdiff :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n) * Φ ((n : ℝ) / x)) -
        (∑ p ∈ (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime, (Λ p) * Φ ((p : ℝ) / x)) =
      ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime),
        (Λ n) * Φ ((n : ℝ) / x) := by linarith
  rw [hdiff, abs_of_nonneg (Finset.sum_nonneg fun n _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hΦ_nn _))]
  calc ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime), (Λ n) * Φ ((n : ℝ) / x)
      ≤ ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime), (Λ n) * Φ_max :=
        Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_left (hΦ_ub _) ArithmeticFunction.vonMangoldt_nonneg
    _ = Φ_max * ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime), Λ n := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ Φ_max * (18 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (sum_not_prime_vonMangoldt_le x) hΦ_max_nn
    _ = 18 * Φ_max * Real.sqrt x := by ring

/-- Replacing primes by prime powers in `smoothedThetaChar` changes it by at most `18 * Φ_max * √x`. -/
theorem norm_smoothedThetaChar_sub_psi_le {Φ : ℝ → ℝ} {Φ_max : ℝ}
    (hΦ_nn : ∀ u : ℝ, 0 ≤ Φ u) (hΦ_ub : ∀ u : ℝ, Φ u ≤ Φ_max) (hΦ_max_nn : 0 ≤ Φ_max)
    (x : ℝ) {d : ℕ} (χ : DirichletCharacter ℂ d) :
    ‖CitedPremises.smoothedThetaChar Φ x χ - smoothedPsiChar Φ x χ‖ ≤
      18 * Φ_max * Real.sqrt x := by
  rw [norm_sub_rev]
  unfold smoothedPsiChar CitedPremises.smoothedThetaChar
  rw [filter_prime_range_eq_Icc]
  have hprime_eq :
      ∑ p ∈ (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime,
          ((Real.log (p : ℝ) * Φ ((p : ℝ) / x) : ℝ) : ℂ) * χ p =
        ∑ p ∈ (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime,
          (((Λ p) * Φ ((p : ℝ) / x) : ℝ) : ℂ) * χ p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [hprime_eq]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 (Nat.floor x)) Nat.Prime (fun n => (((Λ n) * Φ ((n : ℝ) / x) : ℝ) : ℂ) * χ n)
  have hdiff :
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), (((Λ n) * Φ ((n : ℝ) / x) : ℝ) : ℂ) * χ n) -
        (∑ p ∈ (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime,
          (((Λ p) * Φ ((p : ℝ) / x) : ℝ) : ℂ) * χ p) =
      ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime),
        (((Λ n) * Φ ((n : ℝ) / x) : ℝ) : ℂ) * χ n := by
    linear_combination hsplit.symm
  rw [hdiff]
  calc ‖∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime),
          (((Λ n) * Φ ((n : ℝ) / x) : ℝ) : ℂ) * χ n‖
      ≤ ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime),
          ‖(((Λ n) * Φ ((n : ℝ) / x) : ℝ) : ℂ) * χ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime), (Λ n) * Φ_max := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hnn : 0 ≤ (Λ n) * Φ ((n : ℝ) / x) :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hΦ_nn _)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
        calc ((Λ n) * Φ ((n : ℝ) / x)) * ‖χ n‖
            ≤ ((Λ n) * Φ ((n : ℝ) / x)) * 1 :=
              mul_le_mul_of_nonneg_left (χ.norm_le_one _) hnn
          _ = (Λ n) * Φ ((n : ℝ) / x) := mul_one _
          _ ≤ (Λ n) * Φ_max :=
              mul_le_mul_of_nonneg_left (hΦ_ub _) ArithmeticFunction.vonMangoldt_nonneg
    _ = Φ_max * ∑ n ∈ (Finset.Icc 1 (Nat.floor x)).filter (fun n => ¬ n.Prime), Λ n := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ Φ_max * (18 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (sum_not_prime_vonMangoldt_le x) hΦ_max_nn
    _ = 18 * Φ_max * Real.sqrt x := by ring

/-! ### Part 2: Unified Fubini–Mellin Identity on `Re(s) = 3 / 2` -/

private lemma div_cpow_neg_eq_mul {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (((n : ℝ) / x : ℝ) : ℂ) ^ (-s) = ((n : ℂ) ^ s)⁻¹ * (x : ℂ) ^ s := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hprod : ((n : ℝ) : ℂ) = (((n : ℝ) / x : ℝ) : ℂ) * (x : ℂ) := by
    push_cast
    field_simp [hx.ne']
  have hmul := Complex.mul_cpow_ofReal_nonneg (div_nonneg hn_pos.le hx.le) hx.le (-s)
  rw [← hprod, Complex.ofReal_natCast] at hmul
  have hx_ne : (x : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or, ofReal_eq_zero]
    exact Or.inl hx.ne'
  have hxs : (x : ℂ) ^ (-s) * (x : ℂ) ^ s = 1 := by
    rw [cpow_neg, inv_mul_cancel₀]
    rw [Ne, cpow_eq_zero_iff, not_and_or, ofReal_eq_zero]
    exact Or.inl hx.ne'
  calc (((n : ℝ) / x : ℝ) : ℂ) ^ (-s)
      = (((n : ℝ) / x : ℝ) : ℂ) ^ (-s) * ((x : ℂ) ^ (-s) * (x : ℂ) ^ s) := by rw [hxs, mul_one]
    _ = ((((n : ℝ) / x : ℝ) : ℂ) ^ (-s) * (x : ℂ) ^ (-s)) * (x : ℂ) ^ s := by ring
    _ = (n : ℂ) ^ (-s) * (x : ℂ) ^ s := by rw [← hmul]
    _ = ((n : ℂ) ^ s)⁻¹ * (x : ℂ) ^ s := by rw [cpow_neg]

/-- Unified Mellin–Dirichlet vertical integral identity at `σ = 3 / 2` for any sequence `a : ℕ → ℂ`
that is `LSeriesSummable` at `3 / 2`. -/
theorem sum_Icc_eq_vertical_integral_LSeries {Φ : ℝ → ℝ} {del : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ del)
    (a : ℕ → ℂ) (hsum : LSeriesSummable a (3 / 2 : ℂ))
    {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * (Φ ((n : ℝ) / x) : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ y : ℝ, LSeries a ((3 / 2 : ℂ) + (y : ℂ) * I) *
          mellin (fun t : ℝ => (Φ t : ℂ)) ((3 / 2 : ℂ) + (y : ℂ) * I) *
          (x : ℂ) ^ ((3 / 2 : ℂ) + (y : ℂ) * I) := by
  let fC : ℝ → ℂ := fun t => (Φ t : ℂ)
  let sLine : ℝ → ℂ := fun y => ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I
  have hvi : Integrable (fun y : ℝ => mellin fC (sLine y)) :=
    verticalIntegrable_mellin_of_admissible hΦ (by norm_num)
  have hvi_norm : Integrable (fun y : ℝ => ‖mellin fC (sLine y)‖) := hvi.norm
  have hterm_id : ∀ n : ℕ, 1 ≤ n →
      a n * (Φ ((n : ℝ) / x) : ℂ) =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ y : ℝ, LSeries.term a (sLine y) n * (mellin fC (sLine y) * (x : ℂ) ^ (sLine y)) := by
    intro n hn1
    have hn_pos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hux : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr hn_pos) hx
    have hinv := mellinInv_mellin_eq (3 / 2 : ℝ) fC hux
      (mellinConvergent_of_admissible hΦ _)
      (verticalIntegrable_mellin_of_admissible hΦ (by norm_num))
      (Complex.continuous_ofReal.comp (continuous_of_admissible hΦ)).continuousAt
    have hfC_apply : (Φ ((n : ℝ) / x) : ℂ) = fC ((n : ℝ) / x) := rfl
    rw [hfC_apply, ← hinv, mellinInv, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hpull : a n * ((1 / (2 * (Real.pi : ℂ))) *
          ∫ y : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-(sLine y)) • mellin fC (sLine y)) =
        (1 / (2 * (Real.pi : ℂ))) *
          (a n * ∫ y : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-(sLine y)) * mellin fC (sLine y)) := by
      simp only [smul_eq_mul]; ring
    rw [hpull, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [div_cpow_neg_eq_mul hn_pos hx (sLine y), LSeries.term_of_ne_zero (Nat.pos_iff_ne_zero.mp hn_pos)]
    simp only [div_eq_mul_inv]
    ring
  have hfin_eq_tsum :
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * (Φ ((n : ℝ) / x) : ℂ) =
        ∑' n : ℕ, (if n = 0 then 0 else a n * (Φ ((n : ℝ) / x) : ℂ)) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (Nat.floor x))]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; lia
      simp only [hn0, ↓reduceIte]
    · intro n hn
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        have hgt : Nat.floor x < n := by
          by_contra hle
          exact hn (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn0, le_of_not_gt hle⟩)
        have hlt_x : x < (n : ℝ) := Nat.lt_of_floor_lt hgt
        have h1_lt : 1 < (n : ℝ) / x := (one_lt_div hx).mpr hlt_x
        rw [hΦ.supp_hi _ (by linarith [hΦ.delta_pos]), Complex.ofReal_zero, mul_zero]
  rw [hfin_eq_tsum]
  let F : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term a (sLine y) n * (mellin fC (sLine y) * (x : ℂ) ^ (sLine y))
  have hLHS_terms : ∀ n : ℕ,
      (if n = 0 then 0 else a n * (Φ ((n : ℝ) / x) : ℂ)) =
        (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, F n y := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [F, LSeries.term_zero]
    · simp only [hn0, ↓reduceIte]
      exact hterm_id n (Nat.one_le_iff_ne_zero.mpr hn0)
  simp_rw [hLHS_terms]
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    have hc1 : Continuous (fun y : ℝ => LSeries.term a (sLine y) n) := by
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [LSeries.term_zero]; exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn0]
        refine continuous_const.div ?_ (fun y => ?_)
        · exact (by fun_prop : Continuous sLine).const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn0))
        · rw [Ne, cpow_eq_zero_iff, not_and_or, Nat.cast_eq_zero]
          exact Or.inl hn0
    have hc2 : Continuous (fun y : ℝ => mellin fC (sLine y)) :=
      (differentiable_mellin_of_admissible hΦ).continuous.comp (by fun_prop)
    have hc3 : Continuous (fun y : ℝ => (x : ℂ) ^ (sLine y)) :=
      (by fun_prop : Continuous sLine).const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
    exact (hc1.mul (hc2.mul hc3)).aestronglyMeasurable
  have hsum_norm : Summable (fun n : ℕ => ‖LSeries.term a (3 / 2 : ℂ) n‖) :=
    summable_norm_iff.mpr hsum
  have hF_norm_le : ∀ (n : ℕ) (y : ℝ),
      ‖F n y‖ = ‖LSeries.term a (3 / 2 : ℂ) n‖ * (x ^ (3 / 2 : ℝ) * ‖mellin fC (sLine y)‖) := by
    intro n y
    simp only [F, norm_mul]
    have ht_norm : ‖LSeries.term a (sLine y) n‖ = ‖LSeries.term a (3 / 2 : ℂ) n‖ := by
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · simp only [LSeries.term_of_ne_zero hn0, norm_div]
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
          Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
        simp [sLine]
    have hx_norm : ‖(x : ℂ) ^ (sLine y)‖ = x ^ (3 / 2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [sLine]
    rw [ht_norm, hx_norm]
    ring
  have hlint_ne_top : (∑' n : ℕ, ∫⁻ y : ℝ, ‖F n y‖ₑ) ≠ ⊤ := by
    let Cy : ℝ → ℝ := fun y => x ^ (3 / 2 : ℝ) * ‖mellin fC (sLine y)‖
    have hCy_int : Integrable Cy := hvi_norm.const_mul _
    have hCy_nn : ∀ y : ℝ, 0 ≤ Cy y := fun y => by positivity
    have hI_lt : (∫⁻ y : ℝ, ENNReal.ofReal (Cy y)) < ⊤ :=
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hCy_nn)).mp hCy_int.hasFiniteIntegral
    have hterm_lint : ∀ n : ℕ,
        (∫⁻ y : ℝ, ‖F n y‖ₑ) = ENNReal.ofReal ‖LSeries.term a (3 / 2 : ℂ) n‖ *
          ∫⁻ y : ℝ, ENNReal.ofReal (Cy y) := by
      intro n
      have heq : (fun y : ℝ => ‖F n y‖ₑ) =
          fun y : ℝ => ENNReal.ofReal ‖LSeries.term a (3 / 2 : ℂ) n‖ * ENNReal.ofReal (Cy y) := by
        ext y
        rw [← ofReal_norm, hF_norm_le n y,
          ENNReal.ofReal_mul (norm_nonneg _)]
      rw [heq, lintegral_const_mul'' _ hCy_int.aemeasurable.ennreal_ofReal]
    simp_rw [hterm_lint, ENNReal.tsum_mul_right]
    have htsum_lt : (∑' n : ℕ, ENNReal.ofReal ‖LSeries.term a (3 / 2 : ℂ) n‖) < ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum_norm]
      exact ENNReal.ofReal_lt_top
    exact (ENNReal.mul_lt_top htsum_lt hI_lt).ne
  have hsum_int : Summable (fun n : ℕ => ∫ y : ℝ, F n y) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ =>
        ‖LSeries.term a (3 / 2 : ℂ) n‖ * ∫ y : ℝ, x ^ (3 / 2 : ℝ) * ‖mellin fC (sLine y)‖)
      (hsum_norm.mul_right _) fun n => ?_
    calc ‖∫ y : ℝ, F n y‖ ≤ ∫ y : ℝ, ‖F n y‖ := norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, ‖LSeries.term a (3 / 2 : ℂ) n‖ *
            (x ^ (3 / 2 : ℝ) * ‖mellin fC (sLine y)‖) := by
            simp_rw [hF_norm_le]
      _ = ‖LSeries.term a (3 / 2 : ℂ) n‖ *
            ∫ y : ℝ, x ^ (3 / 2 : ℝ) * ‖mellin fC (sLine y)‖ := integral_const_mul _ _
  rw [tsum_mul_left, ← MeasureTheory.integral_tsum hF_meas hlint_ne_top]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  have hswap : (∑' n : ℕ, F n y) =
      (∑' n : ℕ, LSeries.term a (sLine y) n) * (mellin fC (sLine y) * (x : ℂ) ^ (sLine y)) :=
    tsum_mul_right
  rw [hswap]
  have hsLine_eq : sLine y = (3 / 2 : ℂ) + (y : ℂ) * I := by simp [sLine]
  rw [hsLine_eq]
  change LSeries a ((3 / 2 : ℂ) + (y : ℂ) * I) *
      (mellin (fun t : ℝ => (Φ t : ℂ)) ((3 / 2 : ℂ) + (y : ℂ) * I) *
        (x : ℂ) ^ ((3 / 2 : ℂ) + (y : ℂ) * I)) = _
  ring

/-- Exact vertical Mellin integral representation of `(smoothedPsiAll Φ x : ℂ)` at `σ = 3 / 2`. -/
theorem smoothedPsiAll_eq_vertical_integral {Φ : ℝ → ℝ} {del : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ del) {x : ℝ} (hx : 0 < x) :
    (smoothedPsiAll Φ x : ℂ) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ y : ℝ, (-(deriv riemannZeta ((3 / 2 : ℂ) + (y : ℂ) * I) /
            riemannZeta ((3 / 2 : ℂ) + (y : ℂ) * I))) *
          mellin (fun t : ℝ => (Φ t : ℂ)) ((3 / 2 : ℂ) + (y : ℂ) * I) *
          (x : ℂ) ^ ((3 / 2 : ℂ) + (y : ℂ) * I) := by
  have hLHS : (smoothedPsiAll Φ x : ℂ) =
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n : ℂ) * (Φ ((n : ℝ) / x) : ℂ) := by
    unfold smoothedPsiAll
    push_cast
    rfl
  rw [hLHS, sum_Icc_eq_vertical_integral_LSeries hΦ (fun n => (Λ n : ℂ))
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)) hx]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hre : 1 < ((3 / 2 : ℂ) + (y : ℂ) * I).re := by simp; norm_num
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  change LSeries (↗Λ) ((3 / 2 : ℂ) + (y : ℂ) * I) * _ * _ = _
  rw [hL, neg_div]

/-- Exact vertical Mellin integral representation of `smoothedPsiChar Φ x χ` at `σ = 3 / 2`. -/
theorem smoothedPsiChar_eq_vertical_integral {Φ : ℝ → ℝ} {del : ℝ}
    (hΦ : External.SmoothedKernelAdmissible Φ del) {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {x : ℝ} (hx : 0 < x) :
    smoothedPsiChar Φ x χ =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ y : ℝ, (-(deriv (DirichletCharacter.LFunction χ) ((3 / 2 : ℂ) + (y : ℂ) * I) /
            DirichletCharacter.LFunction χ ((3 / 2 : ℂ) + (y : ℂ) * I))) *
          mellin (fun t : ℝ => (Φ t : ℂ)) ((3 / 2 : ℂ) + (y : ℂ) * I) *
          (x : ℂ) ^ ((3 / 2 : ℂ) + (y : ℂ) * I) := by
  let a : ℕ → ℂ := ↗χ * ↗Λ
  have hLHS : smoothedPsiChar Φ x χ =
      ∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * (Φ ((n : ℝ) / x) : ℂ) := by
    unfold smoothedPsiChar
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [a]
    ring
  rw [hLHS, sum_Icc_eq_vertical_integral_LSeries hΦ a
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num)) hx]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  set s : ℂ := (3 / 2 : ℂ) + (y : ℂ) * I
  have hre : 1 < s.re := by simp [s]; norm_num
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hre,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hre] at hL
  change L (↗χ * ↗Λ) s * _ * _ = _
  rw [hL, neg_div]

end
end BuchstabSwitchingK2.SmoothExplicitFormula
