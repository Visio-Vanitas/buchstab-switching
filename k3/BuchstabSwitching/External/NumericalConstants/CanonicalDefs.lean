import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Canonical Mathematical Definitions of `li(2)` and Meissel–Mertens `M_0`

Defines the exact mathematical constants consumed by the remaining classical analytic premises:
- `canonicalLi2`: Cauchy principal-value logarithmic integral at `2`, given by the convergent
  Ramanujan–Soldner power series `γ + log(log 2) + ∑'_{k=0}^∞ (log 2)^(k+1) / ((k+1) * (k+1)!)`;
- `meisselMertensConst`: Meissel–Mertens constant `M_0 = γ + ∑'_{p prime} (log(1 - 1/p) + 1/p)`.

Also establishes basic termwise bounds and absolute summability for both series.
-/

namespace BuchstabSwitching.External

/-- Canonical Ramanujan–Soldner series definition of `li(2) = Ei(log 2)`. -/
noncomputable def canonicalLi2 : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log 2) +
    ∑' k : ℕ, (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))

/-- Canonical Meissel–Mertens constant `M_0 = γ + ∑_{p prime} (log(1 - 1/p) + 1/p)`. -/
noncomputable def meisselMertensConst : ℝ :=
  Real.eulerMascheroniConstant +
    ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))

lemma summable_canonicalLi2_term :
    Summable (fun k : ℕ =>
      (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))) := by
  have hlog_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexp : Summable (fun k : ℕ => (Real.log 2) ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
    (Real.summable_pow_div_factorial (Real.log 2)).comp_injective (add_left_injective 1)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hexp
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have hfac_pos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k + 1)
  have hden : ((k + 1).factorial : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ) :=
    le_mul_of_one_le_left hfac_pos.le hk1
  exact div_le_div_of_nonneg_left (pow_nonneg hlog_nn _) hfac_pos hden

/-- For `u ≥ 2`, `0 ≤ -(Real.log (1 - 1 / u) + 1 / u) ≤ 1 / (2 * u * (u - 1))`. -/
lemma neg_log_one_sub_inv_add_inv_bounds {u : ℝ} (hu : 2 ≤ u) :
    0 ≤ -(Real.log (1 - 1 / u) + 1 / u) ∧
      -(Real.log (1 - 1 / u) + 1 / u) ≤ 1 / (2 * u * (u - 1)) := by
  have hu_pos : 0 < u := by linarith
  have hu1_pos : 0 < u - 1 := by linarith
  have h1mu_pos : 0 < 1 - 1 / u := by
    have : 1 / u < 1 := (div_lt_one hu_pos).mpr (by linarith)
    linarith
  constructor
  · have hle := Real.log_le_sub_one_of_pos h1mu_pos
    linarith
  · set x : ℝ := 1 / u
    have hx_pos : 0 < x := one_div_pos.mpr hu_pos
    have hx_lt1 : x < 1 := (div_lt_one hu_pos).mpr (by linarith)
    have hx_abs : |x| < 1 := by rw [abs_of_pos hx_pos]; exact hx_lt1
    have hshift := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_pow_div_log_of_abs_lt_one hx_abs)
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one] at hshift
    have hgeom := (hasSum_geometric_of_lt_one hx_pos.le hx_lt1).mul_left (x ^ 2 / 2)
    have hle : -Real.log (1 - x) - x ≤ (x ^ 2 / 2) * (1 - x)⁻¹ := by
      refine hasSum_le (fun n => ?_) hshift hgeom
      have hden : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      calc x ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℝ) + 1)
          ≤ x ^ (n + 1 + 1) / 2 := div_le_div_of_nonneg_left (by positivity) zero_lt_two hden
        _ = (x ^ 2 / 2) * x ^ n := by ring
    have hsimp : (x ^ 2 / 2) * (1 - x)⁻¹ = 1 / (2 * u * (u - 1)) := by
      rw [← one_div]; dsimp only [x]; field_simp [hu_pos.ne', hu1_pos.ne', h1mu_pos.ne']
    dsimp only [x] at hle
    linarith

lemma summable_neg_meisselMertens_term :
    Summable (fun p : Nat.Primes => -(Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))) := by
  have hp2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp_sub : Summable (fun p : Nat.Primes => (1 : ℝ) / (p.1 : ℝ) ^ 2) :=
    hp2.comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le
    (fun p => (neg_log_one_sub_inv_add_inv_bounds (by exact_mod_cast p.2.two_le)).1)
    (fun p => ?_) hp_sub
  have hp_ge2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  have hbd := (neg_log_one_sub_inv_add_inv_bounds hp_ge2).2
  have hden : (p.1 : ℝ) ^ 2 ≤ 2 * (p.1 : ℝ) * ((p.1 : ℝ) - 1) := by nlinarith
  exact hbd.trans (one_div_le_one_div_of_le (by positivity) hden)

lemma summable_meisselMertens_term :
    Summable (fun p : Nat.Primes => Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)) := by
  simpa using summable_neg_meisselMertens_term.neg

end BuchstabSwitching.External
