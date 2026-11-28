import BuchstabSwitching.External.NumericalConstants.CanonicalDefs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Certified Unconditional Bounds on Classical Transcendental Constants

Proves `10^-15`-accurate rational interval enclosures for `log 2`, `exp 2`, the Euler–Mascheroni
constant `γ`, `exp γ`, `exp (-γ)`, `α_0 = (γ + log 2) / 2`, and `canonicalLi2 = li(2)`:
- `ln2_bounds_cert`, `e2_bounds_cert`;
- `gamma_bounds_cert` via sixth-order Euler–Maclaurin monotonicity and `harmonic 256`;
- `eGamma_bounds_cert`, `eNegGamma_bounds_cert`, `alpha0_bounds_cert`;
- `li2_bounds_cert` via `log(log 2) = -log(3/2) + log((3/2) log 2)` and Ramanujan–Soldner series.
-/

namespace BuchstabSwitching.External

noncomputable section

/-! ## 1. `10^20`-Scale Fixed-Point Arithmetic and `artanh` Logarithm Evaluator -/

private def scaleT : ℕ := 100000000000000000000
private def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

private lemma scaleT_pos : (0 : ℝ) < (scaleT : ℝ) := by unfold scaleT; positivity
private lemma scaleT_eq : (scaleT : ℝ) = (10 : ℝ) ^ 20 := by unfold scaleT; norm_num

private lemma floorDiv_le_real {a b : ℕ} (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]; exact_mod_cast Nat.div_mul_le_self a b

private lemma real_le_ceilDiv {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((ceilDiv a b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h3 : a ≤ ceilDiv a b * b := by
    by_cases ha : a = 0
    · subst ha; simp
    · unfold ceilDiv
      have h1 := Nat.div_add_mod (a + b - 1) b
      have h2 := Nat.mod_lt (a + b - 1) hb
      have hcomm : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
      omega
  exact_mod_cast h3

private lemma floorDiv_scale_le {a b : ℕ} (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) / (scaleT : ℝ) ≤ ((a : ℝ) / (scaleT : ℝ)) / (b : ℝ) :=
  (div_le_div_of_nonneg_right (floorDiv_le_real hb) scaleT_pos.le).trans_eq (by ring)

private lemma le_ceilDiv_scale {a b : ℕ} (hb : 0 < b) :
    ((a : ℝ) / (scaleT : ℝ)) / (b : ℝ) ≤ ((ceilDiv a b : ℕ) : ℝ) / (scaleT : ℝ) :=
  (by ring : ((a : ℝ) / (scaleT : ℝ)) / (b : ℝ) = ((a : ℝ) / (b : ℝ)) / (scaleT : ℝ)).trans_le
    (div_le_div_of_nonneg_right (real_le_ceilDiv hb) scaleT_pos.le)

private def logRatioGo (a b : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => ((scaleT * a) / b, ceilDiv (scaleT * a) b, 0, 0)
  | i + 1 =>
    match logRatioGo a b i with
    | (tLo, tHi, sLo, sHi) =>
      let d := 2 * i + 1
      ((tLo * (a * a)) / (b * b), ceilDiv (tHi * (a * a)) (b * b),
        sLo + (2 * tLo) / d, sHi + ceilDiv (2 * tHi) d)

private def logRatioEval (num den n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  logRatioGo (num - den) (num + den) n

private lemma logRatioGo_sound {a b : ℕ} (hb : 0 < b) :
    ∀ n : ℕ,
      let res := logRatioGo a b n
      let u : ℝ := (a : ℝ) / (b : ℝ)
      (res.1 : ℝ) / (scaleT : ℝ) ≤ u ^ (2 * n + 1) ∧
      u ^ (2 * n + 1) ≤ (res.2.1 : ℝ) / (scaleT : ℝ) ∧
      (res.2.2.1 : ℝ) / (scaleT : ℝ) ≤
        ∑ j ∈ Finset.range n, (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ∧
      ∑ j ∈ Finset.range n, (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
        (res.2.2.2 : ℝ) / (scaleT : ℝ) := by
  intro n
  have hS : (0 : ℝ) < (scaleT : ℝ) := scaleT_pos
  induction n with
  | zero =>
    dsimp [logRatioGo]
    have ht1 : (((scaleT * a) / b : ℕ) : ℝ) / (scaleT : ℝ) ≤ (a : ℝ) / (b : ℝ) :=
      (floorDiv_scale_le hb).trans_eq (by push_cast; field_simp [hS.ne'])
    have ht2 : (a : ℝ) / (b : ℝ) ≤ ((ceilDiv (scaleT * a) b : ℕ) : ℝ) / (scaleT : ℝ) :=
      (by push_cast; field_simp [hS.ne'] :
        (a : ℝ) / (b : ℝ) = (((scaleT * a : ℕ) : ℝ) / (scaleT : ℝ)) / (b : ℝ)).trans_le
        (le_ceilDiv_scale hb)
    simpa using ⟨ht1, ht2⟩
  | succ i ih =>
    rcases ih with ⟨htLo, htHi, hsLo, hsHi⟩
    set res := logRatioGo a b i
    set u : ℝ := (a : ℝ) / (b : ℝ)
    have hbb : 0 < b * b := Nat.mul_pos hb hb
    have hd_pos : 0 < 2 * i + 1 := by omega
    have hpow : u ^ (2 * (i + 1) + 1) = u ^ (2 * i + 1) * ((a : ℝ) * (a : ℝ) / ((b : ℝ) * (b : ℝ))) := by
      dsimp [u]; ring
    have htLo' : (((res.1 * (a * a)) / (b * b) : ℕ) : ℝ) / (scaleT : ℝ) ≤ u ^ (2 * (i + 1) + 1) := by
      rw [hpow]; refine (floorDiv_scale_le hbb).trans ?_
      rw [show (((res.1 * (a * a) : ℕ) : ℝ) / (scaleT : ℝ)) / ((b * b : ℕ) : ℝ) =
        ((res.1 : ℝ) / (scaleT : ℝ)) * ((a : ℝ) * (a : ℝ) / ((b : ℝ) * (b : ℝ))) by push_cast; ring]
      gcongr
    have htHi' : u ^ (2 * (i + 1) + 1) ≤ ((ceilDiv (res.2.1 * (a * a)) (b * b) : ℕ) : ℝ) / (scaleT : ℝ) := by
      rw [hpow]; refine (mul_le_mul_of_nonneg_right htHi (by positivity)).trans ?_
      rw [show ((res.2.1 : ℝ) / (scaleT : ℝ)) * ((a : ℝ) * (a : ℝ) / ((b : ℝ) * (b : ℝ))) =
        (((res.2.1 * (a * a) : ℕ) : ℝ) / (scaleT : ℝ)) / ((b * b : ℕ) : ℝ) by push_cast; ring]
      exact le_ceilDiv_scale hbb
    have hterm_lo : (((2 * res.1) / (2 * i + 1) : ℕ) : ℝ) / (scaleT : ℝ) ≤
        (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * u ^ (2 * i + 1) := by
      refine (floorDiv_scale_le hd_pos).trans ?_
      rw [show (((2 * res.1 : ℕ) : ℝ) / (scaleT : ℝ)) / ((2 * i + 1 : ℕ) : ℝ) =
        (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * ((res.1 : ℝ) / (scaleT : ℝ)) by push_cast; ring]
      gcongr
    have hterm_hi : (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * u ^ (2 * i + 1) ≤
        ((ceilDiv (2 * res.2.1) (2 * i + 1) : ℕ) : ℝ) / (scaleT : ℝ) := by
      refine (mul_le_mul_of_nonneg_left htHi (by positivity)).trans ?_
      rw [show (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * ((res.2.1 : ℝ) / (scaleT : ℝ)) =
        (((2 * res.2.1 : ℕ) : ℝ) / (scaleT : ℝ)) / ((2 * i + 1 : ℕ) : ℝ) by push_cast; ring]
      exact le_ceilDiv_scale hd_pos
    have hmatch : logRatioGo a b (i + 1) =
        ((res.1 * (a * a)) / (b * b), ceilDiv (res.2.1 * (a * a)) (b * b),
          res.2.2.1 + (2 * res.1) / (2 * i + 1), res.2.2.2 + ceilDiv (2 * res.2.1) (2 * i + 1)) := by
      simp [logRatioGo, res]
    rw [hmatch]; dsimp only
    refine ⟨htLo', htHi', ?_, ?_⟩
    · rw [Finset.sum_range_succ, Nat.cast_add res.2.2.1, add_div]; exact add_le_add hsLo hterm_lo
    · rw [Finset.sum_range_succ, Nat.cast_add res.2.2.2, add_div]; exact add_le_add hsHi hterm_hi

private lemma logRatioEval_sound {num den n : ℕ} (hden : 0 < den) (hlo : den ≤ num)
    (hhi : num ≤ 2 * den) (hn : 1 ≤ n) :
    let res := logRatioEval num den n
    (res.2.2.1 : ℝ) / (scaleT : ℝ) ≤ Real.log ((num : ℝ) / (den : ℝ)) ∧
      Real.log ((num : ℝ) / (den : ℝ)) ≤ ((res.2.2.2 + res.2.1 : ℕ) : ℝ) / (scaleT : ℝ) := by
  set a : ℕ := num - den
  set b : ℕ := num + den
  set u : ℝ := (a : ℝ) / (b : ℝ)
  have hb_pos : 0 < b := by omega
  have hu_nn : 0 ≤ u := by positivity
  have hu_le : u ≤ (1 / 3 : ℝ) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hb_pos) (by norm_num)]
    exact_mod_cast (by omega : a * 3 ≤ 1 * b)
  have hu_abs : |u| < 1 := by rw [abs_of_nonneg hu_nn]; linarith
  have hlog_eq : Real.log ((num : ℝ) / (den : ℝ)) = Real.log (1 + u) - Real.log (1 - u) := by
    have hb_real : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    have ha_real : (a : ℝ) = (num : ℝ) - (den : ℝ) := Nat.cast_sub hlo
    have hb_eq : (b : ℝ) = (num : ℝ) + (den : ℝ) := by push_cast [b]; rfl
    have h1pu : 1 + u = (2 * (num : ℝ)) / (b : ℝ) := by
      simp only [u]; rw [one_add_div hb_real.ne', ha_real, hb_eq]; ring
    have h1mu : 1 - u = (2 * (den : ℝ)) / (b : ℝ) := by
      simp only [u]; rw [one_sub_div hb_real.ne', ha_real, hb_eq]; ring
    have hnum_pos : (0 : ℝ) < (num : ℝ) := by exact_mod_cast lt_of_lt_of_le hden hlo
    have hden_pos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
    rw [← Real.log_div (by rw [h1pu]; positivity) (by rw [h1mu]; positivity), h1pu, h1mu]
    congr 1; field_simp
  have hhasSum : HasSum (fun j : ℕ => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1))
      (Real.log ((num : ℝ) / (den : ℝ))) :=
    hlog_eq ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  obtain ⟨_, htHi, hsLo, hsHi⟩ := logRatioGo_sound (a := a) hb_pos n
  constructor
  · exact hsLo.trans (sum_le_hasSum (Finset.range n) (fun j _ => by positivity) hhasSum)
  · set f : ℕ → ℝ := fun j => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)
    have hsplit := hhasSum.summable.sum_add_tsum_nat_add n
    have hu2_le : u ^ 2 ≤ 1 / 9 := by nlinarith
    have hgeom : HasSum (fun m : ℕ => (u ^ 2) ^ m) (1 - u ^ 2)⁻¹ :=
      hasSum_geometric_of_lt_one (sq_nonneg u) (by linarith)
    have htail_le : ∀ m : ℕ, f (m + n) ≤ ((2 / 3 : ℝ) * u ^ (2 * n + 1)) * (u ^ 2) ^ m := by
      intro m
      have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hden_le : (1 : ℝ) / (2 * ((m + n : ℕ) : ℝ) + 1) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
      dsimp only [f]
      rw [show u ^ (2 * (m + n) + 1) = u ^ (2 * n + 1) * (u ^ 2) ^ m by ring]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hden_le zero_le_two)
        (by positivity)).trans_eq (by ring)
    have htsum_le : ∑' m : ℕ, f (m + n) ≤ ((2 / 3 : ℝ) * u ^ (2 * n + 1)) * (1 - u ^ 2)⁻¹ := by
      have h1 := Summable.tsum_le_tsum htail_le
        (hhasSum.summable.comp_injective (add_left_injective n)) (hgeom.summable.mul_left _)
      rwa [tsum_mul_left, hgeom.tsum_eq] at h1
    have hinv_le : (1 - u ^ 2)⁻¹ ≤ (9 / 8 : ℝ) := by
      rw [← one_div]
      exact (one_div_le_one_div_of_le (by norm_num) (by linarith : (8 / 9 : ℝ) ≤ 1 - u ^ 2)).trans_eq
        (by norm_num)
    have htail_u : ((2 / 3 : ℝ) * u ^ (2 * n + 1)) * (1 - u ^ 2)⁻¹ ≤ u ^ (2 * n + 1) := by
      have hpow_nn : 0 ≤ u ^ (2 * n + 1) := by positivity
      exact (mul_le_mul_of_nonneg_left hinv_le (by positivity)).trans (by linarith)
    change Real.log ((num : ℝ) / (den : ℝ)) ≤
      (((logRatioGo a b n).2.2.2 + (logRatioGo a b n).2.1 : ℕ) : ℝ) / (scaleT : ℝ)
    rw [Nat.cast_add, add_div]
    linarith [hsplit, hhasSum.tsum_eq, htsum_le, htail_u, hsHi, htHi]

private lemma logRatioEval_ln2 :
    logRatioEval 2 1 21 = (0, 1, 69314718055994530933, 69314718055994530957) := by decide

private lemma ln2_sharp :
    (69314718055994530933 : ℝ) / (scaleT : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718055994530958 : ℝ) / (scaleT : ℝ) := by
  have h := logRatioEval_sound (num := 2) (den := 1) (n := 21)
    (by omega) (by omega) (by omega) (by omega)
  rw [logRatioEval_ln2] at h; simpa using h

theorem ln2_bounds_cert :
    (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180559946 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := ln2_sharp; rw [scaleT_eq] at hlo hhi; constructor <;> linarith

/-! ## 2. `exp` Evaluator on `[0, 1]` and `e2_bounds_cert` -/

private lemma taylorStep_bounds {num den i tLo tHi : ℕ} (hden : 0 < den)
    (htLo : (tLo : ℝ) / (scaleT : ℝ) ≤ ((num : ℝ) / (den : ℝ)) ^ i / (i.factorial : ℝ))
    (htHi : ((num : ℝ) / (den : ℝ)) ^ i / (i.factorial : ℝ) ≤ (tHi : ℝ) / (scaleT : ℝ)) :
    (((tLo * num) / (den * (i + 1)) : ℕ) : ℝ) / (scaleT : ℝ) ≤
        ((num : ℝ) / (den : ℝ)) ^ (i + 1) / ((i + 1).factorial : ℝ) ∧
      ((num : ℝ) / (den : ℝ)) ^ (i + 1) / ((i + 1).factorial : ℝ) ≤
        ((ceilDiv (tHi * num) (den * (i + 1)) : ℕ) : ℝ) / (scaleT : ℝ) := by
  set x : ℝ := (num : ℝ) / (den : ℝ)
  have hd_pos : 0 < den * (i + 1) := Nat.mul_pos hden (by omega)
  have hden_ne : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  have hS_ne : (scaleT : ℝ) ≠ 0 := scaleT_pos.ne'
  have hstep_id : x ^ (i + 1) / ((i + 1).factorial : ℝ) =
      (x ^ i / (i.factorial : ℝ)) * x / ((i : ℝ) + 1) := by
    rw [Nat.factorial_succ, pow_succ]; push_cast
    rw [div_mul_eq_mul_div, div_div, mul_comm (i.factorial : ℝ) ((i : ℝ) + 1)]
  rw [hstep_id]
  constructor
  · refine (floorDiv_scale_le hd_pos).trans ?_
    rw [show (((tLo * num : ℕ) : ℝ) / (scaleT : ℝ)) / ((den * (i + 1) : ℕ) : ℝ) =
      ((tLo : ℝ) / (scaleT : ℝ)) * x / ((i : ℝ) + 1) by dsimp [x]; push_cast; field_simp]
    gcongr
  · refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htHi (by positivity))
      (by positivity)).trans ?_
    rw [show ((tHi : ℝ) / (scaleT : ℝ)) * x / ((i : ℝ) + 1) =
      (((tHi * num : ℕ) : ℝ) / (scaleT : ℝ)) / ((den * (i + 1) : ℕ) : ℝ) by
      dsimp [x]; push_cast; field_simp]
    exact le_ceilDiv_scale hd_pos

private def expUnitGo (num den : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (scaleT, scaleT, scaleT, scaleT)
  | i + 1 =>
    match expUnitGo num den i with
    | (tLo, tHi, sLo, sHi) =>
      let d := den * (i + 1)
      let tLo' := (tLo * num) / d
      let tHi' := ceilDiv (tHi * num) d
      (tLo', tHi', sLo + tLo', sHi + tHi')

private lemma expUnitGo_sound {num den : ℕ} (hden : 0 < den) :
    ∀ n : ℕ,
      let res := expUnitGo num den n
      let x : ℝ := (num : ℝ) / (den : ℝ)
      (res.1 : ℝ) / (scaleT : ℝ) ≤ x ^ n / (n.factorial : ℝ) ∧
      x ^ n / (n.factorial : ℝ) ≤ (res.2.1 : ℝ) / (scaleT : ℝ) ∧
      (res.2.2.1 : ℝ) / (scaleT : ℝ) ≤ ∑ m ∈ Finset.range (n + 1), x ^ m / (m.factorial : ℝ) ∧
      ∑ m ∈ Finset.range (n + 1), x ^ m / (m.factorial : ℝ) ≤ (res.2.2.2 : ℝ) / (scaleT : ℝ) := by
  intro n
  induction n with
  | zero => simp [expUnitGo, div_self scaleT_pos.ne']
  | succ i ih =>
    rcases ih with ⟨htLo, htHi, hsLo, hsHi⟩
    obtain ⟨htLo', htHi'⟩ := taylorStep_bounds hden htLo htHi
    set res := expUnitGo num den i
    have hmatch : expUnitGo num den (i + 1) =
        ((res.1 * num) / (den * (i + 1)), ceilDiv (res.2.1 * num) (den * (i + 1)),
          res.2.2.1 + (res.1 * num) / (den * (i + 1)),
          res.2.2.2 + ceilDiv (res.2.1 * num) (den * (i + 1))) := by simp [expUnitGo, res]
    rw [hmatch]; dsimp only
    refine ⟨htLo', htHi', ?_, ?_⟩
    · rw [Finset.sum_range_succ, Nat.cast_add res.2.2.1, add_div]; exact add_le_add hsLo htLo'
    · rw [Finset.sum_range_succ, Nat.cast_add res.2.2.2, add_div]; exact add_le_add hsHi htHi'

private lemma expUnit_bounds {num den : ℕ} (hden : 0 < den) (hle : num ≤ den) :
    let res := expUnitGo num den 21
    (res.2.2.1 : ℝ) / (scaleT : ℝ) ≤ Real.exp ((num : ℝ) / (den : ℝ)) ∧
      Real.exp ((num : ℝ) / (den : ℝ)) ≤ ((res.2.2.2 + 1 : ℕ) : ℝ) / (scaleT : ℝ) := by
  set x : ℝ := (num : ℝ) / (den : ℝ)
  have hx_nn : 0 ≤ x := by positivity
  have hx_le1 : x ≤ 1 := (div_le_one (by exact_mod_cast hden)).mpr (by exact_mod_cast hle)
  have hx_abs : |x| ≤ 1 := by rw [abs_of_nonneg hx_nn]; exact hx_le1
  obtain ⟨_, _, hsLo, hsHi⟩ := expUnitGo_sound (num := num) hden 21
  constructor
  · exact hsLo.trans (Real.sum_le_exp_of_nonneg hx_nn 22)
  · have hdiff := (le_abs_self _).trans (Real.exp_bound hx_abs (n := 22) (by omega))
    have hpow : |x| ^ 22 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx_abs
    have htail : |x| ^ 22 * (((22 : ℕ).succ : ℝ) / (((22 : ℕ).factorial : ℝ) * (22 : ℝ))) ≤
        1 / (scaleT : ℝ) :=
      (mul_le_mul_of_nonneg_right hpow (by positivity)).trans (by norm_num [Nat.factorial, scaleT])
    change Real.exp x ≤ (((expUnitGo num den 21).2.2.2 + 1 : ℕ) : ℝ) / (scaleT : ℝ)
    rw [Nat.cast_add, Nat.cast_one, add_div]; linarith

private lemma expUnitGo_one :
    expUnitGo 1 1 21 = (1, 2, 271828182845904523526, 271828182845904523545) := by decide

theorem e2_bounds_cert :
    (7.389056098930650 : ℝ) ≤ Real.exp 2 ∧ Real.exp 2 ≤ (7.389056098930651 : ℝ) := by
  have he1 := expUnit_bounds (num := 1) (den := 1) (by omega) (by omega)
  rw [expUnitGo_one] at he1; dsimp only at he1; push_cast at he1; rw [div_one] at he1
  rw [show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
  rcases he1 with ⟨hlo, hhi⟩; rw [scaleT_eq] at hlo hhi
  have hsq_lo := pow_le_pow_left₀ (by positivity) hlo 2
  have hsq_hi := pow_le_pow_left₀ (Real.exp_pos 1).le hhi 2
  constructor <;> linarith

/-! ## 3. Euler–Mascheroni Constant `γ`, `exp γ`, `exp (-γ)`, and `α_0` -/

private noncomputable def gammaSeqLo (k : ℕ) : ℝ :=
  (harmonic k : ℝ) - Real.log (k : ℝ) - 1 / (2 * (k : ℝ)) +
    1 / (12 * (k : ℝ) ^ 2) - 1 / (120 * (k : ℝ) ^ 4)

private noncomputable def gammaSeqHi (k : ℕ) : ℝ :=
  gammaSeqLo k + 1 / (252 * (k : ℝ) ^ 6)

private lemma log_succ_sub_log_bounds {x : ℝ} (hx : 1 ≤ x) :
    let u : ℝ := 1 / (2 * x + 1)
    2 * (u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / 7) ≤ Real.log (x + 1) - Real.log x ∧
      Real.log (x + 1) - Real.log x ≤
        2 * (u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / (7 * (1 - u ^ 2))) := by
  set u : ℝ := 1 / (2 * x + 1)
  have hx_pos : 0 < x := by linarith
  have h2x1_pos : 0 < 2 * x + 1 := by linarith
  have hu_nn : 0 ≤ u := by positivity
  have hu_le : u ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hu_abs : |u| < 1 := by rw [abs_of_nonneg hu_nn]; linarith
  have h1pu : 1 + u = 2 * (x + 1) / (2 * x + 1) := by dsimp [u]; field_simp; ring
  have h1mu : 1 - u = 2 * x / (2 * x + 1) := by dsimp [u]; field_simp; ring
  have hlog_eq : Real.log (x + 1) - Real.log x = Real.log (1 + u) - Real.log (1 - u) := by
    rw [← Real.log_div (by positivity) hx_pos.ne',
      ← Real.log_div (by rw [h1pu]; positivity) (by rw [h1mu]; positivity), h1pu, h1mu]
    congr 1; field_simp
  have hhasSum : HasSum (fun j : ℕ => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1))
      (Real.log (x + 1) - Real.log x) :=
    hlog_eq ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  set f : ℕ → ℝ := fun j => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)
  have hsum4 : ∑ j ∈ Finset.range 4, f j = 2 * (u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / 7) := by
    simp only [f, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]; push_cast; ring
  constructor
  · rw [← hsum4]; exact sum_le_hasSum (Finset.range 4) (fun j _ => by positivity) hhasSum
  · have hsplit := hhasSum.summable.sum_add_tsum_nat_add 4
    have hgeom : HasSum (fun m : ℕ => (u ^ 2) ^ m) (1 - u ^ 2)⁻¹ :=
      hasSum_geometric_of_lt_one (sq_nonneg u) (by nlinarith)
    have htail_le : ∀ m : ℕ, f (m + 4) ≤ ((2 / 9 : ℝ) * u ^ 9) * (u ^ 2) ^ m := by
      intro m
      have hden_le : (1 : ℝ) / (2 * ((m + 4 : ℕ) : ℝ) + 1) ≤ 1 / 9 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
      dsimp only [f]
      rw [show u ^ (2 * (m + 4) + 1) = u ^ 9 * (u ^ 2) ^ m by ring]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hden_le zero_le_two)
        (by positivity)).trans_eq (by ring)
    have htsum_le : ∑' m : ℕ, f (m + 4) ≤ ((2 / 9 : ℝ) * u ^ 9) * (1 - u ^ 2)⁻¹ := by
      have h1 := Summable.tsum_le_tsum htail_le
        (hhasSum.summable.comp_injective (add_left_injective 4)) (hgeom.summable.mul_left _)
      rwa [tsum_mul_left, hgeom.tsum_eq] at h1
    have h1mu2_pos : 0 < 1 - u ^ 2 := by nlinarith
    have h97 : (2 / 9 : ℝ) * u ^ 9 * (1 - u ^ 2)⁻¹ ≤ (2 / 7 : ℝ) * u ^ 9 * (1 - u ^ 2)⁻¹ := by
      gcongr; norm_num
    have hcomb : 2 * (u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / 7) +
        (2 / 7 : ℝ) * u ^ 9 * (1 - u ^ 2)⁻¹ =
        2 * (u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / (7 * (1 - u ^ 2))) := by
      field_simp [h1mu2_pos.ne']; ring
    linarith [hsplit, hhasSum.tsum_eq, hsum4, htsum_le, h97, hcomb]

private lemma gamma_poly_a {x : ℝ} (hx : 0 < x) :
    let u : ℝ := 1 / (2 * x + 1)
    0 < 1 / (x + 1) - 2 * (u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / (7 * (1 - u ^ 2))) -
      (1 / (2 * (x + 1)) - 1 / (2 * x)) +
      (1 / (12 * (x + 1) ^ 2) - 1 / (12 * x ^ 2)) -
      (1 / (120 * (x + 1) ^ 4) - 1 / (120 * x ^ 4)) := by
  intro u
  have h1mu2 : 1 - u ^ 2 = 4 * x * (x + 1) / (2 * x + 1) ^ 2 := by dsimp [u]; field_simp; ring
  refine lt_of_lt_of_eq (by positivity :
    0 < (7 + 98 * x + 532 * x ^ 2 + 1508 * x ^ 3 + 2354 * x ^ 4 + 1920 * x ^ 5 + 640 * x ^ 6) /
      (840 * x ^ 4 * (x + 1) ^ 4 * (2 * x + 1) ^ 5)) ?_
  rw [h1mu2]; dsimp [u]; field_simp; ring

private lemma gamma_poly_b {x : ℝ} (hx : 0 < x) :
    let u : ℝ := 1 / (2 * x + 1)
    0 < 2 * (u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / 7) - 1 / (x + 1) +
      (1 / (2 * (x + 1)) - 1 / (2 * x)) -
      (1 / (12 * (x + 1) ^ 2) - 1 / (12 * x ^ 2)) +
      (1 / (120 * (x + 1) ^ 4) - 1 / (120 * x ^ 4)) +
      (1 / (252 * x ^ 6) - 1 / (252 * (x + 1) ^ 6)) := by
  intro u
  refine lt_of_lt_of_eq (by positivity :
    0 < (10 + 200 * x + 1809 * x ^ 2 + 9720 * x ^ 3 + 34317 * x ^ 4 + 82926 * x ^ 5 +
      138774 * x ^ 6 + 158928 * x ^ 7 + 119322 * x ^ 8 + 53060 * x ^ 9 + 10612 * x ^ 10) /
      (2520 * x ^ 6 * (x + 1) ^ 6 * (2 * x + 1) ^ 7)) ?_
  dsimp [u]; field_simp; ring

private lemma gammaSeq_step {k : ℕ} (hk : 1 ≤ k) :
    gammaSeqLo k < gammaSeqLo (k + 1) ∧ gammaSeqHi (k + 1) < gammaSeqHi k := by
  have hx1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx0 : (0 : ℝ) < (k : ℝ) := by linarith
  obtain ⟨hlog_lo, hlog_hi⟩ := log_succ_sub_log_bounds hx1
  have hpa := gamma_poly_a hx0; have hpb := gamma_poly_b hx0
  have hharm : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
    rw [harmonic_succ, Rat.cast_add, ← one_div]; push_cast; rfl
  unfold gammaSeqHi gammaSeqLo; rw [hharm]; push_cast
  dsimp only at hlog_lo hlog_hi hpa hpb
  constructor <;> linarith

private lemma gammaSeq_mono {k : ℕ} (hk : 1 ≤ k) :
    ∀ d : ℕ, gammaSeqLo k ≤ gammaSeqLo (k + d) ∧ gammaSeqHi (k + d) ≤ gammaSeqHi k := by
  intro d; induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨h1, h2⟩ := gammaSeq_step (k := k + d) (by omega)
    exact ⟨ih.1.trans h1.le, h2.le.trans ih.2⟩

private lemma tendsto_inv_pow_mul_natCast (c : ℝ) {p : ℕ} (hp : p ≠ 0) :
    Filter.Tendsto (fun k : ℕ => 1 / (c * (k : ℝ) ^ p)) Filter.atTop (nhds 0) := by
  by_cases hc : c = 0
  · subst hc; simp
  · have h1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ)⁻¹) ^ p) Filter.atTop (nhds (0 ^ p)) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).pow p
    rw [zero_pow hp] at h1
    have h2 := h1.const_mul c⁻¹; rw [mul_zero] at h2
    exact h2.congr (fun k => by rw [inv_pow, one_div, mul_inv])

private lemma gammaSeq_bounds_eulerMascheroni {k : ℕ} (hk : 1 ≤ k) :
    gammaSeqLo k ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ gammaSeqHi k := by
  have ht0 := Real.tendsto_harmonic_sub_log
  have ht1 : Filter.Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) Filter.atTop (nhds 0) :=
    (tendsto_inv_pow_mul_natCast 2 (p := 1) (by omega)).congr (fun n => by rw [pow_one])
  have ht2 := tendsto_inv_pow_mul_natCast 12 (p := 2) (by omega)
  have ht4 := tendsto_inv_pow_mul_natCast 120 (p := 4) (by omega)
  have ht6 := tendsto_inv_pow_mul_natCast 252 (p := 6) (by omega)
  have htLo : Filter.Tendsto gammaSeqLo Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have h := ((ht0.sub ht1).add ht2).sub ht4; rwa [sub_zero, add_zero, sub_zero] at h
  have htHi : Filter.Tendsto gammaSeqHi Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have h := htLo.add ht6; rwa [add_zero] at h
  have hevLo : ∀ᶠ n in Filter.atTop, gammaSeqLo k ≤ gammaSeqLo n :=
    Filter.eventually_atTop.mpr ⟨k, fun n hn => by
      simpa [Nat.add_sub_of_le hn] using (gammaSeq_mono hk (n - k)).1⟩
  have hevHi : ∀ᶠ n in Filter.atTop, gammaSeqHi n ≤ gammaSeqHi k :=
    Filter.eventually_atTop.mpr ⟨k, fun n hn => by
      simpa [Nat.add_sub_of_le hn] using (gammaSeq_mono hk (n - k)).2⟩
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds htLo hevLo,
    le_of_tendsto_of_tendsto htHi tendsto_const_nhds hevHi⟩

private def harmChunkGo (lo : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | i + 1 =>
    match harmChunkGo lo i with
    | (sLo, sHi) =>
      let d := lo + i + 1
      (sLo + scaleT / d, sHi + ceilDiv scaleT d)

private lemma harmChunkGo_sound (lo len : ℕ) :
    let res := harmChunkGo lo len
    (res.1 : ℝ) / (scaleT : ℝ) ≤ ∑ k ∈ Finset.Ico lo (lo + len), (1 : ℝ) / ((k : ℝ) + 1) ∧
      ∑ k ∈ Finset.Ico lo (lo + len), (1 : ℝ) / ((k : ℝ) + 1) ≤ (res.2 : ℝ) / (scaleT : ℝ) := by
  have hS : (0 : ℝ) < (scaleT : ℝ) := scaleT_pos
  induction len with
  | zero => simp [harmChunkGo]
  | succ i ih =>
    rcases ih with ⟨hlo, hhi⟩
    set res := harmChunkGo lo i
    set d : ℕ := lo + i + 1
    have hd_pos : 0 < d := by omega
    have hd_lo : ((scaleT / d : ℕ) : ℝ) / (scaleT : ℝ) ≤ (1 : ℝ) / ((lo : ℝ) + (i : ℝ) + 1) :=
      (floorDiv_scale_le hd_pos).trans_eq (by dsimp [d]; rw [div_self hS.ne']; push_cast; ring)
    have hd_hi : (1 : ℝ) / ((lo : ℝ) + (i : ℝ) + 1) ≤ ((ceilDiv scaleT d : ℕ) : ℝ) / (scaleT : ℝ) :=
      (by dsimp [d]; rw [div_self hS.ne']; push_cast; ring :
        (1 : ℝ) / ((lo : ℝ) + (i : ℝ) + 1) = ((scaleT : ℝ) / (scaleT : ℝ)) / (d : ℝ)).trans_le
        (le_ceilDiv_scale hd_pos)
    have hmatch : harmChunkGo lo (i + 1) = (res.1 + scaleT / d, res.2 + ceilDiv scaleT d) := by
      simp [harmChunkGo, res, d]
    rw [hmatch, show lo + (i + 1) = (lo + i) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    dsimp only; push_cast
    constructor
    · rw [add_div]; exact add_le_add hlo hd_lo
    · rw [add_div]; exact add_le_add hhi hd_hi

private lemma harmonic_eq_sum_range (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [harmonic_succ, Rat.cast_add, Finset.sum_range_succ, ih, ← one_div]; push_cast; rfl

private lemma harmChunk_0 :
    harmChunkGo 0 64 = (474389090370576902576, 474389090370576902627) := by decide
private lemma harmChunk_64 :
    harmChunkGo 64 64 = (68925618888340335050, 68925618888340335110) := by decide
private lemma harmChunk_128 :
    harmChunkGo 128 64 = (40416585045159819135, 40416585045159819198) := by decide
private lemma harmChunk_192 :
    harmChunkGo 192 64 = (28703201977650980009, 28703201977650980070) := by decide

private lemma harmonic_256_bounds :
    (612434496281728036770 : ℝ) / (scaleT : ℝ) ≤ (harmonic 256 : ℝ) ∧
      (harmonic 256 : ℝ) ≤ (612434496281728037005 : ℝ) / (scaleT : ℝ) := by
  have hc0 := harmChunkGo_sound 0 64; rw [harmChunk_0] at hc0
  have hc1 := harmChunkGo_sound 64 64; rw [harmChunk_64] at hc1
  have hc2 := harmChunkGo_sound 128 64; rw [harmChunk_128] at hc2
  have hc3 := harmChunkGo_sound 192 64; rw [harmChunk_192] at hc3
  dsimp only at hc0 hc1 hc2 hc3
  have hsplit : ∑ k ∈ Finset.Ico (0 : ℕ) 256, (1 : ℝ) / ((k : ℝ) + 1) =
      (∑ k ∈ Finset.Ico (0 : ℕ) 64, (1 : ℝ) / ((k : ℝ) + 1)) +
        (∑ k ∈ Finset.Ico (64 : ℕ) 128, (1 : ℝ) / ((k : ℝ) + 1)) +
        (∑ k ∈ Finset.Ico (128 : ℕ) 192, (1 : ℝ) / ((k : ℝ) + 1)) +
        (∑ k ∈ Finset.Ico (192 : ℕ) 256, (1 : ℝ) / ((k : ℝ) + 1)) := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 192) (by omega : (192 : ℕ) ≤ 256)]
    rw [← Finset.sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 128) (by omega : (128 : ℕ) ≤ 192)]
    rw [← Finset.sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 64) (by omega : (64 : ℕ) ≤ 128)]
  rw [harmonic_eq_sum_range, ← Nat.Ico_zero_eq_range, hsplit]
  rw [scaleT_eq] at hc0 hc1 hc2 hc3 ⊢
  constructor <;> linarith

private lemma gamma_sharp :
    (5772156649015328440 : ℝ) / (10000000000000000000 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ (5772156649015328625 : ℝ) / (10000000000000000000 : ℝ) := by
  obtain ⟨hg_lo, hg_hi⟩ := gammaSeq_bounds_eulerMascheroni (k := 256) (by omega)
  obtain ⟨hh_lo, hh_hi⟩ := harmonic_256_bounds
  obtain ⟨hl_lo, hl_hi⟩ := ln2_sharp
  have hlog256 : Real.log ((256 : ℕ) : ℝ) = 8 * Real.log 2 := by
    rw [show ((256 : ℕ) : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.log_pow]; ring
  unfold gammaSeqLo at hg_lo; unfold gammaSeqHi gammaSeqLo at hg_hi
  rw [hlog256] at hg_lo hg_hi; rw [scaleT_eq] at hh_lo hh_hi hl_lo hl_hi
  push_cast at hg_lo hg_hi; constructor <;> linarith

theorem gamma_bounds_cert :
    (0.577215664901532 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ (0.577215664901533 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := gamma_sharp; constructor <;> linarith

private lemma expUnitGo_gamma_lo :
    expUnitGo 5772156649015328440 10000000000000000000 21 =
      (0, 1, 178107241799019795557, 178107241799019795578) := by decide
private lemma expUnitGo_gamma_hi :
    expUnitGo 5772156649015328625 10000000000000000000 21 =
      (0, 1, 178107241799019798851, 178107241799019798873) := by decide

private lemma eGamma_sharp :
    (178107241799019795557 : ℝ) / (scaleT : ℝ) ≤ Real.exp Real.eulerMascheroniConstant ∧
      Real.exp Real.eulerMascheroniConstant ≤ (178107241799019798874 : ℝ) / (scaleT : ℝ) := by
  obtain ⟨hg_lo, hg_hi⟩ := gamma_sharp
  have he_lo := (expUnit_bounds (num := 5772156649015328440)
    (den := 10000000000000000000) (by omega) (by omega)).1
  have he_hi := (expUnit_bounds (num := 5772156649015328625)
    (den := 10000000000000000000) (by omega) (by omega)).2
  rw [expUnitGo_gamma_lo] at he_lo; rw [expUnitGo_gamma_hi] at he_hi
  dsimp only at he_lo he_hi; push_cast at he_lo he_hi
  exact ⟨he_lo.trans (Real.exp_le_exp.mpr hg_lo), (Real.exp_le_exp.mpr hg_hi).trans he_hi⟩

theorem eGamma_bounds_cert :
    (1.781072417990197 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant ∧
      Real.exp Real.eulerMascheroniConstant ≤ (1.781072417990198 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := eGamma_sharp; rw [scaleT_eq] at hlo hhi; constructor <;> linarith

theorem eNegGamma_bounds_cert :
    (0.561459483566885 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) ∧
      Real.exp (-Real.eulerMascheroniConstant) ≤ (0.561459483566886 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := eGamma_sharp
  rw [Real.exp_neg, ← one_div]; rw [scaleT_eq] at hlo hhi
  have h1 := one_div_le_one_div_of_le (Real.exp_pos _) hhi
  have h2 := one_div_le_one_div_of_le (by positivity) hlo
  constructor <;> linarith

theorem alpha0_bounds_cert :
    (0.635181422730739 : ℝ) ≤ (Real.eulerMascheroniConstant + Real.log 2) / 2 ∧
      (Real.eulerMascheroniConstant + Real.log 2) / 2 ≤ (0.635181422730740 : ℝ) := by
  obtain ⟨hg_lo, hg_hi⟩ := gamma_sharp; obtain ⟨hl_lo, hl_hi⟩ := ln2_sharp
  rw [scaleT_eq] at hl_lo hl_hi; constructor <;> linarith

theorem cJ_bounds_cert :
    (7.586785216829545 : ℝ) ≤
        ((Real.eulerMascheroniConstant + Real.log 2) / 2 + (0.78 : ℝ)) *
          (5.36099831086678458 : ℝ) ∧
      ((Real.eulerMascheroniConstant + Real.log 2) / 2 + (0.78 : ℝ)) *
        (5.36099831086678458 : ℝ) ≤ (7.586785216829546 : ℝ) := by
  obtain ⟨hg_lo, hg_hi⟩ := gamma_sharp; obtain ⟨hl_lo, hl_hi⟩ := ln2_sharp
  rw [scaleT_eq] at hl_lo hl_hi; constructor <;> linarith

/-! ## 4. Logarithmic Integral `canonicalLi2 = li(2)` -/

private lemma logRatioEval_3_2 :
    logRatioEval 3 2 15 = (0, 1, 40546510810816438191, 40546510810816438205) := by decide
private lemma logRatioEval_x_lo :
    logRatioEval 1039720770839917963 1000000000000000000 7 =
      (0, 1, 3895218752650005383, 3895218752650005392) := by decide
private lemma logRatioEval_x_hi :
    logRatioEval 1039720770839917965 1000000000000000000 7 =
      (0, 1, 3895218752650005575, 3895218752650005584) := by decide

private lemma log_ln2_bounds :
    ((-40546510810816438206 + 3895218752650005383 : ℝ) / (scaleT : ℝ)) ≤
        Real.log (Real.log 2) ∧
      Real.log (Real.log 2) ≤
        ((-40546510810816438191 + 3895218752650005585 : ℝ) / (scaleT : ℝ)) := by
  obtain ⟨hl_lo, hl_hi⟩ := ln2_sharp
  have hln2_pos : 0 < Real.log 2 := by rw [scaleT_eq] at hl_lo; linarith
  have hsplit_log : Real.log (Real.log 2) =
      -Real.log ((3 : ℝ) / 2) + Real.log ((3 / 2 : ℝ) * Real.log 2) := by
    have hmul : Real.log 2 = (2 / 3 : ℝ) * ((3 / 2 : ℝ) * Real.log 2) := by ring
    have h23 : Real.log (2 / 3 : ℝ) = -Real.log ((3 : ℝ) / 2) := by
      rw [show (2 / 3 : ℝ) = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
    conv_lhs => rw [hmul]
    rw [Real.log_mul (by norm_num) (by positivity), h23]
  have h32 := logRatioEval_sound (num := 3) (den := 2) (n := 15)
    (by omega) (by omega) (by omega) (by omega)
  rw [logRatioEval_3_2] at h32; dsimp only at h32; push_cast at h32
  rcases h32 with ⟨h32_lo, h32_hi⟩
  have hx_lo_le : (1039720770839917963 : ℝ) / (1000000000000000000 : ℝ) ≤
      (3 / 2 : ℝ) * Real.log 2 := by rw [scaleT_eq] at hl_lo; linarith
  have hx_hi_ge : (3 / 2 : ℝ) * Real.log 2 ≤
      (1039720770839917965 : ℝ) / (1000000000000000000 : ℝ) := by rw [scaleT_eq] at hl_hi; linarith
  have hlog_xlo := (logRatioEval_sound (num := 1039720770839917963)
    (den := 1000000000000000000) (n := 7) (by omega) (by omega) (by omega) (by omega)).1
  have hlog_xhi := (logRatioEval_sound (num := 1039720770839917965)
    (den := 1000000000000000000) (n := 7) (by omega) (by omega) (by omega) (by omega)).2
  rw [logRatioEval_x_lo] at hlog_xlo; dsimp only at hlog_xlo; push_cast at hlog_xlo
  rw [logRatioEval_x_hi] at hlog_xhi; dsimp only at hlog_xhi; push_cast at hlog_xhi
  have hmono_lo := Real.log_le_log (by positivity) hx_lo_le
  have hmono_hi := Real.log_le_log (by positivity) hx_hi_ge
  rw [hsplit_log]; rw [scaleT_eq] at h32_lo h32_hi hlog_xlo hlog_xhi ⊢
  constructor <;> linarith

private def li2SeriesGo (num den : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (scaleT, scaleT, 0, 0)
  | i + 1 =>
    match li2SeriesGo num den i with
    | (tLo, tHi, sLo, sHi) =>
      let d := den * (i + 1)
      let tLo' := (tLo * num) / d
      let tHi' := ceilDiv (tHi * num) d
      (tLo', tHi', sLo + tLo' / (i + 1), sHi + ceilDiv tHi' (i + 1))

private lemma li2SeriesGo_sound {num den : ℕ} (hden : 0 < den) :
    ∀ n : ℕ,
      let res := li2SeriesGo num den n
      let x : ℝ := (num : ℝ) / (den : ℝ)
      (res.1 : ℝ) / (scaleT : ℝ) ≤ x ^ n / (n.factorial : ℝ) ∧
      x ^ n / (n.factorial : ℝ) ≤ (res.2.1 : ℝ) / (scaleT : ℝ) ∧
      (res.2.2.1 : ℝ) / (scaleT : ℝ) ≤
        ∑ k ∈ Finset.range n, x ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)) ∧
      ∑ k ∈ Finset.range n, x ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)) ≤
        (res.2.2.2 : ℝ) / (scaleT : ℝ) := by
  intro n
  induction n with
  | zero => simp [li2SeriesGo, div_self scaleT_pos.ne']
  | succ i ih =>
    rcases ih with ⟨htLo, htHi, hsLo, hsHi⟩
    obtain ⟨htLo', htHi'⟩ := taylorStep_bounds hden htLo htHi
    set res := li2SeriesGo num den i
    set x : ℝ := (num : ℝ) / (den : ℝ)
    set tLo' : ℕ := (res.1 * num) / (den * (i + 1))
    set tHi' : ℕ := ceilDiv (res.2.1 * num) (den * (i + 1))
    have hi1_pos : 0 < i + 1 := by omega
    have hdiv_id : x ^ (i + 1) / (((i + 1 : ℕ) : ℝ) * ((i + 1).factorial : ℝ)) =
        (x ^ (i + 1) / ((i + 1).factorial : ℝ)) / ((i + 1 : ℕ) : ℝ) := by rw [div_div, mul_comm]
    have hterm_lo : ((tLo' / (i + 1) : ℕ) : ℝ) / (scaleT : ℝ) ≤
        x ^ (i + 1) / (((i + 1 : ℕ) : ℝ) * ((i + 1).factorial : ℝ)) := by
      rw [hdiv_id]; exact (floorDiv_scale_le hi1_pos).trans (by gcongr)
    have hterm_hi : x ^ (i + 1) / (((i + 1 : ℕ) : ℝ) * ((i + 1).factorial : ℝ)) ≤
        ((ceilDiv tHi' (i + 1) : ℕ) : ℝ) / (scaleT : ℝ) := by
      rw [hdiv_id]; exact (div_le_div_of_nonneg_right htHi' (by positivity)).trans
        (le_ceilDiv_scale hi1_pos)
    have hmatch : li2SeriesGo num den (i + 1) =
        (tLo', tHi', res.2.2.1 + tLo' / (i + 1), res.2.2.2 + ceilDiv tHi' (i + 1)) := by
      simp [li2SeriesGo, res, tLo', tHi']
    rw [hmatch]; dsimp only
    refine ⟨htLo', htHi', ?_, ?_⟩
    · rw [Finset.sum_range_succ, Nat.cast_add res.2.2.1, add_div]; exact add_le_add hsLo hterm_lo
    · rw [Finset.sum_range_succ, Nat.cast_add res.2.2.2, add_div]; exact add_le_add hsHi hterm_hi

private lemma li2SeriesGo_lo :
    li2SeriesGo 6931471805599453093 10000000000000000000 20 =
      (0, 1, 83446103579762425099, 83446103579762425118) := by decide
private lemma li2SeriesGo_hi :
    li2SeriesGo 6931471805599453096 10000000000000000000 20 =
      (0, 1, 83446103579762425143, 83446103579762425162) := by decide

private lemma li2_series_bounds :
    (83446103579762425099 : ℝ) / (scaleT : ℝ) ≤
        (∑' k : ℕ, (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))) ∧
      (∑' k : ℕ, (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))) ≤
        (83446103579762425163 : ℝ) / (scaleT : ℝ) := by
  obtain ⟨hl_lo, hl_hi⟩ := ln2_sharp
  set xLo : ℝ := (6931471805599453093 : ℝ) / (10000000000000000000 : ℝ)
  set xHi : ℝ := (6931471805599453096 : ℝ) / (10000000000000000000 : ℝ)
  have hxLo_le : xLo ≤ Real.log 2 := by dsimp [xLo]; rw [scaleT_eq] at hl_lo; linarith
  have hxHi_ge : Real.log 2 ≤ xHi := by dsimp [xHi]; rw [scaleT_eq] at hl_hi; linarith
  have hln2_nn : 0 ≤ Real.log 2 := by dsimp [xLo] at hxLo_le; linarith
  have hln2_le34 : Real.log 2 ≤ 3 / 4 := by dsimp [xHi] at hxHi_ge; linarith
  set f : ℕ → ℝ := fun k =>
    (Real.log 2) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ))
  have hsum := summable_canonicalLi2_term
  have hs_lo := (li2SeriesGo_sound (num := 6931471805599453093)
    (den := 10000000000000000000) (by omega) 20).2.2.1
  have hs_hi := (li2SeriesGo_sound (num := 6931471805599453096)
    (den := 10000000000000000000) (by omega) 20).2.2.2
  rw [li2SeriesGo_lo] at hs_lo; dsimp only at hs_lo
  rw [li2SeriesGo_hi] at hs_hi; dsimp only at hs_hi
  constructor
  · have hmono : ∑ k ∈ Finset.range 20, xLo ^ (k + 1) /
        (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)) ≤ ∑ k ∈ Finset.range 20, f k :=
      Finset.sum_le_sum (fun k _ => by dsimp [f]; gcongr)
    exact (hs_lo.trans hmono).trans
      (hsum.sum_le_tsum (Finset.range 20) (fun k _ => by dsimp [f]; positivity))
  · have hsplit := hsum.sum_add_tsum_nat_add 20
    have hmono : ∑ k ∈ Finset.range 20, f k ≤ ∑ k ∈ Finset.range 20, xHi ^ (k + 1) /
        (((k + 1 : ℕ) : ℝ) * ((k + 1).factorial : ℝ)) :=
      Finset.sum_le_sum (fun k _ => by dsimp [f]; gcongr)
    have hgeom : HasSum (fun m : ℕ => (3 / 4 : ℝ) ^ m) ((1 - 3 / 4)⁻¹) :=
      hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
    have htail_term : ∀ m : ℕ, f (m + 20) ≤
        (1 / ((21 : ℝ) * ((21 : ℕ).factorial : ℝ))) * (3 / 4 : ℝ) ^ m := by
      intro m
      have hpow1 : (Real.log 2) ^ (m + 20 + 1) ≤ (3 / 4 : ℝ) ^ m := by
        rw [show m + 20 + 1 = 21 + m by omega, pow_add]
        have hp21 : (Real.log 2) ^ 21 ≤ 1 := pow_le_one₀ hln2_nn (by linarith)
        have hpm : (Real.log 2) ^ m ≤ (3 / 4 : ℝ) ^ m := pow_le_pow_left₀ hln2_nn hln2_le34 m
        exact (mul_le_mul hp21 hpm (pow_nonneg hln2_nn m) zero_le_one).trans_eq (one_mul _)
      have hden_ge : (21 : ℝ) * ((21 : ℕ).factorial : ℝ) ≤
          ((m + 20 + 1 : ℕ) : ℝ) * ((m + 20 + 1).factorial : ℝ) :=
        mul_le_mul (by exact_mod_cast (by omega : 21 ≤ m + 20 + 1))
          (by exact_mod_cast Nat.factorial_le (by omega : 21 ≤ m + 20 + 1))
          (by positivity) (by positivity)
      dsimp [f]
      exact (div_le_div₀ (by positivity) hpow1 (by positivity) hden_ge).trans_eq (by ring)
    have htsum_le : ∑' m : ℕ, f (m + 20) ≤ 1 / (scaleT : ℝ) := by
      have h1 := Summable.tsum_le_tsum htail_term
        (hsum.comp_injective (add_left_injective 20)) (hgeom.summable.mul_left _)
      rw [tsum_mul_left, hgeom.tsum_eq] at h1
      exact h1.trans (by norm_num [Nat.factorial, scaleT])
    have hadd : (83446103579762425163 : ℝ) / (scaleT : ℝ) =
        (83446103579762425162 : ℝ) / (scaleT : ℝ) + 1 / (scaleT : ℝ) := by ring
    rw [hadd]; linarith [hsplit, hs_hi, hmono, htsum_le]

theorem li2_bounds_cert :
    (1.045163780117492 : ℝ) ≤ canonicalLi2 ∧ canonicalLi2 ≤ (1.045163780117493 : ℝ) := by
  obtain ⟨hg_lo, hg_hi⟩ := gamma_sharp
  obtain ⟨hll_lo, hll_hi⟩ := log_ln2_bounds
  obtain ⟨hs_lo, hs_hi⟩ := li2_series_bounds
  unfold canonicalLi2; rw [scaleT_eq] at hll_lo hll_hi hs_lo hs_hi
  constructor <;> linarith

end

end BuchstabSwitching.External
