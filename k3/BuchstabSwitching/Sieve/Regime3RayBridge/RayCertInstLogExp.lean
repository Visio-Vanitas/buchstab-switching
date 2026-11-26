import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStarCertSound
import Mathlib.Tactic

/-!
# Certified Closed-Form Rational `log` and `exp` Evaluators (`10^12` Scale)

Provides kernel-verified fast rational bounds (`logRatioLo`, `logRatioHi`, `expGe`, `expNegUb`)
used to verify the `L = 120` Selberg upper-sieve strip grid and error bounds via `decide`
(zero `sorry`, zero axioms, zero `native_decide`).
-/

namespace BuchstabSwitching

noncomputable section

section RayCertLogExp

/-! ## 1. Closed-Form 2/3-Term `artanh` Bounds for `log (num / den)` (`1 ≤ num / den ≤ 2`) -/

def logRatioLo (num den : ℕ) : ℕ :=
  let a := num - den
  let b := num + den
  (2 * scaleS * a) / b + (2 * scaleS * a ^ 3) / (3 * b ^ 3)

def logRatioHi (num den : ℕ) : ℕ :=
  let a := num - den
  let b := num + den
  hstarCeilDiv (2 * scaleS * a) b +
    hstarCeilDiv (2 * scaleS * a ^ 3) (3 * b ^ 3) +
    hstarCeilDiv (scaleS * a ^ 5) (10 * num * den * b ^ 3)

private lemma real_le_ceilDiv' {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((hstarCeilDiv a b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h3 : a ≤ hstarCeilDiv a b * b := by
    by_cases ha : a = 0
    · subst ha; simp
    · unfold hstarCeilDiv
      have h1 := Nat.div_add_mod (a + b - 1) b
      have h2 := Nat.mod_lt (a + b - 1) hb
      have hcomm : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
      omega
  exact_mod_cast h3

private lemma log_ratio_hasSum {num den : ℕ} (hden : 0 < den) (hlo : den ≤ num) (hhi : num ≤ 2 * den) :
    let a : ℕ := num - den
    let b : ℕ := num + den
    let u : ℝ := (a : ℝ) / (b : ℝ)
    0 ≤ u ∧ u ≤ (1 / 3 : ℝ) ∧ |u| < 1 ∧
      HasSum (fun j : ℕ => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1))
        (Real.log ((num : ℝ) / (den : ℝ))) := by
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
  exact ⟨hu_nn, hu_le, hu_abs, hlog_eq ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs⟩

lemma logRatioLo_sound {num den : ℕ} (hden : 0 < den) (hlo : den ≤ num) (hhi : num ≤ 2 * den) :
    ((logRatioLo num den : ℕ) : ℝ) / (scaleS : ℝ) ≤ Real.log ((num : ℝ) / (den : ℝ)) := by
  obtain ⟨hu_nn, _, _, hhasSum⟩ := log_ratio_hasSum hden hlo hhi
  set a : ℕ := num - den
  set b : ℕ := num + den
  set u : ℝ := (a : ℝ) / (b : ℝ)
  have hb_pos : 0 < b := by omega
  have hb3_pos : 0 < 3 * b ^ 3 := by positivity
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have hsum_le : ∑ j ∈ Finset.range 2, (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
      Real.log ((num : ℝ) / (den : ℝ)) :=
    sum_le_hasSum (Finset.range 2) (fun j _ => by positivity) hhasSum
  have hsum_eval : ∑ j ∈ Finset.range 2, (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) =
      2 * (a : ℝ) / (b : ℝ) + 2 * (a : ℝ) ^ 3 / (3 * (b : ℝ) ^ 3) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, u]
    push_cast
    ring
  have ht1 : (((2 * scaleS * a) / b : ℕ) : ℝ) / (scaleS : ℝ) ≤ 2 * (a : ℝ) / (b : ℝ) := by
    have h1 := floorDiv_le_real (a := 2 * scaleS * a) hb_pos
    have h2 : ((2 * (scaleS : ℝ) * (a : ℝ)) / (b : ℝ)) / (scaleS : ℝ) =
        2 * (a : ℝ) / (b : ℝ) := by field_simp [hS.ne']
    exact (div_le_div_of_nonneg_right (by simpa [Nat.cast_mul] using h1) hS.le).trans_eq h2
  have ht2 : (((2 * scaleS * a ^ 3) / (3 * b ^ 3) : ℕ) : ℝ) / (scaleS : ℝ) ≤
      2 * (a : ℝ) ^ 3 / (3 * (b : ℝ) ^ 3) := by
    have h1 := floorDiv_le_real (a := 2 * scaleS * a ^ 3) hb3_pos
    have h2 : ((2 * (scaleS : ℝ) * (a : ℝ) ^ 3) / (3 * (b : ℝ) ^ 3)) / (scaleS : ℝ) =
        2 * (a : ℝ) ^ 3 / (3 * (b : ℝ) ^ 3) := by field_simp [hS.ne']
    exact (div_le_div_of_nonneg_right (by simpa [Nat.cast_mul, Nat.cast_pow] using h1) hS.le).trans_eq h2
  unfold logRatioLo
  push_cast
  rw [add_div]
  linarith

lemma logRatioHi_sound {num den : ℕ} (hden : 0 < den) (hlo : den ≤ num) (hhi : num ≤ 2 * den) :
    Real.log ((num : ℝ) / (den : ℝ)) ≤ ((logRatioHi num den : ℕ) : ℝ) / (scaleS : ℝ) := by
  obtain ⟨hu_nn, hu_le, _, hhasSum⟩ := log_ratio_hasSum hden hlo hhi
  set a : ℕ := num - den
  set b : ℕ := num + den
  set u : ℝ := (a : ℝ) / (b : ℝ)
  have hb_pos : 0 < b := by omega
  have hb3_pos : 0 < 3 * b ^ 3 := by positivity
  have hnum_pos : 0 < num := lt_of_lt_of_le hden hlo
  have hden10_pos : 0 < 10 * num * den * b ^ 3 := by positivity
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  set f : ℕ → ℝ := fun j => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)
  have hsplit := hhasSum.summable.sum_add_tsum_nat_add 2
  have hu2_lt1 : u ^ 2 < 1 := by nlinarith
  have hgeom : HasSum (fun m : ℕ => (u ^ 2) ^ m) (1 - u ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one (sq_nonneg u) hu2_lt1
  have htail_le : ∀ m : ℕ, f (m + 2) ≤ ((2 / 5 : ℝ) * u ^ 5) * (u ^ 2) ^ m := by
    intro m
    have hden_le : (1 : ℝ) / (2 * ((m + 2 : ℕ) : ℝ) + 1) ≤ 1 / 5 :=
      one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
    dsimp only [f]
    rw [show u ^ (2 * (m + 2) + 1) = u ^ 5 * (u ^ 2) ^ m by ring]
    have hpow_nn : 0 ≤ u ^ 5 * (u ^ 2) ^ m := by positivity
    calc (2 : ℝ) * (1 / (2 * ((m + 2 : ℕ) : ℝ) + 1)) * (u ^ 5 * (u ^ 2) ^ m)
        ≤ (2 : ℝ) * (1 / 5) * (u ^ 5 * (u ^ 2) ^ m) := by gcongr
      _ = ((2 / 5 : ℝ) * u ^ 5) * (u ^ 2) ^ m := by ring
  have htsum_bound : ∑' m : ℕ, f (m + 2) ≤ ((2 / 5 : ℝ) * u ^ 5) * (1 - u ^ 2)⁻¹ := by
    have hsum_m := hhasSum.summable.comp_injective (add_left_injective 2)
    have h1 := Summable.tsum_le_tsum htail_le hsum_m (hgeom.summable.mul_left _)
    rwa [tsum_mul_left, hgeom.tsum_eq] at h1
  have htail_id : ((2 / 5 : ℝ) * u ^ 5) * (1 - u ^ 2)⁻¹ =
      (a : ℝ) ^ 5 / (10 * (num : ℝ) * (den : ℝ) * (b : ℝ) ^ 3) := by
    have hb_ne : (b : ℝ) ≠ 0 := by exact_mod_cast hb_pos.ne'
    have hnum_ne : (num : ℝ) ≠ 0 := by exact_mod_cast hnum_pos.ne'
    have hden_ne : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
    have hba : (b : ℝ) ^ 2 - (a : ℝ) ^ 2 = 4 * (num : ℝ) * (den : ℝ) := by
      have ha_r : (a : ℝ) = (num : ℝ) - (den : ℝ) := Nat.cast_sub hlo
      have hb_r : (b : ℝ) = (num : ℝ) + (den : ℝ) := by push_cast [b]; rfl
      rw [ha_r, hb_r]; ring
    have h1mu2 : 1 - u ^ 2 = (4 * (num : ℝ) * (den : ℝ)) / (b : ℝ) ^ 2 := by
      dsimp only [u]; rw [div_pow, one_sub_div (pow_ne_zero 2 hb_ne), hba]
    rw [h1mu2, inv_div]
    dsimp only [u]
    field_simp [hb_ne, hnum_ne, hden_ne]
    ring
  have hsum2_eval : ∑ j ∈ Finset.range 2, f j =
      2 * (a : ℝ) / (b : ℝ) + 2 * (a : ℝ) ^ 3 / (3 * (b : ℝ) ^ 3) := by
    simp only [f, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, u]
    push_cast; ring
  have ht1 : 2 * (a : ℝ) / (b : ℝ) ≤
      ((hstarCeilDiv (2 * scaleS * a) b : ℕ) : ℝ) / (scaleS : ℝ) := by
    have h1 := real_le_ceilDiv' (a := 2 * scaleS * a) hb_pos
    have h2 : 2 * (a : ℝ) / (b : ℝ) = ((2 * (scaleS : ℝ) * (a : ℝ)) / (b : ℝ)) / (scaleS : ℝ) := by
      field_simp [hS.ne']
    rw [h2]; exact div_le_div_of_nonneg_right (by simpa [Nat.cast_mul] using h1) hS.le
  have ht2 : 2 * (a : ℝ) ^ 3 / (3 * (b : ℝ) ^ 3) ≤
      ((hstarCeilDiv (2 * scaleS * a ^ 3) (3 * b ^ 3) : ℕ) : ℝ) / (scaleS : ℝ) := by
    have h1 := real_le_ceilDiv' (a := 2 * scaleS * a ^ 3) hb3_pos
    have h2 : 2 * (a : ℝ) ^ 3 / (3 * (b : ℝ) ^ 3) =
        ((2 * (scaleS : ℝ) * (a : ℝ) ^ 3) / (3 * (b : ℝ) ^ 3)) / (scaleS : ℝ) := by
      field_simp [hS.ne']
    rw [h2]; exact div_le_div_of_nonneg_right (by simpa [Nat.cast_mul, Nat.cast_pow] using h1) hS.le
  have ht3 : (a : ℝ) ^ 5 / (10 * (num : ℝ) * (den : ℝ) * (b : ℝ) ^ 3) ≤
      ((hstarCeilDiv (scaleS * a ^ 5) (10 * num * den * b ^ 3) : ℕ) : ℝ) / (scaleS : ℝ) := by
    have h1 := real_le_ceilDiv' (a := scaleS * a ^ 5) hden10_pos
    have h2 : (a : ℝ) ^ 5 / (10 * (num : ℝ) * (den : ℝ) * (b : ℝ) ^ 3) =
        (((scaleS : ℝ) * (a : ℝ) ^ 5) / (10 * (num : ℝ) * (den : ℝ) * (b : ℝ) ^ 3)) /
          (scaleS : ℝ) := by
      field_simp [hS.ne']
    rw [h2]; exact div_le_div_of_nonneg_right (by simpa [Nat.cast_mul, Nat.cast_pow] using h1) hS.le
  unfold logRatioHi
  push_cast
  rw [add_div, add_div]
  linarith [hsplit, hhasSum.tsum_eq]

/-! ## 2. Closed-Form 32-Step `exp` Lower Bound and `exp(-x)` Upper Bound -/

def expGeAuxGo (num yDen : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, s => s
  | k + 1, t, s =>
    let j := 8 - (k + 1)
    let t' := (t * num) / (yDen * (j + 1))
    expGeAuxGo num yDen k t' (s + t')

def expGeAux (num den : ℕ) : ℕ :=
  expGeAuxGo num (32 * den) 8 scaleS scaleS

def expGe (num den : ℕ) : ℕ :=
  let r0 := expGeAux num den
  let r1 := (r0 * r0) / scaleS
  let r2 := (r1 * r1) / scaleS
  let r3 := (r2 * r2) / scaleS
  let r4 := (r3 * r3) / scaleS
  (r4 * r4) / scaleS

def expNegUb (num den : ℕ) : ℕ :=
  if num == 0 then scaleS
  else if 40 * den ≤ num then 1
  else hstarCeilDiv (scaleS * scaleS) (expGe num den)

private lemma expGeAuxGo_ge_scaleS (num den : ℕ) :
    ∀ k t s : ℕ, scaleS ≤ s → scaleS ≤ expGeAuxGo num (32 * den) k t s := by
  intro k
  induction k with
  | zero => intro _ s hs; simpa [expGeAuxGo] using hs
  | succ k ih =>
    intro t s hs
    dsimp [expGeAuxGo]
    exact ih _ _ (le_trans hs (Nat.le_add_right _ _))

private lemma expGe_ge_scaleS (num den : ℕ) : scaleS ≤ expGe num den := by
  have hsq : ∀ r : ℕ, scaleS ≤ r → scaleS ≤ (r * r) / scaleS := by
    intro r hr
    have hS : 0 < scaleS := by unfold scaleS; omega
    exact (Nat.le_div_iff_mul_le hS).mpr (Nat.mul_le_mul hr hr)
  have h0 : scaleS ≤ expGeAux num den := expGeAuxGo_ge_scaleS num den 8 scaleS scaleS le_rfl
  exact hsq _ (hsq _ (hsq _ (hsq _ (hsq _ h0))))

private lemma expGeAuxGo_sound (num den : ℕ) (hden : 0 < den) :
    ∀ k j t s : ℕ, k + j = 8 →
      (t : ℝ) / (scaleS : ℝ) ≤ ((num : ℝ) / (32 * (den : ℝ))) ^ j / (j.factorial : ℝ) →
      (s : ℝ) / (scaleS : ℝ) ≤
        ∑ m ∈ Finset.range (j + 1), ((num : ℝ) / (32 * (den : ℝ))) ^ m / (m.factorial : ℝ) →
      (expGeAuxGo num (32 * den) k t s : ℝ) / (scaleS : ℝ) ≤
        Real.exp ((num : ℝ) / (32 * (den : ℝ))) := by
  intro k
  induction k with
  | zero =>
    intro j t s _ _ hs
    dsimp [expGeAuxGo]
    exact hs.trans (Real.sum_le_exp_of_nonneg (by positivity) (j + 1))
  | succ k ih =>
    intro j t s hkj ht hs
    have hj_eq : 8 - (k + 1) = j := by omega
    set yDen : ℕ := 32 * den
    set t' : ℕ := (t * num) / (yDen * (j + 1))
    have ht'_le : (t' : ℝ) / (scaleS : ℝ) ≤
        ((num : ℝ) / (32 * (den : ℝ))) ^ (j + 1) / ((j + 1).factorial : ℝ) := by
      have hden_pos : 0 < yDen * (j + 1) := Nat.mul_pos (Nat.mul_pos (by norm_num) hden) (by omega)
      have h1 := floorDiv_le_real (a := t * num) hden_pos
      have hy : (yDen : ℝ) = 32 * (den : ℝ) := by dsimp [yDen]; push_cast; ring
      have h2 : (((t * num : ℕ) : ℝ) / ((yDen * (j + 1) : ℕ) : ℝ)) / (scaleS : ℝ) =
          ((t : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (32 * (den : ℝ))) / ((j : ℝ) + 1) := by
        push_cast; rw [hy]; field_simp [scaleS_pos.ne']
      have h3 : ((t : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (32 * (den : ℝ))) / ((j : ℝ) + 1) ≤
          (((num : ℝ) / (32 * (den : ℝ))) ^ j / (j.factorial : ℝ)) *
            ((num : ℝ) / (32 * (den : ℝ))) / ((j : ℝ) + 1) := by gcongr
      have h4 : (((num : ℝ) / (32 * (den : ℝ))) ^ j / (j.factorial : ℝ)) *
            ((num : ℝ) / (32 * (den : ℝ))) / ((j : ℝ) + 1) =
          ((num : ℝ) / (32 * (den : ℝ))) ^ (j + 1) / ((j + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ, pow_succ]
        push_cast
        rw [div_mul_eq_mul_div, div_div, mul_comm (j.factorial : ℝ) ((j : ℝ) + 1)]
      exact (div_le_div_of_nonneg_right h1 scaleS_pos.le).trans (h2 ▸ h3.trans_eq h4)
    have hs'_le : ((s + t' : ℕ) : ℝ) / (scaleS : ℝ) ≤
        ∑ m ∈ Finset.range (j + 1 + 1),
          ((num : ℝ) / (32 * (den : ℝ))) ^ m / (m.factorial : ℝ) := by
      rw [Finset.sum_range_succ]
      push_cast
      rw [add_div]
      exact add_le_add hs ht'_le
    dsimp [expGeAuxGo]
    rw [hj_eq]
    exact ih (j + 1) t' (s + t') (by omega) ht'_le hs'_le

lemma expGe_sound {num den : ℕ} (hden : 0 < den) :
    ((expGe num den : ℕ) : ℝ) / (scaleS : ℝ) ≤ Real.exp ((num : ℝ) / (den : ℝ)) := by
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have h0 : (expGeAux num den : ℝ) / (scaleS : ℝ) ≤ Real.exp ((num : ℝ) / (32 * (den : ℝ))) := by
    unfold expGeAux
    exact expGeAuxGo_sound num den hden 8 0 scaleS scaleS rfl
      (by simp [div_self hS.ne']) (by simp [div_self hS.ne'])
  have hstep : ∀ (r : ℕ) (y : ℝ), (r : ℝ) / (scaleS : ℝ) ≤ y →
      (((r * r) / scaleS : ℕ) : ℝ) / (scaleS : ℝ) ≤ y ^ 2 := by
    intro r y hry
    have h1 := floorDiv_le_real (a := r * r) (b := scaleS) (by unfold scaleS; omega)
    have h2 : (((r * r : ℕ) : ℝ) / (scaleS : ℝ)) / (scaleS : ℝ) = ((r : ℝ) / (scaleS : ℝ)) ^ 2 := by
      push_cast; ring
    have h3 : ((r : ℝ) / (scaleS : ℝ)) ^ 2 ≤ y ^ 2 :=
      pow_le_pow_left₀ (by positivity) hry 2
    exact (div_le_div_of_nonneg_right h1 hS.le).trans (h2 ▸ h3)
  set r0 := expGeAux num den
  set r1 := (r0 * r0) / scaleS
  set r2 := (r1 * r1) / scaleS
  set r3 := (r2 * r2) / scaleS
  set r4 := (r3 * r3) / scaleS
  have h1 := hstep r0 _ h0
  have h2 := hstep r1 _ h1
  have h3 := hstep r2 _ h2
  have h4 := hstep r3 _ h3
  have h5 := hstep r4 _ h4
  have hexp32 : ((((Real.exp ((num : ℝ) / (32 * (den : ℝ))) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 =
      Real.exp ((num : ℝ) / (den : ℝ)) := by
    have hp : ((((Real.exp ((num : ℝ) / (32 * (den : ℝ))) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 =
        Real.exp ((num : ℝ) / (32 * (den : ℝ))) ^ (32 : ℕ) := by ring
    rw [hp, ← Real.exp_natCast_mul]
    congr 1
    have hden_ne : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
    push_cast; field_simp [hden_ne]
  exact h5.trans_eq hexp32

lemma expNegUb_sound {num den : ℕ} (hden : 0 < den) :
    Real.exp (-((num : ℝ) / (den : ℝ))) ≤ ((expNegUb num den : ℕ) : ℝ) / (scaleS : ℝ) := by
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  unfold expNegUb
  split_ifs with h0 h40
  · have hnum0 : num = 0 := beq_iff_eq.mp h0
    subst hnum0
    simp [div_self hS.ne']
  · have hge40 : (40 : ℝ) ≤ (num : ℝ) / (den : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hden)]
      exact_mod_cast h40
    have hexp_ge2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hexp40 : (scaleS : ℝ) ≤ Real.exp 40 := by
      have hpow : (2 : ℝ) ^ 40 ≤ Real.exp 1 ^ 40 := pow_le_pow_left₀ (by norm_num) hexp_ge2 40
      have he40 : Real.exp 1 ^ 40 = Real.exp 40 := by rw [← Real.exp_natCast_mul]; norm_num
      have h240 : (scaleS : ℝ) ≤ (2 : ℝ) ^ 40 := by unfold scaleS; norm_num
      linarith
    have hexp_ge_S : (scaleS : ℝ) ≤ Real.exp ((num : ℝ) / (den : ℝ)) :=
      hexp40.trans (Real.exp_le_exp.mpr hge40)
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le hS hexp_ge_S
  · have hE_pos : 0 < expGe num den := lt_of_lt_of_le (by unfold scaleS; omega) (expGe_ge_scaleS num den)
    have hE_real_pos : (0 : ℝ) < (expGe num den : ℝ) := by exact_mod_cast hE_pos
    have hE := expGe_sound (num := num) hden
    have hinv : Real.exp (-((num : ℝ) / (den : ℝ))) ≤ (scaleS : ℝ) / (expGe num den : ℝ) := by
      rw [Real.exp_neg, ← one_div]
      have h1 := one_div_le_one_div_of_le (div_pos hE_real_pos hS) hE
      rwa [one_div_div] at h1
    have hceil := real_le_ceilDiv' (a := scaleS * scaleS) hE_pos
    have hdiv : (scaleS : ℝ) / (expGe num den : ℝ) =
        (((scaleS : ℝ) * (scaleS : ℝ)) / (expGe num den : ℝ)) / (scaleS : ℝ) := by
      field_simp [hS.ne', hE_real_pos.ne']
    refine hinv.trans ?_
    rw [hdiv]
    exact div_le_div_of_nonneg_right (by simpa [Nat.cast_mul] using hceil) hS.le

end RayCertLogExp

end

end BuchstabSwitching
