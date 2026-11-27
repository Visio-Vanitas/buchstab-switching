import BuchstabSwitching.Sieve.OddSquarefreeBounds.OddHarmonic
import BuchstabSwitching.Sieve.OddSquarefreeBounds.JOddConvolution
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Asymptotic Enclosure for `J_odd`

Provides tail summability for `h_J`, `H_0`, `H_quarter`, `C_J`, and `J_odd_asymptotic_enclosure`:
`|J_odd X - H₀ * ((1/2) * log X + α₀)| ≤ C_J * X^{-1/4}`.
-/

namespace BuchstabSwitching

section JOddAsymptoticEnclosure

/-- Product formula for `∑_{b ∈ B_cubefree S} |h_J(b)| b^{1/4}`. -/
lemma sum_B_cubefree_abs_rpow (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p) :
    ∑ b ∈ B_cubefree S, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) =
      ∏ p ∈ S, (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
        ((p : ℝ) * ((p : ℝ) - 2))) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp [B_cubefree_empty, h_J_one]
  | @insert p s hps ih =>
    have hp := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime ∧ 2 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [B_cubefree_insert hp.1 hp.2 hps hs,
      Finset.sum_image (B_cubefree_insert_injOn hp.1 hps),
      Finset.sum_product, Finset.prod_insert hps, ← ih hs, mul_comm (1 + _), Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb_pf : b.primeFactors ⊆ s := (Finset.mem_filter.mp hb).2.2.1
    have hcop : b.Coprime p := by
      refine hp.1.coprime_iff_not_dvd.mpr (fun hdvd => ?_) |>.symm
      have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1; omega
      exact hps (hb_pf (Nat.mem_primeFactors.mpr ⟨hp.1, hdvd, hb0⟩))
    have hsum3 : ∀ j : ℕ, j ∈ ({0, 1, 2} : Finset ℕ) →
        |h_J (b * p ^ j)| * ((b * p ^ j : ℕ) : ℝ) ^ (1 / 4 : ℝ) =
          (|h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) * (|h_J (p ^ j)| * ((p ^ j : ℕ) : ℝ) ^ (1 / 4 : ℝ)) := by
      intro j _
      rw [h_J_mul_of_coprime (hcop.pow_right j), abs_mul, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring
    rw [Finset.sum_congr rfl hsum3, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2
    have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have h0 : |h_J (p ^ 0)| * ((p ^ 0 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = 1 := by simp [h_J_one]
    have h1 : |h_J (p ^ 1)| * ((p ^ 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) =
        2 * (p : ℝ) ^ (1 / 4 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
      rw [pow_one, h_J_prime hp.1 hp.2, abs_of_nonneg (by positivity)]
      ring
    have h2 : |h_J (p ^ 2)| * ((p ^ 2 : ℕ) : ℝ) ^ (1 / 4 : ℝ) =
        (p : ℝ) ^ (1 / 2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
      rw [h_J_prime_sq hp.1 hp.2]
      have habs : |-1 / ((p : ℝ) * ((p : ℝ) - 2))| = 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
        rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
      have hrpow : ((p ^ 2 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = (p : ℝ) ^ (1 / 2 : ℝ) := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [habs, hrpow]
      ring
    rw [h0, h1, h2]
    ring

/-- Product formula for `∑_{b ∈ B_cubefree S} h_J(b)`. -/
lemma sum_B_cubefree_h_J (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p) :
    ∑ b ∈ B_cubefree S, h_J b =
      ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
  classical
  induction S using Finset.induction with
  | empty => simp [B_cubefree_empty, h_J_one]
  | @insert p s hps ih =>
    have hp := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime ∧ 2 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [B_cubefree_insert hp.1 hp.2 hps hs,
      Finset.sum_image (B_cubefree_insert_injOn hp.1 hps),
      Finset.sum_product, Finset.prod_insert hps, ← ih hs, mul_comm (1 + _), Finset.sum_mul]
    dsimp only
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb_pf : b.primeFactors ⊆ s := (Finset.mem_filter.mp hb).2.2.1
    have hcop : b.Coprime p := by
      refine hp.1.coprime_iff_not_dvd.mpr (fun hdvd => ?_) |>.symm
      have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1; omega
      exact hps (hb_pf (Nat.mem_primeFactors.mpr ⟨hp.1, hdvd, hb0⟩))
    have hsum3 : ∀ j ∈ ({0, 1, 2} : Finset ℕ), h_J (b * p ^ j) = h_J b * h_J (p ^ j) :=
      fun j _ => h_J_mul_of_coprime (hcop.pow_right j)
    rw [Finset.sum_congr rfl hsum3, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
      pow_zero, pow_one, h_J_one, h_J_prime hp.1 hp.2, h_J_prime_sq hp.1 hp.2]
    ring

/-- Exact vanishing `∑_{b ∈ B_cubefree S} h_J(b) * log b = 0` for every finite set `S` of odd primes. -/
lemma sum_B_cubefree_h_J_mul_log (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p) :
    ∑ b ∈ B_cubefree S, h_J b * Real.log (b : ℝ) = 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp [B_cubefree_empty]
  | @insert p s hps ih =>
    have hp := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime ∧ 2 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [B_cubefree_insert hp.1 hp.2 hps hs,
      Finset.sum_image (B_cubefree_insert_injOn hp.1 hps),
      Finset.sum_product]
    dsimp only
    have hinner : ∀ b ∈ B_cubefree s,
        ∑ j ∈ ({0, 1, 2} : Finset ℕ), h_J (b * p ^ j) * Real.log ((b * p ^ j : ℕ) : ℝ) =
          (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) * (h_J b * Real.log (b : ℝ)) := by
      intro b hb
      have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1; omega
      have hb_real_ne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
      have hp_real_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.1.ne_zero
      have hb_pf : b.primeFactors ⊆ s := (Finset.mem_filter.mp hb).2.2.1
      have hcop : b.Coprime p := by
        refine hp.1.coprime_iff_not_dvd.mpr (fun hdvd => ?_) |>.symm
        exact hps (hb_pf (Nat.mem_primeFactors.mpr ⟨hp.1, hdvd, hb0⟩))
      rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
      have hlog0 : Real.log ((b * p ^ 0 : ℕ) : ℝ) = Real.log (b : ℝ) := by simp
      have hlog1 : Real.log ((b * p ^ 1 : ℕ) : ℝ) = Real.log (b : ℝ) + Real.log (p : ℝ) := by
        push_cast; rw [pow_one, Real.log_mul hb_real_ne hp_real_ne]
      have hlog2 : Real.log ((b * p ^ 2 : ℕ) : ℝ) = Real.log (b : ℝ) + 2 * Real.log (p : ℝ) := by
        push_cast
        rw [Real.log_mul hb_real_ne (pow_ne_zero 2 hp_real_ne), Real.log_pow]
        ring
      rw [h_J_mul_of_coprime (hcop.pow_right 0), h_J_mul_of_coprime (hcop.pow_right 1),
        h_J_mul_of_coprime (hcop.pow_right 2), hlog0, hlog1, hlog2,
        pow_zero, pow_one, h_J_one, h_J_prime hp.1 hp.2, h_J_prime_sq hp.1 hp.2]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ih hs, mul_zero]

lemma summable_abs_h_J_mul_rpow :
    Summable (fun b : ℕ => |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) := by
  have hz32 : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  set C_bd : ℝ := Real.exp (9 * ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹)
  refine summable_of_sum_range_le (c := C_bd) (fun b => by positivity) (fun M => ?_)
  set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
  have hP : ∀ p ∈ P, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
  have hsub : (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2) ⊆
      B_cubefree P := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, B_cubefree, Finset.mem_Icc] at hb ⊢
    rcases hb with ⟨hbM, hb_odd, hb_fac⟩
    have hb0 : b ≠ 0 := by intro h0; subst h0; exact absurd hb_odd (by decide)
    have hb_pf : b.primeFactors ⊆ P := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd := Nat.dvd_of_mem_primeFactors hp
      have hp_ne2 : p ≠ 2 := by
        intro h2; subst h2
        exact Nat.not_even_iff_odd.mpr hb_odd (even_iff_two_dvd.mpr hp_dvd)
      have hp_le : p ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hp_dvd
      have hp_ge2 : 2 ≤ p := hp_prime.two_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, by omega⟩
    have hb_le : b ≤ ∏ p ∈ P, p ^ 2 := by
      have h_eq : b = ∏ p ∈ b.primeFactors, p ^ b.factorization p :=
        (prod_primeFactors_pow_factorization hb0).symm
      calc b = ∏ p ∈ b.primeFactors, p ^ b.factorization p := h_eq
        _ ≤ ∏ p ∈ b.primeFactors, p ^ 2 := by
            refine Finset.prod_le_prod fun p hp => ?_
            exact Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (hb_fac p hp)
        _ ≤ ∏ p ∈ P, p ^ 2 := by
            refine Finset.prod_le_prod_of_subset_of_one_le hb_pf fun p hp _ => ?_
            exact Nat.one_le_pow 2 p (hP p hp).1.pos
    exact ⟨⟨Nat.pos_of_ne_zero hb0, hb_le⟩, hb_odd, hb_pf, hb_fac⟩
  have hsum_eq : ∑ b ∈ Finset.range M, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) =
      ∑ b ∈ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2),
        |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hcond : Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2
    · exact (ite_eq_left hcond).symm
    · have hh0 : h_J b = 0 := by unfold h_J; exact ite_eq_right hcond
      rw [ite_eq_right hcond, hh0, abs_zero, zero_mul]
  have hprod_le_exp : ∏ p ∈ P, (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
      ((p : ℝ) * ((p : ℝ) - 2))) ≤ C_bd := by
    have hprod_gen : ∀ (S : Finset ℕ), (∀ p ∈ S, 2 < p) →
        ∏ p ∈ S, (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
          ((p : ℝ) * ((p : ℝ) - 2))) ≤
          ∏ p ∈ S, Real.exp ((2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
            ((p : ℝ) * ((p : ℝ) - 2))) := by
      intro S hS
      classical
      induction S using Finset.induction with
      | empty => simp
      | @insert a s has ih =>
        rw [Finset.prod_insert has, Finset.prod_insert has]
        have ha3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hS a (Finset.mem_insert_self a s)
        have ha2_pos : (0 : ℝ) < (a : ℝ) - 2 := by linarith
        have ha_nn : (0 : ℝ) ≤ 1 + (2 * (a : ℝ) ^ (1 / 4 : ℝ) + (a : ℝ) ^ (1 / 2 : ℝ)) /
            ((a : ℝ) * ((a : ℝ) - 2)) := by positivity
        have ha_le : 1 + (2 * (a : ℝ) ^ (1 / 4 : ℝ) + (a : ℝ) ^ (1 / 2 : ℝ)) /
            ((a : ℝ) * ((a : ℝ) - 2)) ≤
            Real.exp ((2 * (a : ℝ) ^ (1 / 4 : ℝ) + (a : ℝ) ^ (1 / 2 : ℝ)) /
              ((a : ℝ) * ((a : ℝ) - 2))) := by
          rw [add_comm]; exact Real.add_one_le_exp _
        have hs_nn : (0 : ℝ) ≤ ∏ p ∈ s, (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
            ((p : ℝ) * ((p : ℝ) - 2))) := by
          refine Finset.prod_nonneg fun p hp => ?_
          have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p (Finset.mem_insert_of_mem hp)
          have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
          positivity
        exact mul_le_mul ha_le (ih fun p hp => hS p (Finset.mem_insert_of_mem hp)) hs_nn
          (le_trans ha_nn ha_le)
    have h1 := hprod_gen P fun p hp => (hP p hp).2
    rw [← Real.exp_sum] at h1
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have hpt : ∀ p ∈ P, (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
        ((p : ℝ) * ((p : ℝ) - 2)) ≤ 9 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      intro p hp
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).2
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
      have hr1 : (p : ℝ) ^ (1 / 4 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
      have hnum : 2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ) ≤ 3 * (p : ℝ) ^ (1 / 2 : ℝ) := by
        linarith
      have hden : (p : ℝ) ^ 2 / 3 ≤ (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
      have hrpow_id : (p : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) ^ 2 = ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_sub (by positivity),
          ← Real.rpow_neg (by positivity)]
        congr 1; norm_num
      have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      calc (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2))
          ≤ (3 * (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2)) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (3 * (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) ^ 2 / 3) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = 9 * ((p : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) ^ 2) := by ring
        _ = 9 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by rw [hrpow_id]
    calc ∑ p ∈ P, (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
            ((p : ℝ) * ((p : ℝ) - 2))
        ≤ ∑ p ∈ P, 9 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := Finset.sum_le_sum hpt
      _ = 9 * ∑ p ∈ P, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := (Finset.mul_sum P _ _).symm
      _ ≤ 9 * ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact hz32.sum_le_tsum P (fun _ _ => by positivity)
  calc ∑ b ∈ Finset.range M, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)
      = ∑ b ∈ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2),
          |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) := hsum_eq
    _ ≤ ∑ b ∈ B_cubefree P, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∏ p ∈ P, (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
          ((p : ℝ) * ((p : ℝ) - 2))) := sum_B_cubefree_abs_rpow P hP
    _ ≤ C_bd := hprod_le_exp

lemma summable_h_J : Summable h_J := by
  have hnorm : Summable (fun b : ℕ => ‖h_J b‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun b => ?_)
      summable_abs_h_J_mul_rpow
    rw [Real.norm_eq_abs]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [h_J_zero]
    · have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb0
      have hr : (1 : ℝ) ≤ (b : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hb1 (by norm_num)
      calc |h_J b| = |h_J b| * 1 := (mul_one _).symm
        _ ≤ |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  exact hnorm.of_norm

lemma summable_abs_h_J_mul_log : Summable (fun b : ℕ => |h_J b * Real.log (b : ℝ)|) := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun b => ?_)
    (summable_abs_h_J_mul_rpow.mul_left 4)
  rw [abs_mul]
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [h_J_zero]
  · have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb0
    have hlog_nn : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
    have hlog_le : |Real.log (b : ℝ)| ≤ 4 * (b : ℝ) ^ (1 / 4 : ℝ) := by
      rw [abs_of_nonneg hlog_nn]
      have hr : Real.log ((b : ℝ) ^ (1 / 4 : ℝ)) ≤ (b : ℝ) ^ (1 / 4 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_rpow (by positivity)] at hr
      linarith
    calc |h_J b| * |Real.log (b : ℝ)| ≤ |h_J b| * (4 * (b : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_le (abs_nonneg _)
      _ = 4 * (|h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) := by ring

lemma summable_h_J_mul_log : Summable (fun b : ℕ => h_J b * Real.log (b : ℝ)) :=
  (summable_abs_h_J_mul_log.congr fun _ => (Real.norm_eq_abs _).symm).of_norm

lemma tsum_h_J_mul_log_eq_zero : (∑' b : ℕ, h_J b * Real.log (b : ℝ)) = 0 := by
  let g : ℕ → ℝ := fun b => h_J b * Real.log (b : ℝ)
  have hbound : ∀ M : ℕ, |∑ b ∈ Finset.range M, g b| ≤
      (∑' b : ℕ, |g b|) - ∑ b ∈ Finset.range M, |g b| := by
    intro M
    set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
    have hP : ∀ p ∈ P, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
    have hB_zero : ∑ b ∈ B_cubefree P, g b = 0 := sum_B_cubefree_h_J_mul_log P hP
    have hsub_range : (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2) ⊆
        B_cubefree P := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_range, B_cubefree, Finset.mem_Icc] at hb ⊢
      rcases hb with ⟨hbM, hb_odd, hb_fac⟩
      have hb0 : b ≠ 0 := by intro h0; subst h0; exact absurd hb_odd (by decide)
      have hb_pf : b.primeFactors ⊆ P := by
        intro p hp
        have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        have hp_ne2 : p ≠ 2 := by
          intro h2; subst h2
          exact Nat.not_even_iff_odd.mpr hb_odd (even_iff_two_dvd.mpr hp_dvd)
        have hp_le : p ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hp_dvd
        have hp_ge2 : 2 ≤ p := hp_prime.two_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, by omega⟩
      have hb_le : b ≤ ∏ p ∈ P, p ^ 2 := by
        have h_eq : b = ∏ p ∈ b.primeFactors, p ^ b.factorization p :=
          (prod_primeFactors_pow_factorization hb0).symm
        calc b = ∏ p ∈ b.primeFactors, p ^ b.factorization p := h_eq
          _ ≤ ∏ p ∈ b.primeFactors, p ^ 2 := by
              refine Finset.prod_le_prod fun p hp => ?_
              exact Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (hb_fac p hp)
          _ ≤ ∏ p ∈ P, p ^ 2 := by
              refine Finset.prod_le_prod_of_subset_of_one_le hb_pf fun p hp _ => ?_
              exact Nat.one_le_pow 2 p (hP p hp).1.pos
      exact ⟨⟨Nat.pos_of_ne_zero hb0, hb_le⟩, hb_odd, hb_pf, hb_fac⟩
    have hrange_eq : ∑ b ∈ Finset.range M, g b =
        ∑ b ∈ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2), g b := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hcond : Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2
      · exact (ite_eq_left hcond).symm
      · have hh0 : h_J b = 0 := by unfold h_J; exact ite_eq_right hcond
        rw [ite_eq_right hcond]
        simp [g, hh0]
    have hsplit : ∑ b ∈ B_cubefree P, g b =
        (∑ b ∈ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2), g b) +
          ∑ b ∈ B_cubefree P \ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2), g b := by
      exact (Finset.sum_sdiff hsub_range).symm.trans (add_comm _ _)
    have hdiff_eq : ∑ b ∈ Finset.range M, g b =
        -(∑ b ∈ B_cubefree P \ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2), g b) := by
      linarith
    have hdisj : Disjoint (Finset.range M)
        (B_cubefree P \ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2)) := by
      rw [Finset.disjoint_left]
      intro b hbM hbs
      rw [Finset.mem_sdiff] at hbs
      apply hbs.2
      have hcond := (Finset.mem_filter.mp hbs.1).2
      exact Finset.mem_filter.mpr ⟨hbM, hcond.1, hcond.2.2⟩
    calc |∑ b ∈ Finset.range M, g b|
        = |∑ b ∈ B_cubefree P \ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2), g b| := by
          rw [hdiff_eq, abs_neg]
      _ ≤ ∑ b ∈ B_cubefree P \ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2), |g b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑' b : ℕ, |g b|) - ∑ b ∈ Finset.range M, |g b| := by
          have hsum_union : (∑ b ∈ Finset.range M, |g b|) +
              (∑ b ∈ B_cubefree P \ (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2), |g b|) ≤
              ∑' b : ℕ, |g b| := by
            rw [← Finset.sum_union hdisj]
            exact summable_abs_h_J_mul_log.sum_le_tsum _ (fun _ _ => abs_nonneg _)
          linarith
  have ht1 : Filter.Tendsto (fun M : ℕ => |∑ b ∈ Finset.range M, g b|)
      Filter.atTop (nhds |∑' b : ℕ, g b|) :=
    (summable_h_J_mul_log.hasSum.tendsto_sum_nat).abs
  have ht2 : Filter.Tendsto (fun M : ℕ => (∑' b : ℕ, |g b|) - ∑ b ∈ Finset.range M, |g b|)
      Filter.atTop (nhds ((∑' b : ℕ, |g b|) - (∑' b : ℕ, |g b|))) :=
    tendsto_const_nhds.sub summable_abs_h_J_mul_log.hasSum.tendsto_sum_nat
  rw [sub_self] at ht2
  have hle0 : |∑' b : ℕ, g b| ≤ 0 := le_of_tendsto_of_tendsto' ht1 ht2 hbound
  exact abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))

/-- Main Euler-product constant `H₀ = ∑_{Odd b} h_J(b) = ∏_{p > 2} (1 + 1/(p(p-2)))`. -/
noncomputable def H_0 : ℝ := ∑' b : ℕ, h_J b

/-- Weighted absolute-sum constant `H_{1/4} = ∑_{Odd b} |h_J(b)| b^{1/4}`. -/
noncomputable def H_quarter : ℝ := ∑' b : ℕ, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)

/-- Explicit error constant `C_J = (α₀ + C_{f₀}) * H_{1/4}` matching `constants.py:132`. -/
noncomputable def C_J : ℝ := (alpha0 + C_F0) * H_quarter

lemma H_quarter_nonneg : 0 ≤ H_quarter :=
  tsum_nonneg (fun b => by positivity)

/-- Critical-point bound `|(1/2) log t - α₀| ≤ α₀ * t^{1/4}` for all `t ≥ 1`. -/
lemma abs_half_log_sub_alpha0_le (t : ℝ) (ht : 1 ≤ t) :
    |(1 / 2 : ℝ) * Real.log t - alpha0| ≤ alpha0 * t ^ (1 / 4 : ℝ) := by
  have ha0 := alpha0_pos
  have hr1 : 1 ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht
  rw [abs_le]
  constructor
  · nlinarith
  · set u : ℝ := (1 / 4 : ℝ) * Real.log t
    have hu_exp : t ^ (1 / 4 : ℝ) = Real.exp u := by
      rw [Real.rpow_def_of_pos (by linarith)]
      congr 1; ring
    have hlog_u : (1 / 2 : ℝ) * Real.log t = 2 * u := by dsimp only [u]; ring
    rw [hu_exp, hlog_u]
    by_cases hu_small : 2 * u - alpha0 ≤ 0
    · linarith [mul_pos ha0 (Real.exp_pos u)]
    · push Not at hu_small
      set u0 : ℝ := 1 + alpha0 / 2
      have htan : 1 + (u - u0) ≤ Real.exp (u - u0) := by
        linarith [Real.add_one_le_exp (u - u0)]
      have hexp_ge : Real.exp u0 * (1 + u - u0) ≤ Real.exp u := by
        have h1 : Real.exp u = Real.exp u0 * Real.exp (u - u0) := by
          rw [← Real.exp_add]; ring_nf
        rw [h1]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos u0).le
      have hcrit : 2 ≤ alpha0 * Real.exp u0 := by
        have hgam_lo : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
          Real.one_half_lt_eulerMascheroniConstant
        have hlog2_lo : (0.693 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
        have ha0_lo : (0.5965 : ℝ) < alpha0 := by unfold alpha0; linarith
        have hexp1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
        have hexp_rem : 1 + alpha0 / 2 ≤ Real.exp (alpha0 / 2) := by
          have := Real.add_one_le_exp (alpha0 / 2)
          linarith
        have hprod_exp : Real.exp u0 = Real.exp 1 * Real.exp (alpha0 / 2) := by
          dsimp only [u0]; rw [← Real.exp_add]
        have h1 : (1.29825 : ℝ) < 1 + alpha0 / 2 := by linarith
        have h2 : (3.528 : ℝ) < Real.exp u0 := by
          rw [hprod_exp]
          nlinarith [Real.exp_pos (alpha0 / 2)]
        nlinarith
      have hpos_factor : 0 ≤ 1 + u - u0 := by dsimp only [u0]; linarith
      calc 2 * u - alpha0 = 2 * (1 + u - u0) := by dsimp only [u0]; ring
        _ ≤ (alpha0 * Real.exp u0) * (1 + u - u0) :=
            mul_le_mul_of_nonneg_right hcrit hpos_factor
        _ = alpha0 * (Real.exp u0 * (1 + u - u0)) := by ring
        _ ≤ alpha0 * Real.exp u := mul_le_mul_of_nonneg_left hexp_ge ha0.le

/-- Asymptotic enclosure `|J_odd X - H₀ * ((1/2) * log X + α₀)| ≤ C_J * X^{-1/4}` for `X ≥ 1`. -/
theorem J_odd_asymptotic_enclosure (X : ℝ) (hX : 1 ≤ X) :
    |J_odd X - H_0 * ((1 / 2 : ℝ) * Real.log X + alpha0)| ≤ C_J * X ^ (-(1 / 4 : ℝ)) := by
  set N : ℕ := Nat.floor X
  have hX_pos : 0 < X := by linarith
  have hN_le_X : (N : ℝ) ≤ X := Nat.floor_le hX_pos.le
  have hX_lt_N1 : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
  rw [J_odd_eq_sum_h_J X hX]
  -- Write J_odd X as ∑_{b ≤ N} h_J b * oddHarmonicSum (X / b)
  have hsum_Icc : ∑ b ∈ (Finset.Icc 1 N).filter Odd, h_J b * oddHarmonicSum (X / (b : ℝ)) =
      ∑ b ∈ Finset.range (N + 1),
        (if 1 ≤ b then h_J b * oddHarmonicSum (X / (b : ℝ)) else 0) := by
    have h1 : (Finset.Icc 1 N).filter Odd ⊆ Finset.range (N + 1) := by
      intro b hb; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hb ⊢; omega
    have h2 : ∑ b ∈ Finset.range (N + 1),
        (if 1 ≤ b then h_J b * oddHarmonicSum (X / (b : ℝ)) else 0) =
        ∑ b ∈ (Finset.Icc 1 N).filter Odd,
          (if 1 ≤ b then h_J b * oddHarmonicSum (X / (b : ℝ)) else 0) := by
      symm
      refine Finset.sum_subset h1 ?_
      intro b hb hnb
      simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hb hnb
      by_cases hb1 : 1 ≤ b
      · have hnot_odd : ¬ Odd b := fun ho => hnb ⟨⟨hb1, by omega⟩, ho⟩
        have hh0 : h_J b = 0 := by unfold h_J; simp [hnot_odd]
        simp [hb1, hh0]
      · simp [hb1]
    rw [h2]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    simp [hb1]
  rw [hsum_Icc]
  -- Expand H₀ * ((1/2) log X + α₀) via ∑' b, h_J b = H₀ and ∑' b, h_J b * log b = 0
  let L : ℝ := (1 / 2 : ℝ) * Real.log X + alpha0
  have hmain_id : H_0 * L =
      (∑ b ∈ Finset.range (N + 1), h_J b * L) -
        (1 / 2 : ℝ) * (∑ b ∈ Finset.range (N + 1), h_J b * Real.log (b : ℝ)) +
        ∑' i : ℕ, h_J (i + (N + 1)) * (L - (1 / 2 : ℝ) * Real.log ((i + (N + 1) : ℕ) : ℝ)) := by
    have h1 : H_0 * L = ∑' b : ℕ, h_J b * L := by
      unfold H_0; rw [← tsum_mul_right]
    have h2 : (0 : ℝ) = -(1 / 2 : ℝ) * ∑' b : ℕ, h_J b * Real.log (b : ℝ) := by
      rw [tsum_h_J_mul_log_eq_zero, mul_zero]
    have hsum_L : Summable (fun b : ℕ => h_J b * L) := summable_h_J.mul_right L
    have hsum_log : Summable (fun b : ℕ => -(1 / 2 : ℝ) * (h_J b * Real.log (b : ℝ))) :=
      summable_h_J_mul_log.mul_left (-(1 / 2 : ℝ))
    have hsum_comb : Summable (fun b : ℕ => h_J b * (L - (1 / 2 : ℝ) * Real.log (b : ℝ))) := by
      convert hsum_L.add hsum_log using 1
      ext b; ring
    have htsum_eq : H_0 * L = ∑' b : ℕ, h_J b * (L - (1 / 2 : ℝ) * Real.log (b : ℝ)) := by
      calc H_0 * L = H_0 * L + 0 := (add_zero _).symm
        _ = (∑' b : ℕ, h_J b * L) + (-(1 / 2 : ℝ) * ∑' b : ℕ, h_J b * Real.log (b : ℝ)) := by
            rw [← h1, ← h2]
        _ = (∑' b : ℕ, h_J b * L) + ∑' b : ℕ, (-(1 / 2 : ℝ) * (h_J b * Real.log (b : ℝ))) := by
            rw [tsum_mul_left]
        _ = ∑' b : ℕ, h_J b * (L - (1 / 2 : ℝ) * Real.log (b : ℝ)) := by
            rw [← hsum_L.tsum_add hsum_log]
            refine tsum_congr fun b => by ring
    rw [htsum_eq, ← hsum_comb.sum_add_tsum_nat_add (N + 1)]
    congr 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by ring
  -- Express difference as finite error sum + tail sum
  let E_fin : ℝ := ∑ b ∈ Finset.range (N + 1),
    (if 1 ≤ b then h_J b * (oddHarmonicSum (X / (b : ℝ)) -
      ((1 / 2 : ℝ) * Real.log (X / (b : ℝ)) + alpha0)) else 0)
  let E_tail : ℝ := ∑' i : ℕ,
    h_J (i + (N + 1)) * ((1 / 2 : ℝ) * Real.log ((i + (N + 1) : ℕ) : ℝ) - L)
  have hdiff_eq : (∑ b ∈ Finset.range (N + 1),
        (if 1 ≤ b then h_J b * oddHarmonicSum (X / (b : ℝ)) else 0)) - H_0 * L =
      E_fin + E_tail := by
    rw [hmain_id]
    have hfin_eq : (∑ b ∈ Finset.range (N + 1),
          (if 1 ≤ b then h_J b * oddHarmonicSum (X / (b : ℝ)) else 0)) -
        ((∑ b ∈ Finset.range (N + 1), h_J b * L) -
          (1 / 2 : ℝ) * ∑ b ∈ Finset.range (N + 1), h_J b * Real.log (b : ℝ)) = E_fin := by
      have h0 : ∑ b ∈ Finset.range (N + 1), h_J b * L =
          ∑ b ∈ Finset.range (N + 1), (if 1 ≤ b then h_J b * L else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb1 : 1 ≤ b
        · simp [hb1]
        · have hb0 : b = 0 := by omega
          subst hb0; simp [h_J_zero]
      have h0' : ∑ b ∈ Finset.range (N + 1), h_J b * Real.log (b : ℝ) =
          ∑ b ∈ Finset.range (N + 1), (if 1 ≤ b then h_J b * Real.log (b : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb1 : 1 ≤ b
        · simp [hb1]
        · have hb0 : b = 0 := by omega
          subst hb0; simp [h_J_zero]
      rw [h0, h0', Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb1 : 1 ≤ b
      · have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
        have hlog_div := Real.log_div hX_pos.ne' hb_pos.ne'
        simp only [hb1, ↓reduceIte, L]
        rw [hlog_div]
        ring
      · simp [hb1]
    have htail_neg : -(∑' i : ℕ, h_J (i + (N + 1)) *
        (L - (1 / 2 : ℝ) * Real.log ((i + (N + 1) : ℕ) : ℝ))) = E_tail := by
      rw [← tsum_neg]
      refine tsum_congr fun i => by ring
    linarith
  rw [hdiff_eq]
  -- Bound |E_fin| and |E_tail|
  have hE_fin : |E_fin| ≤
      (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) *
        ∑ b ∈ Finset.range (N + 1), |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) := by
    calc |E_fin|
        ≤ ∑ b ∈ Finset.range (N + 1),
            |if 1 ≤ b then h_J b * (oddHarmonicSum (X / (b : ℝ)) -
              ((1 / 2 : ℝ) * Real.log (X / (b : ℝ)) + alpha0)) else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.range (N + 1),
            (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) * (|h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) := by
          refine Finset.sum_le_sum fun b hb => ?_
          by_cases hb1 : 1 ≤ b
          · simp only [hb1, ↓reduceIte, abs_mul]
            have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
            have hb_le_N : b ≤ N := by have := Finset.mem_range.mp hb; omega
            have hb_le_X : (b : ℝ) ≤ X := (by exact_mod_cast hb_le_N : (b : ℝ) ≤ N).trans hN_le_X
            have hXb : 1 ≤ X / (b : ℝ) := (one_le_div hb_pos).mpr hb_le_X
            have hE := oddHarmonicSum_sub_asym_abs_le (X / (b : ℝ)) hXb
            have hbx_le1 : (b : ℝ) / X ≤ 1 := (div_le_one hX_pos).mpr hb_le_X
            have hbx_rpow : (b : ℝ) / X ≤ ((b : ℝ) / X) ^ (1 / 4 : ℝ) := by
              calc (b : ℝ) / X = ((b : ℝ) / X) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ ((b : ℝ) / X) ^ (1 / 4 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_ge (div_pos hb_pos hX_pos) hbx_le1 (by norm_num)
            have hbx_eq : ((b : ℝ) / X) ^ (1 / 4 : ℝ) = X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ) := by
              rw [Real.div_rpow hb_pos.le hX_pos.le, Real.rpow_neg hX_pos.le]
              ring
            have hCF_le : C_F0 / (X / (b : ℝ)) ≤ (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ) := by
              have h1 : C_F0 / (X / (b : ℝ)) = C_F0 * ((b : ℝ) / X) := by field_simp
              have h2 : C_F0 * ((b : ℝ) / X) ≤ C_F0 * (X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_left (hbx_rpow.trans_eq hbx_eq) C_F0_pos.le
              have h3 : C_F0 ≤ alpha0 + C_F0 := by linarith [alpha0_pos]
              have h4 : C_F0 * (X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ)) ≤
                  (alpha0 + C_F0) * (X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_right h3 (by positivity)
              linarith
            calc |h_J b| * |oddHarmonicSum (X / (b : ℝ)) - ((1 / 2 : ℝ) * Real.log (X / (b : ℝ)) + alpha0)|
                ≤ |h_J b| * (C_F0 / (X / (b : ℝ))) :=
                  mul_le_mul_of_nonneg_left hE (abs_nonneg _)
              _ ≤ |h_J b| * ((alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hCF_le (abs_nonneg _)
              _ = (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) * (|h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) := by ring
          · simp only [hb1, ↓reduceIte, abs_zero]
            have : (0 : ℝ) ≤ alpha0 + C_F0 := by linarith [alpha0_pos, C_F0_pos]
            positivity
      _ = (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) *
            ∑ b ∈ Finset.range (N + 1), |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) :=
          (Finset.mul_sum _ _ _).symm
  have hE_tail : |E_tail| ≤
      (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) *
        ∑' i : ℕ, |h_J (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
    have hshift_sum : Summable (fun i : ℕ =>
        |h_J (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ)) :=
      summable_abs_h_J_mul_rpow.comp_injective (add_left_injective (N + 1))
    have hterm : ∀ i : ℕ,
        ‖h_J (i + (N + 1)) * ((1 / 2 : ℝ) * Real.log ((i + (N + 1) : ℕ) : ℝ) - L)‖ ≤
          (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) *
            (|h_J (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ)) := by
      intro i
      rw [Real.norm_eq_abs, abs_mul]
      set b : ℕ := i + (N + 1)
      have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
      have hb_gt_X : X < (b : ℝ) := by
        have h1 : N + 1 ≤ b := by dsimp only [b]; omega
        have h2 : (N : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast h1
        linarith
      have hbX_ge1 : 1 ≤ (b : ℝ) / X := (one_le_div hX_pos).mpr hb_gt_X.le
      have hlog_eq : (1 / 2 : ℝ) * Real.log (b : ℝ) - L =
          (1 / 2 : ℝ) * Real.log ((b : ℝ) / X) - alpha0 := by
        dsimp only [L]; rw [Real.log_div hb_pos.ne' hX_pos.ne']; ring
      have hcrit := abs_half_log_sub_alpha0_le ((b : ℝ) / X) hbX_ge1
      have hbx_eq : ((b : ℝ) / X) ^ (1 / 4 : ℝ) = X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ) := by
        rw [Real.div_rpow hb_pos.le hX_pos.le, Real.rpow_neg hX_pos.le]
        ring
      have ha_le : alpha0 ≤ alpha0 + C_F0 := by linarith [C_F0_pos]
      rw [hlog_eq]
      calc |h_J b| * |(1 / 2 : ℝ) * Real.log ((b : ℝ) / X) - alpha0|
          ≤ |h_J b| * (alpha0 * (X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ))) := by
            rw [← hbx_eq]
            exact mul_le_mul_of_nonneg_left hcrit (abs_nonneg _)
        _ ≤ |h_J b| * ((alpha0 + C_F0) * (X ^ (-(1 / 4 : ℝ)) * (b : ℝ) ^ (1 / 4 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha_le (by positivity)) (abs_nonneg _)
        _ = (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) * (|h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) := by ring
    have hnorm_sum : Summable (fun i : ℕ =>
        ‖h_J (i + (N + 1)) * ((1 / 2 : ℝ) * Real.log ((i + (N + 1) : ℕ) : ℝ) - L)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
        (hshift_sum.mul_left ((alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ))))
    have h1 : |E_tail| ≤ ∑' i : ℕ,
        ‖h_J (i + (N + 1)) * ((1 / 2 : ℝ) * Real.log ((i + (N + 1) : ℕ) : ℝ) - L)‖ :=
      norm_tsum_le_tsum_norm hnorm_sum
    have h2 : (∑' i : ℕ, ‖h_J (i + (N + 1)) * ((1 / 2 : ℝ) * Real.log ((i + (N + 1) : ℕ) : ℝ) - L)‖) ≤
        ∑' i : ℕ, (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) *
          (|h_J (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ)) :=
      Summable.tsum_le_tsum hterm hnorm_sum
        (hshift_sum.mul_left ((alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ))))
    rw [tsum_mul_left] at h2
    exact h1.trans h2
  have hsplit_Hq : (∑ b ∈ Finset.range (N + 1), |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) +
      (∑' i : ℕ, |h_J (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ)) = H_quarter :=
    summable_abs_h_J_mul_rpow.sum_add_tsum_nat_add (N + 1)
  calc |E_fin + E_tail| ≤ |E_fin| + |E_tail| := abs_add_le _ _
    _ ≤ (alpha0 + C_F0) * X ^ (-(1 / 4 : ℝ)) *
          ((∑ b ∈ Finset.range (N + 1), |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)) +
            ∑' i : ℕ, |h_J (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ) ^ (1 / 4 : ℝ)) := by
        linarith
    _ = C_J * X ^ (-(1 / 4 : ℝ)) := by
        rw [hsplit_Hq]
        unfold C_J
        ring

end JOddAsymptoticEnclosure

end BuchstabSwitching
