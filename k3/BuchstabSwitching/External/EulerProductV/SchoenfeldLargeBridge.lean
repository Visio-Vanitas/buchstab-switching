import BuchstabSwitching.External.EulerProductV.MertensCancel
import BuchstabSwitching.External.SchoenfeldRH.PrimeCountingRH
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Large-Range Mertens Euler-Product Bound (`x ≥ 10^12`) under Schoenfeld RH

Proves `eulerR3_mem_Icc_large`: for `x ≥ 10^12`, assuming `SchoenfeldRHBound li2` and
`MertensPrimeSumPremise meisselMertensConst`,
`1 - 1 / (2 * (Real.log x)^2) ≤ eulerR3 x ≤ 1 + 1 / (2 * (Real.log x)^2)`.

## Proof Strategy
1. Express `∑_{z ≤ p < M} 1/p` (`z = ⌈x⌉`, `M = 4^z`) via `primeCounting` differences and split
   into an `offsetLogIntegral` main term (`li2` cancels) plus a Schoenfeld remainder sum.
2. Bound the main term against `log(log(M - 1)) - log(log(z - 1))` via elementary logarithm
   sandwiches and constant-integrand monotonicity on `[n - 1, n]`.
3. Bound the Schoenfeld remainder sum via discrete Abel summation and an algebraic telescoping
   majorant `F(m) = (2 log m + 6) / √m` for `log n / (n √n)`.
4. Combine with `MertensPrimeSumPremise` at `M = 4^z` and apply `eulerR3_mem_Icc_of_mertens_err`,
   closing the numerical budget for `x ≥ 10^12` via iterated square roots `x = s^16`.
-/

namespace BuchstabSwitching.External

/-! ## 1. Elementary Logarithm, Exponential, and Power Inequalities -/

private lemma exp_one_bounds : (27 / 10 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 3 := by
  constructor
  · have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at hs
    linarith
  · have hbd := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by omega : 0 < 4)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hbd
    linarith [le_of_abs_le hbd]

private lemma log_four_bounds : 1 < Real.log 4 ∧ Real.log 4 < 2 := by
  obtain ⟨he_lo, he_hi⟩ := exp_one_bounds
  constructor
  · exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith)
  · have he2 : (27 / 10 : ℝ) ^ 2 ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) he_lo.le 2
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)

private lemma log_sub_sandwich {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (q - p) / q ≤ Real.log q - Real.log p ∧ Real.log q - Real.log p ≤ (q - p) / p := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  constructor
  · have hle := Real.log_le_sub_one_of_pos (div_pos hp hq)
    rw [Real.log_div hp.ne' hq.ne'] at hle
    have hid : p / q - 1 = -((q - p) / q) := by field_simp [hq.ne']; ring
    linarith
  · have hle := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hle
    have hid : q / p - 1 = (q - p) / p := by field_simp [hp.ne']
    linarith

private lemma log_log_sub_bounds {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    0 ≤ Real.log (Real.log b) - Real.log (Real.log a) ∧
      Real.log (Real.log b) - Real.log (Real.log a) ≤ (b - a) / a := by
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hlog_a_gt1 : 1 < Real.log a :=
    (Real.lt_log_iff_exp_lt ha_pos).mpr (lt_of_lt_of_le exp_one_bounds.2 ha)
  have hlog_le : Real.log a ≤ Real.log b := Real.log_le_log ha_pos hab
  have hs1 := log_sub_sandwich ha_pos hab
  have hs2 := log_sub_sandwich (by linarith : 0 < Real.log a) hlog_le
  refine ⟨sub_nonneg.mpr (Real.log_le_log (by linarith) hlog_le), ?_⟩
  calc Real.log (Real.log b) - Real.log (Real.log a)
      ≤ (Real.log b - Real.log a) / Real.log a := hs2.2
    _ ≤ Real.log b - Real.log a := div_le_self (by linarith) hlog_a_gt1.le
    _ ≤ (b - a) / a := hs1.2

private lemma sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
    calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := hstep
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by ring

private lemma log_le_ten_div_27_mul {s : ℝ} (hs : 0 < s) :
    Real.log s ≤ (10 / 27 : ℝ) * s := by
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hle := Real.log_le_sub_one_of_pos (div_pos hs he_pos)
  rw [Real.log_div hs.ne' he_pos.ne', Real.log_exp] at hle
  have hdiv : s / Real.exp 1 ≤ s / (27 / 10 : ℝ) :=
    div_le_div_of_nonneg_left hs.le (by norm_num) exp_one_bounds.1.le
  linarith

private lemma large_x_log_and_cube {x : ℝ} (hx : (10 : ℝ) ^ 12 ≤ x) :
    25 < Real.log x ∧ (Real.log x) ^ 3 ≤ (1 / 10 : ℝ) * Real.sqrt (x - 1) := by
  have hx_pos : 0 < x := by linarith
  constructor
  · have he25 : Real.exp 25 < (3 : ℝ) ^ 25 := by
      rw [show (25 : ℝ) = ((25 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_lt_pow_left₀ exp_one_bounds.2 (Real.exp_pos 1).le (by omega)
    have hnum : (3 : ℝ) ^ 25 < (10 : ℝ) ^ 12 := by norm_num
    exact (Real.lt_log_iff_exp_lt hx_pos).mpr (by linarith)
  · set s1 : ℝ := Real.sqrt x
    set s2 : ℝ := Real.sqrt s1
    set s3 : ℝ := Real.sqrt s2
    set s : ℝ := Real.sqrt s3
    have hs1_pos : 0 < s1 := Real.sqrt_pos.mpr hx_pos
    have hs2_pos : 0 < s2 := Real.sqrt_pos.mpr hs1_pos
    have hs3_pos : 0 < s3 := Real.sqrt_pos.mpr hs2_pos
    have hs_pos : 0 < s := Real.sqrt_pos.mpr hs3_pos
    have hs_sq : s ^ 2 = s3 := Real.sq_sqrt hs3_pos.le
    have hs3_sq : s3 ^ 2 = s2 := Real.sq_sqrt hs2_pos.le
    have hs2_sq : s2 ^ 2 = s1 := Real.sq_sqrt hs1_pos.le
    have hs1_sq : s1 ^ 2 = x := Real.sq_sqrt hx_pos.le
    have hs8 : s1 = s ^ 8 := by
      calc s1 = s2 ^ 2 := hs2_sq.symm
        _ = (s3 ^ 2) ^ 2 := by rw [hs3_sq]
        _ = ((s ^ 2) ^ 2) ^ 2 := by rw [hs_sq]
        _ = s ^ 8 := by ring
    have hs16 : x = s ^ 16 := by
      calc x = s1 ^ 2 := hs1_sq.symm
        _ = (s ^ 8) ^ 2 := by rw [hs8]
        _ = s ^ 16 := by ring
    have hs5 : (5 : ℝ) ≤ s := by
      by_contra hlt
      push Not at hlt
      have hp16 : s ^ 16 ≤ (5 : ℝ) ^ 16 := pow_le_pow_left₀ hs_pos.le hlt.le 16
      have hnum : (5 : ℝ) ^ 16 < (10 : ℝ) ^ 12 := by norm_num
      linarith
    have hlog_x : Real.log x ≤ 6 * s := by
      rw [hs16, Real.log_pow]
      have hls := log_le_ten_div_27_mul hs_pos
      push_cast
      linarith
    have hlog_nn : 0 ≤ Real.log x := (Real.log_pos (by linarith)).le
    have hcube : (Real.log x) ^ 3 ≤ 216 * s ^ 3 := by
      calc (Real.log x) ^ 3 ≤ (6 * s) ^ 3 := pow_le_pow_left₀ hlog_nn hlog_x 3
        _ = 216 * s ^ 3 := by ring
    have hs5_pow : (3125 : ℝ) ≤ s ^ 5 := by
      calc (3125 : ℝ) = (5 : ℝ) ^ 5 := by norm_num
        _ ≤ s ^ 5 := pow_le_pow_left₀ (by norm_num) hs5 5
    have hs8_ge : 3125 * s ^ 3 ≤ s1 := by
      rw [hs8, show s ^ 8 = s ^ 5 * s ^ 3 by ring]
      exact mul_le_mul_of_nonneg_right hs5_pow (by positivity)
    have hsq_sub : (9 / 10 : ℝ) * s1 ≤ Real.sqrt (x - 1) := by
      rw [Real.le_sqrt (by positivity) (by linarith)]
      have hsq : ((9 / 10 : ℝ) * s1) ^ 2 = (81 / 100 : ℝ) * x := by
        rw [mul_pow, hs1_sq]; ring
      linarith
    linarith

/-! ## 2. Discrete Telescoping, Abel Summation, and Majorant Step Bounds -/

private lemma sum_Ico_sub_pred (g : ℕ → ℝ) {z M : ℕ} (hzM : z ≤ M) :
    ∑ n ∈ Finset.Ico z M, (g n - g (n - 1)) = g (M - 1) - g (z - 1) := by
  induction M, hzM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    simp only [Nat.add_sub_cancel]
    ring

private lemma sum_Ico_abel (A : ℕ → ℝ) {z M : ℕ} (hzM : z ≤ M) :
    ∑ n ∈ Finset.Ico z M, (A n - A (n - 1)) / (n : ℝ) =
      A (M - 1) / (M : ℝ) - A (z - 1) / (z : ℝ) +
        ∑ n ∈ Finset.Ico z M, A n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
  induction M, hzM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, Finset.sum_Ico_succ_top hk, ih]
    simp only [Nat.add_sub_cancel, div_eq_mul_inv, one_mul]
    ring

private lemma primeCounting_sub_pred {n : ℕ} (hn : 1 ≤ n) :
    (primeCounting (n : ℝ) : ℝ) - (primeCounting ((n - 1 : ℕ) : ℝ) : ℝ) =
      if n.Prime then 1 else 0 := by
  rw [primeCounting_nat, primeCounting_nat, show n - 1 + 1 = n by omega,
    Finset.range_add_one, Finset.filter_insert]
  split_ifs with hp
  · have hmem : n ∉ (Finset.range n).filter Nat.Prime := by simp
    rw [Finset.card_insert_of_notMem hmem]
    push_cast
    ring
  · ring

private lemma sum_primes_Ico_eq_main_add_err (li2 : ℝ) {z M : ℕ} (hz : 1 ≤ z) :
    (∑ p ∈ (Finset.Ico z M).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) =
      (∑ n ∈ Finset.Ico z M,
        (offsetLogIntegral (n : ℝ) - offsetLogIntegral ((n - 1 : ℕ) : ℝ)) / (n : ℝ)) +
      (∑ n ∈ Finset.Ico z M,
        (((primeCounting (n : ℝ) : ℝ) - logIntegral li2 (n : ℝ)) -
          ((primeCounting ((n - 1 : ℕ) : ℝ) : ℝ) - logIntegral li2 ((n - 1 : ℕ) : ℝ))) /
          (n : ℝ)) := by
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := hz.trans (Finset.mem_Ico.mp hn).1
  have hpc := primeCounting_sub_pred hn1
  have hsplit : (if n.Prime then (1 : ℝ) / (n : ℝ) else 0) =
      ((primeCounting (n : ℝ) : ℝ) - (primeCounting ((n - 1 : ℕ) : ℝ) : ℝ)) / (n : ℝ) := by
    rw [hpc]; split_ifs <;> simp
  rw [hsplit]
  unfold logIntegral
  ring

private noncomputable def abelMaj (m : ℕ) : ℝ :=
  (2 * Real.log (m : ℝ) + 6) / Real.sqrt (m : ℝ)

private lemma abelMaj_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ abelMaj m := by
  unfold abelMaj
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  positivity

private lemma log_div_mul_sqrt_le_abelMaj_diff {n : ℕ} (hn : 4 ≤ n) :
    Real.log (n : ℝ) / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤ 2 * (abelMaj (n - 1) - abelMaj n) := by
  set a : ℝ := ((n - 1 : ℕ) : ℝ)
  set b : ℝ := (n : ℝ)
  have ha3 : 3 ≤ a := by
    dsimp only [a]
    exact_mod_cast (by omega : 3 ≤ n - 1)
  have hba : b = a + 1 := by
    dsimp only [a, b]
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hsq_a : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha_pos
  have hsq_b : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb_pos
  have hsq_le : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
  have hsq_a2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha_pos.le
  have hsq_b2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb_pos.le
  have hinv_sqrt : 1 / (2 * b * Real.sqrt b) ≤ 1 / Real.sqrt a - 1 / Real.sqrt b := by
    have hdiff : 1 / Real.sqrt a - 1 / Real.sqrt b =
        (Real.sqrt b - Real.sqrt a) / (Real.sqrt a * Real.sqrt b) := by
      field_simp [hsq_a.ne', hsq_b.ne']
    rw [hdiff, div_le_div_iff₀ (by positivity) (by positivity)]
    have hprod : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) = 1 := by
      nlinarith [hsq_a2, hsq_b2, hba]
    have hsum_le : Real.sqrt a * (Real.sqrt b + Real.sqrt a) ≤ 2 * b := by
      nlinarith [hsq_le, hsq_b2]
    have hstep : Real.sqrt a ≤ 2 * b * (Real.sqrt b - Real.sqrt a) := by
      have hpos_sum : 0 < Real.sqrt b + Real.sqrt a := by positivity
      nlinarith [hprod, hsum_le]
    nlinarith [hstep, hsq_b]
  have hlog_a_pos : 0 < Real.log a := Real.log_pos (by linarith)
  have hterm1 : (Real.log a + 3) / (b * Real.sqrt b) ≤
      (2 * Real.log a + 6) * (1 / Real.sqrt a - 1 / Real.sqrt b) := by
    calc (Real.log a + 3) / (b * Real.sqrt b)
        = (2 * Real.log a + 6) * (1 / (2 * b * Real.sqrt b)) := by ring
      _ ≤ (2 * Real.log a + 6) * (1 / Real.sqrt a - 1 / Real.sqrt b) :=
          mul_le_mul_of_nonneg_left hinv_sqrt (by positivity)
  have hlog_diff : Real.log b - Real.log a ≤ 1 / a := by
    have hs := (log_sub_sandwich ha_pos (by linarith : a ≤ b)).2
    rw [show b - a = 1 by linarith] at hs
    exact hs
  have h2a_le_3b : 2 * (1 / a) ≤ 3 / b := by
    rw [mul_one_div, div_le_div_iff₀ ha_pos hb_pos]
    linarith
  have hterm2 : 2 * (Real.log b - Real.log a) / Real.sqrt b ≤ 3 / (b * Real.sqrt b) := by
    calc 2 * (Real.log b - Real.log a) / Real.sqrt b
        ≤ (3 / b) / Real.sqrt b :=
          div_le_div_of_nonneg_right (by linarith) hsq_b.le
      _ = 3 / (b * Real.sqrt b) := by rw [div_div]
  have hmaj_split : abelMaj (n - 1) - abelMaj n =
      (2 * Real.log a + 6) * (1 / Real.sqrt a - 1 / Real.sqrt b) -
        2 * (Real.log b - Real.log a) / Real.sqrt b := by
    dsimp only [abelMaj, a, b]
    simp only [div_eq_mul_inv, one_mul]
    ring
  have hlog_b_le : Real.log b ≤ 2 * Real.log a := by
    have hba2 : b ≤ a ^ 2 := by nlinarith
    calc Real.log b ≤ Real.log (a ^ 2) := Real.log_le_log hb_pos hba2
      _ = 2 * Real.log a := by rw [Real.log_pow]; norm_num
  have hlog_b_div : Real.log b / (b * Real.sqrt b) ≤ 2 * (Real.log a / (b * Real.sqrt b)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hlog_b_le (by positivity)
  have hsplit_a3 : (Real.log a + 3) / (b * Real.sqrt b) =
      Real.log a / (b * Real.sqrt b) + 3 / (b * Real.sqrt b) := add_div _ _ _
  change Real.log b / (b * Real.sqrt b) ≤ 2 * (abelMaj (n - 1) - abelMaj n)
  linarith

/-! ## 3. Main Term & Schoenfeld Remainder Bounds on `Ico z M` -/

private lemma inv_log_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
      (Real.log_pos ht1).ne').continuousWithinAt
  rw [← Set.uIcc_of_le hab] at hcont
  exact hcont.intervalIntegrable

private lemma main_step_abs_le {n : ℕ} (hn : 4 ≤ n) :
    |(offsetLogIntegral (n : ℝ) - offsetLogIntegral ((n - 1 : ℕ) : ℝ)) / (n : ℝ) -
        (Real.log (Real.log (n : ℝ)) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)))| ≤
      1 / (((n - 1 : ℕ) : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) -
        1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  set a : ℝ := ((n - 1 : ℕ) : ℝ)
  set b : ℝ := (n : ℝ)
  have ha3 : 3 ≤ a := by
    dsimp only [a]
    exact_mod_cast (by omega : 3 ≤ n - 1)
  have hba : b = a + 1 := by
    dsimp only [a, b]
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hab : a ≤ b := by linarith
  have hlog_a : 1 < Real.log a :=
    (Real.lt_log_iff_exp_lt ha_pos).mpr (lt_of_lt_of_le exp_one_bounds.2 ha3)
  have hlog_b : 1 < Real.log b := lt_of_lt_of_le hlog_a (Real.log_le_log ha_pos hab)
  have hadj : offsetLogIntegral a + ∫ t in a..b, 1 / Real.log t = offsetLogIntegral b :=
    intervalIntegral.integral_add_adjacent_intervals
      (inv_log_integrable (by linarith) (by linarith)) (inv_log_integrable (by linarith) hab)
  have hint_eq : offsetLogIntegral b - offsetLogIntegral a = ∫ t in a..b, 1 / Real.log t := by
    linarith
  have hint : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b :=
    inv_log_integrable (by linarith) hab
  have hli_lo : 1 / (b * Real.log b) ≤ (offsetLogIntegral b - offsetLogIntegral a) / b := by
    rw [hint_eq, le_div_iff₀ hb_pos]
    have hconst : ∫ _ in a..b, (1 / Real.log b : ℝ) = 1 / Real.log b := by
      rw [intervalIntegral.integral_const, smul_eq_mul, show b - a = 1 by linarith, one_mul]
    have hmono : ∫ _ in a..b, (1 / Real.log b : ℝ) ≤ ∫ t in a..b, 1 / Real.log t :=
      intervalIntegral.integral_mono_on hab intervalIntegrable_const hint fun t ht =>
        one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
          (Real.log_le_log (by linarith [ht.1]) ht.2)
    rw [hconst] at hmono
    have : 1 / (b * Real.log b) * b = 1 / Real.log b := by field_simp [hb_pos.ne']
    linarith
  have hli_hi : (offsetLogIntegral b - offsetLogIntegral a) / b ≤ 1 / (a * Real.log a) := by
    rw [hint_eq]
    have hconst : ∫ _ in a..b, (1 / Real.log a : ℝ) = 1 / Real.log a := by
      rw [intervalIntegral.integral_const, smul_eq_mul, show b - a = 1 by linarith, one_mul]
    have hmono : ∫ t in a..b, 1 / Real.log t ≤ ∫ _ in a..b, (1 / Real.log a : ℝ) :=
      intervalIntegral.integral_mono_on hab hint intervalIntegrable_const fun t ht =>
        one_div_le_one_div_of_le (by linarith) (Real.log_le_log ha_pos ht.1)
    rw [hconst] at hmono
    calc (∫ t in a..b, 1 / Real.log t) / b
        ≤ (1 / Real.log a) / b := div_le_div_of_nonneg_right hmono hb_pos.le
      _ = 1 / (b * Real.log a) := by rw [div_div]; ring
      _ ≤ 1 / (a * Real.log a) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right hab (by positivity))
  have hs_ab := log_sub_sandwich ha_pos hab
  rw [show b - a = 1 by linarith] at hs_ab
  have hs_ll := log_sub_sandwich (by positivity : 0 < Real.log a) (Real.log_le_log ha_pos hab)
  have hll_lo : 1 / (b * Real.log b) ≤ Real.log (Real.log b) - Real.log (Real.log a) := by
    calc 1 / (b * Real.log b) = (1 / b) / Real.log b := by rw [div_div]
      _ ≤ (Real.log b - Real.log a) / Real.log b :=
          div_le_div_of_nonneg_right hs_ab.1 (by positivity)
      _ ≤ Real.log (Real.log b) - Real.log (Real.log a) := hs_ll.1
  have hll_hi : Real.log (Real.log b) - Real.log (Real.log a) ≤ 1 / (a * Real.log a) := by
    calc Real.log (Real.log b) - Real.log (Real.log a)
        ≤ (Real.log b - Real.log a) / Real.log a := hs_ll.2
      _ ≤ (1 / a) / Real.log a := div_le_div_of_nonneg_right hs_ab.2 (by positivity)
      _ = 1 / (a * Real.log a) := by rw [div_div]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma main_sum_Ico_abs_le {z M : ℕ} (hz : 4 ≤ z) (hzM : z ≤ M) :
    |(∑ n ∈ Finset.Ico z M,
        (offsetLogIntegral (n : ℝ) - offsetLogIntegral ((n - 1 : ℕ) : ℝ)) / (n : ℝ)) -
      (Real.log (Real.log ((M - 1 : ℕ) : ℝ)) - Real.log (Real.log ((z - 1 : ℕ) : ℝ)))| ≤
      1 / ((z - 1 : ℕ) : ℝ) := by
  have htele := sum_Ico_sub_pred (fun m : ℕ => Real.log (Real.log (m : ℝ))) hzM
  rw [← htele, ← Finset.sum_sub_distrib]
  have htri : |∑ n ∈ Finset.Ico z M,
      ((offsetLogIntegral (n : ℝ) - offsetLogIntegral ((n - 1 : ℕ) : ℝ)) / (n : ℝ) -
        (Real.log (Real.log (n : ℝ)) - Real.log (Real.log ((n - 1 : ℕ) : ℝ))))| ≤
      ∑ n ∈ Finset.Ico z M,
        (1 / (((n - 1 : ℕ) : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) -
          1 / ((n : ℝ) * Real.log (n : ℝ))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    exact main_step_abs_le (hz.trans (Finset.mem_Ico.mp hn).1)
  have htele2 := sum_Ico_sub_pred (fun m : ℕ => -(1 / ((m : ℝ) * Real.log (m : ℝ)))) hzM
  have hsum_eq : ∑ n ∈ Finset.Ico z M,
      (1 / (((n - 1 : ℕ) : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) -
        1 / ((n : ℝ) * Real.log (n : ℝ))) =
      1 / (((z - 1 : ℕ) : ℝ) * Real.log ((z - 1 : ℕ) : ℝ)) -
        1 / (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ)) := by
    simpa [sub_eq_add_neg, add_comm] using htele2
  have hz3 : (3 : ℝ) ≤ ((z - 1 : ℕ) : ℝ) := by
    have : 3 ≤ z - 1 := by omega
    exact_mod_cast this
  have hM3 : (3 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
    have : 3 ≤ M - 1 := by omega
    exact_mod_cast this
  have hlog_z1 : 1 < Real.log ((z - 1 : ℕ) : ℝ) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_of_lt_of_le exp_one_bounds.2 hz3)
  have hlog_M1 : 0 < Real.log ((M - 1 : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have hM_nn : 0 ≤ 1 / (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ)) := by positivity
  have hz_le : 1 / (((z - 1 : ℕ) : ℝ) * Real.log ((z - 1 : ℕ) : ℝ)) ≤
      1 / ((z - 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le (by linarith)
      (le_mul_of_one_le_right (by linarith) hlog_z1.le)
  linarith

private lemma schoenfeld_err_sum_Ico_abs_le {li2 : ℝ} (hS : SchoenfeldRHBound li2)
    {z M : ℕ} (hz : 2658 ≤ z) (hzM : z ≤ M) :
    |∑ n ∈ Finset.Ico z M,
        (((primeCounting (n : ℝ) : ℝ) - logIntegral li2 (n : ℝ)) -
          ((primeCounting ((n - 1 : ℕ) : ℝ) : ℝ) - logIntegral li2 ((n - 1 : ℕ) : ℝ))) /
          (n : ℝ)| ≤
      Real.log (M : ℝ) / (24 * Real.sqrt (M : ℝ)) +
        (5 * Real.log ((z - 1 : ℕ) : ℝ) + 12) / (24 * Real.sqrt ((z - 1 : ℕ) : ℝ)) := by
  let A : ℕ → ℝ := fun m => (primeCounting (m : ℝ) : ℝ) - logIntegral li2 (m : ℝ)
  have hpi24 : (24 : ℝ) ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
  have hA_bd : ∀ m : ℕ, 2657 ≤ m → |A m| ≤ Real.sqrt (m : ℝ) * Real.log (m : ℝ) / 24 := by
    intro m hm
    have hm_r : (2657 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hSm := hS (m : ℝ) hm_r
    have hnum_nn : 0 ≤ Real.sqrt (m : ℝ) * Real.log (m : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
    exact hSm.trans (div_le_div_of_nonneg_left hnum_nn (by norm_num) hpi24)
  change |∑ n ∈ Finset.Ico z M, (A n - A (n - 1)) / (n : ℝ)| ≤ _
  rw [sum_Ico_abel A hzM]
  have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hz1_pos : (0 : ℝ) < ((z - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < z - 1)
  have htri1 : |A (M - 1) / (M : ℝ) - A (z - 1) / (z : ℝ) +
      ∑ n ∈ Finset.Ico z M, A n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))| ≤
      |A (M - 1)| / (M : ℝ) + |A (z - 1)| / (z : ℝ) +
        ∑ n ∈ Finset.Ico z M, |A n| * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
    have h1 := abs_add_le (A (M - 1) / (M : ℝ) - A (z - 1) / (z : ℝ))
      (∑ n ∈ Finset.Ico z M, A n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)))
    have h2 := abs_sub (A (M - 1) / (M : ℝ)) (A (z - 1) / (z : ℝ))
    rw [abs_div, abs_of_pos hM_pos, abs_div, abs_of_pos hz_pos] at h2
    have h3 : |∑ n ∈ Finset.Ico z M, A n * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))| ≤
        ∑ n ∈ Finset.Ico z M, |A n| * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hn_pos : (0 : ℝ) < (n : ℝ) :=
        by exact_mod_cast (by omega : 0 < z).trans_le (Finset.mem_Ico.mp hn).1
      have hdiff_nn : 0 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        exact sub_nonneg.mpr (one_div_le_one_div_of_le hn_pos hle)
      rw [abs_mul, abs_of_nonneg hdiff_nn]
    linarith
  have hbd_M : |A (M - 1)| / (M : ℝ) ≤ Real.log (M : ℝ) / (24 * Real.sqrt (M : ℝ)) := by
    have hAM := hA_bd (M - 1) (by omega)
    have hle_M : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le M 1
    have hM1_ge1 : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M - 1)
    have hsq_M : Real.sqrt ((M - 1 : ℕ) : ℝ) ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt hle_M
    have hlog_M : Real.log ((M - 1 : ℕ) : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by linarith) hle_M
    have hprod_le : Real.sqrt ((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) ≤
        Real.sqrt (M : ℝ) * Real.log (M : ℝ) :=
      mul_le_mul hsq_M hlog_M (Real.log_nonneg hM1_ge1) (Real.sqrt_nonneg _)
    have hsqM_pos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM_pos
    calc |A (M - 1)| / (M : ℝ)
        ≤ (Real.sqrt (M : ℝ) * Real.log (M : ℝ) / 24) / (M : ℝ) :=
          div_le_div_of_nonneg_right
            (hAM.trans (div_le_div_of_nonneg_right hprod_le (by norm_num))) hM_pos.le
      _ = Real.log (M : ℝ) / (24 * Real.sqrt (M : ℝ)) := by
          field_simp [hM_pos.ne', hsqM_pos.ne']
          rw [Real.sq_sqrt hM_pos.le]
          ring
  have hbd_z : |A (z - 1)| / (z : ℝ) ≤
      Real.log ((z - 1 : ℕ) : ℝ) / (24 * Real.sqrt ((z - 1 : ℕ) : ℝ)) := by
    have hAz := hA_bd (z - 1) (by omega)
    have hz1_le_z : ((z - 1 : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast Nat.sub_le z 1
    have hsqz1_pos : 0 < Real.sqrt ((z - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hz1_pos
    calc |A (z - 1)| / (z : ℝ)
        ≤ |A (z - 1)| / ((z - 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hz1_pos hz1_le_z
      _ ≤ (Real.sqrt ((z - 1 : ℕ) : ℝ) * Real.log ((z - 1 : ℕ) : ℝ) / 24) /
            ((z - 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hAz hz1_pos.le
      _ = Real.log ((z - 1 : ℕ) : ℝ) / (24 * Real.sqrt ((z - 1 : ℕ) : ℝ)) := by
          field_simp [hz1_pos.ne', hsqz1_pos.ne']
          rw [Real.sq_sqrt hz1_pos.le]
          ring
  have hbd_sum : ∑ n ∈ Finset.Ico z M, |A n| * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) ≤
      (1 / 12 : ℝ) * abelMaj (z - 1) := by
    have hterm : ∑ n ∈ Finset.Ico z M, |A n| * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) ≤
        ∑ n ∈ Finset.Ico z M, (1 / 12 : ℝ) * (abelMaj (n - 1) - abelMaj n) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn_ge : z ≤ n := (Finset.mem_Ico.mp hn).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hsqn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
      have hAn := hA_bd n (by omega)
      have hdiff_le : 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by
        have heq : 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) =
            1 / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hn_pos.ne']; ring
        rw [heq]
        have hle : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n + 1 : ℕ) : ℝ) := by push_cast; nlinarith
        exact one_div_le_one_div_of_le (by positivity) hle
      have hdiff_nn : 0 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        exact sub_nonneg.mpr (one_div_le_one_div_of_le hn_pos hle)
      have hprod : |A n| * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) ≤
          (Real.sqrt (n : ℝ) * Real.log (n : ℝ) / 24) * (1 / (n : ℝ) ^ 2) :=
        mul_le_mul hAn hdiff_le hdiff_nn (by
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
          have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg this
          positivity)
      have hid : (Real.sqrt (n : ℝ) * Real.log (n : ℝ) / 24) * (1 / (n : ℝ) ^ 2) =
          (1 / 24 : ℝ) * (Real.log (n : ℝ) / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
        field_simp [hn_pos.ne', hsqn_pos.ne']
        rw [Real.sq_sqrt hn_pos.le]
        ring
      have hmaj := log_div_mul_sqrt_le_abelMaj_diff (n := n) (by omega)
      linarith
    rw [← Finset.mul_sum] at hterm
    have htele := sum_Ico_sub_pred (fun m => -abelMaj m) hzM
    have hsum_eq : ∑ n ∈ Finset.Ico z M, (abelMaj (n - 1) - abelMaj n) =
        abelMaj (z - 1) - abelMaj (M - 1) := by
      simpa [sub_eq_add_neg, add_comm] using htele
    rw [hsum_eq] at hterm
    have hM1_nn : 0 ≤ abelMaj (M - 1) := abelMaj_nonneg (by omega)
    linarith
  have hcomb : Real.log ((z - 1 : ℕ) : ℝ) / (24 * Real.sqrt ((z - 1 : ℕ) : ℝ)) +
      (1 / 12 : ℝ) * abelMaj (z - 1) =
      (5 * Real.log ((z - 1 : ℕ) : ℝ) + 12) / (24 * Real.sqrt ((z - 1 : ℕ) : ℝ)) := by
    unfold abelMaj
    ring
  linarith

/-! ## 4. Bridge at `M = 4^z` and Main Large-Range Theorem -/

private lemma mertens_sum_err_large {li2 : ℝ}
    (hS : SchoenfeldRHBound li2)
    (hMert : MertensPrimeSumPremise meisselMertensConst)
    {x : ℝ} (hx : (10 : ℝ) ^ 12 ≤ x) :
    |(∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
        (Real.log (Real.log x) + meisselMertensConst)| ≤
      (5 * Real.log x + 12) / (24 * Real.sqrt (x - 1)) + 5 / (x - 1) := by
  set z : ℕ := Nat.ceil x
  set M : ℕ := 4 ^ z
  have hz_ge_x : x ≤ (z : ℝ) := Nat.le_ceil x
  have hz_lt_x1 : (z : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hz_big : 10 ^ 12 ≤ z := by exact_mod_cast hx.trans hz_ge_x
  have hz2_le_2z : z ^ 2 ≤ 2 ^ z := sq_le_two_pow (by omega)
  have h2z_le_M : 2 ^ z ≤ M := Nat.pow_le_pow_left (by omega) z
  have hz_lt_z2 : z < z ^ 2 := by nlinarith
  have hzM : z ≤ M := (hz_lt_z2.trans_le (hz2_le_2z.trans h2z_le_M)).le
  have hM_gt_10_12 : (10 : ℝ) ^ 12 < (M : ℝ) := by
    have : 10 ^ 12 < M := hz_big.trans_lt (hz_lt_z2.trans_le (hz2_le_2z.trans h2z_le_M))
    exact_mod_cast this
  set w : ℝ := ((z - 1 : ℕ) : ℝ)
  have hw_eq : w = (z : ℝ) - 1 := by
    dsimp only [w]; rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hx1_le_w : x - 1 ≤ w := by linarith
  have hw_le_x : w ≤ x := by linarith
  have hx1_pos : 0 < x - 1 := by linarith
  have hw3 : 3 ≤ w := by linarith
  have hM1_ge_w : w ≤ ((M - 1 : ℕ) : ℝ) := by
    dsimp only [w]
    exact_mod_cast Nat.sub_le_sub_right hzM 1
  -- 1. Mertens bound at `M`
  have hmb := hMert.mertensSumBounds (M : ℝ) (by linarith)
  rw [Nat.ceil_natCast] at hmb
  have hlog_M_eq : Real.log (M : ℝ) = (z : ℝ) * Real.log 4 := by
    dsimp only [M]; push_cast; rw [Real.log_pow]
  obtain ⟨hl4_lo, hl4_hi⟩ := log_four_bounds
  have hz_pos : (0 : ℝ) < (z : ℝ) := by linarith
  have hlog_M_ge_z : (z : ℝ) ≤ Real.log (M : ℝ) := by
    rw [hlog_M_eq]; nlinarith
  have hlog_M_le_2z : Real.log (M : ℝ) ≤ 2 * (z : ℝ) := by
    rw [hlog_M_eq]; nlinarith
  have hDM_abs : |(∑ p ∈ (Finset.range M).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
      (Real.log (Real.log (M : ℝ)) + meisselMertensConst)| ≤ 1 / (x - 1) := by
    have hhi_eq := jsMertensHiErr_eq_tail hM_gt_10_12
    have hlo_le : jsMertensLoErr (M : ℝ) ≤ 1 / (x - 1) := by
      unfold jsMertensLoErr
      calc (2.964e-6 : ℝ) / Real.log (M : ℝ)
          ≤ 1 / Real.log (M : ℝ) := div_le_div_of_nonneg_right (by norm_num) (by linarith)
        _ ≤ 1 / (x - 1) := one_div_le_one_div_of_le hx1_pos (by linarith)
    have hhi_le : jsMertensHiErr (M : ℝ) ≤ 1 / (x - 1) := by
      rw [hhi_eq]
      calc (6.836e-6 : ℝ) / Real.log (M : ℝ)
          ≤ 1 / Real.log (M : ℝ) := div_le_div_of_nonneg_right (by norm_num) (by linarith)
        _ ≤ 1 / (x - 1) := one_div_le_one_div_of_le hx1_pos (by linarith)
    exact abs_le.mpr ⟨by linarith [hmb.1], by linarith [hmb.2]⟩
  -- 2. Split `range M` into `range z` and `Ico z M`
  have hIco_sub : (∑ p ∈ (Finset.Ico z M).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) =
      (∑ p ∈ (Finset.range M).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
        (∑ p ∈ (Finset.range z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) := by
    simp only [Finset.sum_filter]
    exact Finset.sum_Ico_eq_sub (fun p => if p.Prime then (1 : ℝ) / (p : ℝ) else 0) hzM
  -- 3. Main and error bounds on `Ico z M`
  have hsplit := sum_primes_Ico_eq_main_add_err li2 (z := z) (M := M) (by omega)
  have hmain := main_sum_Ico_abs_le (z := z) (M := M) (by omega) hzM
  have herr := schoenfeld_err_sum_Ico_abs_le hS (z := z) (M := M) (by omega) hzM
  -- 4. Boundary log-log shifts and `M`-boundary error
  have hll_M : |Real.log (Real.log (M : ℝ)) - Real.log (Real.log ((M - 1 : ℕ) : ℝ))| ≤
      1 / (x - 1) := by
    have hM1_eq : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have hb := log_log_sub_bounds (a := ((M - 1 : ℕ) : ℝ)) (b := (M : ℝ))
      (by linarith) (by linarith)
    have hle : ((M : ℝ) - ((M - 1 : ℕ) : ℝ)) / ((M - 1 : ℕ) : ℝ) ≤ 1 / (x - 1) := by
      rw [show (M : ℝ) - ((M - 1 : ℕ) : ℝ) = 1 by linarith]
      exact one_div_le_one_div_of_le hx1_pos (by linarith)
    exact abs_le.mpr ⟨by linarith [hb.1], hb.2.trans hle⟩
  have hll_x : |Real.log (Real.log x) - Real.log (Real.log w)| ≤ 1 / (x - 1) := by
    have hb := log_log_sub_bounds hw3 hw_le_x
    have hle : (x - w) / w ≤ 1 / (x - 1) := by
      calc (x - w) / w ≤ 1 / w := div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ 1 / (x - 1) := one_div_le_one_div_of_le hx1_pos hx1_le_w
    exact abs_le.mpr ⟨by linarith [hb.1], hb.2.trans hle⟩
  have hM_err : Real.log (M : ℝ) / (24 * Real.sqrt (M : ℝ)) ≤ 1 / (x - 1) := by
    have hM_sq_eq : (M : ℝ) = ((2 : ℝ) ^ z) ^ 2 := by
      dsimp only [M]; push_cast
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    have hsqM : Real.sqrt (M : ℝ) = (2 : ℝ) ^ z := by
      rw [hM_sq_eq, Real.sqrt_sq (by positivity)]
    have hz2_r : (z : ℝ) ^ 2 ≤ Real.sqrt (M : ℝ) := by
      rw [hsqM]; exact_mod_cast hz2_le_2z
    calc Real.log (M : ℝ) / (24 * Real.sqrt (M : ℝ))
        ≤ (2 * (z : ℝ)) / (24 * (z : ℝ) ^ 2) :=
          div_le_div₀ (by positivity) hlog_M_le_2z (by positivity)
            (mul_le_mul_of_nonneg_left hz2_r (by norm_num))
      _ = 1 / (12 * (z : ℝ)) := by field_simp [hz_pos.ne']; ring
      _ ≤ 1 / (x - 1) := one_div_le_one_div_of_le hx1_pos (by linarith)
  have hw_err : (5 * Real.log w + 12) / (24 * Real.sqrt w) ≤
      (5 * Real.log x + 12) / (24 * Real.sqrt (x - 1)) := by
    have hlog_wx : Real.log w ≤ Real.log x := Real.log_le_log (by linarith) hw_le_x
    have hsq_wx : Real.sqrt (x - 1) ≤ Real.sqrt w := Real.sqrt_le_sqrt hx1_le_w
    have hlog_w_pos : 0 < Real.log w := Real.log_pos (by linarith)
    have hsq_x1_pos : 0 < Real.sqrt (x - 1) := Real.sqrt_pos.mpr hx1_pos
    exact div_le_div₀ (by linarith) (by linarith) (by positivity)
      (mul_le_mul_of_nonneg_left hsq_wx (by norm_num))
  have hw_inv : 1 / w ≤ 1 / (x - 1) := one_div_le_one_div_of_le hx1_pos hx1_le_w
  have h5_eq : 5 / (x - 1) = 5 * (1 / (x - 1)) := by ring
  obtain ⟨hb_DM1, hb_DM2⟩ := abs_le.mp hDM_abs
  obtain ⟨hb_main1, hb_main2⟩ := abs_le.mp hmain
  obtain ⟨hb_err1, hb_err2⟩ := abs_le.mp herr
  obtain ⟨hb_llM1, hb_llM2⟩ := abs_le.mp hll_M
  obtain ⟨hb_llx1, hb_llx2⟩ := abs_le.mp hll_x
  change |(∑ p ∈ (Finset.range z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
      (Real.log (Real.log x) + meisselMertensConst)| ≤ _
  dsimp only [w] at hb_llx1 hb_llx2 hw_err hw_inv
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Large-range (`x ≥ 10^12`) normalized Mertens Euler-product bound under `SchoenfeldRHBound`
and `MertensPrimeSumPremise meisselMertensConst`. -/
theorem eulerR3_mem_Icc_large {li2 : ℝ}
    (hS : SchoenfeldRHBound li2)
    (hMert : MertensPrimeSumPremise meisselMertensConst)
    {x : ℝ} (hx : (10 : ℝ) ^ 12 ≤ x) :
    1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
      eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2) := by
  set E : ℝ := (5 * Real.log x + 12) / (24 * Real.sqrt (x - 1)) + 5 / (x - 1)
  have herr := abs_le.mp (mertens_sum_err_large hS hMert hx)
  obtain ⟨hlog25, hcube⟩ := large_x_log_and_cube hx
  have hx1_pos : 0 < x - 1 := by linarith
  have hsq_pos : 0 < Real.sqrt (x - 1) := Real.sqrt_pos.mpr hx1_pos
  have hlog_pos : 0 < Real.log x := by linarith
  have hE_nn : 0 ≤ E := by dsimp only [E]; positivity
  have hsq_ge : (24 : ℝ) ≤ Real.sqrt (x - 1) := by
    rw [Real.le_sqrt (by norm_num) hx1_pos.le]; linarith
  have hx1_sq : Real.sqrt (x - 1) * Real.sqrt (x - 1) = x - 1 :=
    Real.mul_self_sqrt hx1_pos.le
  have hpart1 : (5 * Real.log x + 12) / (24 * Real.sqrt (x - 1)) ≤
      Real.log x / (4 * Real.sqrt (x - 1)) := by
    calc (5 * Real.log x + 12) / (24 * Real.sqrt (x - 1))
        ≤ (6 * Real.log x) / (24 * Real.sqrt (x - 1)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = Real.log x / (4 * Real.sqrt (x - 1)) := by
          field_simp [hsq_pos.ne']; ring
  have hpart2 : 5 / (x - 1) + 1 / (2 * (x - 1)) ≤
      Real.log x / (4 * Real.sqrt (x - 1)) := by
    have hsum : 5 / (x - 1) + 1 / (2 * (x - 1)) = (11 / 2 : ℝ) / (x - 1) := by
      field_simp [hx1_pos.ne']; ring
    rw [hsum, div_le_div_iff₀ hx1_pos (by positivity)]
    nlinarith [hx1_sq, hsq_ge, hlog25]
  have hE_sum : E + 1 / (2 * (x - 1)) ≤ Real.log x / (2 * Real.sqrt (x - 1)) := by
    have hq : Real.log x / (4 * Real.sqrt (x - 1)) + Real.log x / (4 * Real.sqrt (x - 1)) =
        Real.log x / (2 * Real.sqrt (x - 1)) := by
      field_simp [hsq_pos.ne']; ring
    dsimp only [E]; linarith
  have hbudget : Real.log x / (2 * Real.sqrt (x - 1)) ≤
      (9 / 20 : ℝ) / (Real.log x) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpow3 : Real.log x * (Real.log x) ^ 2 = (Real.log x) ^ 3 := by ring
    linarith
  have h_lo_bd : E + 1 / (2 * (x - 1)) ≤ (9 / 20 : ℝ) / (Real.log x) ^ 2 :=
    hE_sum.trans hbudget
  have h_hi_bd : E ≤ 1 / (2 * (Real.log x) ^ 2) := by
    have hpos_tail : 0 ≤ 1 / (2 * (x - 1)) := by positivity
    have h9_20 : (9 / 20 : ℝ) / (Real.log x) ^ 2 ≤ 1 / (2 * (Real.log x) ^ 2) := by
      rw [show (1 : ℝ) / (2 * (Real.log x) ^ 2) = (1 / 2 : ℝ) / (Real.log x) ^ 2 by
        field_simp [hlog_pos.ne']]
      exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
    linarith
  exact eulerR3_mem_Icc_of_mertens_err (by linarith)
    (by linarith [herr.1]) (by linarith [herr.2]) hE_nn h_hi_bd h_lo_bd

end BuchstabSwitching.External
