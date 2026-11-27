import BuchstabSwitching.External.RobinOmega.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Abel Partial-Summation Asymptotic Segment (`m ≥ 13000`) for `RobinOmegaBound`

Proves the asymptotic prime-counting inequality
`(Nat.primeCounting m : ℝ) < 1.3841 * Chebyshev.theta m / Real.log (Chebyshev.theta m)`
for all `m ≥ 13000`, from explicit rational bounds on `Real.log 2` and a linear lower bound
`(84 / 100) * m ≤ Chebyshev.theta m`, via `Chebyshev.primeCounting_eq_theta_div_log_add_integral`
and a 6-interval partition `[2, 4, 16, 64, 256, 512, m^(4/5), m]`.
-/

namespace BuchstabSwitching.External

/-! ## Elementary exponential and logarithmic estimates -/

private lemma exp_one_lt_2719_div_1000 : Real.exp 1 < (2719 / 1000 : ℝ) := by
  have hb := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  linarith

private lemma exp_47_div_5_lt_13000 : Real.exp (47 / 5 : ℝ) < (13000 : ℝ) := by
  have hpow : (Real.exp (47 / 5 : ℝ)) ^ 5 = (Real.exp 1) ^ 47 := by
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]
    norm_num
  have h1 : (Real.exp 1) ^ 47 < (2719 / 1000 : ℝ) ^ 47 :=
    pow_lt_pow_left₀ exp_one_lt_2719_div_1000 (Real.exp_pos 1).le (by norm_num)
  have h2 : (2719 / 1000 : ℝ) ^ 47 < (13000 : ℝ) ^ 5 := by norm_num
  have hpow5 : (Real.exp (47 / 5 : ℝ)) ^ 5 < (13000 : ℝ) ^ 5 := by linarith
  by_contra hge
  have hle : (13000 : ℝ) ≤ Real.exp (47 / 5 : ℝ) := not_lt.mp hge
  have hpow_ge : (13000 : ℝ) ^ 5 ≤ (Real.exp (47 / 5 : ℝ)) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) hle 5
  linarith

private lemma log_ge_47_div_5 {m : ℕ} (hm : 13000 ≤ m) :
    (47 / 5 : ℝ) ≤ Real.log (m : ℝ) := by
  have hm_real : (13000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp : Real.exp (47 / 5 : ℝ) ≤ (m : ℝ) := le_trans exp_47_div_5_lt_13000.le hm_real
  rw [← Real.log_exp (47 / 5 : ℝ)]
  exact Real.log_le_log (Real.exp_pos _) hexp

private lemma log_six_lt_nine_div_five : Real.log 6 < (9 / 5 : ℝ) := by
  have hpow : (Real.exp (9 / 5 : ℝ)) ^ 5 = (Real.exp 1) ^ 9 := by
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]
    norm_num
  have h1 : (2716 / 1000 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 :=
    pow_le_pow_left₀ (by norm_num) exp_one_ge_2716_div_1000_basic 9
  have h2 : (6 : ℝ) ^ 5 < (2716 / 1000 : ℝ) ^ 9 := by norm_num
  have hlt : (6 : ℝ) < Real.exp (9 / 5 : ℝ) := by
    by_contra hge
    have hle : Real.exp (9 / 5 : ℝ) ≤ 6 := not_lt.mp hge
    have hpow_le : (Real.exp (9 / 5 : ℝ)) ^ 5 ≤ (6 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hle 5
    linarith
  rw [← Real.log_exp (9 / 5 : ℝ)]
  exact Real.log_lt_log (by norm_num) hlt

private lemma log_25_div_18_lt_one_div_three : Real.log (25 / 18 : ℝ) < (1 / 3 : ℝ) := by
  have hpow : (Real.exp (1 / 3 : ℝ)) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_natCast_mul]
    norm_num
  have h1 : (25 / 18 : ℝ) ^ 3 < (2716 / 1000 : ℝ) := by norm_num
  have h2 : (2716 / 1000 : ℝ) ≤ (Real.exp (1 / 3 : ℝ)) ^ 3 := by
    rw [hpow]
    exact exp_one_ge_2716_div_1000_basic
  have hlt : (25 / 18 : ℝ) < Real.exp (1 / 3 : ℝ) := by
    by_contra hge
    have hle : Real.exp (1 / 3 : ℝ) ≤ (25 / 18 : ℝ) := not_lt.mp hge
    have hpow_le : (Real.exp (1 / 3 : ℝ)) ^ 3 ≤ (25 / 18 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hle 3
    linarith
  rw [← Real.log_exp (1 / 3 : ℝ)]
  exact Real.log_lt_log (by norm_num) hlt

private lemma log_four_lt_25_div_18 (h_ln2_hi : Real.log 2 < (25 / 36 : ℝ)) :
    Real.log 4 < (25 / 18 : ℝ) := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4, Real.log_pow]
  norm_num
  linarith

private lemma log_div_self_le_10_div_13000
    (h_ln2_hi : Real.log 2 < (25 / 36 : ℝ)) {m : ℕ} (hm : 13000 ≤ m) :
    Real.log (m : ℝ) / (m : ℝ) ≤ (10 / 13000 : ℝ) := by
  have hm_real : (13000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have he_le : Real.exp 1 ≤ (13000 : ℝ) := le_trans exp_one_lt_three.le (by norm_num)
  have hanti : Real.log (m : ℝ) / (m : ℝ) ≤ Real.log 13000 / 13000 :=
    log_div_self_antitoneOn he_le (le_trans he_le hm_real) hm_real
  have h13000_lt : (13000 : ℝ) < (2 : ℝ) ^ (14 : ℕ) := by norm_num
  have hlog_lt : Real.log 13000 < 10 := by
    have hlt := Real.log_lt_log (by norm_num) h13000_lt
    rw [Real.log_pow] at hlt
    norm_num at hlt
    linarith
  have hdiv : Real.log 13000 / 13000 ≤ (10 / 13000 : ℝ) := by linarith
  exact le_trans hanti hdiv

/-! ## Integral bounds for Abel summation -/

/-- Monotonicity upper bound for `∫ t in a..b, 1 / (log t)^2` on `(1, ∞)`. -/
lemma integral_one_div_log_sq_le_sub {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t ^ 2 ≤ (b - a) / Real.log a ^ 2 := by
  have hlog_a : 0 < Real.log a := Real.log_pos ha
  have hmono : ∫ t in a..b, 1 / Real.log t ^ 2 ≤ ∫ _ in a..b, 1 / Real.log a ^ 2 := by
    refine intervalIntegral.integral_mono_on hab
      (Chebyshev.intervalIntegrable_one_div_log_sq ha (lt_of_lt_of_le ha hab))
      intervalIntegrable_const (fun t ht => ?_)
    have hlog_le : Real.log a ≤ Real.log t :=
      Real.log_le_log (lt_trans zero_lt_one ha) ht.1
    exact one_div_le_one_div_of_le (pow_pos hlog_a 2) (pow_le_pow_left₀ hlog_a.le hlog_le 2)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] at hmono
  exact hmono

private lemma integral_one_div_log_sq_split {a b c : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    ∫ t in a..c, 1 / Real.log t ^ 2 =
      (∫ t in a..b, 1 / Real.log t ^ 2) + ∫ t in b..c, 1 / Real.log t ^ 2 :=
  (intervalIntegral.integral_add_adjacent_intervals
    (Chebyshev.intervalIntegrable_one_div_log_sq ha hb)
    (Chebyshev.intervalIntegrable_one_div_log_sq hb hc)).symm

private lemma integral_theta_div_le
    (h_ln2_hi : Real.log 2 < (25 / 36 : ℝ)) {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2) ≤
      (25 / 18 : ℝ) * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hf : IntervalIntegrable
      (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) MeasureTheory.volume 2 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set Set.Ioc_subset_Icc_self
  have hg : IntervalIntegrable
      (fun t => (25 / 18 : ℝ) * (1 / Real.log t ^ 2)) MeasureTheory.volume 2 x :=
    (Chebyshev.intervalIntegrable_one_div_log_sq (a := 2) (b := x)
      (by norm_num) (by linarith)).const_mul _
  have hlog4 : Real.log 4 ≤ (25 / 18 : ℝ) := (log_four_lt_25_div_18 h_ln2_hi).le
  calc
    ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)
      ≤ ∫ t in (2 : ℝ)..x, (25 / 18 : ℝ) * (1 / Real.log t ^ 2) := by
        refine intervalIntegral.integral_mono_on hx hf hg (fun t ht => ?_)
        have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
        have hth : Chebyshev.theta t ≤ (25 / 18 : ℝ) * t :=
          le_trans (Chebyshev.theta_le_log4_mul_x ht_pos.le)
            (mul_le_mul_of_nonneg_right hlog4 ht_pos.le)
        have hden : 0 ≤ t * Real.log t ^ 2 := mul_nonneg ht_pos.le (sq_nonneg _)
        calc
          Chebyshev.theta t / (t * Real.log t ^ 2)
            ≤ ((25 / 18 : ℝ) * t) / (t * Real.log t ^ 2) :=
              div_le_div_of_nonneg_right hth hden
          _ = (25 / 18 : ℝ) * (1 / Real.log t ^ 2) := by
              have hne : t ≠ 0 := ht_pos.ne'
              field_simp
    _ = (25 / 18 : ℝ) * ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 :=
        intervalIntegral.integral_const_mul _ _

private lemma integral_two_pow_le
    (h_ln2_lo : (9 / 13 : ℝ) < Real.log 2)
    {a b : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : a = (2 : ℝ) ^ k) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t ^ 2 ≤
      (b - a) / ((k : ℝ) * (9 / 13 : ℝ)) ^ 2 := by
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1_lt : 1 < a := by
    rw [ha]
    have h2le : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    linarith [show (2 : ℝ) ^ (1 : ℕ) = 2 by norm_num]
  have hsub := integral_one_div_log_sq_le_sub h1_lt hab
  have hlo_pos : 0 < (k : ℝ) * (9 / 13 : ℝ) := by positivity
  have hlog_ge : (k : ℝ) * (9 / 13 : ℝ) ≤ Real.log a := by
    rw [ha, Real.log_pow]
    exact mul_le_mul_of_nonneg_left h_ln2_lo.le (by positivity)
  have hsq : ((k : ℝ) * (9 / 13 : ℝ)) ^ 2 ≤ (Real.log a) ^ 2 :=
    pow_le_pow_left₀ hlo_pos.le hlog_ge 2
  have hbn : 0 ≤ b - a := sub_nonneg.mpr hab
  exact le_trans hsub (div_le_div_of_nonneg_left hbn (pow_pos hlo_pos 2) hsq)

private noncomputable def iPref : ℝ :=
  2 / (9 / 13 : ℝ) ^ 2 + 12 / (18 / 13 : ℝ) ^ 2 + 48 / (36 / 13 : ℝ) ^ 2 +
    192 / (54 / 13 : ℝ) ^ 2 + 256 / (72 / 13 : ℝ) ^ 2

private lemma integral_two_to_512_le (h_ln2_lo : (9 / 13 : ℝ) < Real.log 2) :
    ∫ t in (2 : ℝ)..512, 1 / Real.log t ^ 2 ≤ iPref := by
  rw [integral_one_div_log_sq_split (b := 4) (by norm_num) (by norm_num) (by norm_num),
    integral_one_div_log_sq_split (a := 4) (b := 16) (by norm_num) (by norm_num) (by norm_num),
    integral_one_div_log_sq_split (a := 16) (b := 64) (by norm_num) (by norm_num) (by norm_num),
    integral_one_div_log_sq_split (a := 64) (b := 256) (by norm_num) (by norm_num) (by norm_num)]
  have h1 : ∫ t in (2 : ℝ)..4, 1 / Real.log t ^ 2 ≤ 2 / (9 / 13 : ℝ) ^ 2 :=
    le_trans (integral_two_pow_le h_ln2_lo (k := 1) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
  have h2 : ∫ t in (4 : ℝ)..16, 1 / Real.log t ^ 2 ≤ 12 / (18 / 13 : ℝ) ^ 2 :=
    le_trans (integral_two_pow_le h_ln2_lo (k := 2) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
  have h3 : ∫ t in (16 : ℝ)..64, 1 / Real.log t ^ 2 ≤ 48 / (36 / 13 : ℝ) ^ 2 :=
    le_trans (integral_two_pow_le h_ln2_lo (k := 4) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
  have h4 : ∫ t in (64 : ℝ)..256, 1 / Real.log t ^ 2 ≤ 192 / (54 / 13 : ℝ) ^ 2 :=
    le_trans (integral_two_pow_le h_ln2_lo (k := 6) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
  have h5 : ∫ t in (256 : ℝ)..512, 1 / Real.log t ^ 2 ≤ 256 / (72 / 13 : ℝ) ^ 2 :=
    le_trans (integral_two_pow_le h_ln2_lo (k := 8) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
  unfold iPref
  linarith

private lemma integral_512_to_m_le
    (h_ln2_lo : (9 / 13 : ℝ) < Real.log 2) {m : ℕ} (hm : 13000 ≤ m) :
    ∫ t in (512 : ℝ)..(m : ℝ), 1 / Real.log t ^ 2 ≤
      (m : ℝ) * (((3 / 2 : ℝ) / Real.log (m : ℝ)) / (81 * (9 / 13 : ℝ) ^ 2) +
        (25 / (16 * Real.log (m : ℝ) ^ 2)) * (1 - (3 / 2 : ℝ) / Real.log (m : ℝ))) := by
  set L : ℝ := Real.log (m : ℝ)
  set u : ℝ := Real.exp (L / 5)
  set y : ℝ := u ^ 4
  have hm_real : (13000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : 0 < (m : ℝ) := by linarith
  have hL_ge : (47 / 5 : ℝ) ≤ L := log_ge_47_div_5 hm
  have hL_pos : 0 < L := by linarith
  have hu_pos : 0 < u := Real.exp_pos (L / 5)
  have hu_pow5 : u ^ 5 = (m : ℝ) := by
    dsimp [u]
    rw [← Real.exp_natCast_mul]
    have h5 : (5 : ℕ) * (L / 5) = L := by norm_num; ring
    rw [h5]
    exact Real.exp_log hm_pos
  have hu_ge_six : (6 : ℝ) ≤ u := by
    by_contra hlt
    have hu6 : u < 6 := not_le.mp hlt
    have hp : u ^ 5 < (6 : ℝ) ^ 5 := pow_lt_pow_left₀ hu6 hu_pos.le (by norm_num)
    rw [hu_pow5] at hp
    norm_num at hp
    linarith
  have hy_ge_512 : (512 : ℝ) ≤ y := by
    have h64 : (6 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu_ge_six 4
    dsimp [y]
    linarith [show (512 : ℝ) ≤ (6 : ℝ) ^ 4 by norm_num]
  have hy_le_m : y ≤ (m : ℝ) := by
    rw [← hu_pow5]
    dsimp [y]
    have hpow : u ^ 5 = u ^ 4 * u := by ring
    rw [hpow]
    nlinarith [pow_nonneg hu_pos.le 4]
  have hL_le_u : L ≤ (3 / 2 : ℝ) * u := by
    have hlog_u : Real.log u = L / 5 := Real.log_exp (L / 5)
    have hdiv_pos : 0 < u / 6 := by linarith
    have hlog_div : Real.log (u / 6) ≤ u / 6 - 1 := Real.log_le_sub_one_of_pos hdiv_pos
    rw [Real.log_div hu_pos.ne' (by norm_num), hlog_u] at hlog_div
    have hlog6 := log_six_lt_nine_div_five
    linarith
  have hy_div_m : y / (m : ℝ) = 1 / u := by
    rw [← hu_pow5]
    dsimp [y]
    have hne : u ≠ 0 := hu_pos.ne'
    field_simp
  have hy_div_m_le : y / (m : ℝ) ≤ (3 / 2 : ℝ) / L := by
    rw [hy_div_m, div_le_div_iff₀ hu_pos hL_pos]
    linarith
  have hlog_y : Real.log y = (4 / 5 : ℝ) * L := by
    dsimp [y, u]
    rw [Real.log_pow, Real.log_exp]
    norm_num
    ring
  rw [integral_one_div_log_sq_split (b := y) (by norm_num) (by linarith) (by linarith)]
  have h_part1 : ∫ t in (512 : ℝ)..y, 1 / Real.log t ^ 2 ≤ y / (81 * (9 / 13 : ℝ) ^ 2) := by
    have hp1 := integral_two_pow_le h_ln2_lo (a := 512) (b := y) (k := 9)
      (by norm_num) (by norm_num) hy_ge_512
    have hp1' : (y - 512) / ((9 : ℕ) * (9 / 13 : ℝ)) ^ 2 ≤ y / (81 * (9 / 13 : ℝ) ^ 2) := by
      norm_num
      linarith
    exact le_trans hp1 hp1'
  have h_part2 : ∫ t in y..(m : ℝ), 1 / Real.log t ^ 2 ≤
      ((m : ℝ) - y) * (25 / (16 * L ^ 2)) := by
    have hp2 := integral_one_div_log_sq_le_sub (by linarith : 1 < y) hy_le_m
    have heq : ((m : ℝ) - y) / Real.log y ^ 2 = ((m : ℝ) - y) * (25 / (16 * L ^ 2)) := by
      rw [hlog_y]
      have hne : L ≠ 0 := hL_pos.ne'
      field_simp
      ring
    rwa [heq] at hp2
  set A : ℝ := 1 / (81 * (9 / 13 : ℝ) ^ 2)
  set B : ℝ := 25 / (16 * L ^ 2)
  have hB_le : B ≤ 25 / (16 * (47 / 5 : ℝ) ^ 2) := by
    dsimp [B]
    have hsq : (47 / 5 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL_ge 2
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hB_le_A : B ≤ A := le_trans hB_le (by dsimp [A]; norm_num)
  have hAB : 0 ≤ A - B := sub_nonneg.mpr hB_le_A
  have hsum_eq : y / (81 * (9 / 13 : ℝ) ^ 2) + ((m : ℝ) - y) * B =
      (m : ℝ) * ((y / (m : ℝ)) * (A - B) + B) := by
    dsimp [A]
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    field_simp
    ring
  have hmono_y : (m : ℝ) * ((y / (m : ℝ)) * (A - B) + B) ≤
      (m : ℝ) * (((3 / 2 : ℝ) / L) * (A - B) + B) := by
    apply mul_le_mul_of_nonneg_left _ hm_pos.le
    linarith [mul_le_mul_of_nonneg_right hy_div_m_le hAB]
  have hrhs_eq : (m : ℝ) * (((3 / 2 : ℝ) / L) * (A - B) + B) =
      (m : ℝ) * (((3 / 2 : ℝ) / L) / (81 * (9 / 13 : ℝ) ^ 2) + B * (1 - (3 / 2 : ℝ) / L)) := by
    dsimp [A]
    ring
  linarith

/-! ## Main asymptotic theorem (`m ≥ 13000`) -/

/-- For all `m ≥ 13000`, Abel partial summation and the 6-interval partition yield
`(Nat.primeCounting m : ℝ) < 1.3841 * Chebyshev.theta m / Real.log (Chebyshev.theta m)`. -/
theorem robin_primeCounting_lt_of_ge_13000
    (h_ln2_lo : (9 / 13 : ℝ) < Real.log 2)
    (h_ln2_hi : Real.log 2 < (25 / 36 : ℝ))
    (h_theta_lb : ∀ m : ℕ, 13000 ≤ m → (84 / 100 : ℝ) * (m : ℝ) ≤ Chebyshev.theta (m : ℝ))
    {m : ℕ} (hm : 13000 ≤ m) :
    (Nat.primeCounting m : ℝ) <
      (1.3841 : ℝ) * Chebyshev.theta (m : ℝ) / Real.log (Chebyshev.theta (m : ℝ)) := by
  set T : ℝ := Chebyshev.theta (m : ℝ)
  set L : ℝ := Real.log (m : ℝ)
  set T_lo : ℝ := (84 / 100 : ℝ) * (m : ℝ)
  have hm_real : (13000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : 0 < (m : ℝ) := by linarith
  have hL_ge : (47 / 5 : ℝ) ≤ L := log_ge_47_div_5 hm
  have hL_pos : 0 < L := by linarith
  have hT_ge : T_lo ≤ T := h_theta_lb m hm
  have hT_lo_ge : (10920 : ℝ) ≤ T_lo := by dsimp [T_lo]; linarith
  have hT_lo_pos : 0 < T_lo := by linarith
  have hT_pos : 0 < T := lt_of_lt_of_le hT_lo_pos hT_ge
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  -- Abel summation identity at x = m
  have h_abel : (Nat.primeCounting m : ℝ) =
      T / L + ∫ t in (2 : ℝ)..(m : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2) := by
    have h := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := (m : ℝ)) (by linarith)
    rwa [Nat.floor_natCast] at h
  -- First term bound: (T / L) * (log T / T) = log T / L < 1 + (1 / 3) / (47 / 5)
  have h_term1 : (T / L) * (Real.log T / T) < 1 + (1 / 3 : ℝ) / (47 / 5 : ℝ) := by
    have hcancel : (T / L) * (Real.log T / T) = Real.log T / L := by
      have hne : T ≠ 0 := hT_pos.ne'
      field_simp
    have hT_ub : T ≤ (25 / 18 : ℝ) * (m : ℝ) :=
      le_trans (Chebyshev.theta_le_log4_mul_x hm_pos.le)
        (mul_le_mul_of_nonneg_right (log_four_lt_25_div_18 h_ln2_hi).le hm_pos.le)
    have hlogT_ub : Real.log T < (1 / 3 : ℝ) + L := by
      have h1 : Real.log T ≤ Real.log ((25 / 18 : ℝ) * (m : ℝ)) :=
        Real.log_le_log hT_pos hT_ub
      rw [Real.log_mul (by norm_num) hm_pos.ne'] at h1
      linarith [log_25_div_18_lt_one_div_three]
    have hdiv1 : Real.log T / L < ((1 / 3 : ℝ) + L) / L :=
      div_lt_div_of_pos_right hlogT_ub hL_pos
    have hdiv_eq : ((1 / 3 : ℝ) + L) / L = 1 + (1 / 3 : ℝ) / L := by
      have hne : L ≠ 0 := hL_pos.ne'
      field_simp
      ring
    have hdiv2 : (1 / 3 : ℝ) / L ≤ (1 / 3 : ℝ) / (47 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL_ge
    rw [hcancel]
    linarith
  -- Second term bound: log T / T ≤ L / ((84 / 100) * m)
  have h_logT_div_T : Real.log T / T ≤ L / T_lo := by
    have he_le : Real.exp 1 ≤ T_lo := le_trans exp_one_lt_three.le (by linarith)
    have hanti : Real.log T / T ≤ Real.log T_lo / T_lo :=
      log_div_self_antitoneOn he_le (le_trans he_le hT_ge) hT_ge
    have hT_lo_le_m : T_lo ≤ (m : ℝ) := by dsimp [T_lo]; linarith
    have hlog_le : Real.log T_lo ≤ L := Real.log_le_log hT_lo_pos hT_lo_le_m
    exact le_trans hanti (div_le_div_of_nonneg_right hlog_le hT_lo_pos.le)
  -- Integral bound over [2, m]
  set tail : ℝ := (m : ℝ) * (((3 / 2 : ℝ) / L) / (81 * (9 / 13 : ℝ) ^ 2) +
    (25 / (16 * L ^ 2)) * (1 - (3 / 2 : ℝ) / L))
  have hI_nonneg : 0 ≤ ∫ t in (2 : ℝ)..(m : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith) (fun t ht =>
      div_nonneg (Chebyshev.theta_nonneg t) (mul_nonneg (by linarith [ht.1]) (sq_nonneg _)))
  have hI_ub : ∫ t in (2 : ℝ)..(m : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2) ≤
      (25 / 18 : ℝ) * (iPref + tail) := by
    have hth := integral_theta_div_le h_ln2_hi (x := (m : ℝ)) (by linarith)
    have hsp := integral_one_div_log_sq_split (a := 2) (b := 512) (c := (m : ℝ))
      (by norm_num) (by norm_num) (by linarith)
    have hp := integral_two_to_512_le h_ln2_lo
    have ht : ∫ t in (512 : ℝ)..(m : ℝ), 1 / Real.log t ^ 2 ≤ tail :=
      integral_512_to_m_le h_ln2_lo hm
    rw [hsp] at hth
    linarith
  have h_term2_step1 :
      (∫ t in (2 : ℝ)..(m : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2)) * (Real.log T / T) ≤
        ((25 / 18 : ℝ) * (iPref + tail)) * (L / T_lo) :=
    mul_le_mul hI_ub h_logT_div_T
      (div_nonneg hlogT_pos.le hT_pos.le) (le_trans hI_nonneg hI_ub)
  have h_expand : ((25 / 18 : ℝ) * (iPref + tail)) * (L / T_lo) =
      ((25 / 18 : ℝ) * iPref / (84 / 100 : ℝ)) * (L / (m : ℝ)) +
        ((25 / 18 : ℝ) / (84 / 100 : ℝ)) * ((3 / 2 : ℝ) / (81 * (9 / 13 : ℝ) ^ 2) +
          (25 / 16 : ℝ) * ((1 / L) * (1 - (3 / 2 : ℝ) * (1 / L)))) := by
    dsimp [tail, T_lo]
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    have hL_ne : L ≠ 0 := hL_pos.ne'
    field_simp
  have h_pref_ub : ((25 / 18 : ℝ) * iPref / (84 / 100 : ℝ)) * (L / (m : ℝ)) ≤
      ((25 / 18 : ℝ) * iPref / (84 / 100 : ℝ)) * (10 / 13000 : ℝ) := by
    have hLm := log_div_self_le_10_div_13000 h_ln2_hi hm
    have hc_pos : 0 ≤ (25 / 18 : ℝ) * iPref / (84 / 100 : ℝ) := by
      unfold iPref
      norm_num
    exact mul_le_mul_of_nonneg_left hLm hc_pos
  have h_quad_ub : (1 / L) * (1 - (3 / 2 : ℝ) * (1 / L)) ≤
      (5 / 47 : ℝ) * (1 - (3 / 2 : ℝ) * (5 / 47 : ℝ)) := by
    have ht_le : 1 / L ≤ (5 / 47 : ℝ) := by
      rw [div_le_div_iff₀ hL_pos (by norm_num)]
      linarith
    have ht_pos : 0 < 1 / L := one_div_pos.mpr hL_pos
    have hdiff : (5 / 47 : ℝ) * (1 - (3 / 2 : ℝ) * (5 / 47 : ℝ)) -
        (1 / L) * (1 - (3 / 2 : ℝ) * (1 / L)) =
        ((5 / 47 : ℝ) - 1 / L) * (1 - (3 / 2 : ℝ) * (1 / L + 5 / 47)) := by ring
    have h1 : 0 ≤ (5 / 47 : ℝ) - 1 / L := by linarith
    have h2 : 0 ≤ 1 - (3 / 2 : ℝ) * (1 / L + 5 / 47) := by linarith
    linarith [mul_nonneg h1 h2]
  have h_ratio : (Nat.primeCounting m : ℝ) * (Real.log T / T) < (1.3841 : ℝ) := by
    have h_split : (Nat.primeCounting m : ℝ) * (Real.log T / T) =
        (T / L) * (Real.log T / T) +
          (∫ t in (2 : ℝ)..(m : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2)) *
            (Real.log T / T) := by
      rw [h_abel, add_mul]
    have h_num : (1 + (1 / 3 : ℝ) / (47 / 5 : ℝ)) +
        (((25 / 18 : ℝ) * iPref / (84 / 100 : ℝ)) * (10 / 13000 : ℝ) +
          ((25 / 18 : ℝ) / (84 / 100 : ℝ)) * ((3 / 2 : ℝ) / (81 * (9 / 13 : ℝ) ^ 2) +
            (25 / 16 : ℝ) * ((5 / 47 : ℝ) * (1 - (3 / 2 : ℝ) * (5 / 47 : ℝ))))) <
        (1.3841 : ℝ) := by
      unfold iPref
      norm_num
    rw [h_split]
    rw [h_expand] at h_term2_step1
    linarith
  have h_mul : (Nat.primeCounting m : ℝ) * Real.log T < (1.3841 : ℝ) * T := by
    have h1 := mul_lt_mul_of_pos_right h_ratio hT_pos
    have h2 : (Nat.primeCounting m : ℝ) * (Real.log T / T) * T =
        (Nat.primeCounting m : ℝ) * Real.log T := by
      have hne : T ≠ 0 := hT_pos.ne'
      field_simp
    rwa [h2] at h1
  exact (lt_div_iff₀ hlogT_pos).mpr h_mul

end BuchstabSwitching.External
