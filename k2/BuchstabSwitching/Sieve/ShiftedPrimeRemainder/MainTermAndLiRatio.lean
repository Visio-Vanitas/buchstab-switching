import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.CountingAndRem

/-!
# Main-Term Lower Bound `|A_N| > N / log N` and `Li(N) / |A_N|` Ratio Upper Bound

Establishes `offsetLogIntegral_gt_div_log`, `offsetLogIntegral_sub_div_log_ge`,
`shiftedSet_card_gt_div_log` (Johnston–Starichkova Lemma 3.1), and
`offsetLogIntegral_div_shiftedSet_card_le` (`li_ratio_ub`).
-/

namespace BuchstabSwitching

section MainTermLowerAndLiRatio

private lemma inv_log_continuousOn_Ioi' :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [Set.mem_Ioi.mp ht]
  have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (Set.mem_Ioi.mp ht))
  exact (continuousAt_const.div (Real.continuousAt_log ht0) hlog0).continuousWithinAt

private lemma inv_log_integrable_Icc {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  refine (inv_log_continuousOn_Ioi'.mono ?_).intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  exact Set.mem_Ioi.mpr (by linarith [ht.1])

private lemma integral_inv_log_ge_const {a b c : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hc : Real.log b ≤ c) :
    (b - a) / c ≤ ∫ t in a..b, 1 / Real.log t := by
  have hint1 := inv_log_integrable_Icc ha hab
  calc (b - a) / c
      = ∫ _ in a..b, (1 / c : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ ∫ t in a..b, 1 / Real.log t := by
        refine intervalIntegral.integral_mono_on hab intervalIntegrable_const hint1 ?_
        intro t ht
        have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
        have hlog_le : Real.log t ≤ c := (Real.log_le_log (by linarith [ht.1]) ht.2).trans hc
        exact one_div_le_one_div_of_le hlog_pos hlog_le

private lemma offsetLogIntegral_exp_two_gt :
    Real.exp 2 / 2 < External.offsetLogIntegral (Real.exp 2) := by
  set r : ℝ := Real.exp (1 / 8 : ℝ)
  have hr_gt : (1133 / 1000 : ℝ) < r := by
    by_contra hle
    push Not at hle
    have hpow : r ^ 8 ≤ (1133 / 1000 : ℝ) ^ 8 := pow_le_pow_left₀ (Real.exp_pos _).le hle 8
    have hr8 : r ^ 8 = Real.exp 1 := by
      dsimp only [r]
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hr8] at hpow
    have hnum : (1133 / 1000 : ℝ) ^ 8 < (2716 / 1000 : ℝ) := by norm_num
    linarith [exp_one_ge_2716_div_1000]
  have hr_pow : ∀ k : ℕ, r ^ k = Real.exp ((k : ℝ) / 8) := fun k => by
    dsimp only [r]
    rw [← Real.exp_nat_mul]
    ring_nf
  have hr6_gt2 : (2 : ℝ) < r ^ 6 := by
    have h1 : (2 : ℝ) < (1133 / 1000 : ℝ) ^ 6 := by norm_num
    have h2 : (1133 / 1000 : ℝ) ^ 6 < r ^ 6 :=
      pow_lt_pow_left₀ hr_gt (by norm_num) (by norm_num)
    linarith
  have hr_ge1 : (1 : ℝ) ≤ r := by linarith
  have hr_pow_mono : ∀ {a b : ℕ}, a ≤ b → r ^ a ≤ r ^ b := fun hab =>
    pow_le_pow_right₀ hr_ge1 hab
  have hsplit_sum :
      ∫ t in (r ^ 6)..(r ^ 16), 1 / Real.log t =
        ∑ k ∈ Finset.Ico (6 : ℕ) 16, ∫ t in (r ^ k)..(r ^ (k + 1)), 1 / Real.log t := by
    have hgen : ∀ n : ℕ, 6 ≤ n →
        ∫ t in (r ^ 6)..(r ^ n), 1 / Real.log t =
          ∑ k ∈ Finset.Ico (6 : ℕ) n, ∫ t in (r ^ k)..(r ^ (k + 1)), 1 / Real.log t := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        rw [Finset.sum_Ico_succ_top hm, ← ih]
        have h1 := inv_log_integrable_Icc hr6_gt2.le (hr_pow_mono hm)
        have h2 := inv_log_integrable_Icc (hr6_gt2.le.trans (hr_pow_mono hm))
          (hr_pow_mono (Nat.le_succ m))
        exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    exact hgen 16 (by norm_num)
  have hsplit_all :
      External.offsetLogIntegral (r ^ 16) =
        (∫ t in (2 : ℝ)..(r ^ 6), 1 / Real.log t) +
          ∑ k ∈ Finset.Ico (6 : ℕ) 16, ∫ t in (r ^ k)..(r ^ (k + 1)), 1 / Real.log t := by
    unfold External.offsetLogIntegral
    have h1 := inv_log_integrable_Icc (le_refl 2) hr6_gt2.le
    have h2 := inv_log_integrable_Icc hr6_gt2.le (hr_pow_mono (by norm_num : 6 ≤ 16))
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, hsplit_sum]
  have hlb0 : (r ^ 6 - 2) * (4 / 3 : ℝ) ≤ ∫ t in (2 : ℝ)..(r ^ 6), 1 / Real.log t := by
    have hlog6 : Real.log (r ^ 6) ≤ (3 / 4 : ℝ) := by
      rw [hr_pow 6, Real.log_exp]
      norm_num
    have h := integral_inv_log_ge_const (le_refl 2) hr6_gt2.le hlog6
    linarith
  have hlb_sum :
      ∑ k ∈ Finset.Ico (6 : ℕ) 16, (r ^ (k + 1) - r ^ k) * (8 / ((k : ℝ) + 1)) ≤
        ∑ k ∈ Finset.Ico (6 : ℕ) 16, ∫ t in (r ^ k)..(r ^ (k + 1)), 1 / Real.log t := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk6 : 6 ≤ k := (Finset.mem_Ico.mp hk).1
    have hlogk : Real.log (r ^ (k + 1)) ≤ ((k : ℝ) + 1) / 8 := by
      rw [hr_pow (k + 1), Real.log_exp]
      push_cast
      rfl
    have h := integral_inv_log_ge_const (hr6_gt2.le.trans (hr_pow_mono hk6))
      (hr_pow_mono (Nat.le_succ k)) hlogk
    have heq : (r ^ (k + 1) - r ^ k) / (((k : ℝ) + 1) / 8) =
        (r ^ (k + 1) - r ^ k) * (8 / ((k : ℝ) + 1)) := by
      have hk_ne : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hk_ne]
    rw [← heq]
    simpa [Nat.succ_eq_add_one] using h
  have hsum_id :
      (r ^ 6 - 2) * (4 / 3 : ℝ) +
          ∑ k ∈ Finset.Ico (6 : ℕ) 16, (r ^ (k + 1) - r ^ k) * (8 / ((k : ℝ) + 1)) - r ^ 16 / 2 =
        (∑ k ∈ Finset.Ico (6 : ℕ) 16, (8 / ((k : ℝ) * ((k : ℝ) + 1))) * r ^ k) - 8 / 3 := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ]
    ring
  have hpoly_pos :
      (8 / 3 : ℝ) < ∑ k ∈ Finset.Ico (6 : ℕ) 16, (8 / ((k : ℝ) * ((k : ℝ) + 1))) * r ^ k := by
    have hcomp :
        ∑ k ∈ Finset.Ico (6 : ℕ) 16, (8 / ((k : ℝ) * ((k : ℝ) + 1))) * (1133 / 1000 : ℝ) ^ k <
          ∑ k ∈ Finset.Ico (6 : ℕ) 16, (8 / ((k : ℝ) * ((k : ℝ) + 1))) * r ^ k := by
      refine Finset.sum_lt_sum_of_nonempty ⟨6, by simp⟩ fun k hk => ?_
      have hk6 : 6 ≤ k := (Finset.mem_Ico.mp hk).1
      have hpow_lt : (1133 / 1000 : ℝ) ^ k < r ^ k :=
        pow_lt_pow_left₀ hr_gt (by norm_num) (by omega)
      refine mul_lt_mul_of_pos_left hpow_lt ?_
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      positivity
    have hnum :
        (8 / 3 : ℝ) <
          ∑ k ∈ Finset.Ico (6 : ℕ) 16, (8 / ((k : ℝ) * ((k : ℝ) + 1))) * (1133 / 1000 : ℝ) ^ k := by
      rw [Finset.sum_Ico_eq_sum_range]
      norm_num [Finset.sum_range_succ]
    linarith
  have hr16 : Real.exp 2 = r ^ 16 := by
    rw [hr_pow 16]
    norm_num
  rw [hr16]
  linarith

/-- For all `x ≥ Real.exp 2`, `x / Real.log x < External.offsetLogIntegral x`. -/
theorem offsetLogIntegral_gt_div_log {x : ℝ} (hx : Real.exp 2 ≤ x) :
    x / Real.log x < External.offsetLogIntegral x := by
  let G : ℝ → ℝ := fun t => External.offsetLogIntegral t - t / Real.log t
  have hexp2_gt2 : (2 : ℝ) < Real.exp 2 := by
    have h1 : (2 : ℝ) < (27 / 10 : ℝ) ^ 2 := by norm_num
    have h2 : (27 / 10 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) exp_one_ge_27_div_10 2
    have h3 : (Real.exp 1) ^ 2 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    linarith
  have hG_hasDeriv : ∀ t ∈ Set.Icc (Real.exp 2) x,
      HasDerivAt G (1 / (Real.log t) ^ 2) t := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le (Real.exp_pos 2) ht.1
    have ht_gt2 : 2 < t := lt_of_lt_of_le hexp2_gt2 ht.1
    have hlog_ge2 : (2 : ℝ) ≤ Real.log t := by
      calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 2) ht.1
    have hlog_pos : 0 < Real.log t := by linarith
    have hint : IntervalIntegrable (fun s : ℝ => 1 / Real.log s) MeasureTheory.volume 2 t :=
      inv_log_integrable_Icc (le_refl 2) ht_gt2.le
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => 1 / Real.log s)
        (nhds t) MeasureTheory.volume :=
      inv_log_continuousOn_Ioi'.stronglyMeasurableAtFilter isOpen_Ioi t
        (Set.mem_Ioi.mpr (by linarith))
    have hcont : ContinuousAt (fun s : ℝ => 1 / Real.log s) t :=
      inv_log_continuousOn_Ioi'.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))
    have hintDeriv : HasDerivAt External.offsetLogIntegral (1 / Real.log t) t :=
      intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
    have hfrac : HasDerivAt (fun s : ℝ => s / Real.log s)
        (((1 : ℝ) * Real.log t - t * t⁻¹) / (Real.log t) ^ 2) t :=
      (hasDerivAt_id t).div (Real.hasDerivAt_log ht_pos.ne') hlog_pos.ne'
    convert hintDeriv.sub hfrac using 1
    field_simp [ht_pos.ne', hlog_pos.ne']
    ring
  have hG0 : 0 < G (Real.exp 2) := by
    dsimp only [G]
    rw [Real.log_exp]
    linarith [offsetLogIntegral_exp_two_gt]
  rcases eq_or_lt_of_le hx with rfl | hlt
  · dsimp only [G] at hG0
    linarith
  have hG_cont : ContinuousOn G (Set.Icc (Real.exp 2) x) := fun t ht =>
    (hG_hasDeriv t ht).continuousAt.continuousWithinAt
  have hG_diff : DifferentiableOn ℝ G (interior (Set.Icc (Real.exp 2) x)) := fun t ht =>
    (hG_hasDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hG_nonneg : ∀ t ∈ interior (Set.Icc (Real.exp 2) x), 0 ≤ deriv G t := by
    intro t ht
    rw [(hG_hasDeriv t (interior_subset ht)).deriv]
    positivity
  have hmono : MonotoneOn G (Set.Icc (Real.exp 2) x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) hG_cont hG_diff hG_nonneg
  have hGx : 0 < G x := lt_of_lt_of_le hG0 (hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt.le)
  dsimp only [G] at hGx
  linarith

/-- Lower bound on `Li(x) - x / log x` for `x ≥ 2 * exp 2` via monotonicity of
`t ↦ Li(t) - t / log t` on `[x/2, x]`. -/
theorem offsetLogIntegral_sub_div_log_ge {x : ℝ} (hx : 2 * Real.exp 2 ≤ x) :
    x / (2 * (Real.log x) ^ 2) ≤ External.offsetLogIntegral x - x / Real.log x := by
  let G : ℝ → ℝ := fun t => External.offsetLogIntegral t - t / Real.log t
  have hx2_ge : Real.exp 2 ≤ x / 2 := by linarith
  have hexp2_gt2 : (2 : ℝ) < Real.exp 2 := by
    have h1 : (2 : ℝ) < (27 / 10 : ℝ) ^ 2 := by norm_num
    have h2 : (27 / 10 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) exp_one_ge_27_div_10 2
    have h3 : (Real.exp 1) ^ 2 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    linarith
  have hx2_gt2 : (2 : ℝ) < x / 2 := lt_of_lt_of_le hexp2_gt2 hx2_ge
  have hx2_le_x : x / 2 ≤ x := by linarith
  have hG_hasDeriv : ∀ t ∈ Set.uIcc (x / 2) x,
      HasDerivAt G (1 / (Real.log t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx2_le_x] at ht
    have ht_gt2 : 2 < t := lt_of_lt_of_le hx2_gt2 ht.1
    have ht_pos : 0 < t := by linarith
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith)
    have hint : IntervalIntegrable (fun s : ℝ => 1 / Real.log s) MeasureTheory.volume 2 t :=
      inv_log_integrable_Icc (le_refl 2) ht_gt2.le
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => 1 / Real.log s)
        (nhds t) MeasureTheory.volume :=
      inv_log_continuousOn_Ioi'.stronglyMeasurableAtFilter isOpen_Ioi t
        (Set.mem_Ioi.mpr (by linarith))
    have hcont : ContinuousAt (fun s : ℝ => 1 / Real.log s) t :=
      inv_log_continuousOn_Ioi'.continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))
    have hintDeriv : HasDerivAt External.offsetLogIntegral (1 / Real.log t) t :=
      intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
    have hfrac : HasDerivAt (fun s : ℝ => s / Real.log s)
        (((1 : ℝ) * Real.log t - t * t⁻¹) / (Real.log t) ^ 2) t :=
      (hasDerivAt_id t).div (Real.hasDerivAt_log ht_pos.ne') hlog_pos.ne'
    convert hintDeriv.sub hfrac using 1
    field_simp [ht_pos.ne', hlog_pos.ne']
    ring
  have hint_deriv : IntervalIntegrable (fun t : ℝ => 1 / (Real.log t) ^ 2)
      MeasureTheory.volume (x / 2) x := by
    have hcont : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ 2) (Set.Icc (x / 2) x) := by
      intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      have ht0 : t ≠ 0 := by linarith
      have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
      exact (continuousAt_const.div ((Real.continuousAt_log ht0).pow 2)
        (pow_ne_zero 2 hl0)).continuousWithinAt
    rw [← Set.uIcc_of_le hx2_le_x] at hcont
    exact hcont.intervalIntegrable
  have hftc : ∫ t in (x / 2)..x, 1 / (Real.log t) ^ 2 = G x - G (x / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hG_hasDeriv hint_deriv
  have hGx2_pos : 0 < G (x / 2) := by
    dsimp only [G]
    linarith [offsetLogIntegral_gt_div_log hx2_ge]
  have hint_lb : x / (2 * (Real.log x) ^ 2) ≤ ∫ t in (x / 2)..x, 1 / (Real.log t) ^ 2 := by
    calc x / (2 * (Real.log x) ^ 2)
        = ∫ _ in (x / 2)..x, (1 / (Real.log x) ^ 2 : ℝ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ ∫ t in (x / 2)..x, 1 / (Real.log t) ^ 2 := by
          refine intervalIntegral.integral_mono_on hx2_le_x intervalIntegrable_const hint_deriv ?_
          intro t ht
          have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
          have hlog_le : Real.log t ≤ Real.log x := Real.log_le_log (by linarith [ht.1]) ht.2
          exact one_div_le_one_div_of_le (sq_pos_of_pos hlog_pos)
            (pow_le_pow_left₀ hlog_pos.le hlog_le 2)
  linarith

private lemma rel_loss_bound_of_four_mul_pow18 {x : ℝ} (hx : 4 * (10 : ℝ) ^ 18 ≤ x) :
    (Real.sqrt x * (Real.log x) ^ 2 / (8 * Real.pi) + External.omegaUpperFn x * Real.log x) / x ≤
      1 / 4 := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h40 : (40 : ℝ) ≤ Real.log x := forty_le_log_of_four_mul_pow18 hx
  have hlog_pos : 0 < Real.log x := by linarith
  have hlog_log : (3 : ℝ) ≤ Real.log (Real.log x) := by
    have h27 : (Real.exp 1) ^ 3 < (40 : ℝ) := by
      have h1 : (Real.exp 1) ^ 3 < (274 / 100 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ External.exp_one_lt_274_div_100 (Real.exp_pos 1).le (by norm_num)
      have h2 : (274 / 100 : ℝ) ^ 3 < 40 := by norm_num
      linarith
    have h3 : Real.exp 3 < Real.log x := by
      have he3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      linarith
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (Real.log x) := Real.log_le_log (Real.exp_pos 3) h3.le
  set u : ℝ := Real.log x
  have hx_eq : x = Real.exp u := (Real.exp_log hx_pos).symm
  have hsqrt_eq : Real.sqrt x = Real.exp (u / 2) := by
    have hsq : (Real.exp (u / 2)) ^ 2 = (Real.sqrt x) ^ 2 := by
      rw [← Real.exp_nat_mul, Real.sq_sqrt hx_pos.le]
      have harg : (2 : ℕ) * (u / 2) = u := by norm_num; ring
      rw [harg, Real.exp_log hx_pos]
    nlinarith [Real.exp_pos (u / 2), Real.sqrt_nonneg x]
  have hexp_half : (u / 2) ^ 5 / 120 ≤ Real.exp (u / 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ u / 2) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial] at hsum
    have hpos_terms : (u / 2) ^ 5 / 120 ≤
        1 + u / 2 + (u / 2) ^ 2 / 2 + (u / 2) ^ 3 / 6 + (u / 2) ^ 4 / 24 + (u / 2) ^ 5 / 120 := by
      have : 0 ≤ 1 + u / 2 + (u / 2) ^ 2 / 2 + (u / 2) ^ 3 / 6 + (u / 2) ^ 4 / 24 := by positivity
      linarith
    linarith [hsum]
  have hexp_full : u ^ 4 / 24 ≤ Real.exp u := by
    have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ u) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial] at hsum
    have hpos_terms : u ^ 4 / 24 ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 := by
      have : 0 ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by positivity
      linarith
    linarith [hsum]
  have hterm1 : Real.sqrt x * u ^ 2 / (8 * Real.pi) / x ≤ 1 / 8 * x / x := by
    have h1 : u ^ 2 / Real.sqrt x ≤ 120 * 4 / (u / 2) ^ 3 := by
      have h3_id : 120 * 4 / (u / 2) ^ 3 * ((u / 2) ^ 5 / 120) = u ^ 2 := by
        have hu0 : u ≠ 0 := by linarith
        field_simp
        ring
      rw [hsqrt_eq, div_le_iff₀ (Real.exp_pos _)]
      calc u ^ 2 = (120 * 4 / (u / 2) ^ 3) * ((u / 2) ^ 5 / 120) := h3_id.symm
        _ ≤ (120 * 4 / (u / 2) ^ 3) * Real.exp (u / 2) :=
          mul_le_mul_of_nonneg_left hexp_half (by positivity)
    have h2 : 120 * 4 / (u / 2) ^ 3 ≤ 120 * 4 / (20 : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) (by linarith) 3)
    have h3 : u ^ 2 / Real.sqrt x ≤ 1 := by linarith
    have hpi : 24 ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hid : Real.sqrt x * u ^ 2 / (8 * Real.pi) / x = (u ^ 2 / Real.sqrt x) / (8 * Real.pi) := by
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx_pos.le
      field_simp [hx_pos.ne', hsqrt_pos.ne']
      nlinarith
    rw [hid]
    calc (u ^ 2 / Real.sqrt x) / (8 * Real.pi)
        ≤ 1 / (8 * Real.pi) := div_le_div_of_nonneg_right h3 (by positivity)
      _ ≤ 1 / 24 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi
      _ ≤ 1 / 8 * x / x := by
          rw [mul_div_cancel_right₀ _ hx_pos.ne']
          norm_num
  have hterm2 : External.omegaUpperFn x * u / x ≤ 1 / 8 := by
    have h1 : External.omegaUpperFn x * u = (1.3841 : ℝ) * u ^ 2 / Real.log u := by
      unfold External.omegaUpperFn
      ring
    have h2 : External.omegaUpperFn x * u / x ≤ (1.3841 : ℝ) * u ^ 2 / 3 / (u ^ 4 / 24) := by
      rw [h1, hx_eq]
      have hnum : (1.3841 : ℝ) * u ^ 2 / Real.log u ≤ (1.3841 : ℝ) * u ^ 2 / 3 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog_log
      have hden_pos : 0 < u ^ 4 / 24 := by positivity
      calc (1.3841 : ℝ) * u ^ 2 / Real.log u / Real.exp u
          ≤ ((1.3841 : ℝ) * u ^ 2 / 3) / Real.exp u :=
            div_le_div_of_nonneg_right hnum (Real.exp_pos u).le
        _ ≤ ((1.3841 : ℝ) * u ^ 2 / 3) / (u ^ 4 / 24) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hexp_full
    have h3 : (1.3841 : ℝ) * u ^ 2 / 3 / (u ^ 4 / 24) = (1.3841 : ℝ) * 8 / u ^ 2 := by
      have hu0 : u ≠ 0 := by linarith
      field_simp
      ring
    have h4 : (1.3841 : ℝ) * 8 / u ^ 2 ≤ (1.3841 : ℝ) * 8 / 40 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) h40 2)
    linarith
  have hadd : (Real.sqrt x * u ^ 2 / (8 * Real.pi) + External.omegaUpperFn x * u) / x =
      Real.sqrt x * u ^ 2 / (8 * Real.pi) / x + External.omegaUpperFn x * u / x := by
    ring
  rw [hadd]
  have hterm1' : Real.sqrt x * u ^ 2 / (8 * Real.pi) / x ≤ 1 / 8 := by
    simpa [mul_div_cancel_right₀ _ hx_pos.ne'] using hterm1
  linarith

private lemma loss_le_quarter_div_log_sq {x : ℝ} (hx : 4 * (10 : ℝ) ^ 18 ≤ x) :
    Real.sqrt x * Real.log x / (8 * Real.pi) + External.omegaUpperFn x ≤
      x / (4 * (Real.log x) ^ 2) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h40 : (40 : ℝ) ≤ Real.log x := forty_le_log_of_four_mul_pow18 hx
  have hlog_pos : 0 < Real.log x := by linarith
  have hlog_log : (3 : ℝ) ≤ Real.log (Real.log x) := by
    have h27 : (Real.exp 1) ^ 3 < (40 : ℝ) := by
      have h1 : (Real.exp 1) ^ 3 < (274 / 100 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ External.exp_one_lt_274_div_100 (Real.exp_pos 1).le (by norm_num)
      have h2 : (274 / 100 : ℝ) ^ 3 < 40 := by norm_num
      linarith
    have h3 : Real.exp 3 < Real.log x := by
      have he3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      linarith
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (Real.log x) := Real.log_le_log (Real.exp_pos 3) h3.le
  set u : ℝ := Real.log x
  have hx_eq : x = Real.exp u := (Real.exp_log hx_pos).symm
  have hsqrt_eq : Real.sqrt x = Real.exp (u / 2) := by
    have hsq : (Real.exp (u / 2)) ^ 2 = (Real.sqrt x) ^ 2 := by
      rw [← Real.exp_nat_mul, Real.sq_sqrt hx_pos.le]
      have harg : (2 : ℕ) * (u / 2) = u := by norm_num; ring
      rw [harg, Real.exp_log hx_pos]
    nlinarith [Real.exp_pos (u / 2), Real.sqrt_nonneg x]
  have hexp_half : (u / 2) ^ 5 / 120 ≤ Real.exp (u / 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ u / 2) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial] at hsum
    have hpos_terms : (u / 2) ^ 5 / 120 ≤
        1 + u / 2 + (u / 2) ^ 2 / 2 + (u / 2) ^ 3 / 6 + (u / 2) ^ 4 / 24 + (u / 2) ^ 5 / 120 := by
      have : 0 ≤ 1 + u / 2 + (u / 2) ^ 2 / 2 + (u / 2) ^ 3 / 6 + (u / 2) ^ 4 / 24 := by positivity
      linarith
    linarith [hsum]
  have hexp_full : u ^ 5 / 120 ≤ Real.exp u := by
    have hsum := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ u) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial] at hsum
    have hpos_terms : u ^ 5 / 120 ≤
        1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 := by
      have : 0 ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 := by positivity
      linarith
    linarith [hsum]
  have hterm1 : Real.sqrt x * u ^ 3 / (8 * Real.pi) / x ≤ 1 / 8 := by
    have h1 : u ^ 3 / Real.sqrt x ≤ 120 * 8 / (u / 2) ^ 2 := by
      have h3_id : 120 * 8 / (u / 2) ^ 2 * ((u / 2) ^ 5 / 120) = u ^ 3 := by
        have hu0 : u ≠ 0 := by linarith
        field_simp
        ring
      rw [hsqrt_eq, div_le_iff₀ (Real.exp_pos _)]
      calc u ^ 3 = (120 * 8 / (u / 2) ^ 2) * ((u / 2) ^ 5 / 120) := h3_id.symm
        _ ≤ (120 * 8 / (u / 2) ^ 2) * Real.exp (u / 2) :=
          mul_le_mul_of_nonneg_left hexp_half (by positivity)
    have h2 : 120 * 8 / (u / 2) ^ 2 ≤ 120 * 8 / (20 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) (by linarith) 2)
    have h3 : u ^ 3 / Real.sqrt x ≤ 3 := by linarith
    have hpi : 24 ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hid : Real.sqrt x * u ^ 3 / (8 * Real.pi) / x = (u ^ 3 / Real.sqrt x) / (8 * Real.pi) := by
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx_pos.le
      field_simp [hx_pos.ne', hsqrt_pos.ne']
      nlinarith
    rw [hid]
    calc (u ^ 3 / Real.sqrt x) / (8 * Real.pi)
        ≤ 3 / (8 * Real.pi) := div_le_div_of_nonneg_right h3 (by positivity)
      _ ≤ 3 / 24 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi
      _ = 1 / 8 := by norm_num
  have hterm2 : External.omegaUpperFn x * u ^ 2 / x ≤ 1 / 8 := by
    have h1 : External.omegaUpperFn x * u ^ 2 = (1.3841 : ℝ) * u ^ 3 / Real.log u := by
      unfold External.omegaUpperFn
      ring
    have h2 : External.omegaUpperFn x * u ^ 2 / x ≤ (1.3841 : ℝ) * u ^ 3 / 3 / (u ^ 5 / 120) := by
      rw [h1, hx_eq]
      have hnum : (1.3841 : ℝ) * u ^ 3 / Real.log u ≤ (1.3841 : ℝ) * u ^ 3 / 3 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog_log
      have hden_pos : 0 < u ^ 5 / 120 := by positivity
      calc (1.3841 : ℝ) * u ^ 3 / Real.log u / Real.exp u
          ≤ ((1.3841 : ℝ) * u ^ 3 / 3) / Real.exp u :=
            div_le_div_of_nonneg_right hnum (Real.exp_pos u).le
        _ ≤ ((1.3841 : ℝ) * u ^ 3 / 3) / (u ^ 5 / 120) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hexp_full
    have h3 : (1.3841 : ℝ) * u ^ 3 / 3 / (u ^ 5 / 120) = (1.3841 : ℝ) * 40 / u ^ 2 := by
      have hu0 : u ≠ 0 := by linarith
      field_simp
      ring
    have h4 : (1.3841 : ℝ) * 40 / u ^ 2 ≤ (1.3841 : ℝ) * 40 / 40 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) h40 2)
    linarith
  have hsum_le :
      (Real.sqrt x * u / (8 * Real.pi) + External.omegaUpperFn x) * (u ^ 2 / x) ≤ 1 / 4 := by
    have hid :
        (Real.sqrt x * u / (8 * Real.pi) + External.omegaUpperFn x) * (u ^ 2 / x) =
          Real.sqrt x * u ^ 3 / (8 * Real.pi) / x + External.omegaUpperFn x * u ^ 2 / x := by
      ring
    rw [hid]
    linarith
  have hdiv :
      Real.sqrt x * u / (8 * Real.pi) + External.omegaUpperFn x ≤ x / (4 * u ^ 2) := by
    have hpos : 0 < u ^ 2 / x := by positivity
    have hmul := (le_div_iff₀ hpos).mpr hsum_le
    have heq : (1 / 4 : ℝ) / (u ^ 2 / x) = x / (4 * u ^ 2) := by
      field_simp [hx_pos.ne', hlog_pos.ne']
    exact hmul.trans_eq heq
  exact hdiv

/-- Johnston–Starichkova Lemma 3.1 (`|A_N| > N / log N`) derived for `4 * 10^18 ≤ N` directly
from `SchoenfeldRHBound` + `RobinOmegaBound`. -/
theorem shiftedSet_card_gt_div_log {li2 : ℝ} {N : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hN : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ)) :
    (N : ℝ) / Real.log (N : ℝ) < ((shiftedCoprimePrimes N).card : ℝ) := by
  have hN_ge3 : 3 ≤ N := by
    have : (3 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN
  have h40 : (40 : ℝ) ≤ Real.log (N : ℝ) := forty_le_log_of_four_mul_pow18 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := by linarith
  have hS : External.SchoenfeldRHBound li2 := hCls.schoenfeld hGRH
  have hli2_pos : 0 < li2 := (li2_bounds_of_schoenfeld hS).1.trans' (by norm_num)
  have hpi_lb := External.le_primeCounting_of_schoenfeld hS (by exact_mod_cast hN_ge3 : (3 : ℝ) ≤ (N : ℝ))
  have hom_lt := hCls.robin.lt_omegaUpperFn hN_ge3
  have hA_lb : External.offsetLogIntegral (N : ℝ) -
      (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ)) <
      ((shiftedCoprimePrimes N).card : ℝ) := by
    rw [shiftedCoprimePrimes_card_eq_pi_sub]
    dsimp only [External.logIntegral] at hpi_lb
    linarith
  have hexp2 : 2 * Real.exp 2 ≤ (N : ℝ) := by
    have h2e2 : 2 * Real.exp 2 ≤ 2 * (274 / 100 : ℝ) ^ 2 := by
      have hpow : Real.exp 2 = (Real.exp 1) ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have hle : (Real.exp 1) ^ 2 ≤ (274 / 100 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le External.exp_one_lt_274_div_100.le 2
      linarith
    linarith
  have hLi_diff := offsetLogIntegral_sub_div_log_ge hexp2
  have hloss_le := loss_le_quarter_div_log_sq hN
  have hquarter_lt_half :
      (N : ℝ) / (4 * (Real.log (N : ℝ)) ^ 2) < (N : ℝ) / (2 * (Real.log (N : ℝ)) ^ 2) := by
    refine div_lt_div_of_pos_left hN_pos (by positivity) ?_
    nlinarith [sq_pos_of_pos hlog_pos]
  linarith

lemma sqrt_mul_log_sq_div_self_antitoneOn :
    AntitoneOn (fun x : ℝ => Real.sqrt x * (Real.log x) ^ 2 / x) (Set.Ici (Real.exp 4)) := by
  intro x hx y hy hxy
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx
  have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
  have hsqrt_x : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_y : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy_pos
  have hlx_ge : (2 : ℝ) ≤ Real.log x / 2 := by
    have : (4 : ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 4]
      exact Real.log_le_log (Real.exp_pos 4) hx
    linarith
  have hly_ge : (2 : ℝ) ≤ Real.log y / 2 :=
    hlx_ge.trans (div_le_div_of_nonneg_right (Real.log_le_log hx_pos hxy) (by norm_num))
  have hanti := External.sq_div_exp_antitoneOn hlx_ge hly_ge
    (div_le_div_of_nonneg_right (Real.log_le_log hx_pos hxy) (by norm_num))
  have hid : ∀ z : ℝ, 0 < z →
      Real.sqrt z * (Real.log z) ^ 2 / z = 4 * ((Real.log z / 2) ^ 2 / Real.exp (Real.log z / 2)) := by
    intro z hz
    have hsqrt_z : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
    have hexp_half : Real.exp (Real.log z / 2) = Real.sqrt z := by
      have hsq : (Real.exp (Real.log z / 2)) ^ 2 = (Real.sqrt z) ^ 2 := by
        rw [← Real.exp_nat_mul, Real.sq_sqrt hz.le]
        have harg : (2 : ℕ) * (Real.log z / 2) = Real.log z := by norm_num; ring
        rw [harg, Real.exp_log hz]
      nlinarith [Real.exp_pos (Real.log z / 2)]
    rw [hexp_half]
    have hsq : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz.le
    field_simp [hz.ne', hsqrt_z.ne']
    nlinarith
  dsimp only
  rw [hid x hx_pos, hid y hy_pos]
  exact mul_le_mul_of_nonneg_left hanti (by norm_num)

/-- Explicit upper bound on `Li(N) / |A_N|` matching `primes_and_mertens.py:li_ratio_ub`,
uniformly for `4 * 10^18 ≤ X_lo ≤ N`. -/
theorem offsetLogIntegral_div_shiftedSet_card_le {li2 X_lo : ℝ} {N : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) :
    External.offsetLogIntegral (N : ℝ) / ((shiftedCoprimePrimes N).card : ℝ) ≤
      (1 - (Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) +
        External.omegaUpperFn X_lo * Real.log X_lo) / X_lo)⁻¹ := by
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hN_ge3 : 3 ≤ N := by
    have : (3 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN_real
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN_real
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith [forty_le_log_of_four_mul_pow18 hN_real]
  have hexp4_lt : Real.exp 4 ≤ 4 * (10 : ℝ) ^ 18 := by
    have hpow : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hle : (Real.exp 1) ^ 4 ≤ (274 / 100 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le External.exp_one_lt_274_div_100.le 4
    have hnum : (274 / 100 : ℝ) ^ 4 ≤ 4 * (10 : ℝ) ^ 18 := by norm_num
    linarith
  have hexp2_lt : Real.exp 2 ≤ 4 * (10 : ℝ) ^ 18 :=
    (Real.exp_le_exp.mpr (by norm_num : (2 : ℝ) ≤ 4)).trans hexp4_lt
  have hLi_gt := offsetLogIntegral_gt_div_log (hexp2_lt.trans hN_real)
  have hLi_pos : 0 < External.offsetLogIntegral (N : ℝ) :=
    lt_trans (div_pos hN_pos hlogN_pos) hLi_gt
  have hA_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) :=
    lt_trans (div_pos hN_pos hlogN_pos) (shiftedSet_card_gt_div_log hGRH hCls hN_real)
  have hS : External.SchoenfeldRHBound li2 := hCls.schoenfeld hGRH
  have hli2_pos : 0 < li2 := (li2_bounds_of_schoenfeld hS).1.trans' (by norm_num)
  have hpi_lb := External.le_primeCounting_of_schoenfeld hS (by exact_mod_cast hN_ge3 : (3 : ℝ) ≤ (N : ℝ))
  have hom_lt := hCls.robin.lt_omegaUpperFn hN_ge3
  have hA_lb : External.offsetLogIntegral (N : ℝ) -
      (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ)) ≤
      ((shiftedCoprimePrimes N).card : ℝ) := by
    rw [shiftedCoprimePrimes_card_eq_pi_sub]
    dsimp only [External.logIntegral] at hpi_lb
    linarith
  have hA_div_Li :
      1 - (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ)) /
          External.offsetLogIntegral (N : ℝ) ≤
        ((shiftedCoprimePrimes N).card : ℝ) / External.offsetLogIntegral (N : ℝ) := by
    have h1 := div_le_div_of_nonneg_right hA_lb hLi_pos.le
    rw [sub_div, div_self hLi_pos.ne'] at h1
    exact h1
  have hloss_nonneg :
      0 ≤ Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ) := by
    have hom_pos := External.omegaUpperFn_pos_of_three_le hN_ge3
    positivity
  have hLi_inv :
      (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ)) /
          External.offsetLogIntegral (N : ℝ) ≤
        (Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (8 * Real.pi) +
          External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ)) / (N : ℝ) := by
    have h1 :
        (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ)) /
            External.offsetLogIntegral (N : ℝ) ≤
          (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ)) /
            ((N : ℝ) / Real.log (N : ℝ)) :=
      div_le_div_of_nonneg_left hloss_nonneg (div_pos hN_pos hlogN_pos) hLi_gt.le
    have h2 :
        (Real.sqrt (N : ℝ) * Real.log (N : ℝ) / (8 * Real.pi) + External.omegaUpperFn (N : ℝ)) /
            ((N : ℝ) / Real.log (N : ℝ)) =
          (Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (8 * Real.pi) +
            External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ)) / (N : ℝ) := by
      field_simp [hN_pos.ne', hlogN_pos.ne']
    exact h1.trans_eq h2
  have hanti1 :
      Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (8 * Real.pi) / (N : ℝ) ≤
        Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) / X_lo := by
    have hbase := sqrt_mul_log_sq_div_self_antitoneOn
      (hexp4_lt.trans hX_lo) (hexp4_lt.trans hN_real) hX_N
    have hdiv := div_le_div_of_nonneg_right hbase (by positivity : (0 : ℝ) ≤ 8 * Real.pi)
    have hL : Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (N : ℝ) / (8 * Real.pi) =
        Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (8 * Real.pi) / (N : ℝ) := by ring
    have hR : Real.sqrt X_lo * (Real.log X_lo) ^ 2 / X_lo / (8 * Real.pi) =
        Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) / X_lo := by ring
    linarith
  have hanti2 :
      External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ) / (N : ℝ) ≤
        External.omegaUpperFn X_lo * Real.log X_lo / X_lo :=
    External.omegaUpperFn_mul_log_div_self_le (hexp2_lt.trans hX_lo) hX_N
  have hanti_sum :
      (Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (8 * Real.pi) +
          External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ)) / (N : ℝ) ≤
        (Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) +
          External.omegaUpperFn X_lo * Real.log X_lo) / X_lo := by
    have h1 :
        (Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (8 * Real.pi) +
            External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ)) / (N : ℝ) =
          Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (8 * Real.pi) / (N : ℝ) +
            External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ) / (N : ℝ) := by ring
    have h2 :
        (Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) +
            External.omegaUpperFn X_lo * Real.log X_lo) / X_lo =
          Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) / X_lo +
            External.omegaUpperFn X_lo * Real.log X_lo / X_lo := by ring
    linarith
  have hrel_lo := rel_loss_bound_of_four_mul_pow18 hX_lo
  have hden_pos :
      0 < 1 - (Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) +
        External.omegaUpperFn X_lo * Real.log X_lo) / X_lo := by linarith
  have hcomb :
      1 - (Real.sqrt X_lo * (Real.log X_lo) ^ 2 / (8 * Real.pi) +
          External.omegaUpperFn X_lo * Real.log X_lo) / X_lo ≤
        ((shiftedCoprimePrimes N).card : ℝ) / External.offsetLogIntegral (N : ℝ) := by
    linarith
  have hinv := inv_anti₀ hden_pos hcomb
  rwa [inv_div] at hinv

end MainTermLowerAndLiRatio

end BuchstabSwitching
