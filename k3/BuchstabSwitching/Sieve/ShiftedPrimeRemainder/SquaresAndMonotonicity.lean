import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.CountingAndRem
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.MainTermAndLiRatio

/-!
# Prime-Square Divisible Shifted Counts and `epd_norm` Monotonicity

Bounds on `|A_{N, q^2}|` (unconditional `N / q^2` and GRH-conditional), plus the
normalized per-modulus remainder envelope `epdNormFn`, its antitonicity `epd_norm_antitone`,
and the combined normalized remainder bound `abs_shifted_rem_div_card_le_epdNorm`.
-/

namespace BuchstabSwitching

section SquareDivisibleBounds

/-- Unconditional bound `|A_{N, q^2}| ≤ N / q^2` valid for all `N, q : ℕ`. -/
theorem squareDivisible_card_le_div (N q : ℕ) :
    ((squareDivisibleShifted N q).card : ℝ) ≤ (N : ℝ) / (q : ℝ) ^ 2 := by
  by_cases hq0 : q = 0
  · subst hq0
    have hempty : squareDivisibleShifted N 0 = ∅ := by
      ext p
      simp only [squareDivisibleShifted, shiftedCoprimePrimes, Finset.mem_filter, Finset.mem_range,
        Finset.notMem_empty, iff_false]
      rintro ⟨⟨hpN, _, _⟩, hdvd⟩
      have h0 : 0 ∣ N - p := by simpa using hdvd
      rw [zero_dvd_iff] at h0
      omega
    simp [hempty]
  have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
  have hq2_pos : 0 < q ^ 2 := pow_pos hq_pos 2
  have hinj : Set.InjOn (fun p => (N - p) / q ^ 2) (squareDivisibleShifted N q : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ hEq
    have hp₁' := Finset.mem_filter.mp hp₁
    have hp₂' := Finset.mem_filter.mp hp₂
    have hp₁N : p₁ < N := Finset.mem_range.mp (Finset.mem_filter.mp hp₁'.1).1
    have hp₂N : p₂ < N := Finset.mem_range.mp (Finset.mem_filter.mp hp₂'.1).1
    have hmul : ((N - p₁) / q ^ 2) * q ^ 2 = ((N - p₂) / q ^ 2) * q ^ 2 := by
      dsimp only at hEq
      rw [hEq]
    rw [Nat.div_mul_cancel hp₁'.2, Nat.div_mul_cancel hp₂'.2] at hmul
    omega
  have hmaps : Finset.image (fun p => (N - p) / q ^ 2) (squareDivisibleShifted N q) ⊆
      Finset.Icc 1 (N / q ^ 2) := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨p, hp, rfl⟩
    have hp' := Finset.mem_filter.mp hp
    have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp'.1).1
    have hsub_pos : 0 < N - p := Nat.sub_pos_of_lt hpN
    have hk_pos : 0 < (N - p) / q ^ 2 := by
      rcases hp'.2 with ⟨m, hm⟩
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hm; omega
        · exact hpos
      rw [hm, Nat.mul_div_cancel_left _ hq2_pos]
      exact hm_pos
    exact Finset.mem_Icc.mpr ⟨hk_pos, Nat.div_le_div_right (Nat.sub_le N p)⟩
  have hcard_le : (squareDivisibleShifted N q).card ≤ N / q ^ 2 := by
    calc (squareDivisibleShifted N q).card
        = (Finset.image (fun p => (N - p) / q ^ 2) (squareDivisibleShifted N q)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (N / q ^ 2)).card := Finset.card_le_card hmaps
      _ = N / q ^ 2 := by simp
  have hq2_real_pos : (0 : ℝ) < (q : ℝ) ^ 2 := by exact_mod_cast hq2_pos
  rw [le_div_iff₀ hq2_real_pos]
  exact_mod_cast (Nat.le_div_iff_mul_le hq2_pos).mp hcard_le

private lemma squareDivisible_card_eq_sieveDivMass (N q : ℕ) :
    ((squareDivisibleShifted N q).card : ℝ) =
      sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) (q ^ 2) := by
  rw [sieveDivMass_shiftedSet]
  rfl

/-- Elementary decomposition `|A_{N, q^2}| ≤ |A_N| / (q(q-1)) + |r_N(q^2)|` for prime `q`. -/
theorem squareDivisible_card_le_add_rem {N q : ℕ} (hq : q.Prime) :
    ((squareDivisibleShifted N q).card : ℝ) ≤
      ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) +
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun d => 1 / (Nat.totient d : ℝ)) (q ^ 2)| := by
  have htot : (Nat.totient (q ^ 2) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
    have hnat : Nat.totient (q ^ 2) = q * (q - 1) := by
      rw [Nat.totient_prime_pow hq (by norm_num)]
      ring_nf
    have hq1 : 1 ≤ q := hq.one_lt.le
    rw [hnat]
    push_cast [hq1]
    ring
  have hrem := sieveDivMass_eq_main_add_rem (shiftedSet N) (fun _ => (1 : ℝ))
    (fun d => 1 / (Nat.totient d : ℝ)) (q ^ 2)
  rw [squareDivisible_card_eq_sieveDivMass, hrem, sieveMass_shiftedSet, htot]
  have hle : sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun d => 1 / (Nat.totient d : ℝ)) (q ^ 2) ≤
      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun d => 1 / (Nat.totient d : ℝ)) (q ^ 2)| :=
    le_abs_self _
  have hdiv : (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) * ((shiftedCoprimePrimes N).card : ℝ) =
      ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := by ring
  linarith

/-- Under GRH, for `q` prime with `¬ q ∣ N` and `q^2 ≤ √N`,
`|A_{N, q^2}| ≤ |A_N| / (q(q-1)) + (c_π(X_lo) + 1/(16π)) √N log N + ω_ub(N)`. -/
theorem squareDivisible_card_le_grh {li2 X_lo : ℝ} {N q : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ))
    (hq : q.Prime) (hqN : ¬ q ∣ N) (hq2_sqrt : ((q ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ)) :
    ((squareDivisibleShifted N q).card : ℝ) ≤
      ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) +
        ((External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
          External.omegaUpperFn (N : ℝ)) := by
  have hq2_ge3 : 3 ≤ q ^ 2 := by
    have hq2 : 2 ≤ q := hq.two_le
    nlinarith
  have hcop : Nat.Coprime (q ^ 2) N :=
    (hq.coprime_iff_not_dvd.mpr hqN).pow_left 2
  have hbd := shifted_rem_bound hGRH hCls hX_lo hX_N hq2_ge3 hq2_sqrt hcop
  linarith [squareDivisible_card_le_add_rem (N := N) hq]

end SquareDivisibleBounds

section EpdNormMonotonicity

/-- Normalized per-modulus GRH remainder envelope (`primes_and_mertens.py:epd_norm_iv`):
`(c_π(X_lo) + 1/(16π)) * (log x)^2 / √x + ω_ub(x) * log x / x`. -/
noncomputable def epdNormFn (X_lo li2 x : ℝ) : ℝ :=
  (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * (Real.log x) ^ 2 / Real.sqrt x +
    External.omegaUpperFn x * Real.log x / x

/-- For fixed `X_lo ≥ 4 * 10^18` and `0 ≤ li2`, `epdNormFn X_lo li2` is antitone on `[X_lo, ∞)`. -/
theorem epd_norm_antitoneOn {X_lo li2 : ℝ} (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hli2 : 0 ≤ li2) :
    AntitoneOn (epdNormFn X_lo li2) (Set.Ici X_lo) := by
  intro x hx y hy hxy
  have hx_lo : 4 * (10 : ℝ) ^ 18 ≤ x := hX_lo.trans hx
  have hy_lo : 4 * (10 : ℝ) ^ 18 ≤ y := hX_lo.trans hy
  have hX1 : (1 : ℝ) < X_lo := lt_of_lt_of_le (by norm_num) hX_lo
  have hcoeff_nonneg : 0 ≤ External.c_pi X_lo li2 + 1 / (16 * Real.pi) := by
    have hc := External.c_pi_nonneg hX1 hli2
    have hpi := Real.pi_pos
    positivity
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
  have h1 := sqrt_mul_log_sq_div_self_antitoneOn
    (hexp4_lt.trans hx_lo) (hexp4_lt.trans hy_lo) hxy
  have h1' : (Real.log y) ^ 2 / Real.sqrt y ≤ (Real.log x) ^ 2 / Real.sqrt x := by
    have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_lo
    have hy_pos : 0 < y := lt_of_lt_of_le (by norm_num) hy_lo
    have hsqrt_x : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hsqrt_y : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy_pos
    have hid : ∀ z : ℝ, 0 < z →
        Real.sqrt z * (Real.log z) ^ 2 / z = (Real.log z) ^ 2 / Real.sqrt z := by
      intro z hz
      have hsq : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz.le
      field_simp [hz.ne', (Real.sqrt_pos.mpr hz).ne']
      nlinarith
    dsimp only at h1
    rwa [hid x hx_pos, hid y hy_pos] at h1
  have h2 := External.omegaUpperFn_mul_log_div_self_le (hexp2_lt.trans hx_lo) hxy
  unfold epdNormFn
  have hmul :
      (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * ((Real.log y) ^ 2 / Real.sqrt y) ≤
        (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * ((Real.log x) ^ 2 / Real.sqrt x) :=
    mul_le_mul_of_nonneg_left h1' hcoeff_nonneg
  have hrewrite : ∀ z : ℝ,
      (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * (Real.log z) ^ 2 / Real.sqrt z =
        (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * ((Real.log z) ^ 2 / Real.sqrt z) := by
    intro z; ring
  rw [hrewrite y, hrewrite x]
  linarith

/-- Pointwise inequality version of `epd_norm_antitoneOn` for `4 * 10^18 ≤ X_lo ≤ N`. -/
theorem epd_norm_antitone {X_lo li2 : ℝ} {N : ℕ}
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hli2 : 0 ≤ li2) (hX_N : X_lo ≤ (N : ℝ)) :
    (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * (Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ) +
        External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ) / (N : ℝ) ≤
      (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * (Real.log X_lo) ^ 2 / Real.sqrt X_lo +
        External.omegaUpperFn X_lo * Real.log X_lo / X_lo :=
  epd_norm_antitoneOn hX_lo hli2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hX_N) hX_N

/-- Combined normalized remainder bound: for `4 * 10^18 ≤ X_lo ≤ N`, `3 ≤ d ≤ √N`, `(d, N) = 1`,
`|r_N(d)| / |A_N| ≤ epdNormFn X_lo li2 X_lo`. -/
theorem abs_shifted_rem_div_card_le_epdNorm {li2 X_lo : ℝ} {N d : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ))
    (hd : 3 ≤ d) (hd_sqrt : (d : ℝ) ≤ Real.sqrt (N : ℝ)) (hcop : Nat.Coprime d N) :
    |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) d| /
        ((shiftedCoprimePrimes N).card : ℝ) ≤
      epdNormFn X_lo li2 X_lo := by
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN_real
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith [forty_le_log_of_four_mul_pow18 hN_real]
  have hli2_nonneg : 0 ≤ li2 := hCls.li2_bounds.1.le.trans' (by norm_num)
  have hrem := shifted_rem_bound hGRH hCls hX_lo hX_N hd hd_sqrt hcop
  have hcard := shiftedSet_card_gt_div_log hGRH hCls hN_real
  have hdiv :
      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) d| /
          ((shiftedCoprimePrimes N).card : ℝ) ≤
        ((External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
          External.omegaUpperFn (N : ℝ)) / ((N : ℝ) / Real.log (N : ℝ)) := by
    have h1 :
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) (fun k => 1 / (Nat.totient k : ℝ)) d| /
            ((shiftedCoprimePrimes N).card : ℝ) ≤
          ((External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
            External.omegaUpperFn (N : ℝ)) / ((shiftedCoprimePrimes N).card : ℝ) :=
      div_le_div_of_nonneg_right hrem (Nat.cast_nonneg _)
    have hrem_nonneg :
        0 ≤ (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
          External.omegaUpperFn (N : ℝ) := (abs_nonneg _).trans hrem
    have h2 :
        ((External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
            External.omegaUpperFn (N : ℝ)) / ((shiftedCoprimePrimes N).card : ℝ) ≤
          ((External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
            External.omegaUpperFn (N : ℝ)) / ((N : ℝ) / Real.log (N : ℝ)) :=
      div_le_div_of_nonneg_left hrem_nonneg (div_pos hN_pos hlogN_pos) hcard.le
    exact h1.trans h2
  have heq :
      ((External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
          External.omegaUpperFn (N : ℝ)) / ((N : ℝ) / Real.log (N : ℝ)) =
        epdNormFn X_lo li2 (N : ℝ) := by
    have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
    have hterm :
        (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) *
            (Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2) / (N : ℝ) =
          (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * (Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ) := by
      conv_lhs => rhs; rw [← hsq]
      field_simp [hsqrt_pos.ne']
    unfold epdNormFn
    calc ((External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) +
            External.omegaUpperFn (N : ℝ)) / ((N : ℝ) / Real.log (N : ℝ))
        = (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) *
            (Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2) / (N : ℝ) +
            External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ) / (N : ℝ) := by
          field_simp [hN_pos.ne', hlogN_pos.ne']
      _ = (External.c_pi X_lo li2 + 1 / (16 * Real.pi)) * (Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ) +
            External.omegaUpperFn (N : ℝ) * Real.log (N : ℝ) / (N : ℝ) := by rw [hterm]
  rw [heq] at hdiv
  exact hdiv.trans (epd_norm_antitone hX_lo hli2_nonneg hX_N)

end EpdNormMonotonicity

end BuchstabSwitching
