import BuchstabSwitching.Sieve.LinearSieveBJS.Contraction
import Mathlib.Tactic

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 3. Universal Exponential Decay of `fHat` (BJS v6 Lemma 8 / Nathanson Lemma 9.7) -/

section FHatDecay

/-- Valid decay sequence for `fHat n s ≤ 2 * e^2 * c_n^{n-1} * h_bjs s`. -/
def ValidDecaySeq (c_seq : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → 0 < c_seq n ∧ c_seq n ≤ 9607 / 10000) ∧
    (∀ n s, 1 ≤ n → (if Even n then (2 : ℝ) else 1) ≤ s →
      fHat n s ≤ 2 * Real.exp 2 * (c_seq n) ^ (n - 1) * h_bjs s)

theorem fHat_two_eq_of_Icc {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    fHat 2 s = (3 * Real.log (3 / (s - 1)) - (4 - s)) / s := by
  have htail := (fHat_tail_integral 1 le_rfl (s := s) (M := 4) (by norm_num)).1
    (by decide) hs2
  rw [htail]
  have hEq : EqOn (fun t => fHat 1 (t - 1)) (fun t => 3 * (1 / (t - 1)) - 1) (uIcc s 4) := by
    intro t ht
    rw [uIcc_of_le hs4] at ht
    dsimp only
    rw [fHat_one_of_Icc (by linarith [ht.1]) (by linarith [ht.2])]
    have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
    field_simp [ht1]
  rw [integral_congr hEq]
  have hint1 : IntervalIntegrable (fun t => 3 * (1 / (t - 1))) volume s 4 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hs4]
    refine continuousOn_const.mul (continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_)
    intro t ht
    show t - 1 ≠ 0
    linarith [ht.1]
  have hint2 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume s 4 := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hlog_int : ∫ t in s..4, 1 / (t - 1) = Real.log 3 - Real.log (s - 1) := by
    have hd : ∀ t ∈ uIcc s 4, HasDerivAt (fun x : ℝ => Real.log (x - 1)) (1 / (t - 1)) t := by
      intro t ht
      rw [uIcc_of_le hs4] at ht
      have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
        refine ((hasDerivAt_id t).sub_const (1 : ℝ)).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
      have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
      simpa [one_div] using hsub.log ht1
    have hint : IntervalIntegrable (fun t => 1 / (t - 1)) volume s 4 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hs4]
      exact continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => by
        show t - 1 ≠ 0; linarith [ht.1]
    rw [integral_eq_sub_of_hasDerivAt hd hint]
    norm_num
  rw [hlog_int, Real.log_div (by norm_num) (by linarith)]
  ring

theorem fHat_two_le_exp_two_mul {s : ℝ} (hs2 : 2 ≤ s) :
    fHat 2 s ≤ Real.exp 2 * (9607 / 10000 : ℝ) * h_bjs s := by
  by_cases hs4 : 4 ≤ s
  · rw [fHat_support 2 (by omega) (by norm_num; exact hs4)]
    exact mul_nonneg (by positivity) (h_bjs_nonneg s)
  · have hs4' : s ≤ 4 := le_of_not_ge hs4
    have hanti := fHat_antitone 2 (by omega)
    have h2m : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
    have h2m3 : Real.exp 2 * Real.exp (-3) = Real.exp (-1) := by rw [← Real.exp_add]; norm_num
    by_cases hs22 : s ≤ 22 / 10
    · have hf : fHat 2 s ≤ fHat 2 2 :=
        hanti (by simp only [Set.mem_Ici]; norm_num) (by simp only [Set.mem_Ici]; linarith) hs2
      rw [fHat_two_eq_of_Icc (le_refl 2) (by norm_num), show (3 : ℝ) / (2 - 1) = 3 by norm_num] at hf
      have hf' : fHat 2 s ≤ 65 / 100 := by
        have := log_three_lt_eleven_tenths
        linarith
      rw [h_bjs_of_two_to_three hs2 (by linarith)]
      have hexp : Real.exp (-22 / 10 : ℝ) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
      have h_rhs : (65 / 100 : ℝ) ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-22 / 10 : ℝ) := by
        have hcomb : Real.exp 2 * Real.exp (-22 / 10 : ℝ) = Real.exp (-(1 / 5 : ℝ)) := by
          rw [← Real.exp_add]; ring_nf
        rw [mul_comm (Real.exp 2) _, mul_assoc, hcomb, Real.exp_neg, ← one_div]
        have hinv : (10000000 / 12214028 : ℝ) ≤ 1 / Real.exp (1 / 5 : ℝ) := by
          rw [le_div_iff₀ (Real.exp_pos _)]
          linarith [exp_one_fifth_lt]
        nlinarith
      calc fHat 2 s ≤ 65 / 100 := hf'
        _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-22 / 10 : ℝ) := h_rhs
        _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-s) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
    · have hs22' : 22 / 10 ≤ s := le_of_not_ge hs22
      by_cases hs25 : s ≤ 25 / 10
      · have hf : fHat 2 s ≤ fHat 2 (22 / 10) :=
          hanti (by simp only [Set.mem_Ici]; norm_num) (by simp only [Set.mem_Ici]; linarith) hs22'
        rw [fHat_two_eq_of_Icc (s := 22 / 10) (by norm_num) (by norm_num),
          show (3 : ℝ) / (22 / 10 - 1) = 5 / 2 by norm_num] at hf
        have hlog52 : Real.log (5 / 2 : ℝ) < 11 / 12 := by
          rw [Real.log_lt_iff_lt_exp (by norm_num)]
          have hpow : (5 / 2 : ℝ) ^ 12 < (Real.exp (11 / 12 : ℝ)) ^ 12 := by
            rw [← Real.exp_natCast_mul]
            have h1 : (2.718 : ℝ) < Real.exp 1 := by linarith [exp_one_gt_d9']
            have h11 : (2.718 : ℝ) ^ 11 < (Real.exp 1) ^ 11 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
            rw [← Real.exp_natCast_mul] at h11
            norm_num at h11 ⊢
            linarith
          exact lt_of_pow_lt_pow_left₀ 12 (Real.exp_pos _).le hpow
        have hf' : fHat 2 s ≤ 45 / 100 := by linarith
        rw [h_bjs_of_two_to_three (by linarith) (by linarith)]
        have hexp : Real.exp (-25 / 10 : ℝ) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
        have h_rhs : (45 / 100 : ℝ) ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-25 / 10 : ℝ) := by
          have hcomb : Real.exp 2 * Real.exp (-25 / 10 : ℝ) = Real.exp (-(1 / 2 : ℝ)) := by
            rw [← Real.exp_add]; ring_nf
          rw [mul_comm (Real.exp 2) _, mul_assoc, hcomb, Real.exp_neg, ← one_div]
          have hhalf : Real.exp (1 / 2 : ℝ) ≤ 165 / 100 := by
            have hpow : (Real.exp (1 / 2 : ℝ)) ^ 2 < (165 / 100 : ℝ) ^ 2 := by
              rw [← Real.exp_natCast_mul]; norm_num
              linarith [exp_one_lt_d9']
            exact (lt_of_pow_lt_pow_left₀ 2 (by norm_num) hpow).le
          have hinv : (100 / 165 : ℝ) ≤ 1 / Real.exp (1 / 2 : ℝ) := by
            rw [le_div_iff₀ (Real.exp_pos _)]
            linarith
          nlinarith
        calc fHat 2 s ≤ 45 / 100 := hf'
          _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-25 / 10 : ℝ) := h_rhs
          _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-s) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
      · have hs25' : 25 / 10 ≤ s := le_of_not_ge hs25
        by_cases hs3 : s ≤ 3
        · have hf : fHat 2 s ≤ fHat 2 (25 / 10) :=
            hanti (by simp only [Set.mem_Ici]; norm_num) (by simp only [Set.mem_Ici]; linarith) hs25'
          rw [fHat_two_eq_of_Icc (s := 25 / 10) (by norm_num) (by norm_num),
            show (3 : ℝ) / (25 / 10 - 1) = 2 by norm_num] at hf
          have hf' : fHat 2 s ≤ 24 / 100 := by
            have := log_two_lt_seven_tenths
            linarith
          rw [h_bjs_of_two_to_three (by linarith) hs3]
          have hexp : Real.exp (-3 : ℝ) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
          have h_rhs : (24 / 100 : ℝ) ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-3 : ℝ) := by
            rw [mul_comm (Real.exp 2) _, mul_assoc, h2m3]
            have := exp_neg_one_gt
            nlinarith
          calc fHat 2 s ≤ 24 / 100 := hf'
            _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-3 : ℝ) := h_rhs
            _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * Real.exp (-s) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
        · have hs3' : 3 ≤ s := le_of_not_ge hs3
          rw [fHat_two_eq_of_Icc (by linarith) hs4', h_bjs_of_three_le hs3']
          have hlog : Real.log (3 / (s - 1)) ≤ 3 / (s - 1) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos (by norm_num) (by linarith))
          have hf_bd : (3 * Real.log (3 / (s - 1)) - (4 - s)) / s ≤ (4 - s) ^ 2 / (s * (s - 1)) := by
            have hs0 : 0 < s := by linarith
            have hs1 : 0 < s - 1 := by linarith
            have hid : (3 * (3 / (s - 1) - 1) - (4 - s)) / s = (4 - s) ^ 2 / (s * (s - 1)) := by
              field_simp [hs0.ne', hs1.ne']
              ring
            rw [← hid]
            exact div_le_div_of_nonneg_right (by linarith) hs0.le
          by_cases hs35 : s ≤ 35 / 10
          · have hf' : fHat 2 s ≤ 1 / 6 := by
              rw [fHat_two_eq_of_Icc (by linarith) hs4']
              have hnum : (4 - s) ^ 2 ≤ 1 := by nlinarith
              have hden : (6 : ℝ) ≤ s * (s - 1) := by nlinarith
              have h1 : (4 - s) ^ 2 / (s * (s - 1)) ≤ 1 / 6 :=
                div_le_div₀ (by norm_num) hnum (by norm_num) hden
              linarith
            have h_rhs : (1 / 6 : ℝ) ≤ Real.exp 2 * (9607 / 10000 : ℝ) * ((3 / s) * Real.exp (-s)) := by
              have h3s : (3 / (35 / 10) : ℝ) ≤ 3 / s :=
                div_le_div_of_nonneg_left (by norm_num) (by linarith) hs35
              have hexp : Real.exp (-35 / 10 : ℝ) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
              have hcomb : Real.exp 2 * Real.exp (-35 / 10 : ℝ) = Real.exp (-3 / 2 : ℝ) := by
                rw [← Real.exp_add]; ring_nf
              have he32 : Real.exp (3 / 2 : ℝ) ≤ 45 / 10 := by
                have hpow : (Real.exp (3 / 2 : ℝ)) ^ 2 < (45 / 10 : ℝ) ^ 2 := by
                  rw [← Real.exp_natCast_mul]; norm_num
                  have h3 : (Real.exp 1) ^ 3 < (27182818286 / 10000000000 : ℝ) ^ 3 :=
                    pow_lt_pow_left₀ exp_one_lt_d9' (Real.exp_pos 1).le (by norm_num)
                  rw [← Real.exp_natCast_mul] at h3
                  norm_num at h3 ⊢
                  linarith
                exact (lt_of_pow_lt_pow_left₀ 2 (by norm_num) hpow).le
              have hinv : (10 / 45 : ℝ) ≤ Real.exp (-3 / 2 : ℝ) := by
                rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.exp_neg, ← one_div,
                  le_div_iff₀ (Real.exp_pos _)]
                linarith
              have hprod : (1 / 6 : ℝ) ≤ (9607 / 10000 : ℝ) * (3 / (35 / 10)) * Real.exp (-3 / 2 : ℝ) := by
                nlinarith
              calc (1 / 6 : ℝ)
                  ≤ (9607 / 10000 : ℝ) * (3 / (35 / 10)) * Real.exp (-3 / 2 : ℝ) := hprod
                _ = Real.exp 2 * (9607 / 10000 : ℝ) * ((3 / (35 / 10)) * Real.exp (-35 / 10 : ℝ)) := by
                    rw [← hcomb]; ring
                _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * ((3 / s) * Real.exp (-s)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    exact mul_le_mul h3s hexp (Real.exp_pos _).le (by positivity)
            have hf_le : fHat 2 s ≤ 1 / 6 := hf'
            rw [fHat_two_eq_of_Icc (by linarith) hs4'] at hf_le
            exact hf_le.trans h_rhs
          · have hs35' : 35 / 10 ≤ s := le_of_not_ge hs35
            have hf' : (4 - s) ^ 2 / (s * (s - 1)) ≤ 1 / 35 := by
              have hnum : (4 - s) ^ 2 ≤ 1 / 4 := by nlinarith
              have hden : (35 / 4 : ℝ) ≤ s * (s - 1) := by nlinarith
              have h1 : (4 - s) ^ 2 / (s * (s - 1)) ≤ (1 / 4) / (35 / 4) :=
                div_le_div₀ (by norm_num) hnum (by norm_num) hden
              linarith
            have h_rhs : (1 / 35 : ℝ) ≤ Real.exp 2 * (9607 / 10000 : ℝ) * ((3 / s) * Real.exp (-s)) := by
              have h3s : (3 / 4 : ℝ) ≤ 3 / s :=
                div_le_div_of_nonneg_left (by norm_num) (by linarith) hs4'
              have hexp : Real.exp (-4 : ℝ) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
              have hcomb : Real.exp 2 * Real.exp (-4 : ℝ) = Real.exp (-2 : ℝ) := by
                rw [← Real.exp_add]; ring_nf
              have he2 : (10000000000 / 27182818286 : ℝ) ^ 2 ≤ Real.exp (-2 : ℝ) := by
                rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, exp_neg_nat_eq 2]
                exact pow_le_pow_left₀ (by norm_num) exp_neg_one_gt.le 2
              have hprod : (1 / 35 : ℝ) ≤ (9607 / 10000 : ℝ) * (3 / 4) * Real.exp (-2 : ℝ) := by
                nlinarith
              calc (1 / 35 : ℝ)
                  ≤ (9607 / 10000 : ℝ) * (3 / 4) * Real.exp (-2 : ℝ) := hprod
                _ = Real.exp 2 * (9607 / 10000 : ℝ) * ((3 / 4) * Real.exp (-4 : ℝ)) := by
                    rw [← hcomb]; ring
                _ ≤ Real.exp 2 * (9607 / 10000 : ℝ) * ((3 / s) * Real.exp (-s)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    exact mul_le_mul h3s hexp (Real.exp_pos _).le (by positivity)
            linarith

private lemma fHat_le_bjs_strong :
    ∀ (n : ℕ), 2 ≤ n → ∀ {s : ℝ}, (Even n → 2 ≤ s) → (Odd n → 1 ≤ s) →
      fHat n s ≤ Real.exp 2 * (9607 / 10000 : ℝ) ^ (n - 1) * h_bjs s := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro s hev _
    simpa using fHat_two_le_exp_two_mul (hev (by decide))
  | succ m hm ih =>
    intro s hev hodd
    have hs1 : 1 ≤ s := by
      by_cases hm_ev : Even (m + 1)
      · exact (by norm_num : (1 : ℝ) ≤ 2).trans (hev hm_ev)
      · exact hodd (Nat.not_even_iff_odd.mp hm_ev)
    have hnot1 : ¬ s < 1 := not_lt.mpr hs1
    by_cases hs_supp : (m : ℝ) + 3 ≤ s
    · rw [fHat_support (m + 1) (by omega) (by push_cast; linarith)]
      exact mul_nonneg (by positivity) (h_bjs_nonneg s)
    · have hs_lt : s < (m : ℝ) + 3 := lt_of_not_ge hs_supp
      have hcont : Continuous (fun t => h_bjs (t - 1)) :=
        h_bjs_continuous.comp (continuous_id.sub continuous_const)
      have hf_cont : ContinuousOn (fun t => fHat m (t - 1)) (Set.Ici 2) :=
        (fHat_continuousOn m (by omega)).comp (continuousOn_id.sub continuousOn_const) fun t ht => by
          simp only [Set.mem_Ici] at ht ⊢; linarith
      set C : ℝ := Real.exp 2 * (9607 / 10000 : ℝ) ^ (m - 1)
      have hC_nn : 0 ≤ C := by positivity
      have hint_bound : ∀ u : ℝ, (Even m → 3 ≤ u) → (Odd m → 2 ≤ u) → u ≤ (m : ℝ) + 3 →
          ∫ t in u..((m : ℝ) + 3), fHat m (t - 1) ≤ C * ∫ t in u..((m : ℝ) + 3), h_bjs (t - 1) := by
        intro u hu_ev hu_odd hu_le
        have hi1 : IntervalIntegrable (fun t => fHat m (t - 1)) volume u ((m : ℝ) + 3) := by
          refine (hf_cont.mono fun t ht => ?_).intervalIntegrable
          rw [Set.mem_uIcc] at ht
          rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici]
          · have : 2 ≤ u := by
              by_cases hm_ev : Even m
              · linarith [hu_ev hm_ev]
              · exact hu_odd (Nat.not_even_iff_odd.mp hm_ev)
            linarith
          · linarith
        have hi2 : IntervalIntegrable (fun t => C * h_bjs (t - 1)) volume u ((m : ℝ) + 3) :=
          (continuous_const.mul hcont).intervalIntegrable _ _
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on hu_le hi1 hi2 fun t ht => ?_
        exact ih (fun hm_ev => by linarith [hu_ev hm_ev, ht.1])
          (fun hm_odd => by linarith [hu_odd hm_odd, ht.1])
      have hpow : Real.exp 2 * (9607 / 10000 : ℝ) ^ m = C * (9607 / 10000 : ℝ) := by
        dsimp [C]
        rw [show m = (m - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      by_cases hsucc_ev : Even (m + 1)
      · have hs2 : 2 ≤ s := hev hsucc_ev
        have hm_odd : Odd m := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hsucc_ev)
        have htail := (fHat_tail_integral m (by omega) (s := s) (M := (m : ℝ) + 3)
          le_rfl).1 hsucc_ev hs2
        rw [htail]
        have hI := hint_bound s (fun hm_ev => absurd hm_ev (Nat.not_even_iff_odd.mpr hm_odd))
          (fun _ => hs2) hs_lt.le
        have hH := H_bjs_le_two hs2 hs_lt.le
        have hs0 : 0 < s := by linarith
        calc (1 / s) * ∫ t in s..((m : ℝ) + 3), fHat m (t - 1)
            ≤ (1 / s) * (C * ∫ t in s..((m : ℝ) + 3), h_bjs (t - 1)) :=
              mul_le_mul_of_nonneg_left hI (by positivity)
          _ ≤ (1 / s) * (C * (kappa2 * s * h_bjs s)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hC_nn) (by positivity)
          _ = C * (9607 / 10000 : ℝ) * h_bjs s := by unfold kappa2; field_simp [hs0.ne']
          _ = Real.exp 2 * (9607 / 10000 : ℝ) ^ (m + 1 - 1) * h_bjs s := by
              rw [Nat.add_sub_cancel, hpow]
      · have hsucc_odd : Odd (m + 1) := Nat.not_even_iff_odd.mp hsucc_ev
        have hm_ev : Even m := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hsucc_odd)
        by_cases hs3 : 3 ≤ s
        · have htail := (fHat_tail_integral m (by omega) (s := s) (M := (m : ℝ) + 3)
            le_rfl).2 hsucc_odd hs3
          rw [htail]
          have hI := hint_bound s (fun _ => hs3) (fun hm_odd => absurd hm_ev (Nat.not_even_iff_odd.mpr hm_odd)) hs_lt.le
          have hH := H_bjs_le_three hs3 hs_lt.le
          have hk3 : kappa3 ≤ (9607 / 10000 : ℝ) := by unfold kappa3; norm_num
          have hs0 : 0 < s := by linarith
          calc (1 / s) * ∫ t in s..((m : ℝ) + 3), fHat m (t - 1)
              ≤ (1 / s) * (C * ∫ t in s..((m : ℝ) + 3), h_bjs (t - 1)) :=
                mul_le_mul_of_nonneg_left hI (by positivity)
            _ ≤ (1 / s) * (C * (kappa3 * s * h_bjs s)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hC_nn) (by positivity)
            _ = C * kappa3 * h_bjs s := by field_simp [hs0.ne']
            _ ≤ C * (9607 / 10000 : ℝ) * h_bjs s :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk3 hC_nn) (h_bjs_nonneg s)
            _ = Real.exp 2 * (9607 / 10000 : ℝ) ^ (m + 1 - 1) * h_bjs s := by
                rw [Nat.add_sub_cancel, hpow]
        · have hs3' : s ≤ 3 := le_of_not_ge hs3
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          have hmod : (k + 2) % 2 ≠ 0 := by
            intro h0; exact hsucc_ev (Nat.even_iff.mpr (by simpa [Nat.add_assoc] using h0))
          have hmax : max 3 s = 3 := max_eq_left hs3'
          have hdef : fHat (k + 2) s = (1 / s) * ∫ t in (3 : ℝ)..((k : ℝ) + 4), fHat (k + 1) (t - 1) := by
            rw [fHat]
            simp only [hnot1, ↓reduceIte, hmod, hmax]
          have hcast3 : ((k + 1 : ℕ) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
          have hk3_le : (3 : ℝ) ≤ (k : ℝ) + 4 := by linarith
          have hI := hint_bound 3 (fun _ => le_refl 3)
            (fun hm_odd => absurd hm_ev (Nat.not_even_iff_odd.mpr hm_odd))
            (by push_cast; linarith)
          rw [hcast3] at hI
          have hH := H_bjs_three_le_tilde hs1 hs3' (M := (k : ℝ) + 4) hk3_le
          have hkt : kappaTilde ≤ (9607 / 10000 : ℝ) := by unfold kappaTilde; norm_num
          have hs0 : 0 < s := by linarith
          calc fHat (k + 1 + 1) s
              = (1 / s) * ∫ t in (3 : ℝ)..((k : ℝ) + 4), fHat (k + 1) (t - 1) := hdef
            _ ≤ (1 / s) * (C * ∫ t in (3 : ℝ)..((k : ℝ) + 4), h_bjs (t - 1)) :=
                mul_le_mul_of_nonneg_left hI (by positivity)
            _ ≤ (1 / s) * (C * (kappaTilde * s * h_bjs s)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hC_nn) (by positivity)
            _ = C * kappaTilde * h_bjs s := by field_simp [hs0.ne']
            _ ≤ C * (9607 / 10000 : ℝ) * h_bjs s :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkt hC_nn) (h_bjs_nonneg s)
            _ = Real.exp 2 * (9607 / 10000 : ℝ) ^ (k + 1 + 1 - 1) * h_bjs s := by
                rw [Nat.add_sub_cancel, hpow]

/-- **BJS v6 Lemma 8 (Nathanson Lemma 9.7)**:
`fHat n s ≤ 2 * e^2 * (9607 / 10000) ^ (n - 1) * h_bjs s` for all `n ≥ 1` and `s ≥ 1`. -/
theorem fHat_le_bjs_universal :
    ∀ (n : ℕ) (s : ℝ), 1 ≤ n → 1 ≤ s →
      fHat n s ≤ 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (n - 1) * h_bjs s := by
  intro n s hn hs1
  rcases eq_or_lt_of_le hn with rfl | hn2
  · simpa using fHat_one_le_h_bjs hs1
  · by_cases hev : Even n
    · by_cases hs2 : 2 ≤ s
      · have h := fHat_le_bjs_strong n hn2 (fun _ => hs2) (fun hodd => absurd hev (Nat.not_even_iff_odd.mpr hodd))
        have hnn : 0 ≤ Real.exp 2 * (9607 / 10000 : ℝ) ^ (n - 1) * h_bjs s := by
          have : 0 ≤ h_bjs s := h_bjs_nonneg s
          positivity
        linarith
      · have hs2' : s ≤ 2 := le_of_not_ge hs2
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        have hnot1 : ¬ s < 1 := not_lt.mpr hs1
        have hnot21 : ¬ (2 : ℝ) < 1 := by norm_num
        have hmod : (m + 2) % 2 = 0 := Nat.even_iff.mp hev
        have hmax : max 2 s = 2 := max_eq_left hs2'
        have hs_def : fHat (m + 2) s = (1 / s) * ∫ t in (2 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1) := by
          rw [fHat]; simp only [hnot1, ↓reduceIte, hmod, hmax]
        have h2_def : fHat (m + 2) 2 = (1 / 2) * ∫ t in (2 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1) := by
          rw [fHat]; simp only [hnot21, ↓reduceIte, hmod, max_self]
        have hs0 : 0 < s := by linarith
        have hf_eq : fHat (m + 2) s = (2 / s) * fHat (m + 2) 2 := by
          rw [hs_def, h2_def]; field_simp [hs0.ne']
        have h2s : 2 / s ≤ 2 := div_le_self (by norm_num) hs1
        have hstrong := fHat_le_bjs_strong (m + 2) hn2 (fun _ => le_refl 2)
          (fun hodd => absurd hev (Nat.not_even_iff_odd.mpr hodd))
        have hh : h_bjs 2 = h_bjs s := by rw [h_bjs_of_le_two (le_refl 2), h_bjs_of_le_two hs2']
        rw [hf_eq]
        calc (2 / s) * fHat (m + 2) 2
            ≤ 2 * fHat (m + 2) 2 := mul_le_mul_of_nonneg_right h2s (fHat_nonneg _ _)
          _ ≤ 2 * (Real.exp 2 * (9607 / 10000 : ℝ) ^ (m + 2 - 1) * h_bjs 2) :=
              mul_le_mul_of_nonneg_left hstrong (by norm_num)
          _ = 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (m + 2 - 1) * h_bjs s := by rw [hh]; ring
    · have h := fHat_le_bjs_strong n hn2 (fun hev' => absurd hev' hev) (fun _ => hs1)
      have hnn : 0 ≤ Real.exp 2 * (9607 / 10000 : ℝ) ^ (n - 1) * h_bjs s := by
        have : 0 ≤ h_bjs s := h_bjs_nonneg s
        positivity
      linarith

/-- Constant universal decay sequence `c_n = 9607 / 10000` (BJS v6 Lemma 8). -/
def constDecaySeq : ℕ → ℝ := fun _ => (9607 / 10000 : ℝ)

theorem validDecaySeq_const : ValidDecaySeq constDecaySeq := by
  refine ⟨fun n _ => ⟨by unfold constDecaySeq; norm_num, by unfold constDecaySeq; norm_num⟩, ?_⟩
  intro n s hn hs
  have hs1 : 1 ≤ s := by split_ifs at hs <;> linarith
  exact fHat_le_bjs_universal n s hn hs1

end FHatDecay

end

end BuchstabSwitching
