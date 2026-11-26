import BuchstabSwitching.Sieve.Regime2SlabBridge.LowerOptions
import BuchstabSwitching.Sieve.Regime2SlabBridge.Decomposition
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBuchstab
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ### 5. Prime-Square Sums and Master Slab Bridge Theorems (`2a`/`2b` and `2c`) -/

section PrimeSquaresAndMaster

private lemma sum_Ico_inv_mul_pred_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / ((a : ℝ) - 1) := by
  have htele : ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
      1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
    have htele' : ∑ n ∈ Finset.Ico a b,
          ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (((n + 1 : ℕ) : ℝ) - 1)) =
        1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [Finset.sum_Ico_succ_top hk, ih]
        push_cast
        ring
    rw [← htele']
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring_nf
  have hcongr : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) =
      ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
  have hb_nn : 0 ≤ 1 / ((b : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
  rw [hcongr, htele]
  linarith

lemma sum_Ico_inv_sq_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have hle : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
    have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    exact one_div_le_one_div_of_le hpos (by nlinarith)
  exact hle.trans (sum_Ico_inv_mul_pred_le a b ha hab)

/-- Prime-restricted telescoping bound: `∑_{z ≤ q < b, q prime} 1 / (q * (q - 1)) ≤ 1 / (z - 1)`
for all `2 ≤ z`. -/
theorem sum_Ico_primes_inv_mul_pred_le (z b : ℕ) (hz : 2 ≤ z) :
    ∑ q ∈ (Finset.Ico z b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤
      1 / ((z : ℝ) - 1) := by
  rcases le_or_gt z b with hzb | hbz
  · calc ∑ q ∈ (Finset.Ico z b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))
        ≤ ∑ q ∈ Finset.Ico z b, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun q hq _ => by
            have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hz.trans (Finset.mem_Ico.mp hq).1
            have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
            positivity
      _ ≤ 1 / ((z : ℝ) - 1) := sum_Ico_inv_mul_pred_le z b hz hzb
  · have hemp : Finset.Ico z b = ∅ := Finset.Ico_eq_empty_of_le hbz.le
    simp only [hemp, Finset.filter_empty, Finset.sum_empty]
    have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by linarith
    positivity

/-- Exact-prefix + tail split for `∑_{z ≤ q < b, q prime} 1 / (q * (q - 1))` at `p_cut`
(used with `p_cut = 27000` in Regimes `2a`/`2b`). -/
theorem sum_inv_mul_pred_split_le (z b p_cut : ℕ) (hz : 2 ≤ z) (hp : 2 ≤ p_cut) :
    ∑ q ∈ (Finset.Ico z b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤
      ∑ q ∈ (Finset.Ico z (min b p_cut)).filter Nat.Prime,
          (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) +
        (if p_cut < b then 1 / ((p_cut : ℝ) - 1) else 0) := by
  rcases le_or_gt b p_cut with hbp | hpb
  · have hnp : ¬ p_cut < b := by omega
    simp only [min_eq_left hbp, hnp, ↓reduceIte, add_zero, le_rfl]
  · simp only [min_eq_right hpb.le, hpb, ↓reduceIte]
    rcases le_or_gt z p_cut with hzp | hpz
    · have hunion : Finset.Ico z b = Finset.Ico z p_cut ∪ Finset.Ico p_cut b := by
        ext q; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hdisj : Disjoint ((Finset.Ico z p_cut).filter Nat.Prime)
          ((Finset.Ico p_cut b).filter Nat.Prime) := by
        rw [Finset.disjoint_left]
        intro q h1 h2
        have a1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1).2
        have a2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1
        omega
      rw [hunion, Finset.filter_union, Finset.sum_union hdisj]
      exact add_le_add le_rfl (sum_Ico_primes_inv_mul_pred_le p_cut b hp)
    · have hemp : Finset.Ico z p_cut = ∅ := Finset.Ico_eq_empty_of_le hpz.le
      simp only [hemp, Finset.filter_empty, Finset.sum_empty, zero_add]
      have hp2 : (2 : ℝ) ≤ (p_cut : ℝ) := by exact_mod_cast hp
      have hpz' : (p_cut : ℝ) - 1 ≤ (z : ℝ) - 1 := by
        have : (p_cut : ℝ) ≤ (z : ℝ) := by exact_mod_cast hpz.le
        linarith
      exact (sum_Ico_primes_inv_mul_pred_le z b hz).trans
        (one_div_le_one_div_of_le (by linarith) hpz')

/-- Prime-square sum bound over `midPrimes N z y` splitting at `q_sq` (`q_sq^2 ≤ √X_lo`):
for `q ≤ q_sq` uses `squareDivisible_card_le_grh` (`|A_N|/(q(q-1)) + |r(q^2)|`), and for
`q > q_sq` uses `squareDivisible_card_le_div` (`≤ N / q^2`) combined with `|A_N| > N / log N`. -/
theorem sum_squareDivisible_card_le {li2 X_lo X_hi : ℝ} {N z y q_sq : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN_hi : (N : ℝ) < X_hi)
    (hN : Even N) (hz2 : 2 ≤ z) (_hzy : z ≤ y)
    (hq_sq1 : 1 ≤ q_sq) (hq_sq_rt : ((q_sq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt X_lo)
    {s_q2 cnt_lo : ℝ}
    (hs_q2 : ∑ q ∈ (Finset.Ico z (min y (q_sq + 1))).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ s_q2)
    (hcnt_lo : (((midPrimes N z (min y (q_sq + 1))).card : ℝ)) ≤ cnt_lo) :
    (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
      (1 / 2 : ℝ) *
        (s_q2 + cnt_lo * epdNormFn X_lo li2 X_lo +
          (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ))) *
        ((shiftedCoprimePrimes N).card : ℝ) := by
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hcard_gt := shiftedSet_card_gt_div_log hGRH hCls hN_real
  have hcard_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) :=
    lt_trans (div_pos hN_pos hlog_pos) hcard_gt
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log X_hi := Real.log_le_log hN_pos hN_hi.le
  let M_lo := (midPrimes N z y).filter (· ≤ q_sq)
  let M_hi := (midPrimes N z y).filter (q_sq < ·)
  have hpart : midPrimes N z y = M_lo ∪ M_hi := by
    ext q
    simp only [M_lo, M_hi, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      rcases le_or_gt q q_sq with h | h
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr ⟨hq, h⟩
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
  have hdisj : Disjoint M_lo M_hi := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have a1 := (Finset.mem_filter.mp h1).2
    have a2 := (Finset.mem_filter.mp h2).2
    omega
  rw [hpart, Finset.sum_union hdisj]
  have hM_lo_eq : M_lo = midPrimes N z (min y (q_sq + 1)) := by
    ext q
    simp only [M_lo, midPrimes, Finset.mem_filter, Finset.mem_Ico, lt_min_iff, Nat.lt_succ_iff]
    tauto
  have hM_lo_sum :
      ∑ q ∈ M_lo, ((squareDivisibleShifted N q).card : ℝ) ≤
        (s_q2 + cnt_lo * epdNormFn X_lo li2 X_lo) *
          ((shiftedCoprimePrimes N).card : ℝ) := by
    have hpt : ∀ q ∈ M_lo,
        ((squareDivisibleShifted N q).card : ℝ) ≤
          ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) +
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
      intro q hq
      have hqm := (Finset.mem_filter.mp hq).1
      have hq_le := (Finset.mem_filter.mp hq).2
      have hq_pr := (Finset.mem_filter.mp hqm).2.1
      have hqN := (Finset.mem_filter.mp hqm).2.2
      have hq2_sqrt : ((q ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have h1 : q ^ 2 ≤ q_sq ^ 2 := Nat.pow_le_pow_left hq_le 2
        have h2 : ((q ^ 2 : ℕ) : ℝ) ≤ ((q_sq ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
        exact (h2.trans hq_sq_rt).trans (Real.sqrt_le_sqrt hX_N)
      have hgrh := squareDivisible_card_le_grh hGRH hCls hX_lo hX_N hq_pr hqN hq2_sqrt
      have hq_ne2 : q ≠ 2 := fun h => hqN (h ▸ even_iff_two_dvd.mp hN)
      have hq3 : 3 ≤ q := lt_of_le_of_ne hq_pr.two_le hq_ne2.symm
      have hq2_ge3 : 3 ≤ q ^ 2 := by nlinarith
      have hcop2 : Nat.Coprime (q ^ 2) N := (hq_pr.coprime_iff_not_dvd.mpr hqN).pow_left 2
      have hrem2 := (div_le_iff₀ hcard_pos).mp
        (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hq2_ge3 hq2_sqrt hcop2)
      have hadd := squareDivisible_card_le_add_rem (N := N) hq_pr
      linarith
    have hsum1 : ∑ q ∈ M_lo, ((squareDivisibleShifted N q).card : ℝ) ≤
        (∑ q ∈ M_lo, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) +
          (M_lo.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
      calc ∑ q ∈ M_lo, ((squareDivisibleShifted N q).card : ℝ)
          ≤ ∑ q ∈ M_lo, (((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) +
              epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) :=
            Finset.sum_le_sum hpt
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hsub_ico : M_lo ⊆ (Finset.Ico z (min y (q_sq + 1))).filter Nat.Prime := by
      intro q hq
      rw [hM_lo_eq] at hq
      rcases Finset.mem_filter.mp hq with ⟨hqico, hqpr, _⟩
      exact Finset.mem_filter.mpr ⟨hqico, hqpr⟩
    have hsum_inv : ∑ q ∈ M_lo, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ s_q2 := by
      calc ∑ q ∈ M_lo, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))
          ≤ ∑ q ∈ (Finset.Ico z (min y (q_sq + 1))).filter Nat.Prime,
              (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_ico fun q hq _ => by
              have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
                exact_mod_cast hz2.trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
              have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
              positivity
        _ ≤ s_q2 := hs_q2
    have hpull : ∑ q ∈ M_lo, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) =
        (∑ q ∈ M_lo, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) * ((shiftedCoprimePrimes N).card : ℝ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by ring
    have hcnt_le : (M_lo.card : ℝ) ≤ cnt_lo := by rw [hM_lo_eq]; exact hcnt_lo
    have h1 : (∑ q ∈ M_lo, ((shiftedCoprimePrimes N).card : ℝ) / ((q : ℝ) * ((q : ℝ) - 1))) ≤
        s_q2 * ((shiftedCoprimePrimes N).card : ℝ) := by
      rw [hpull]
      exact mul_le_mul_of_nonneg_right hsum_inv hcard_pos.le
    have h2 : (M_lo.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) ≤
        (cnt_lo * epdNormFn X_lo li2 X_lo) * ((shiftedCoprimePrimes N).card : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hcnt_le (mul_nonneg hepd_nn hcard_pos.le)
      linarith
    linarith
  have hM_hi_sum :
      ∑ q ∈ M_hi, ((squareDivisibleShifted N q).card : ℝ) ≤
        (if y ≤ q_sq + 1 then (0 : ℝ) else Real.log X_hi / (q_sq : ℝ)) *
          ((shiftedCoprimePrimes N).card : ℝ) := by
    by_cases hy_le : y ≤ q_sq + 1
    · have hemp : M_hi = ∅ := by
        ext q
        simp only [M_hi, midPrimes, Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty,
          iff_false]
        omega
      simp [hemp, hy_le]
    · simp only [hy_le, ↓reduceIte]
      have hN_le_card_log : (N : ℝ) ≤ ((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi := by
        have h1 : (N : ℝ) ≤ ((shiftedCoprimePrimes N).card : ℝ) * Real.log (N : ℝ) :=
          ((div_lt_iff₀ hlog_pos).mp hcard_gt).le
        have h2 : ((shiftedCoprimePrimes N).card : ℝ) * Real.log (N : ℝ) ≤
            ((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi :=
          mul_le_mul_of_nonneg_left hlogN_le hcard_pos.le
        exact h1.trans h2
      have hpt : ∀ q ∈ M_hi,
          ((squareDivisibleShifted N q).card : ℝ) ≤
            Real.log X_hi * ((1 : ℝ) / (q : ℝ) ^ 2) * ((shiftedCoprimePrimes N).card : ℝ) := by
        intro q hq
        have hdiv := squareDivisible_card_le_div N q
        have hq_pos : (0 : ℝ) < (q : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos
        have h1 : (N : ℝ) / (q : ℝ) ^ 2 ≤
            (((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi) / (q : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hN_le_card_log (sq_nonneg _)
        have h2 : (((shiftedCoprimePrimes N).card : ℝ) * Real.log X_hi) / (q : ℝ) ^ 2 =
            Real.log X_hi * ((1 : ℝ) / (q : ℝ) ^ 2) * ((shiftedCoprimePrimes N).card : ℝ) := by ring
        linarith
      have hsub_ico : M_hi ⊆ Finset.Ico (q_sq + 1) y := by
        intro q hq
        simp only [M_hi, midPrimes, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
        exact ⟨by omega, hq.1.1.2⟩
      have hsum_sq : ∑ q ∈ M_hi, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (q_sq : ℝ) := by
        have ha2 : 2 ≤ q_sq + 1 := by omega
        have hab : q_sq + 1 ≤ y := by omega
        calc ∑ q ∈ M_hi, (1 : ℝ) / (q : ℝ) ^ 2
            ≤ ∑ q ∈ Finset.Ico (q_sq + 1) y, (1 : ℝ) / (q : ℝ) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_ico (fun _ _ _ => by positivity)
          _ ≤ 1 / (((q_sq + 1 : ℕ) : ℝ) - 1) := sum_Ico_inv_sq_le (q_sq + 1) y ha2 hab
          _ = 1 / (q_sq : ℝ) := by push_cast; ring_nf
      have hlogX_hi_pos : 0 ≤ Real.log X_hi := hlog_pos.le.trans hlogN_le
      calc ∑ q ∈ M_hi, ((squareDivisibleShifted N q).card : ℝ)
          ≤ ∑ q ∈ M_hi,
              Real.log X_hi * ((1 : ℝ) / (q : ℝ) ^ 2) * ((shiftedCoprimePrimes N).card : ℝ) :=
            Finset.sum_le_sum hpt
        _ = Real.log X_hi * (∑ q ∈ M_hi, (1 : ℝ) / (q : ℝ) ^ 2) *
              ((shiftedCoprimePrimes N).card : ℝ) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ Real.log X_hi * (1 / (q_sq : ℝ)) * ((shiftedCoprimePrimes N).card : ℝ) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_sq hlogX_hi_pos)
              hcard_pos.le
        _ = (Real.log X_hi / (q_sq : ℝ)) * ((shiftedCoprimePrimes N).card : ℝ) := by ring
  linarith

/-- **Master Regime 2a/2b Slab Bridge Theorem**:
Combines `lower_odd_bonf`, a partition `bpts` with per-slice upper bounds of the
`V_N(z)/V_full(z)`-factored form (produced by `slice_even_bonf_sum_upper` and
`slice_trivial_sum_upper`), prime-square error `err_q2`, and Note §2 Lemma 2 positivity
(`0 ≤ b_full`, allowing replacement of `V_N(z) / V_full(z)` by `1`) to prove
`main_lb * |A_N| - err_ub * |A_N| ≤ (switchingBalance N z y : ℝ)`. -/
theorem regime2ab_switchingBalance_lb {N z y k : ℕ} (hN : Even N)
    (bpts : Fin (k + 1) → ℕ) (hb0 : bpts 0 = z) (hbk : bpts ⟨k, Nat.lt_succ_self k⟩ = y)
    (hmono : ∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ)
    {r_odd rem_a err_q2 main_lb err_ub : ℝ}
    (h_lower :
      ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * r_odd -
          rem_a * ((shiftedCoprimePrimes N).card : ℝ) ≤
        sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z))
    (m_sl e_sl : Fin k → ℝ)
    (h_slices : ∀ i : Fin k,
      ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * m_sl i +
          e_sl i * ((shiftedCoprimePrimes N).card : ℝ))
    (h_q2 : (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
      err_q2 * ((shiftedCoprimePrimes N).card : ℝ))
    (hb_pos : 0 ≤ External.VN 2 z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i)
    (hmain_le : main_lb ≤ External.VN 2 z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i)
    (herr_le : rem_a + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2 ≤ err_ub) :
    main_lb * ((shiftedCoprimePrimes N).card : ℝ) -
        err_ub * ((shiftedCoprimePrimes N).card : ℝ) ≤
      (switchingBalance N z y : ℝ) := by
  rw [switchingBalance_eq_sieveCount]
  have hsum_aq :
      ∑ q ∈ midPrimes N z y,
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
            (∑ i : Fin k, m_sl i) +
          (∑ i : Fin k, e_sl i) * ((shiftedCoprimePrimes N).card : ℝ) := by
    rw [slice_partition_sum_eq bpts N z y hb0 hbk hmono]
    calc ∑ i : Fin k,
            ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
              sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ))
                (shiftedPrimesBelow N z)
        ≤ ∑ i : Fin k,
            (((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * m_sl i +
              e_sl i * ((shiftedCoprimePrimes N).card : ℝ)) :=
          Finset.sum_le_sum fun i _ => h_slices i
      _ = ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) *
              (∑ i : Fin k, m_sl i) +
            (∑ i : Fin k, e_sl i) * ((shiftedCoprimePrimes N).card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hV2_pos : 0 < External.VN 2 z := External.VN_pos_of_even z (by decide)
  have hV_ratio_ge1 : 1 ≤ External.VN N z / External.VN 2 z :=
    (one_le_div hV2_pos).mpr (VN_two_le_VN hN z)
  set b_full := External.VN 2 z * r_odd - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i
  have hmain_eq :
      ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * r_odd -
          (1 / 2 : ℝ) * (((shiftedCoprimePrimes N).card : ℝ) *
            (External.VN N z / External.VN 2 z) * (∑ i : Fin k, m_sl i)) =
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * b_full := by
    dsimp only [b_full]
    field_simp [hV2_pos.ne']
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hb_scale :
      main_lb * ((shiftedCoprimePrimes N).card : ℝ) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * b_full := by
    calc main_lb * ((shiftedCoprimePrimes N).card : ℝ)
        ≤ b_full * ((shiftedCoprimePrimes N).card : ℝ) :=
          mul_le_mul_of_nonneg_right hmain_le hcard_nn
      _ = ((shiftedCoprimePrimes N).card : ℝ) * 1 * b_full := by ring
      _ ≤ ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / External.VN 2 z) * b_full := by
          refine mul_le_mul_of_nonneg_right ?_ hb_pos
          exact mul_le_mul_of_nonneg_left hV_ratio_ge1 hcard_nn
  have herr_scale :
      (rem_a + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2) * ((shiftedCoprimePrimes N).card : ℝ) ≤
        err_ub * ((shiftedCoprimePrimes N).card : ℝ) :=
    mul_le_mul_of_nonneg_right herr_le hcard_nn
  linarith

/-- **Master Regime 2c Slab Bridge Theorem**:
Combines any lower bound (e.g. `max(lower_odd_bonf_norm, lower_finite_buchstab_norm)`),
a partition `bpts` with per-slice upper bounds normalized by `|A_N| * External.VN N z`
(e.g. `min(slice_even_bonf_norm_sum_upper, slice_finite_buchstab_sum_upper, slice_selberg_sum_upper)`),
and prime-square error `err_q2` to prove
`(main_lb - err_ub) * (|A_N| * External.VN N z) ≤ (switchingBalance N z y : ℝ)`. -/
theorem regime2c_switchingBalance_lb {N z y k : ℕ} (hN : Even N)
    (bpts : Fin (k + 1) → ℕ) (hb0 : bpts 0 = z) (hbk : bpts ⟨k, Nat.lt_succ_self k⟩ = y)
    (hmono : ∀ i : Fin k, bpts i.castSucc ≤ bpts i.succ)
    {sa_norm rem_a_norm err_q2 main_lb err_ub : ℝ}
    (h_lower :
      (sa_norm - rem_a_norm) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
        sieveCount (shiftedSet N) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z))
    (m_sl e_sl : Fin k → ℝ)
    (h_slices : ∀ i : Fin k,
      ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        (m_sl i + e_sl i) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z))
    (h_q2 : (1 / 2 : ℝ) * ∑ q ∈ midPrimes N z y, ((squareDivisibleShifted N q).card : ℝ) ≤
      err_q2 * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z))
    (hmain_le : main_lb ≤ sa_norm - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i)
    (herr_le : rem_a_norm + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2 ≤ err_ub) :
    (main_lb - err_ub) * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
      (switchingBalance N z y : ℝ) := by
  rw [switchingBalance_eq_sieveCount]
  have hsum_aq :
      ∑ q ∈ midPrimes N z y,
          sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
        ((∑ i : Fin k, m_sl i) + (∑ i : Fin k, e_sl i)) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    rw [slice_partition_sum_eq bpts N z y hb0 hbk hmono]
    calc ∑ i : Fin k,
            ∑ q ∈ (midPrimes N z y).filter (fun q => bpts i.castSucc ≤ q ∧ q < bpts i.succ),
              sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ))
                (shiftedPrimesBelow N z)
        ≤ ∑ i : Fin k, (m_sl i + e_sl i) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) :=
          Finset.sum_le_sum fun i _ => h_slices i
      _ = ((∑ i : Fin k, m_sl i) + (∑ i : Fin k, e_sl i)) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib]
  have hscale_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z :=
    mul_nonneg (Nat.cast_nonneg _) (External.VN_pos_of_even z hN).le
  have hnet_le : main_lb - err_ub ≤
      (sa_norm - (1 / 2 : ℝ) * ∑ i : Fin k, m_sl i) -
        (rem_a_norm + (1 / 2 : ℝ) * ∑ i : Fin k, e_sl i + err_q2) := by linarith
  have hmul_le := mul_le_mul_of_nonneg_right hnet_le hscale_nn
  linarith

end PrimeSquaresAndMaster

end

end BuchstabSwitching
