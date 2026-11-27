import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStarCertData
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStarCertSound
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import Mathlib.Tactic

namespace BuchstabSwitching

/-!
# Certified Finite-Prefix + Asymptotic Proof of `ClosedHStarCond` for `Q0_100`

Proves `closedHStarCond_Q0_100` unconditionally from `External.MertensPrimeSumPremise M0`:
1. `ClosedHStarPrefixPremise8000` lowers the prefix cutoff from `250000` to `8000` using
   `jsMertensHiErr b ≤ 1.614e-3` for all integers `b > 8000` (from `Real.exp 8.9 < 8000`).
2. An integer fixed-point (`10^12` scale) causal scan over the `975` primes in `[3, 8000] \ Q0_100`,
   with certified `Real.log` lower/upper bounds from the `artanh` series and `Real.log_two_*_d9`,
   verifies Cases 1–3 purely in the Lean kernel via `decide` + `norm_num`.
-/

/-! ## 2. Prefix Premise Reduction at `B = 8000` -/

noncomputable section

/-- Causal finite-table closed-interval `(H*)` check up to `B ≥ 8000`, using
`jsMertensHiErr b ≤ 1.614e-3` for all `b > 8000`. -/
def ClosedHStarPrefixPremise8000 (Q0 : Finset ℕ) (B : ℕ) (M0 K : ℝ) : Prop :=
  8000 ≤ B ∧ (∀ q ∈ Q0, q < B) ∧
  (∀ a b : ℕ, a.Prime → b.Prime → 3 ≤ a → a ≤ b → b ≤ B → a ∉ Q0 → b ∉ Q0 →
    ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0),
      ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ K * (Real.log (b : ℝ) / Real.log (a : ℝ))) ∧
  (∀ a : ℕ, a.Prime → 3 ≤ a → a ≤ B → a ∉ Q0 →
    let eta_plus_B : ℝ := (1.614e-3 : ℝ)
    let euler_tail_B := (3 : ℝ) / (2 * ((B : ℝ) - 1))
    let sum_B := ∑ p ∈ (Finset.Icc 1 B).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
    let tail_cross_exp := Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B +
      1 / (B : ℝ) + euler_tail_B
    (∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
      ((p : ℝ) - 1) / ((p : ℝ) - 2)) * Real.exp tail_cross_exp ≤
      K * (Real.log (B : ℝ) / Real.log (a : ℝ))) ∧
  (let eta_plus_B : ℝ := (1.614e-3 : ℝ)
   let euler_tail_B := (3 : ℝ) / (2 * ((B : ℝ) - 1))
   Real.exp (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B) ≤ K)

private lemma exp_89_lt_8000 : Real.exp (8.9 : ℝ) < (8000 : ℝ) := by
  have h8 : Real.exp 8 < (2982 : ℝ) := by
    have hpow := pow_lt_pow_left₀ (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < 2.7183)
      (Real.exp_pos 1).le (by norm_num : 8 ≠ 0)
    rw [← Real.exp_nat_mul] at hpow
    have hnum : (2.7183 : ℝ) ^ 8 < (2982 : ℝ) := by norm_num
    norm_num at hpow; linarith
  have h09 : Real.exp (9 / 10 : ℝ) < (2.46 : ℝ) := by
    have hbd := Real.exp_bound (x := (9 / 10 : ℝ)) (n := 6) (by norm_num) (by omega)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 10)] at hbd
    have hbd2 := le_of_abs_le hbd
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.succ_eq_add_one,
      Nat.factorial] at hbd2
    norm_num at hbd2; linarith
  have heq : Real.exp (8.9 : ℝ) = Real.exp 8 * Real.exp (9 / 10 : ℝ) := by
    rw [← Real.exp_add]; congr 1; norm_num
  rw [heq]; nlinarith [Real.exp_pos (8 : ℝ), Real.exp_pos (9 / 10 : ℝ)]

/-- For every integer `b > 8000`, `jsMertensHiErr b ≤ 1.614e-3`. -/
theorem jsMertensHiErr_le_1614 {b : ℕ} (hb : 8000 < b) :
    External.jsMertensHiErr (b : ℝ) ≤ (1.614e-3 : ℝ) := by
  have hb_real : (8000 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hlog89 : (8.9 : ℝ) < Real.log (b : ℝ) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (exp_89_lt_8000.trans hb_real)
  by_cases hbig : (10 : ℝ) ^ 12 < (b : ℝ)
  · rw [External.jsMertensHiErr_eq_tail hbig]
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6.836e-6) (by norm_num) hlog89.le
    linarith
  · push Not at hbig
    by_cases h10 : (10 : ℝ) < Real.log (b : ℝ)
    · rw [External.jsMertensHiErr_eq_bjv hbig h10]
      have hexp10_lt : Real.exp 10 < (b : ℝ) := (Real.lt_log_iff_exp_lt (by linarith)).mp h10
      have h143_sq : (143 : ℝ) ^ 2 < Real.exp 10 := by
        have h10e := pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) < Real.exp 1)
          (by norm_num) (by norm_num : 10 ≠ 0)
        rw [← Real.exp_nat_mul] at h10e; norm_num at h10e ⊢; linarith
      have hsqrt_gt : (143 : ℝ) < Real.sqrt (b : ℝ) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 143)]
        exact Real.sqrt_lt_sqrt (by norm_num) (h143_sq.trans hexp10_lt)
      have hden_gt : (1430 : ℝ) < Real.sqrt (b : ℝ) * Real.log (b : ℝ) := by nlinarith
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1430) hden_gt.le
      linarith
    · push Not at h10
      rw [External.jsMertensHiErr_eq_mid hbig h10 hlog89]

private lemma sum_Ico_recip_shift_le (a b k : ℕ) (hk : k + 2 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (((n : ℝ) - k) * ((n : ℝ) - (k + 1))) ≤
      1 / ((a : ℝ) - (k + 1)) := by
  have htele : ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - (k + 1)) - 1 / ((n : ℝ) - k)) =
      1 / ((a : ℝ) - (k + 1)) - 1 / ((b : ℝ) - (k + 1)) := by
    have htele' : ∑ n ∈ Finset.Ico a b,
          ((1 : ℝ) / ((n : ℝ) - (k + 1)) - 1 / (((n + 1 : ℕ) : ℝ) - (k + 1))) =
        1 / ((a : ℝ) - (k + 1)) - 1 / ((b : ℝ) - (k + 1)) := by
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; push_cast; ring
    rw [← htele']; refine Finset.sum_congr rfl fun n _ => ?_; push_cast; ring_nf
  have hcongr : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (((n : ℝ) - k) * ((n : ℝ) - (k + 1))) =
      ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - (k + 1)) - 1 / ((n : ℝ) - k)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (k : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hk.trans (Finset.mem_Ico.mp hn).1
    have h1 : (n : ℝ) - (k : ℝ) ≠ 0 := by linarith
    have h2 : (n : ℝ) - ((k : ℝ) + 1) ≠ 0 := by linarith
    field_simp; ring
  have hb' : (k : ℝ) + 2 ≤ (b : ℝ) := by exact_mod_cast hk.trans hab
  have hb_nn : 0 ≤ 1 / ((b : ℝ) - (k + 1)) := div_nonneg zero_le_one (by linarith)
  rw [hcongr, htele]; linarith

private lemma prod_tail_inv_one_sub_pred_le' {B : ℕ} (hB : 3 ≤ B) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ B < p) :
    ∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤
      Real.exp ((∑ p ∈ S, (1 : ℝ) / (p : ℝ)) + (3 : ℝ) / (2 * ((B : ℝ) - 1))) := by
  have hlog_pt : ∀ p ∈ S, Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
      (1 : ℝ) / (p : ℝ) + ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) +
        (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2)))) := by
    intro p hp
    have hpr : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by have := (hS p hp).2; omega : 4 ≤ p)
    have hneg := neg_log_one_sub_le (div_nonneg zero_le_one (by linarith))
      ((one_div_lt (by linarith : (0 : ℝ) < p - 1) zero_lt_one).mpr (by linarith))
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    have hid1 : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by field_simp; ring
    have hid2 : -Real.log (1 - 1 / ((p : ℝ) - 1)) = Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
      rw [hid1, ← Real.log_inv, inv_div]
    have hid3 : (1 / ((p : ℝ) - 1)) ^ 2 / (2 * (1 - 1 / ((p : ℝ) - 1))) =
        (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by rw [hid1]; field_simp
    have hid4 : (1 : ℝ) / ((p : ℝ) - 1) = (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp; ring
    linarith
  have hprod_eq : ∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2) =
      Real.exp (∑ p ∈ S, Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpr : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by have := (hS p hp).2; omega : 4 ≤ p)
    rw [Real.exp_log (div_pos (by linarith) (by linarith))]
  let b : ℕ := max (B + 1) (S.sup id + 1)
  have hS_sub : S ⊆ Finset.Ico (B + 1) b := fun p hp => Finset.mem_Ico.mpr ⟨(hS p hp).2,
    lt_of_le_of_lt (Finset.le_sup (f := id) hp) (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))⟩
  have hB1 : (B : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hB0 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hsum1 : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((B : ℝ) - 1) := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hS_sub (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      fun n hn _ => by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ B + 1).trans (Finset.mem_Ico.mp hn).1
        have : 0 < (n : ℝ) - 1 := by linarith
        positivity
    have h2 := sum_Ico_recip_shift_le (B + 1) b 0 (by omega) (le_max_left _ _)
    have h3 : (1 : ℝ) / (((B + 1 : ℕ) : ℝ) - ((0 : ℕ) + 1)) ≤ 1 / ((B : ℝ) - 1) := by
      rw [show ((B + 1 : ℕ) : ℝ) - ((0 : ℕ) + 1) = (B : ℝ) by push_cast; ring]
      exact one_div_le_one_div_of_le hB0 (by linarith)
    have h4 : ∑ n ∈ Finset.Ico (B + 1) b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) =
        ∑ n ∈ Finset.Ico (B + 1) b, (1 : ℝ) / (((n : ℝ) - (0 : ℕ)) * ((n : ℝ) - ((0 : ℕ) + 1))) :=
      Finset.sum_congr rfl fun n _ => by push_cast; ring_nf
    linarith
  have hsum2 : ∑ p ∈ S, (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤ 1 / (2 * ((B : ℝ) - 1)) := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hS_sub
      (f := fun n : ℕ => (1 / 2 : ℝ) * (1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)))) fun n hn _ => by
        have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ B + 1).trans (Finset.mem_Ico.mp hn).1
        have : 0 < (n : ℝ) - 1 := by linarith
        have : 0 < (n : ℝ) - 2 := by linarith
        positivity
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 := sum_Ico_recip_shift_le (B + 1) b 1 (by omega) (le_max_left _ _)
    have h3 : (1 : ℝ) / (((B + 1 : ℕ) : ℝ) - ((1 : ℕ) + 1)) = 1 / ((B : ℝ) - 1) := by
      rw [show ((B + 1 : ℕ) : ℝ) - ((1 : ℕ) + 1) = (B : ℝ) - 1 by push_cast; ring]
    have h4 : ∑ n ∈ Finset.Ico (B + 1) b, (1 : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2)) =
        ∑ n ∈ Finset.Ico (B + 1) b, (1 : ℝ) / (((n : ℝ) - (1 : ℕ)) * ((n : ℝ) - ((1 : ℕ) + 1))) :=
      Finset.sum_congr rfl fun n _ => by push_cast; ring_nf
    have h5 : (1 / 2 : ℝ) * (1 / ((B : ℝ) - 1)) = 1 / (2 * ((B : ℝ) - 1)) := by field_simp
    rw [← Finset.mul_sum]; linarith
  have hsum_all : ∑ p ∈ S, Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
      (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) + (3 : ℝ) / (2 * ((B : ℝ) - 1)) := by
    have hs := Finset.sum_le_sum hlog_pt
    simp only [Finset.sum_add_distrib] at hs
    have hcomb : 1 / ((B : ℝ) - 1) + 1 / (2 * ((B : ℝ) - 1)) = (3 : ℝ) / (2 * ((B : ℝ) - 1)) := by
      field_simp; ring
    linarith
  rw [hprod_eq]; exact Real.exp_le_exp.mpr hsum_all

/-- Bridges `MertensPrimeSumPremise` + `ClosedHStarPrefixPremise8000` to global
`ClosedHStarCond` on `S0 = {odd primes} \ Q0`. -/
theorem closedHStarCond_of_prefixCheck_B8000 {Q0 : Finset ℕ} {B : ℕ} {M0 K : ℝ}
    (hM : External.MertensPrimeSumPremise M0)
    (hPre : ClosedHStarPrefixPremise8000 Q0 B M0 K) :
    ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0) K := by
  rcases hPre with ⟨hB, _, hCase1, hCase2, hCase3⟩
  set eta_plus_B : ℝ := (1.614e-3 : ℝ)
  set euler_tail_B := (3 : ℝ) / (2 * ((B : ℝ) - 1))
  set sum_B := ∑ p ∈ (Finset.Icc 1 B).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
  have hB3 : 3 ≤ B := by omega
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  classical
  unfold ClosedHStarCond
  intro a b ha_pr hb_pr ha3 hab ⟨_, _, haQ0⟩ ⟨_, _, hbQ0⟩
  suffices hmain :
      ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0),
        ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ K * (Real.log (b : ℝ) / Real.log (a : ℝ)) by
    refine le_trans (le_of_eq ?_) hmain
    trans ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0), (1 - gTotRay p)⁻¹
    · refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨fun ⟨h1, h2, _, _, h3⟩ => ⟨h1, h2, h3⟩,
        fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h2, ha3.trans h1.1, h3⟩⟩
    · exact Finset.prod_congr rfl fun p hp => gTotRay_inv_one_sub
        (Finset.mem_filter.mp hp).2.1 (ha3.trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
  by_cases hbB : b ≤ B
  · exact hCase1 a b ha_pr hb_pr ha3 hab hbB haQ0 hbQ0
  · push Not at hbB
    have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb_pr.one_lt)
    have hsum_b_le : ∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log (b : ℝ)) + M0 + eta_plus_B + 1 / (B : ℝ) := by
      have hsub_union : (Finset.Icc 1 b).filter Nat.Prime ⊆ ((Finset.range b).filter Nat.Prime) ∪ {b} := by
        intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_range,
          Finset.mem_singleton] at hp ⊢
        rcases eq_or_lt_of_le hp.1.2 with rfl | hlt
        · exact Or.inr rfl
        · exact Or.inl ⟨hlt, hp.2⟩
      have hdisj_rb : Disjoint ((Finset.range b).filter Nat.Prime) ({b} : Finset ℕ) := by
        simp [Finset.disjoint_singleton_right]
      have hmert : ∑ p ∈ (Finset.range b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          Real.log (Real.log (b : ℝ)) + M0 + External.jsMertensHiErr (b : ℝ) := by
        have hm0 := (hM.mertensSumBounds (b : ℝ) (by exact_mod_cast hb_pr.two_le)).2
        rw [Nat.ceil_natCast] at hm0; convert hm0
      have hsum_sub : ∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          (∑ p ∈ (Finset.range b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) + 1 / (b : ℝ) :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub_union fun _ _ _ => by positivity).trans_eq
          (by rw [Finset.sum_union hdisj_rb, Finset.sum_singleton])
      have heta : External.jsMertensHiErr (b : ℝ) ≤ eta_plus_B := jsMertensHiErr_le_1614 (by omega : 8000 < b)
      have h1b : 1 / (b : ℝ) ≤ 1 / (B : ℝ) := one_div_le_one_div_of_le hB_pos (by exact_mod_cast hbB.le)
      calc ∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
          ≤ (∑ p ∈ (Finset.range b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) + 1 / (b : ℝ) := hsum_sub
        _ ≤ (Real.log (Real.log (b : ℝ)) + M0 + External.jsMertensHiErr (b : ℝ)) + 1 / (b : ℝ) := by gcongr
        _ ≤ (Real.log (Real.log (b : ℝ)) + M0 + eta_plus_B) + 1 / (B : ℝ) := by gcongr
        _ = Real.log (Real.log (b : ℝ)) + M0 + eta_plus_B + 1 / (B : ℝ) := by ring
    by_cases haB : a ≤ B
    · have hsplit_Icc : (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0) =
          (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0) ∪
          (Finset.Icc (B + 1) b).filter (fun p => p.Prime ∧ p ∉ Q0) := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun ⟨⟨hap, hpb⟩, hpr, hQ⟩ =>
          (le_or_gt p B).elim (fun h => Or.inl ⟨⟨hap, h⟩, hpr, hQ⟩) (fun h => Or.inr ⟨⟨h, hpb⟩, hpr, hQ⟩),
          fun h => h.elim (fun ⟨⟨hap, hpB⟩, hpr, hQ⟩ => ⟨⟨hap, hpB.trans hbB.le⟩, hpr, hQ⟩)
            (fun ⟨⟨hBp, hpb⟩, hpr, hQ⟩ => ⟨⟨by omega, hpb⟩, hpr, hQ⟩)⟩
      have hdisj : Disjoint ((Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0))
          ((Finset.Icc (B + 1) b).filter (fun p => p.Prime ∧ p ∉ Q0)) := by
        rw [Finset.disjoint_left]; intro p h1 h2; simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
      let T := (Finset.Icc (B + 1) b).filter (fun p => p.Prime ∧ p ∉ Q0)
      have htail := prod_tail_inv_one_sub_pred_le' hB3 T fun p hp =>
        let hm := Finset.mem_filter.mp hp; ⟨hm.2.1, by linarith [(Finset.mem_Icc.mp hm.1).1]⟩
      have hsum_T_le : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ≤
          ∑ p ∈ (Finset.Icc (B + 1) b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp =>
          let hm := Finset.mem_filter.mp hp; Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩)
          fun _ _ _ => by positivity
      have hIcc_split : (Finset.Icc 1 b).filter Nat.Prime =
          (Finset.Icc 1 B).filter Nat.Prime ∪ (Finset.Icc (B + 1) b).filter Nat.Prime := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun ⟨⟨hp1, hpb⟩, hpr⟩ =>
          (le_or_gt p B).elim (fun h => Or.inl ⟨⟨hp1, h⟩, hpr⟩) (fun h => Or.inr ⟨⟨h, hpb⟩, hpr⟩),
          fun h => h.elim (fun ⟨⟨hp1, hpB⟩, hpr⟩ => ⟨⟨hp1, hpB.trans hbB.le⟩, hpr⟩)
            (fun ⟨⟨hBp, hpb⟩, hpr⟩ => ⟨⟨by omega, hpb⟩, hpr⟩)⟩
      have hIcc_disj : Disjoint ((Finset.Icc 1 B).filter Nat.Prime)
          ((Finset.Icc (B + 1) b).filter Nat.Prime) := by
        rw [Finset.disjoint_left]; intro p h1 h2; simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
      have hsum_diff : ∑ p ∈ (Finset.Icc (B + 1) b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
          (∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) - sum_B := by
        have hu := Finset.sum_union hIcc_disj (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
        rw [← hIcc_split] at hu
        have hsumB_eq : ∑ x ∈ (Finset.Icc 1 B).filter Nat.Prime, (1 : ℝ) / (x : ℝ) = sum_B := rfl
        linarith
      have hexp_tail_le : Real.exp ((∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B) ≤
          Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
            euler_tail_B) * (Real.log (b : ℝ) / Real.log (B : ℝ)) := by
        have harg : (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B ≤
            Real.log (Real.log (b : ℝ) / Real.log (B : ℝ)) +
              (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) + euler_tail_B) := by
          rw [Real.log_div hlogb_pos.ne' hlogB_pos.ne']; linarith
        calc Real.exp ((∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B)
            ≤ Real.exp (Real.log (Real.log (b : ℝ) / Real.log (B : ℝ)) +
                (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) + euler_tail_B)) :=
              Real.exp_le_exp.mpr harg
          _ = Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
                euler_tail_B) * (Real.log (b : ℝ) / Real.log (B : ℝ)) := by
              rw [add_comm, Real.exp_add, Real.exp_log (div_pos hlogb_pos hlogB_pos)]
      have hpref_nn : 0 ≤ ∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
          ((p : ℝ) - 1) / ((p : ℝ) - 2) := Finset.prod_nonneg fun p hp => by
        have : (3 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast ha3.trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        exact div_nonneg (by linarith) (by linarith)
      have hc2 := hCase2 a ha_pr ha3 haB haQ0
      dsimp only at hc2
      have hc2' : (∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
            ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
            euler_tail_B) ≤ K * (Real.log (B : ℝ) / Real.log (a : ℝ)) := by convert hc2
      have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha_pr.one_lt)
      calc ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0), ((p : ℝ) - 1) / ((p : ℝ) - 2)
          = (∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
                ((p : ℝ) - 1) / ((p : ℝ) - 2)) * ∏ p ∈ T, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
            rw [hsplit_Icc, Finset.prod_union hdisj]
        _ ≤ _ := mul_le_mul_of_nonneg_left (htail.trans hexp_tail_le) hpref_nn
        _ = ((∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
                ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
              Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
                euler_tail_B)) * (Real.log (b : ℝ) / Real.log (B : ℝ)) := by ring
        _ ≤ (K * (Real.log (B : ℝ) / Real.log (a : ℝ))) * (Real.log (b : ℝ) / Real.log (B : ℝ)) :=
            mul_le_mul_of_nonneg_right hc2' (div_nonneg hlogb_pos.le hlogB_pos.le)
        _ = K * (Real.log (b : ℝ) / Real.log (a : ℝ)) := by field_simp [hlogB_pos.ne', hloga_pos.ne']
    · push Not at haB
      let T := (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0)
      have htail := prod_tail_inv_one_sub_pred_le' hB3 T fun p hp =>
        let hm := Finset.mem_filter.mp hp; ⟨hm.2.1, lt_of_lt_of_le haB (Finset.mem_Icc.mp hm.1).1⟩
      have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha_pr.one_lt)
      have hmert_a : Real.log (Real.log (a : ℝ)) + M0 - External.jsMertensLoErr (a : ℝ) ≤
          ∑ p ∈ (Finset.range a).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
        have hm0 := (hM.mertensSumBounds (a : ℝ) (by exact_mod_cast ha_pr.two_le)).1
        rw [Nat.ceil_natCast] at hm0; convert hm0
      have hT_sub_diff : T ⊆ (Finset.Icc 1 b).filter Nat.Prime \ (Finset.range a).filter Nat.Prime := by
        intro p hp; simp only [T, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
        exact ⟨⟨⟨hp.2.1.one_lt.le, hp.1.2⟩, hp.2.1⟩, fun h => by omega⟩
      have hsub_sdiff : (Finset.range a).filter Nat.Prime ⊆ (Finset.Icc 1 b).filter Nat.Prime := by
        intro p hp; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨hp.2.one_lt.le, (lt_of_lt_of_le hp.1 hab).le⟩, hp.2⟩
      have hsum_T_le : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ≤
          (∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
            ∑ p ∈ (Finset.range a).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
        (Finset.sum_le_sum_of_subset_of_nonneg hT_sub_diff fun _ _ _ => by positivity).trans_eq
          (Finset.sum_sdiff_eq_sub hsub_sdiff)
      have hlo_a : External.jsMertensLoErr (a : ℝ) ≤ (2.964e-6 : ℝ) / Real.log (B : ℝ) := by
        unfold External.jsMertensLoErr
        exact div_le_div_of_nonneg_left (by norm_num) hlogB_pos (Real.log_le_log hB_pos (by exact_mod_cast haB.le))
      have harg : (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B ≤
          Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
            (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B) := by
        rw [Real.log_div hlogb_pos.ne' hloga_pos.ne']; linarith
      calc ∏ p ∈ T, ((p : ℝ) - 1) / ((p : ℝ) - 2)
          ≤ Real.exp ((∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B) := htail
        _ ≤ Real.exp (Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
              (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B)) :=
            Real.exp_le_exp.mpr harg
        _ = Real.exp (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B) *
              (Real.log (b : ℝ) / Real.log (a : ℝ)) := by
            rw [add_comm, Real.exp_add, Real.exp_log (div_pos hlogb_pos hloga_pos)]
        _ ≤ K * (Real.log (b : ℝ) / Real.log (a : ℝ)) := by
            dsimp only at hCase3; exact mul_le_mul_of_nonneg_right hCase3 (div_nonneg hlogb_pos.le hloga_pos.le)

/-! ## 4. Verification of Cases 1–3 and Main Theorem `closedHStarCond_Q0_100` -/

private lemma exp_le_one_div_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have hle : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  rw [Real.exp_neg] at hle; rw [one_div, le_inv_comm₀ (Real.exp_pos x) (by linarith)]; exact hle

private lemma primes8000_finset_eq :
    (Finset.Icc 1 8000).filter Nat.Prime = insert 2 (Q0_100 ∪ s0List.toFinset) := by
  ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, List.mem_toFinset]
  constructor
  · rintro ⟨⟨_, hp8000⟩, hpr⟩
    rcases eq_or_lt_of_le hpr.two_le with rfl | hp2
    · exact Or.inl rfl
    · by_cases hq : p ∈ Q0_100
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (s0List_props.2.2 p hpr (by omega) hp8000 hq))
  · rintro (rfl | hq | hs)
    · exact ⟨⟨by norm_num, by norm_num⟩, Nat.prime_two⟩
    · have hp := Q0_100_mem_props p hq; exact ⟨⟨by omega, by omega⟩, hp.1⟩
    · have hp := s0List_props.2.1 p hs; exact ⟨⟨by omega, hp.2.1⟩, hp.2.2.1⟩

private lemma sumInvListLo_le_real (ps : List ℕ) (hpos : ∀ p ∈ ps, 0 < p) (hnodup : ps.Nodup) :
    (sumInvListLo ps : ℝ) / (scaleS : ℝ) ≤ ∑ p ∈ ps.toFinset, (1 : ℝ) / (p : ℝ) := by
  have hfold : ∀ (qs : List ℕ) (acc : ℕ),
      qs.foldl (fun a p => a + scaleS / p) acc = acc + qs.foldl (fun a p => a + scaleS / p) 0 := by
    intro qs; induction qs with
    | nil => intro acc; simp
    | cons q qs ih => intro acc; simp only [List.foldl_cons, Nat.zero_add]; rw [ih, ih (scaleS / q)]; omega
  induction ps with
  | nil => simp [sumInvListLo]
  | cons p ps ih =>
    have hnd := List.nodup_cons.mp hnodup
    have hsum : ∑ x ∈ (p :: ps).toFinset, (1 : ℝ) / (x : ℝ) =
        1 / (p : ℝ) + ∑ x ∈ ps.toFinset, (1 : ℝ) / (x : ℝ) := by
      rw [List.toFinset_cons, Finset.sum_insert (by simpa [List.mem_toFinset] using hnd.1)]
    have hstep : sumInvListLo (p :: ps) = scaleS / p + sumInvListLo ps := by
      simpa [sumInvListLo] using hfold ps (scaleS / p)
    have hdiv : ((scaleS / p : ℕ) : ℝ) / (scaleS : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by
      have h1 := floorDiv_le_real (a := scaleS) (hpos p List.mem_cons_self)
      have h2 : ((scaleS : ℝ) / (p : ℝ)) / (scaleS : ℝ) = 1 / (p : ℝ) := by field_simp [scaleS_pos.ne']
      exact (div_le_div_of_nonneg_right h1 scaleS_pos.le).trans h2.le
    have hrec := ih (fun q hq => hpos q (List.mem_cons_of_mem p hq)) hnd.2
    rw [hsum, hstep]; push_cast
    linarith [add_div ((scaleS / p : ℕ) : ℝ) (sumInvListLo ps : ℝ) (scaleS : ℝ)]

private lemma sumInvChunksLo_le_real (cs : List (List ℕ))
    (hpos : ∀ p ∈ cs.flatten, 0 < p) (hnodup : cs.flatten.Nodup) :
    (sumInvChunksLo cs : ℝ) / (scaleS : ℝ) ≤ ∑ p ∈ cs.flatten.toFinset, (1 : ℝ) / (p : ℝ) := by
  have hfold : ∀ (ds : List (List ℕ)) (acc : ℕ),
      ds.foldl (fun a c => a + sumInvListLo c) acc = acc + ds.foldl (fun a c => a + sumInvListLo c) 0 := by
    intro ds; induction ds with
    | nil => intro acc; simp
    | cons d ds ih => intro acc; simp only [List.foldl_cons, Nat.zero_add]; rw [ih, ih (sumInvListLo d)]; omega
  induction cs with
  | nil => simp [sumInvChunksLo]
  | cons c cs ih =>
    have hfl : (c :: cs).flatten = c ++ cs.flatten := rfl
    have hnd := List.nodup_append.mp (hfl ▸ hnodup)
    have hdisj : Disjoint c.toFinset cs.flatten.toFinset := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact hnd.2.2 x (List.mem_toFinset.mp hx1) x (List.mem_toFinset.mp hx2) rfl
    have hsum : ∑ x ∈ (c :: cs).flatten.toFinset, (1 : ℝ) / (x : ℝ) =
        (∑ x ∈ c.toFinset, (1 : ℝ) / (x : ℝ)) + ∑ x ∈ cs.flatten.toFinset, (1 : ℝ) / (x : ℝ) := by
      rw [hfl, List.toFinset_append, Finset.sum_union hdisj]
    have hstep : sumInvChunksLo (c :: cs) = sumInvListLo c + sumInvChunksLo cs := by
      simpa [sumInvChunksLo] using hfold cs (sumInvListLo c)
    have hc := sumInvListLo_le_real c (fun q hq => hpos q (hfl ▸ List.mem_append_left _ hq)) hnd.1
    have hrec := ih (fun q hq => hpos q (hfl ▸ List.mem_append_right _ hq)) hnd.2.1
    rw [hsum, hstep]; push_cast
    linarith [add_div (sumInvListLo c : ℝ) (sumInvChunksLo cs : ℝ) (scaleS : ℝ)]

/-- Certified `ClosedHStarCond` for `Q0_100` with constant `K = 1 + 1 / 100`. -/
theorem closedHStarCond_Q0_100 {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0) :
    ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0_100) (1 + (1 : ℝ) / 100) := by
  refine closedHStarCond_of_prefixCheck_B8000 (B := 8000) hM ?_
  have hs_props := s0List_props
  have hscan := s0List_scanInv
  have hnd : s0List.Nodup := hs_props.1.nodup
  rw [show (1 + (1 : ℝ) / 100) = (101 : ℝ) / 100 by norm_num]
  refine ⟨le_rfl, fun q hq => by have := Q0_100_mem_props q hq; omega, ?_, ?_, ?_⟩
  · -- Case 1: `3 ≤ a ≤ b ≤ 8000`
    intro a b ha_pr hb_pr ha3 hab hb8000 haQ0 hbQ0
    have ha_mem := hs_props.2.2 a ha_pr ha3 (hab.trans hb8000) haQ0
    have hb_mem := hs_props.2.2 b hb_pr (ha3.trans hab) hb8000 hbQ0
    let A := s0List.filter (fun p => decide (p < a))
    let B := s0List.filter (fun p => decide (p ≤ b))
    let C := s0List.filter (fun p => decide (a ≤ p ∧ p ≤ b))
    have hIcc_eq : (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0_100) = C.toFinset := by
      ext p; simp only [C, Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq]
      exact ⟨fun ⟨⟨hap, hpb⟩, hpr, hnq⟩ => ⟨hs_props.2.2 p hpr (ha3.trans hap) (hpb.trans hb8000) hnq, hap, hpb⟩,
        fun ⟨hp_mem, hap, hpb⟩ => let hp := hs_props.2.1 p hp_mem; ⟨⟨hap, hpb⟩, hp.2.2.1, hp.2.2.2⟩⟩
    have hdisj : Disjoint A.toFinset C.toFinset := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [A, C, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp1 hp2; omega
    have hunion : B.toFinset = A.toFinset ∪ C.toFinset := by
      ext p; simp only [A, B, C, Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      by_cases hp : p ∈ s0List <;> simp [hp]; omega
    have hprod_split : listProd B = listProd A * listProd C := by
      rw [listProd_eq_finset_prod (hnd.filter _), hunion, Finset.prod_union hdisj,
        listProd_eq_finset_prod (hnd.filter _), listProd_eq_finset_prod (hnd.filter _)]
    have hPA_pos : 0 < listProd A := listProd_pos fun p hp => (hs_props.2.1 p (List.mem_filter.mp hp).1).1
    have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha_pr.one_lt)
    have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb_pr.one_lt)
    have hbd := hscan.1.2.2.2.2 hscan.2 a ha_mem b hb_mem hab
    rw [hIcc_eq, ← listProd_eq_finset_prod (hnd.filter _)]
    calc listProd C = ((Real.log (a : ℝ) / listProd A) * (listProd B / Real.log (b : ℝ))) *
            (Real.log (b : ℝ) / Real.log (a : ℝ)) := by
          rw [hprod_split]; field_simp [hPA_pos.ne', hloga_pos.ne', hlogb_pos.ne']
      _ ≤ ((101 : ℝ) / 100) * (Real.log (b : ℝ) / Real.log (a : ℝ)) :=
          mul_le_mul_of_nonneg_right hbd (div_nonneg hlogb_pos.le hloga_pos.le)
  · -- Case 2: Cross case `3 ≤ a ≤ 8000`
    intro a ha_pr ha3 ha8000 haQ0
    dsimp only
    have ha_mem := hs_props.2.2 a ha_pr ha3 ha8000 haQ0
    let A := s0List.filter (fun p => decide (p < a))
    let C := s0List.filter (fun p => decide (a ≤ p))
    have hIcc_eq : (Finset.Icc a 8000).filter (fun p => p.Prime ∧ p ∉ Q0_100) = C.toFinset := by
      ext p; simp only [C, Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq]
      exact ⟨fun ⟨⟨hap, hpb⟩, hpr, hnq⟩ => ⟨hs_props.2.2 p hpr (ha3.trans hap) hpb hnq, hap⟩,
        fun ⟨hp_mem, hap⟩ => let hp := hs_props.2.1 p hp_mem; ⟨⟨hap, hp.2.1⟩, hp.2.2.1, hp.2.2.2⟩⟩
    have hdisj : Disjoint A.toFinset C.toFinset := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [A, C, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp1 hp2; omega
    have hunion : s0List.toFinset = A.toFinset ∪ C.toFinset := by
      ext p; simp only [A, C, Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      by_cases hp : p ∈ s0List <;> simp [hp]; omega
    have hprod_split : listProd s0List = listProd A * listProd C := by
      rw [listProd_eq_finset_prod hnd, hunion, Finset.prod_union hdisj,
        listProd_eq_finset_prod (hnd.filter _), listProd_eq_finset_prod (hnd.filter _)]
    have hPA_pos : 0 < listProd A := listProd_pos fun p hp => (hs_props.2.1 p (List.mem_filter.mp hp).1).1
    have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha_pr.one_lt)
    have hlogB_pos : 0 < Real.log (8000 : ℝ) := Real.log_pos (by norm_num)
    have hlog8000 := logNatIv_sound (n := 8000) (by norm_num) (by norm_num)
    rw [log8000_eval] at hlog8000
    have hll8000_rat := logRatIv_sound (num := 8987196862357) (den := scaleS) (k := 3)
      (by unfold scaleS; positivity) (by unfold scaleS; norm_num) (by unfold scaleS; norm_num)
    rw [log_ln8000_eval] at hll8000_rat
    have hll8000_le := (Real.log_le_log hlogB_pos (by simpa using hlog8000.2)).trans hll8000_rat.2
    have hsum8000_ge : (2458291737869 : ℝ) / (scaleS : ℝ) ≤
        ∑ p ∈ (Finset.Icc 1 8000).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
      rw [primes8000_finset_eq]
      have hdisj2 : Disjoint Q0_100 s0List.toFinset := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        exact (hs_props.2.1 p (List.mem_toFinset.mp hp2)).2.2.2 hp1
      have hsum_q0 := sumInvListLo_le_real (2 :: q0List)
        (fun p hp => (List.mem_cons.mp hp).elim (fun h => by subst h; norm_num)
          (fun hq => by have := Q0_100_mem_props p (q0_eq_toFinset ▸ List.mem_toFinset.mpr hq); omega))
        (List.nodup_cons.mpr ⟨fun hm => by
          have := Q0_100_mem_props 2 (q0_eq_toFinset ▸ List.mem_toFinset.mpr hm); omega, q0_nodup⟩)
      have hsum_s0 := sumInvChunksLo_le_real s0Chunks (fun p hp => by have := hs_props.2.1 p hp; omega) hnd
      change (sumInvChunksLo s0Chunks : ℝ) / (scaleS : ℝ) ≤ ∑ p ∈ s0List.toFinset, (1 : ℝ) / (p : ℝ) at hsum_s0
      rw [List.toFinset_cons, ← q0_eq_toFinset] at hsum_q0
      have hsum_eq : ∑ p ∈ insert 2 (Q0_100 ∪ s0List.toFinset), (1 : ℝ) / (p : ℝ) =
          (∑ p ∈ insert 2 Q0_100, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ s0List.toFinset, (1 : ℝ) / (p : ℝ) := by
        rw [← Finset.insert_union, Finset.sum_union
          (Finset.disjoint_insert_left.mpr
            ⟨fun h => absurd (hs_props.2.1 2 (List.mem_toFinset.mp h)).1 (by norm_num), hdisj2⟩)]
      have hsum_nat : (2458291737869 : ℝ) = (sumInvListLo (2 :: q0List) : ℝ) + (sumInvChunksLo s0Chunks : ℝ) := by
        exact_mod_cast sum_8000_eval.symm
      rw [hsum_eq, hsum_nat]
      linarith [add_div (sumInvListLo (2 :: q0List) : ℝ) (sumInvChunksLo s0Chunks : ℝ) (scaleS : ℝ)]
    have htce_ub : Real.log (Real.log ((8000 : ℕ) : ℝ)) + M0 -
        (∑ p ∈ (Finset.Icc 1 8000).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) +
        (1.614e-3 : ℝ) + 1 / ((8000 : ℕ) : ℝ) + (3 : ℝ) / (2 * (((8000 : ℕ) : ℝ) - 1)) ≤
        (2195801102956 : ℝ) / (scaleS : ℝ) + 0.261498 -
          (2458291737869 : ℝ) / (scaleS : ℝ) + 1.614e-3 + 1 / 8000 + 3 / 15998 := by
      have hm0 := hM.m0_bounds.2
      dsimp only at hll8000_le
      have h8k : (1 : ℝ) / ((8000 : ℕ) : ℝ) = 1 / 8000 := by norm_num
      have h7999 : (3 : ℝ) / (2 * (((8000 : ℕ) : ℝ) - 1)) = 3 / 15998 := by norm_num
      rw [h8k, h7999]
      linarith
    have htce_le_m3 : (2195801102956 : ℝ) / (scaleS : ℝ) + 0.261498 -
        (2458291737869 : ℝ) / (scaleS : ℝ) + 1.614e-3 + 1 / 8000 + 3 / 15998 ≤ (1 / 1000 : ℝ) := by
      unfold scaleS; norm_num
    have hexp_ub : Real.exp (Real.log (Real.log ((8000 : ℕ) : ℝ)) + M0 -
        (∑ p ∈ (Finset.Icc 1 8000).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) +
        (1.614e-3 : ℝ) + 1 / ((8000 : ℕ) : ℝ) + (3 : ℝ) / (2 * (((8000 : ℕ) : ℝ) - 1))) ≤
        1 / (1 - (1 / 1000 : ℝ)) :=
      (Real.exp_le_exp.mpr (htce_ub.trans htce_le_m3)).trans (exp_le_one_div_one_sub (by norm_num))
    have hpre_bd : (Real.log (a : ℝ) / listProd A) * (listProd s0List / Real.log (8000 : ℝ)) ≤
        ((4907693467692 : ℝ) / (scaleS : ℝ)) *
          (((1832176522576 : ℝ) / (scaleS : ℝ)) / ((8987196747791 : ℝ) / (scaleS : ℝ))) :=
      mul_le_mul (hscan.1.2.2.2.1 a ha_mem)
        ((div_le_div_of_nonneg_right hscan.1.2.2.1 hlogB_pos.le).trans
          (div_le_div_of_nonneg_left (by unfold scaleS; positivity) (by unfold scaleS; positivity)
            (by simpa using hlog8000.1)))
        (div_nonneg ((div_pos (by exact_mod_cast hscan.1.1) scaleS_pos).le.trans hscan.1.2.1) hlogB_pos.le)
        (by unfold scaleS; positivity)
    have hpre_le : ((4907693467692 : ℝ) / (scaleS : ℝ)) *
        (((1832176522576 : ℝ) / (scaleS : ℝ)) / ((8987196747791 : ℝ) / (scaleS : ℝ))) ≤ (1001 / 1000 : ℝ) := by
      unfold scaleS
      have hq : ((4907693467692 : ℝ) / ((10 ^ 12 : ℕ) : ℝ)) *
          (((1832176522576 : ℝ) / ((10 ^ 12 : ℕ) : ℝ)) / ((8987196747791 : ℝ) / ((10 ^ 12 : ℕ) : ℝ))) =
          (4907693467692 * 1832176522576 : ℝ) / (10 ^ 12 * 8987196747791 : ℝ) := by
        push_cast; field_simp; norm_num
      rw [hq, div_le_div_iff₀ (by norm_num) (by norm_num)]
      exact_mod_cast (by decide :
        4907693467692 * 1832176522576 * 1000 ≤ 1001 * (10 ^ 12 * 8987196747791))
    have hnum_cross : (1001 / 1000 : ℝ) * (1 / (1 - (1 / 1000 : ℝ))) ≤ (101 : ℝ) / 100 := by norm_num
    have hcross_le := (mul_le_mul (hpre_bd.trans hpre_le) hexp_ub (Real.exp_pos _).le (by norm_num)).trans hnum_cross
    rw [hIcc_eq, ← listProd_eq_finset_prod (hnd.filter _)]
    calc listProd C * Real.exp (Real.log (Real.log ((8000 : ℕ) : ℝ)) + M0 -
            (∑ p ∈ (Finset.Icc 1 8000).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) +
            (1.614e-3 : ℝ) + 1 / ((8000 : ℕ) : ℝ) + (3 : ℝ) / (2 * (((8000 : ℕ) : ℝ) - 1)))
        = (((Real.log (a : ℝ) / listProd A) * (listProd s0List / Real.log (8000 : ℝ))) *
            Real.exp (Real.log (Real.log ((8000 : ℕ) : ℝ)) + M0 -
              (∑ p ∈ (Finset.Icc 1 8000).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) +
              (1.614e-3 : ℝ) + 1 / ((8000 : ℕ) : ℝ) + (3 : ℝ) / (2 * (((8000 : ℕ) : ℝ) - 1)))) *
            (Real.log ((8000 : ℕ) : ℝ) / Real.log (a : ℝ)) := by
          rw [hprod_split]; norm_num; field_simp [hPA_pos.ne', hloga_pos.ne', hlogB_pos.ne']
      _ ≤ ((101 : ℝ) / 100) * (Real.log ((8000 : ℕ) : ℝ) / Real.log (a : ℝ)) :=
          mul_le_mul_of_nonneg_right hcross_le (div_nonneg hlogB_pos.le hloga_pos.le)
  · -- Case 3: Pure tail `8000 < a ≤ b`
    dsimp only
    have hlog8 : (8 : ℝ) < Real.log (8000 : ℝ) := by
      have hpow1 := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num : 8 ≠ 0)
      rw [← Real.exp_nat_mul] at hpow1
      have hnum : (2.7182818286 : ℝ) ^ 8 < (8000 : ℝ) := by norm_num
      norm_num at hpow1; exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith)
    have hdiv : (2.964e-6 : ℝ) / Real.log ((8000 : ℕ) : ℝ) ≤ (2.964e-6 : ℝ) / 8 :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2.964e-6) (by norm_num : (0 : ℝ) < 8)
        (by simpa using hlog8.le)
    have harg_le : (1.614e-3 : ℝ) + (2.964e-6 : ℝ) / Real.log ((8000 : ℕ) : ℝ) +
        1 / ((8000 : ℕ) : ℝ) + (3 : ℝ) / (2 * (((8000 : ℕ) : ℝ) - 1)) ≤ (2 / 1000 : ℝ) := by
      norm_num at hdiv ⊢; linarith
    exact ((Real.exp_le_exp.mpr harg_le).trans (exp_le_one_div_one_sub (by norm_num))).trans (by norm_num)

end

end BuchstabSwitching
