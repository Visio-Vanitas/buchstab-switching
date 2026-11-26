import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.LinearSieveBJS
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ## 2. Closed-Interval `(H*)` Condition and `Q0_100` Bridge -/

section ClosedHStar

open Classical in
/-- Closed-interval two-variable Mertens condition `(H*)` on prime subset `S0`:
for all primes `3 ≤ a ≤ b` in `S0`,
`∏_{a ≤ p ≤ b, p ∈ S0} (1 - g p)⁻¹ ≤ K * (log b / log a)`. -/
def ClosedHStarCond (g : ℕ → ℝ) (S0 : ℕ → Prop) (K : ℝ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a.Prime → b.Prime → 3 ≤ a → a ≤ b → S0 a → S0 b →
    ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ S0 p), (1 - g p)⁻¹ ≤
      K * (Real.log (b : ℝ) / Real.log (a : ℝ))

/-- Closed-interval `(H*)` on `S0` implies `AllLevelsMertensCond` for ANY finite subset
`P' ⊆ {p | p.Prime ∧ 3 ≤ p ∧ S0 p}` (dropping `p ∣ N` only shrinks the product, and
`[w, z₁) ∩ P'` is contained in `[min', max'] ⊆ [w, z₁]`). -/
theorem allLevelsMertensCond_of_closedHStar {g : ℕ → ℝ} {S0 : ℕ → Prop} {K : ℝ}
    (hK : 1 ≤ K)
    (hg : ∀ p : ℕ, p.Prime → S0 p → 0 ≤ g p ∧ g p < 1)
    {P' : Finset ℕ} (hP' : ∀ p ∈ P', p.Prime ∧ 3 ≤ p ∧ S0 p)
    (hH : ClosedHStarCond g S0 K) :
    AllLevelsMertensCond g P' K := by
  classical
  rw [allLevelsMertensCond_iff_from_one]
  refine allLevelsMertensCondFrom_of_prod_bound (u₀ := (3 : ℝ)) (by norm_num) hK
    (fun p hp => hg p (hP' p hp).1 (hP' p hp).2.2)
    (fun p hp => by exact_mod_cast (hP' p hp).2.1) ?_
  intro w z₁ hw hwz
  have hw3 : (3 : ℝ) ≤ w := le_trans (le_max_left _ _) hw
  have hw1 : 1 < w := by linarith
  have hz1 : 1 < z₁ := lt_trans hw1 hwz
  have hlogw_pos : 0 < Real.log w := Real.log_pos hw1
  have hlogz_pos : 0 < Real.log z₁ := Real.log_pos hz1
  let B : Finset ℕ := P'.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁)
  by_cases hB : B.Nonempty
  · set a : ℕ := B.min' hB
    set b : ℕ := B.max' hB
    have haB : a ∈ B := B.min'_mem hB
    have hbB : b ∈ B := B.max'_mem hB
    have haP : a ∈ P' := (Finset.mem_filter.mp haB).1
    have hbP : b ∈ P' := (Finset.mem_filter.mp hbB).1
    have ha_prop := hP' a haP
    have hb_prop := hP' b hbP
    have hab : a ≤ b := B.min'_le b hbB
    have hsub : B ⊆ (Finset.Icc a b).filter (fun p => p.Prime ∧ S0 p) := by
      intro p hp
      have hpP : p ∈ P' := (Finset.mem_filter.mp hp).1
      have hp_prop := hP' p hpP
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨B.min'_le p hp, B.le_max' p hp⟩, hp_prop.1, hp_prop.2.2⟩
    have hprod_le :
        ∏ p ∈ B, (1 - g p)⁻¹ ≤
          ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ S0 p), (1 - g p)⁻¹ := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro p hp
        have hgp := hg p (hP' p (Finset.mem_filter.mp hp).1).1
          (hP' p (Finset.mem_filter.mp hp).1).2.2
        exact (inv_pos.mpr (by linarith)).le
      · intro p hp _
        have hp_mem := (Finset.mem_filter.mp hp).2
        have hgp := hg p hp_mem.1 hp_mem.2
        exact (one_le_inv₀ (by linarith)).mpr (by linarith)
    have hH_bd := hH ha_prop.1 hb_prop.1 ha_prop.2.1 hab ha_prop.2.2 hb_prop.2.2
    have hwa : w ≤ (a : ℝ) := (Finset.mem_filter.mp haB).2.1
    have hbz : (b : ℝ) ≤ z₁ := (Finset.mem_filter.mp hbB).2.2.le
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_prop.1.pos
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_prop.1.pos
    have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha_prop.1.one_lt)
    have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb_prop.1.one_lt)
    have hlog_wa : Real.log w ≤ Real.log (a : ℝ) := Real.log_le_log (by linarith) hwa
    have hlog_bz : Real.log (b : ℝ) ≤ Real.log z₁ := Real.log_le_log hb_pos hbz
    have hratio_le : Real.log (b : ℝ) / Real.log (a : ℝ) ≤ Real.log z₁ / Real.log w :=
      (div_le_div_of_nonneg_right hlog_bz hloga_pos.le).trans
        (div_le_div_of_nonneg_left hlogz_pos.le hlogw_pos hlog_wa)
    have hK0 : 0 ≤ K := by linarith
    exact hprod_le.trans (hH_bd.trans (mul_le_mul_of_nonneg_left hratio_le hK0))
  · rw [Finset.not_nonempty_iff_eq_empty] at hB
    rw [show P'.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁) = B from rfl, hB, Finset.prod_empty]
    have hlog_le : Real.log w ≤ Real.log z₁ := Real.log_le_log (by linarith) hwz.le
    have hratio : 1 ≤ Real.log z₁ / Real.log w := (one_le_div hlogw_pos).mpr hlog_le
    nlinarith

private def q0_100_list : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 107, 109, 137, 149, 191, 227]

private lemma q0_100_list_nodup : q0_100_list.Nodup := by
  decide

/-- Certified closed-interval `(H*)` pre-sieve `Q0_100` (`k3/scripts/sieve_cert/linear_sieve.py`):
all odd primes `≤ 102` together with `{107, 109, 137, 149, 191, 227}`. -/
def Q0_100 : Finset ℕ :=
  ⟨Multiset.ofList q0_100_list, q0_100_list_nodup⟩

theorem Q0_100_mem_props : ∀ p ∈ Q0_100, p.Prime ∧ 3 ≤ p ∧ p ≤ 227 := by
  intro p hp
  have hmem : p ∈ q0_100_list := hp
  simp only [q0_100_list, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem Q0_100_prod_lt : (∏ p ∈ Q0_100, p) < 10 ^ 55 := by
  have hprod : (∏ p ∈ Q0_100, p) = q0_100_list.prod := rfl
  rw [hprod]
  decide

/-- Shifted-prime density `gTot p = 1 / φ(p)` (`1 / (p - 1)` on primes). -/
def gTotRay (k : ℕ) : ℝ :=
  1 / (Nat.totient k : ℝ)

lemma gTotRay_prime {p : ℕ} (hp : p.Prime) : gTotRay p = 1 / ((p : ℝ) - 1) := by
  unfold gTotRay
  rw [Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_lt.le
  push_cast [hp1]
  rfl

lemma gTotRay_prime_bounds {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ gTotRay p ∧ gTotRay p < 1 := by
  rw [gTotRay_prime hp]
  have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hden : 0 < (p : ℝ) - 1 := by linarith
  exact ⟨div_nonneg zero_le_one hden.le, (one_div_lt hden zero_lt_one).mpr (by linarith)⟩

lemma gTotRay_inv_one_sub {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (1 - gTotRay p)⁻¹ = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [gTotRay_prime hp]
  have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have h1 : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
    field_simp; ring
  rw [h1, inv_div]

/-- Predicate for the remaining primes `S0_100 = {odd primes} \ Q0_100`. -/
def S0_100 (p : ℕ) : Prop :=
  p.Prime ∧ 3 ≤ p ∧ p ∉ Q0_100

/-- Specialization of `allLevelsMertensCond_of_closedHStar` to `P' = (shiftedPrimesBelow N z).filter (· ∉ Q0)`
for any even `N` and any pre-sieve `Q0`. -/
theorem allLevelsMertensCond_shifted_sdiff_of_closedHStar {Q0 : Finset ℕ} {K : ℝ}
    (hK : 1 ≤ K) {N z : ℕ} (hN : Even N)
    (hH : ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0) K) :
    AllLevelsMertensCond gTotRay ((shiftedPrimesBelow N z).filter (· ∉ Q0)) K := by
  refine allLevelsMertensCond_of_closedHStar hK
    (fun p hp hS0 => gTotRay_prime_bounds hp hS0.2.1) ?_ hH
  intro p hp
  have hmem := Finset.mem_filter.mp hp
  have hmem1 := Finset.mem_filter.mp hmem.1
  have hp_pr : p.Prime := hmem1.2.1
  have hp_ndvd : ¬ p ∣ N := hmem1.2.2
  have hp_ne2 : p ≠ 2 := fun h => hp_ndvd (h ▸ even_iff_two_dvd.mp hN)
  have hp3 : 3 ≤ p := lt_of_le_of_ne hp_pr.two_le hp_ne2.symm
  exact ⟨hp_pr, hp3, hp_pr, hp3, hmem.2⟩

/-- Causal finite-table closed-interval `(H*)` check up to `B` (`certify_closed_hstar_q0` in
`k3/scripts/sieve_cert/primes_and_mertens.py:225-284`). -/
def ClosedHStarPrefixPremise (Q0 : Finset ℕ) (B : ℕ) (M0 K : ℝ) : Prop :=
  250000 ≤ B ∧
  (∀ q ∈ Q0, q < B) ∧
  (∀ a b : ℕ, a.Prime → b.Prime → 3 ≤ a → a ≤ b → b ≤ B → a ∉ Q0 → b ∉ Q0 →
    ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0),
      ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ K * (Real.log (b : ℝ) / Real.log (a : ℝ))) ∧
  (∀ a : ℕ, a.Prime → 3 ≤ a → a ≤ B → a ∉ Q0 →
    let eta_plus_B := max (2 / (Real.sqrt (B : ℝ) * Real.log (B : ℝ)))
      ((6.836e-6 : ℝ) / Real.log ((10 : ℝ) ^ 12))
    let euler_tail_B := (3 : ℝ) / (2 * ((B : ℝ) - 1))
    let sum_B := ∑ p ∈ (Finset.Icc 1 B).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
    let tail_cross_exp := Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B +
      1 / (B : ℝ) + euler_tail_B
    (∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
      ((p : ℝ) - 1) / ((p : ℝ) - 2)) * Real.exp tail_cross_exp ≤
      K * (Real.log (B : ℝ) / Real.log (a : ℝ))) ∧
  (let eta_plus_B := max (2 / (Real.sqrt (B : ℝ) * Real.log (B : ℝ)))
    ((6.836e-6 : ℝ) / Real.log ((10 : ℝ) ^ 12))
   let euler_tail_B := (3 : ℝ) / (2 * ((B : ℝ) - 1))
   Real.exp (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B) ≤ K)

private lemma sum_Ico_recip_mul_pred_le' (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
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
    push_cast; ring_nf
  have hcongr : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) =
      ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
  have hb_nn : 0 ≤ 1 / ((b : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
  rw [hcongr, htele]
  linarith

private lemma sum_Ico_recip_sub_one_mul_two_le' (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2)) ≤ 1 / ((a : ℝ) - 2) := by
  have htele : ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) =
      1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2) := by
    have htele' : ∑ n ∈ Finset.Ico a b,
          ((1 : ℝ) / ((n : ℝ) - 2) - 1 / (((n + 1 : ℕ) : ℝ) - 2)) =
        1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2) := by
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [Finset.sum_Ico_succ_top hk, ih]
        push_cast; ring
    rw [← htele']
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring_nf
  have hcongr : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2)) =
      ∑ n ∈ Finset.Ico a b, ((1 : ℝ) / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
    field_simp; ring
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
  have hb_nn : 0 ≤ 1 / ((b : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
  rw [hcongr, htele]
  linarith

/-- Euler-product tail bound for `(p - 1)/(p - 2)` relative to `∑ 1/p` above `B ≥ 3`. -/
private lemma prod_tail_inv_one_sub_pred_le {B : ℕ} (hB : 3 ≤ B) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ B < p) :
    ∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤
      Real.exp ((∑ p ∈ S, (1 : ℝ) / (p : ℝ)) + (3 : ℝ) / (2 * ((B : ℝ) - 1))) := by
  have hlog_pt : ∀ p ∈ S,
      Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
        (1 : ℝ) / (p : ℝ) +
          ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) +
            (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2)))) := by
    intro p hp
    have hp4 : 4 ≤ p := by have := (hS p hp).2; omega
    have hpr : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp4
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hpm2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have hx0 : 0 ≤ (1 : ℝ) / ((p : ℝ) - 1) := by positivity
    have hx1 : (1 : ℝ) / ((p : ℝ) - 1) < 1 := by
      rw [one_div_lt hpm1 zero_lt_one]; linarith
    have hneg := neg_log_one_sub_le hx0 hx1
    have hp0ne : (p : ℝ) ≠ 0 := hp0.ne'
    have hp1ne : (p : ℝ) - 1 ≠ 0 := hpm1.ne'
    have hp2ne : (p : ℝ) - 2 ≠ 0 := hpm2.ne'
    have hid1 : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
      field_simp [hp1ne]; ring
    have hid2 : -Real.log (1 - 1 / ((p : ℝ) - 1)) =
        Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
      rw [hid1, ← Real.log_inv, inv_div]
    have hid3 : (1 / ((p : ℝ) - 1)) ^ 2 / (2 * (1 - 1 / ((p : ℝ) - 1))) =
        (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
      rw [hid1]
      field_simp [hp1ne, hp2ne]
    have hid4 : (1 : ℝ) / ((p : ℝ) - 1) =
        (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [hp0ne, hp1ne]; ring
    linarith
  have hprod_eq : ∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2) =
      Real.exp (∑ p ∈ S, Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp4 : 4 ≤ p := by have := (hS p hp).2; omega
    have hpr : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp4
    rw [Real.exp_log (div_pos (by linarith) (by linarith))]
  let b : ℕ := max (B + 1) (S.sup id + 1)
  have hS_sub : S ⊆ Finset.Ico (B + 1) b := by
    intro p hp
    exact Finset.mem_Ico.mpr ⟨(hS p hp).2,
      lt_of_le_of_lt (Finset.le_sup (f := id) hp) (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))⟩
  have hsum1 : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((B : ℝ) - 1) := by
    have h1 : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        ∑ n ∈ Finset.Ico (B + 1) b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun n hn _ => by
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ B + 1).trans (Finset.mem_Ico.mp hn).1
        have : 0 < (n : ℝ) - 1 := by linarith
        positivity
    have h2 := sum_Ico_recip_mul_pred_le' (B + 1) b (by omega) (le_max_left _ _)
    have h3 : 1 / (((B + 1 : ℕ) : ℝ) - 1) ≤ 1 / ((B : ℝ) - 1) := by
      have hB1 : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 1 < B)
      exact one_div_le_one_div_of_le (by linarith) (by push_cast; linarith)
    exact h1.trans (h2.trans h3)
  have hsum2 : ∑ p ∈ S, (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤
      1 / (2 * ((B : ℝ) - 1)) := by
    have h1 : ∑ p ∈ S, (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))) ≤
        ∑ n ∈ Finset.Ico (B + 1) b, (1 / 2 : ℝ) * (1 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun n hn _ => by
        have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ B + 1).trans (Finset.mem_Ico.mp hn).1
        have hn1 : 0 < (n : ℝ) - 1 := by linarith
        have hn2 : 0 < (n : ℝ) - 2 := by linarith
        positivity
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 := sum_Ico_recip_sub_one_mul_two_le' (B + 1) b (by omega) (le_max_left _ _)
    have h4 : (((B + 1 : ℕ) : ℝ) - 2) = (B : ℝ) - 1 := by push_cast; ring
    rw [h4] at h2
    have hB1 : (B : ℝ) - 1 ≠ 0 := by
      have : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      linarith
    have h5 : (1 / 2 : ℝ) * (1 / ((B : ℝ) - 1)) = 1 / (2 * ((B : ℝ) - 1)) := by
      field_simp
    rw [← Finset.mul_sum]
    linarith
  have hsum_all : ∑ p ∈ S, Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
      (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) + (3 : ℝ) / (2 * ((B : ℝ) - 1)) := by
    calc ∑ p ∈ S, Real.log (((p : ℝ) - 1) / ((p : ℝ) - 2))
        ≤ ∑ p ∈ S, ((1 : ℝ) / (p : ℝ) +
            ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) +
              (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))))) :=
          Finset.sum_le_sum hlog_pt
      _ = (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) +
            ((∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) +
              (∑ p ∈ S, (1 / 2 : ℝ) * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 2))))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) + (1 / ((B : ℝ) - 1) + 1 / (2 * ((B : ℝ) - 1))) := by
          linarith
      _ = (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) + (3 : ℝ) / (2 * ((B : ℝ) - 1)) := by
          have hB1 : (B : ℝ) - 1 ≠ 0 := by
            have : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
            linarith
          field_simp; ring
  rw [hprod_eq]
  exact Real.exp_le_exp.mpr hsum_all

private lemma jsMertensHiErr_le_eta_plus_B {B b : ℕ} (hB : 250000 ≤ B) (hBb : B < b) :
    External.jsMertensHiErr (b : ℝ) ≤
      max (2 / (Real.sqrt (B : ℝ) * Real.log (B : ℝ)))
        ((6.836e-6 : ℝ) / Real.log ((10 : ℝ) ^ 12)) := by
  have hB_real : (250000 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hb_real : (250000 : ℝ) < (b : ℝ) := lt_of_le_of_lt hB_real (by exact_mod_cast hBb)
  have hlogB10 : 10 < Real.log (B : ℝ) := by
    have hexp10 : Real.exp 10 < (250000 : ℝ) := by
      have h1 : Real.exp 1 < (2.75 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h10 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_natCast_mul]; norm_num
      have hpow : (Real.exp 1) ^ 10 < (2.75 : ℝ) ^ 10 :=
        pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
      have hnum : (2.75 : ℝ) ^ 10 < (250000 : ℝ) := by norm_num
      linarith
    rw [← Real.log_exp 10]
    exact Real.log_lt_log (Real.exp_pos 10) (hexp10.trans_le hB_real)
  have hlogb10 : 10 < Real.log (b : ℝ) :=
    hlogB10.trans (Real.log_lt_log (by linarith) (by exact_mod_cast hBb))
  by_cases hbig : (10 : ℝ) ^ 12 < (b : ℝ)
  · rw [External.jsMertensHiErr_eq_tail hbig]
    refine le_trans ?_ (le_max_right _ _)
    have hlog12_pos : 0 < Real.log ((10 : ℝ) ^ 12) := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_left (by norm_num) hlog12_pos
      (Real.log_le_log (by norm_num) hbig.le)
  · push Not at hbig
    rw [External.jsMertensHiErr_eq_bjv hbig hlogb10]
    refine le_trans ?_ (le_max_left _ _)
    have hsqrtB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hsqrt_le : Real.sqrt (B : ℝ) ≤ Real.sqrt (b : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hBb.le)
    have hlog_le : Real.log (B : ℝ) ≤ Real.log (b : ℝ) := Real.log_le_log (by linarith) (by exact_mod_cast hBb.le)
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hsqrtB (by linarith))
      (mul_le_mul hsqrt_le hlog_le (by linarith) (Real.sqrt_nonneg _))

/-- Bridges `MertensPrimeSumPremise` + `ClosedHStarPrefixPremise` (`certify_closed_hstar_q0`)
to global `ClosedHStarCond` on `S0 = {odd primes} \ Q0`. -/
theorem closedHStarCond_of_prefixCheck {Q0 : Finset ℕ} {B : ℕ} {M0 K : ℝ}
    (hM : External.MertensPrimeSumPremise M0)
    (hPre : ClosedHStarPrefixPremise Q0 B M0 K) :
    ClosedHStarCond gTotRay (fun p => p.Prime ∧ 3 ≤ p ∧ p ∉ Q0) K := by
  rcases hPre with ⟨hB, hQ0_lt, hCase1, hCase2, hCase3⟩
  set eta_plus_B := max (2 / (Real.sqrt (B : ℝ) * Real.log (B : ℝ)))
    ((6.836e-6 : ℝ) / Real.log ((10 : ℝ) ^ 12))
  set euler_tail_B := (3 : ℝ) / (2 * ((B : ℝ) - 1))
  set sum_B := ∑ p ∈ (Finset.Icc 1 B).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
  have hB3 : 3 ≤ B := by omega
  have hB_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hB_gt1 : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 1 < B)
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos hB_gt1
  have hlogB_gt1 : 1 < Real.log (B : ℝ) := by
    have he3 : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hB_ge : (250000 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have heB : Real.exp 1 < (B : ℝ) := by linarith
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) heB
  have hllB_pos : 0 < Real.log (Real.log (B : ℝ)) := Real.log_pos hlogB_gt1
  unfold ClosedHStarCond
  classical
  intro a b ha_pr hb_pr ha3 hab ⟨_, _, haQ0⟩ ⟨_, _, hbQ0⟩
  have hprod_rew : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 3 ≤ p) →
      ∏ p ∈ S, (1 - gTotRay p)⁻¹ = ∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    intro S hS
    refine Finset.prod_congr rfl fun p hp => gTotRay_inv_one_sub (hS p hp).1 (hS p hp).2
  suffices hmain :
      ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0),
        ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ K * (Real.log (b : ℝ) / Real.log (a : ℝ)) by
    refine le_trans (le_of_eq ?_) hmain
    trans ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0), (1 - gTotRay p)⁻¹
    · refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨fun ⟨h1, h2, _, _, h3⟩ => ⟨h1, h2, h3⟩,
        fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h2, ha3.trans h1.1, h3⟩⟩
    · exact hprod_rew _ (fun p hp =>
        ⟨(Finset.mem_filter.mp hp).2.1, ha3.trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩)
  by_cases hbB : b ≤ B
  · exact hCase1 a b ha_pr hb_pr ha3 hab hbB haQ0 hbQ0
  · push Not at hbB
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pr.pos
    have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb_pr.one_lt)
    have hsum_b_le : ∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log (b : ℝ)) + M0 + eta_plus_B + 1 / (B : ℝ) := by
      have hsub_union : (Finset.Icc 1 b).filter Nat.Prime ⊆
          ((Finset.range b).filter Nat.Prime) ∪ {b} := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_range,
          Finset.mem_singleton] at hp ⊢
        rcases eq_or_lt_of_le hp.1.2 with rfl | hlt
        · exact Or.inr rfl
        · exact Or.inl ⟨hlt, hp.2⟩
      have hdisj_rb : Disjoint ((Finset.range b).filter Nat.Prime) ({b} : Finset ℕ) := by
        simp [Finset.disjoint_singleton_right]
      have hrange_eq : (Finset.range b).filter Nat.Prime =
          (Finset.range (Nat.ceil (b : ℝ))).filter Nat.Prime := by
        rw [Nat.ceil_natCast]
      have hmert := (hM.mertensSumBounds (b : ℝ) (by exact_mod_cast hb_pr.two_le)).2
      rw [← hrange_eq] at hmert
      have hsum_sub : ∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          (∑ p ∈ (Finset.range b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) + 1 / (b : ℝ) := by
        calc ∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
            ≤ ∑ p ∈ ((Finset.range b).filter Nat.Prime) ∪ {b}, (1 : ℝ) / (p : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_union fun _ _ _ => by positivity
          _ = (∑ p ∈ (Finset.range b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) +
                ∑ p ∈ ({b} : Finset ℕ), (1 : ℝ) / (p : ℝ) :=
              Finset.sum_union hdisj_rb
          _ = (∑ p ∈ (Finset.range b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) + 1 / (b : ℝ) := by
              simp
      have heta : External.jsMertensHiErr (b : ℝ) ≤ eta_plus_B :=
        jsMertensHiErr_le_eta_plus_B hB hbB
      have h1b : 1 / (b : ℝ) ≤ 1 / (B : ℝ) :=
        one_div_le_one_div_of_le hB_pos (by exact_mod_cast hbB.le)
      linarith
    by_cases haB : a ≤ B
    · -- Case 2: `a ≤ B < b`
      have hsplit_Icc : (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0) =
          (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0) ∪
          (Finset.Icc (B + 1) b).filter (fun p => p.Prime ∧ p ∉ Q0) := by
        ext p
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hap, hpb⟩, hpr, hQ⟩
          rcases le_or_gt p B with hpB | hBp
          · exact Or.inl ⟨⟨hap, hpB⟩, hpr, hQ⟩
          · exact Or.inr ⟨⟨hBp, hpb⟩, hpr, hQ⟩
        · rintro (⟨⟨hap, hpB⟩, hpr, hQ⟩ | ⟨⟨hBp, hpb⟩, hpr, hQ⟩)
          · exact ⟨⟨hap, hpB.trans hbB.le⟩, hpr, hQ⟩
          · exact ⟨⟨by omega, hpb⟩, hpr, hQ⟩
      have hdisj : Disjoint ((Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0))
          ((Finset.Icc (B + 1) b).filter (fun p => p.Prime ∧ p ∉ Q0)) := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2
        omega
      let T := (Finset.Icc (B + 1) b).filter (fun p => p.Prime ∧ p ∉ Q0)
      have hT_props : ∀ p ∈ T, p.Prime ∧ B < p := by
        intro p hp
        have hm := Finset.mem_filter.mp hp
        exact ⟨hm.2.1, by linarith [(Finset.mem_Icc.mp hm.1).1]⟩
      have htail := prod_tail_inv_one_sub_pred_le hB3 T hT_props
      have hT_sub_prime : T ⊆ (Finset.Icc (B + 1) b).filter Nat.Prime := fun p hp =>
        let hm := Finset.mem_filter.mp hp; Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩
      have hsum_T_le : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ≤
          ∑ p ∈ (Finset.Icc (B + 1) b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hT_sub_prime fun _ _ _ => by positivity
      have hIcc_split : (Finset.Icc 1 b).filter Nat.Prime =
          (Finset.Icc 1 B).filter Nat.Prime ∪ (Finset.Icc (B + 1) b).filter Nat.Prime := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hp1, hpb⟩, hpr⟩
          rcases le_or_gt p B with hpB | hBp
          · exact Or.inl ⟨⟨hp1, hpB⟩, hpr⟩
          · exact Or.inr ⟨⟨hBp, hpb⟩, hpr⟩
        · rintro (⟨⟨hp1, hpB⟩, hpr⟩ | ⟨⟨hBp, hpb⟩, hpr⟩)
          · exact ⟨⟨hp1, hpB.trans hbB.le⟩, hpr⟩
          · exact ⟨⟨by omega, hpb⟩, hpr⟩
      have hIcc_disj : Disjoint ((Finset.Icc 1 B).filter Nat.Prime)
          ((Finset.Icc (B + 1) b).filter Nat.Prime) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
      have hsum_diff : ∑ p ∈ (Finset.Icc (B + 1) b).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
          (∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) - sum_B := by
        have hu := Finset.sum_union hIcc_disj (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
        rw [← hIcc_split] at hu
        linarith
      have hexp_tail_le :
          Real.exp ((∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B) ≤
            Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
              euler_tail_B) * (Real.log (b : ℝ) / Real.log (B : ℝ)) := by
        have harg : (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B ≤
            Real.log (Real.log (b : ℝ) / Real.log (B : ℝ)) +
              (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) + euler_tail_B) := by
          rw [Real.log_div hlogb_pos.ne' hlogB_pos.ne']
          linarith
        calc Real.exp ((∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B)
            ≤ Real.exp (Real.log (Real.log (b : ℝ) / Real.log (B : ℝ)) +
                (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) + euler_tail_B)) :=
              Real.exp_le_exp.mpr harg
          _ = Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
                euler_tail_B) * Real.exp (Real.log (Real.log (b : ℝ) / Real.log (B : ℝ))) := by
              rw [add_comm, Real.exp_add]
          _ = Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
                euler_tail_B) * (Real.log (b : ℝ) / Real.log (B : ℝ)) := by
              rw [Real.exp_log (div_pos hlogb_pos hlogB_pos)]
      have hpref_nn : 0 ≤ ∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
          ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast ha3.trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        exact div_nonneg (by linarith) (by linarith)
      have hc2 := hCase2 a ha_pr ha3 haB haQ0
      dsimp only at hc2
      have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha_pr.one_lt)
      calc ∏ p ∈ (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0), ((p : ℝ) - 1) / ((p : ℝ) - 2)
          = (∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
                ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
              ∏ p ∈ T, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
            rw [hsplit_Icc, Finset.prod_union hdisj]
        _ ≤ (∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
                ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
              (Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
                euler_tail_B) * (Real.log (b : ℝ) / Real.log (B : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (htail.trans hexp_tail_le) hpref_nn
        _ = ((∏ p ∈ (Finset.Icc a B).filter (fun p => p.Prime ∧ p ∉ Q0),
                ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
              Real.exp (Real.log (Real.log (B : ℝ)) + M0 - sum_B + eta_plus_B + 1 / (B : ℝ) +
                euler_tail_B)) * (Real.log (b : ℝ) / Real.log (B : ℝ)) := by ring
        _ ≤ (K * (Real.log (B : ℝ) / Real.log (a : ℝ))) *
              (Real.log (b : ℝ) / Real.log (B : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hc2 (div_nonneg hlogb_pos.le hlogB_pos.le)
        _ = K * (Real.log (b : ℝ) / Real.log (a : ℝ)) := by
            field_simp [hlogB_pos.ne', hloga_pos.ne']
    · -- Case 3: `B < a ≤ b`
      push Not at haB
      let T := (Finset.Icc a b).filter (fun p => p.Prime ∧ p ∉ Q0)
      have hT_props : ∀ p ∈ T, p.Prime ∧ B < p := fun p hp =>
        let hm := Finset.mem_filter.mp hp
        ⟨hm.2.1, lt_of_lt_of_le haB (Finset.mem_Icc.mp hm.1).1⟩
      have htail := prod_tail_inv_one_sub_pred_le hB3 T hT_props
      have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pr.pos
      have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha_pr.one_lt)
      have hmert_a := (hM.mertensSumBounds (a : ℝ) (by exact_mod_cast ha_pr.two_le)).1
      have hrange_a : (Finset.range (Nat.ceil (a : ℝ))).filter Nat.Prime =
          (Finset.range a).filter Nat.Prime := by rw [Nat.ceil_natCast]
      rw [hrange_a] at hmert_a
      have hT_sub_diff : T ⊆ (Finset.Icc 1 b).filter Nat.Prime \ (Finset.range a).filter Nat.Prime := by
        intro p hp
        simp only [T, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
        exact ⟨⟨⟨hp.2.1.one_lt.le, hp.1.2⟩, hp.2.1⟩, fun h => by omega⟩
      have hsub_sdiff : (Finset.range a).filter Nat.Prime ⊆ (Finset.Icc 1 b).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨hp.2.one_lt.le, lt_of_lt_of_le hp.1 hab |>.le⟩, hp.2⟩
      have hsum_T_le : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ≤
          (∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
            ∑ p ∈ (Finset.range a).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
        calc ∑ p ∈ T, (1 : ℝ) / (p : ℝ)
            ≤ ∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime \ (Finset.range a).filter Nat.Prime,
                (1 : ℝ) / (p : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hT_sub_diff fun _ _ _ => by positivity
          _ = (∑ p ∈ (Finset.Icc 1 b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
                ∑ p ∈ (Finset.range a).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
              rw [Finset.sum_sdiff_eq_sub hsub_sdiff]
      have hlo_a : External.jsMertensLoErr (a : ℝ) ≤ (2.964e-6 : ℝ) / Real.log (B : ℝ) := by
        unfold External.jsMertensLoErr
        exact div_le_div_of_nonneg_left (by norm_num) hlogB_pos
          (Real.log_le_log hB_pos (by exact_mod_cast haB.le))
      have harg : (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B ≤
          Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
            (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B) := by
        rw [Real.log_div hlogb_pos.ne' hloga_pos.ne']
        linarith
      calc ∏ p ∈ T, ((p : ℝ) - 1) / ((p : ℝ) - 2)
          ≤ Real.exp ((∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + euler_tail_B) := htail
        _ ≤ Real.exp (Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
              (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B)) :=
            Real.exp_le_exp.mpr harg
        _ = Real.exp (eta_plus_B + (2.964e-6 : ℝ) / Real.log (B : ℝ) + 1 / (B : ℝ) + euler_tail_B) *
              (Real.log (b : ℝ) / Real.log (a : ℝ)) := by
            rw [add_comm, Real.exp_add, Real.exp_log (div_pos hlogb_pos hloga_pos)]
        _ ≤ K * (Real.log (b : ℝ) / Real.log (a : ℝ)) := by
            dsimp only at hCase3
            exact mul_le_mul_of_nonneg_right hCase3 (div_nonneg hlogb_pos.le hloga_pos.le)

end ClosedHStar

end

end BuchstabSwitching
