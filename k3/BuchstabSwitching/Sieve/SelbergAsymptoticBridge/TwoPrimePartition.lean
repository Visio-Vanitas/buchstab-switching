import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.CouplingAndJOdd
import BuchstabSwitching.Sieve.MertensTwoVar
import Mathlib.Tactic

/-!
# Selberg Asymptotic Bridge: 2-Prime Inclusion-Exclusion and Partition Summation

Provides the generic 2-prime inclusion-exclusion lower bound `J_full_two_prime_ie_ge`,
partition summation `sum_Ico_partition`, Mertens `1/(p-2)` interval bounds
(`sum_prime_inv_sub_two_Ico_le`, `sum_prime_inv_sub_two_Icc_le`,
`sum_prime_inv_sub_two_Ico_ge`), and the single-box 2-prime lower bound `two_prime_box_ge`.
-/

namespace BuchstabSwitching

/-! ## 3. Generic 2-Prime Inclusion-Exclusion and Partition Summation Lemmas -/

section TwoPrimeIEHelpers

/-- Core 2-prime inclusion-exclusion inequality for `J_full z_nat xi` when `Nat.floor xi < z_nat ^ 3`. -/
theorem J_full_two_prime_ie_ge (z_nat : ℕ) {xi : ℝ} (hxi0 : 0 ≤ xi)
    (hxi_lt : Nat.floor xi < z_nat ^ 3) :
    let xi_nat := Nat.floor xi
    let Q_z := (Finset.Ico z_nat (max z_nat (xi_nat + 1))).filter (fun p => p.Prime ∧ 2 < p)
    J_odd xi - ∑ q ∈ Q_z, (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) +
      ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
        (1 / (((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2))) * J_odd (xi / ((q₁ * q₂ : ℕ) : ℝ)) ≤
      J_full z_nat xi := by
  dsimp only
  set xi_nat : ℕ := Nat.floor xi
  set M : ℕ := max z_nat (xi_nat + 1)
  set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hg : ∀ p ∈ P, 0 < (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p ∧
      (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p < 1 := fun p hp =>
    selbergG_bounds (Finset.mem_filter.mp hp).2.2
  have hie := selbergJ_lt_two_prime_inclusion_exclusion_le P (fun p => 1 / ((p : ℝ) - 1))
    z_nat xi_nat hP hg hxi_lt
  dsimp only at hie
  have hPlt_eq : P.filter (· < z_nat) =
      (Finset.range z_nat).filter (fun p => p.Prime ∧ 2 < p) := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hp, hp2⟩, hpz⟩; exact ⟨hpz, hp, hp2⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨⟨lt_of_lt_of_le hpz (le_max_left z_nat _), hp, hp2⟩, hpz⟩
  have hQz_eq : P.filter (z_nat ≤ ·) =
      (Finset.Ico z_nat M).filter (fun p => p.Prime ∧ 2 < p) := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hpM, hp, hp2⟩, hzp⟩; exact ⟨⟨hzp, hpM⟩, hp, hp2⟩
    · rintro ⟨⟨hzp, hpM⟩, hp, hp2⟩; exact ⟨⟨hpM, hp, hp2⟩, hzp⟩
  have hJ0 : selbergJ (fun p => 1 / ((p : ℝ) - 1)) P xi_nat = J_odd xi :=
    selbergJ_range_eq_J_odd (lt_of_lt_of_le (Nat.lt_succ_self xi_nat) (le_max_right _ _))
  have hJ_lt : selbergJ (fun p => 1 / ((p : ℝ) - 1)) (P.filter (· < z_nat)) xi_nat =
      J_full z_nat xi := by
    rw [hPlt_eq]
    rfl
  have hS1 : ∑ q ∈ P.filter (z_nat ≤ ·),
      selbergH (fun p => 1 / ((p : ℝ) - 1)) q *
        selbergJ (fun p => 1 / ((p : ℝ) - 1)) P (xi_nat / q) =
      ∑ q ∈ (Finset.Ico z_nat M).filter (fun p => p.Prime ∧ 2 < p),
        (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) := by
    rw [hQz_eq]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq_mem := (Finset.mem_filter.mp hq).2
    have hq_pr : q.Prime := hq_mem.1
    have hq_gt2 : 2 < q := hq_mem.2
    have hH : selbergH (fun p => 1 / ((p : ℝ) - 1)) q = 1 / ((q : ℝ) - 2) := by
      rw [selbergH_selbergG (by rw [hq_pr.primeFactors]; simp [hq_gt2]), hq_pr.primeFactors,
        Finset.prod_singleton]
    have hJ_q : selbergJ (fun p => 1 / ((p : ℝ) - 1)) P (xi_nat / q) = J_odd (xi / (q : ℝ)) := by
      have hfl : Nat.floor (xi / (q : ℝ)) = xi_nat / q :=
        (floor_div_natCast_eq_floor_div hxi0 hq_pr.pos).symm
      have hdiv_lt : xi_nat / q < M :=
        lt_of_le_of_lt (Nat.div_le_self xi_nat q)
          (lt_of_lt_of_le (Nat.lt_succ_self xi_nat) (le_max_right _ _))
      rw [← hfl]
      exact selbergJ_range_eq_J_odd (hfl ▸ hdiv_lt)
    rw [hH, hJ_q]
  have hS2 : ∑ q₁ ∈ P.filter (z_nat ≤ ·), ∑ q₂ ∈ (P.filter (z_nat ≤ ·)).filter (q₁ < ·),
      selbergH (fun p => 1 / ((p : ℝ) - 1)) q₁ *
      selbergH (fun p => 1 / ((p : ℝ) - 1)) q₂ *
      selbergJ (fun p => 1 / ((p : ℝ) - 1)) P (xi_nat / (q₁ * q₂)) =
      ∑ q₁ ∈ (Finset.Ico z_nat M).filter (fun p => p.Prime ∧ 2 < p),
      ∑ q₂ ∈ ((Finset.Ico z_nat M).filter (fun p => p.Prime ∧ 2 < p)).filter (q₁ < ·),
        (1 / (((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2))) * J_odd (xi / ((q₁ * q₂ : ℕ) : ℝ)) := by
    rw [hQz_eq]
    refine Finset.sum_congr rfl fun q₁ hq₁ => Finset.sum_congr rfl fun q₂ hq₂ => ?_
    have hq₁_mem := (Finset.mem_filter.mp hq₁).2
    have hq₂_mem := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
    have hH₁ : selbergH (fun p => 1 / ((p : ℝ) - 1)) q₁ = 1 / ((q₁ : ℝ) - 2) := by
      rw [selbergH_selbergG (by rw [hq₁_mem.1.primeFactors]; simp [hq₁_mem.2]),
        hq₁_mem.1.primeFactors, Finset.prod_singleton]
    have hH₂ : selbergH (fun p => 1 / ((p : ℝ) - 1)) q₂ = 1 / ((q₂ : ℝ) - 2) := by
      rw [selbergH_selbergG (by rw [hq₂_mem.1.primeFactors]; simp [hq₂_mem.2]),
        hq₂_mem.1.primeFactors, Finset.prod_singleton]
    have hJ_q12 : selbergJ (fun p => 1 / ((p : ℝ) - 1)) P (xi_nat / (q₁ * q₂)) =
        J_odd (xi / ((q₁ * q₂ : ℕ) : ℝ)) := by
      have hpos : 1 ≤ q₁ * q₂ := Nat.mul_pos hq₁_mem.1.pos hq₂_mem.1.pos
      have hfl : Nat.floor (xi / ((q₁ * q₂ : ℕ) : ℝ)) = xi_nat / (q₁ * q₂) :=
        (floor_div_natCast_eq_floor_div hxi0 hpos).symm
      have hdiv_lt : xi_nat / (q₁ * q₂) < M :=
        lt_of_le_of_lt (Nat.div_le_self xi_nat (q₁ * q₂))
          (lt_of_lt_of_le (Nat.lt_succ_self xi_nat) (le_max_right _ _))
      rw [← hfl]
      exact selbergJ_range_eq_J_odd (hfl ▸ hdiv_lt)
    rw [hH₁, hH₂, hJ_q12]
    have hq₁_ne : (q₁ : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hq₁_mem.2
      linarith
    have hq₂_ne : (q₂ : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hq₂_mem.2
      linarith
    rw [mul_assoc, ← mul_assoc (1 / ((q₁ : ℝ) - 2)), one_div_mul_one_div]
  rw [hJ0, hJ_lt, hS1, hS2] at hie
  exact hie

/-- Partitioning `∑ q ∈ Finset.Ico a b, f q` across a monotone sequence `pts : Fin (k1 + 1) → ℕ`. -/
lemma sum_Ico_partition {k1 : ℕ} (pts : Fin (k1 + 1) → ℕ)
    (hmono : ∀ k : Fin k1, pts k.castSucc ≤ pts k.succ) (f : ℕ → ℝ) :
    ∑ q ∈ Finset.Ico (pts 0) (pts ⟨k1, Nat.lt_succ_self k1⟩), f q =
      ∑ k : Fin k1, ∑ q ∈ Finset.Ico (pts k.castSucc) (pts k.succ), f q := by
  induction k1 with
  | zero => simp
  | succ m ih =>
    have hmono' : ∀ k : Fin m, (fun j : Fin (m + 1) => pts j.castSucc) k.castSucc ≤
        (fun j : Fin (m + 1) => pts j.castSucc) k.succ := fun k => hmono k.castSucc
    have hle_m : pts 0 ≤ pts ⟨m, by omega⟩ := by
      have hgen : ∀ j : ℕ, (hj : j ≤ m + 1) → pts 0 ≤ pts ⟨j, by omega⟩ := by
        intro j hj
        induction j with
        | zero => exact le_rfl
        | succ j' ihj =>
          exact (ihj (by omega)).trans (hmono ⟨j', by omega⟩)
      exact hgen m (by omega)
    have hlast : pts ⟨m, by omega⟩ ≤ pts ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ :=
      hmono ⟨m, Nat.lt_succ_self m⟩
    have hsplit : ∑ q ∈ Finset.Ico (pts 0) (pts ⟨m + 1, Nat.lt_succ_self (m + 1)⟩), f q =
        (∑ q ∈ Finset.Ico (pts 0) (pts ⟨m, by omega⟩), f q) +
        ∑ q ∈ Finset.Ico (pts ⟨m, by omega⟩) (pts ⟨m + 1, Nat.lt_succ_self (m + 1)⟩), f q :=
      (Finset.sum_Ico_consecutive f hle_m hlast).symm
    have hih : ∑ q ∈ Finset.Ico (pts 0) (pts ⟨m, by omega⟩), f q =
        ∑ k : Fin m, ∑ q ∈ Finset.Ico (pts k.castSucc.castSucc) (pts k.succ.castSucc), f q :=
      ih (fun j : Fin (m + 1) => pts j.castSucc) hmono'
    rw [hsplit, hih, Fin.sum_univ_castSucc]
    rfl

private lemma sum_Ico_recip_sub_two_tele {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) =
      1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2) := by
  have htele' : ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 2) - 1 / (((n + 1 : ℕ) : ℝ) - 2)) =
      1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2) := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk, ih]
      push_cast
      ring
  rw [← htele']
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast; ring_nf

private lemma sum_Ico_recip_sub_two_prime_le {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Finset.Ico a b).filter Nat.Prime, (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
      2 / ((a : ℝ) - 2) := by
  have hsub : ∑ p ∈ (Finset.Ico a b).filter Nat.Prime, (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
      ∑ n ∈ Finset.Ico a b, (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun n hn => ?_
    split_ifs
    · exact le_rfl
    · have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
      have hn2_pos : (0 : ℝ) < (n : ℝ) - 2 := by linarith
      positivity
  have htele : ∑ n ∈ Finset.Ico a b, (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) =
      2 * ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  have h2 : ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) ≤
      ∑ n ∈ Finset.Ico a b, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha.trans (Finset.mem_Ico.mp hn).1
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
    have hdiff : 1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1) =
        1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
      field_simp; ring
    rw [hdiff]
    have hpos : 0 < ((n : ℝ) - 1) * ((n : ℝ) - 2) := mul_pos (by linarith) (by linarith)
    exact one_div_le_one_div_of_le hpos (by nlinarith)
  have hsum_tele := sum_Ico_recip_sub_two_tele hab
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha.trans hab
  have hb_nonneg : 0 ≤ 2 / ((b : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
  have hmul_eq : 2 * (1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2)) =
      2 / ((a : ℝ) - 2) - 2 / ((b : ℝ) - 2) := by ring
  linarith

/-- Helper: `∑_{p ∈ Ico (⌈w0⌉) (⌈w1⌉), p.Prime} 1/(p-2)` bounded via `MertensSumBounds`. -/
lemma sum_prime_inv_sub_two_Ico_le {M0 : ℝ} {E_lo E_hi : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi) {w0 w1 : ℝ} (hw0 : 2 < w0) (hw : w0 < w1) :
    ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) - 2) ≤
      Real.log (Real.log w1 / Real.log w0) + E_hi w1 + E_lo w0 + 2 / (w0 - 2) := by
  have hsplit : ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) - 2) =
      (∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime, (1 : ℝ) / p) +
        ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime,
          (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_ge : Nat.ceil w0 ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hp_gt2 : 2 < (p : ℝ) := lt_of_lt_of_le hw0 ((Nat.le_ceil w0).trans (by exact_mod_cast hp_ge))
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  have ha3 : 3 ≤ Nat.ceil w0 := Nat.lt_ceil.mpr (by exact_mod_cast hw0)
  have hab : Nat.ceil w0 ≤ Nat.ceil w1 := Nat.ceil_mono hw.le
  have h1 := mertens_sum_Ico_le hM hw0.le hw
  have h2 : ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime,
      (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 2 / (w0 - 2) := by
    refine (sum_Ico_recip_sub_two_prime_le ha3 hab).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith)
      (by linarith [Nat.le_ceil w0])
  linarith

/-- Endpoint-inclusive variant: `∑_{p ∈ Ico (⌈w0⌉) (⌊w1⌋ + 1), p.Prime} 1/(p-2)` bounded with `+ 1/w1`. -/
lemma sum_prime_inv_sub_two_Icc_le {M0 : ℝ} {E_lo E_hi : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi) {w0 w1 : ℝ} (hw0 : 2 < w0) (hw : w0 < w1) :
    ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) - 2) ≤
      Real.log (Real.log w1 / Real.log w0) + E_hi w1 + E_lo w0 + 2 / (w0 - 2) + 1 / w1 := by
  have ha3 : 3 ≤ Nat.ceil w0 := Nat.lt_ceil.mpr (by exact_mod_cast hw0)
  have hceil_le : Nat.ceil w0 ≤ Nat.ceil w1 := Nat.ceil_mono hw.le
  have hw1_nn : 0 ≤ w1 := by linarith
  have hfl_le_ceil : Nat.floor w1 + 1 ≤ Nat.ceil w1 + 1 :=
    Nat.succ_le_succ (Nat.floor_le_ceil w1)
  have hsplit_main :
      ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) - 2) =
      (∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime, (1 : ℝ) / p) +
        ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime,
          (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_ge : Nat.ceil w0 ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hp_gt2 : 2 < (p : ℝ) := lt_of_lt_of_le hw0 ((Nat.le_ceil w0).trans (by exact_mod_cast hp_ge))
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  have h2 : ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime,
      (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤ 2 / (w0 - 2) := by
    by_cases hle : Nat.ceil w0 ≤ Nat.floor w1 + 1
    · refine (sum_Ico_recip_sub_two_prime_le ha3 hle).trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith)
        (by linarith [Nat.le_ceil w0])
    · have hemp : Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1) = ∅ :=
        Finset.Ico_eq_empty_of_le (by omega)
      simp only [hemp, Finset.filter_empty, Finset.sum_empty]
      have : 0 < w0 - 2 := by linarith
      positivity
  have h1 : ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log w1 / Real.log w0) + E_hi w1 + E_lo w0 + 1 / w1 := by
    have hmert := mertens_sum_Ico_le hM hw0.le hw
    rcases eq_or_lt_of_le (Nat.floor_le_ceil w1) with heq | hlt
    · -- `Nat.floor w1 = Nat.ceil w1`, so `w1 = Nat.floor w1` is an integer
      have hw1_eq : (Nat.ceil w1 : ℝ) = w1 := by
        have hfl_le : (Nat.floor w1 : ℝ) ≤ w1 := Nat.floor_le hw1_nn
        have hw1_le : w1 ≤ (Nat.ceil w1 : ℝ) := Nat.le_ceil w1
        have hcast : (Nat.floor w1 : ℝ) = (Nat.ceil w1 : ℝ) := by exact_mod_cast heq
        linarith
      have hico_split : Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1) =
          insert (Nat.ceil w1) (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)) := by
        ext p
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hnotmem : Nat.ceil w1 ∉ (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime := by
        simp
      rw [hico_split, Finset.filter_insert]
      split_ifs with hpr
      · rw [Finset.sum_insert hnotmem, hw1_eq]
        linarith
      · have hw1_nn' : 0 ≤ 1 / w1 := one_div_nonneg.mpr hw1_nn
        linarith
    · -- `Nat.floor w1 + 1 ≤ Nat.ceil w1`
      have hsub : (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime ⊆
          (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
        exact ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 (by omega)⟩, hp.2⟩
      have hle_sum :
          ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.floor w1 + 1)).filter Nat.Prime, (1 : ℝ) / p ≤
          ∑ p ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil w1)).filter Nat.Prime, (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      have hw1_nn' : 0 ≤ 1 / w1 := one_div_nonneg.mpr hw1_nn
      linarith
  linarith

/-- Lower bound for `∑_{p ∈ Ico (⌈A0⌉) (⌈A1⌉), p.Prime} 1/(p-2)` via `MertensSumBounds`. -/
lemma sum_prime_inv_sub_two_Ico_ge {M0 : ℝ} {E_lo E_hi : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi) {A0 A1 : ℝ} (hA0 : 2 < A0) (hA : A0 < A1) :
    max 0 (Real.log (Real.log A1 / Real.log A0) - E_lo A1 - E_hi A0) ≤
      ∑ p ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) - 2) := by
  have hnn : 0 ≤ ∑ p ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime,
      (1 : ℝ) / ((p : ℝ) - 2) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hp_ge : Nat.ceil A0 ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hp_gt2 : 2 < (p : ℝ) := lt_of_lt_of_le hA0 ((Nat.le_ceil A0).trans (by exact_mod_cast hp_ge))
    positivity
  refine max_le hnn ?_
  have hge_p :
      ∑ p ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      ∑ p ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime,
        (1 : ℝ) / ((p : ℝ) - 2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_ge : Nat.ceil A0 ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hp_gt2 : 2 < (p : ℝ) := lt_of_lt_of_le hA0 ((Nat.le_ceil A0).trans (by exact_mod_cast hp_ge))
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hceil : Nat.ceil A0 ≤ Nat.ceil A1 := Nat.ceil_mono hA.le
  have hsub_eq :
      ∑ p ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) =
      (∑ p ∈ (Finset.range (Nat.ceil A1)).filter Nat.Prime, (1 : ℝ) / p) -
        (∑ p ∈ (Finset.range (Nat.ceil A0)).filter Nat.Prime, (1 : ℝ) / p) := by
    simp only [Finset.sum_filter]
    exact Finset.sum_Ico_eq_sub (fun p => if p.Prime then (1 : ℝ) / p else 0) hceil
  have hlo1 := (hM A1 (by linarith)).1
  have hhi0 := (hM A0 hA0.le).2
  have hlog0 : 0 < Real.log A0 := Real.log_pos (by linarith)
  have hlog1 : 0 < Real.log A1 := Real.log_pos (by linarith)
  rw [Real.log_div hlog1.ne' hlog0.ne']
  linarith

/-- Lower bound for a single disjoint 2-prime box `(Ico ⌈A0⌉ ⌈A1⌉) × (Ico ⌈B0⌉ ⌈B1⌉)`. -/
lemma two_prime_box_ge {M0 : ℝ} {E_lo E_hi : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi)
    {A0 A1 B0 B1 xi : ℝ} (hA0 : 2 < A0) (hA : A0 < A1) (hAB : A1 ≤ B0) (hB : B0 < B1)
    (hprod : A1 * B1 ≤ xi) :
    max 0 (Real.log (Real.log A1 / Real.log A0) - E_lo A1 - E_hi A0) *
        max 0 (Real.log (Real.log B1 / Real.log B0) - E_lo B1 - E_hi B0) *
        J_odd (xi / (A1 * B1)) ≤
      ∑ q₁ ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime,
      ∑ q₂ ∈ (Finset.Ico (Nat.ceil B0) (Nat.ceil B1)).filter Nat.Prime,
        (1 / (((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2))) * J_odd (xi / ((q₁ * q₂ : ℕ) : ℝ)) := by
  have hS1 := sum_prime_inv_sub_two_Ico_ge hM hA0 hA
  have hS2 := sum_prime_inv_sub_two_Ico_ge hM (by linarith) hB
  have hJnn : 0 ≤ J_odd (xi / (A1 * B1)) := J_odd_nonneg _
  have hs1_nn : 0 ≤ max 0 (Real.log (Real.log A1 / Real.log A0) - E_lo A1 - E_hi A0) :=
    le_max_left _ _
  have hs2_nn : 0 ≤ max 0 (Real.log (Real.log B1 / Real.log B0) - E_lo B1 - E_hi B0) :=
    le_max_left _ _
  have hprod_le :
      max 0 (Real.log (Real.log A1 / Real.log A0) - E_lo A1 - E_hi A0) *
        max 0 (Real.log (Real.log B1 / Real.log B0) - E_lo B1 - E_hi B0) *
        J_odd (xi / (A1 * B1)) ≤
      (∑ q₁ ∈ (Finset.Ico (Nat.ceil A0) (Nat.ceil A1)).filter Nat.Prime, (1 : ℝ) / ((q₁ : ℝ) - 2)) *
      (∑ q₂ ∈ (Finset.Ico (Nat.ceil B0) (Nat.ceil B1)).filter Nat.Prime, (1 : ℝ) / ((q₂ : ℝ) - 2)) *
      J_odd (xi / (A1 * B1)) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul hS1 hS2 hs2_nn ?_) hJnn
    exact hs1_nn.trans hS1
  refine hprod_le.trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun q₁ hq₁ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun q₂ hq₂ => ?_
  have hq₁_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hq₁).1
  have hq₂_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hq₂).1
  have hq₁_gt2 : 2 < (q₁ : ℝ) := lt_of_lt_of_le hA0 ((Nat.le_ceil A0).trans (by exact_mod_cast hq₁_ico.1))
  have hq₂_gt2 : 2 < (q₂ : ℝ) := lt_of_lt_of_le (by linarith) ((Nat.le_ceil B0).trans (by exact_mod_cast hq₂_ico.1))
  have hq₁_lt : (q₁ : ℝ) < A1 := Nat.lt_ceil.mp hq₁_ico.2
  have hq₂_lt : (q₂ : ℝ) < B1 := Nat.lt_ceil.mp hq₂_ico.2
  have hq₁_pos : (0 : ℝ) < (q₁ : ℝ) := by linarith
  have hq₂_pos : (0 : ℝ) < (q₂ : ℝ) := by linarith
  have hmul_le : ((q₁ * q₂ : ℕ) : ℝ) ≤ A1 * B1 := by
    push_cast
    exact mul_le_mul hq₁_lt.le hq₂_lt.le hq₂_pos.le (by linarith)
  have hdiv_le : xi / (A1 * B1) ≤ xi / ((q₁ * q₂ : ℕ) : ℝ) := by
    have hq12_pos : (0 : ℝ) < ((q₁ * q₂ : ℕ) : ℝ) := by
      push_cast
      exact mul_pos hq₁_pos hq₂_pos
    have hxi_nn : 0 ≤ xi := by
      have : 0 < A1 * B1 := mul_pos (by linarith) (by linarith)
      linarith
    exact div_le_div_of_nonneg_left hxi_nn hq12_pos hmul_le
  have hJ_le : J_odd (xi / (A1 * B1)) ≤ J_odd (xi / ((q₁ * q₂ : ℕ) : ℝ)) :=
    J_odd_mono hdiv_le
  have hcoeff_nn : 0 ≤ 1 / (((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2)) := by
    have : 0 < (q₁ : ℝ) - 2 := by linarith
    have : 0 < (q₂ : ℝ) - 2 := by linarith
    positivity
  have heq : (1 : ℝ) / ((q₁ : ℝ) - 2) * (1 / ((q₂ : ℝ) - 2)) * J_odd (xi / (A1 * B1)) =
      (1 / (((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2))) * J_odd (xi / (A1 * B1)) := by
    rw [one_div_mul_one_div]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hJ_le hcoeff_nn

end TwoPrimeIEHelpers

end BuchstabSwitching
