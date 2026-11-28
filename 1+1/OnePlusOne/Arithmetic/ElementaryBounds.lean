import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

/-!
# Unconditional Elementary & Sieve-Arithmetic Lemmas (`OnePlusOne`)

Every theorem in this file is proved unconditionally in standard Lean/Mathlib logic
with zero external premises:
1. `major_arcs_disjoint`: strict separation of `|a/q - a'/q'|` beyond `Δ(q) + Δ(q')` for `Q₀ ≤ √Y / 2`.
2. `ratio_2p_sub_1_le_pow_eighth`: `(2p - 1)/(p - 1) ≤ p^{1/8}` for all `p ≥ 271`.
3. `twin_prime_partial_product_ge`: unconditional lower bound `0.65928 < ∏_{p ∈ s} (1 - 1/(p-1)^2)`.
4. `totient_sq_ge_half`: `q / 2 ≤ φ(q)^2` for all `q ≥ 1`.
5. `dyadic_geom_sum_lt`: finite geometric sum `∑_{k < m} (1/√2)^k < 2 + √2`.
-/

namespace OnePlusOne.Arithmetic

open scoped BigOperators

/-- Distinct major arcs `|α - a/q| ≤ 1/(2 q √Y)` with `q, q' ≤ (1/2)√Y` are disjoint. -/
theorem major_arcs_disjoint {Y : ℝ} (hY : 4 ≤ Y)
    {q q' : ℕ} {a a' : ℤ}
    (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hqY : (q : ℝ) ≤ Real.sqrt Y / 2)
    (hq'Y : (q' : ℝ) ≤ Real.sqrt Y / 2)
    (hne : (a : ℝ) / q ≠ (a' : ℝ) / q') :
    1 / (2 * (q : ℝ) * Real.sqrt Y) + 1 / (2 * (q' : ℝ) * Real.sqrt Y) ≤
      |(a : ℝ) / q - (a' : ℝ) / q'| := by
  have hsq : 0 < Real.sqrt Y := Real.sqrt_pos.mpr (by linarith)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hdiff_ne : a * (q' : ℤ) - a' * (q : ℤ) ≠ 0 := by
    intro heq
    apply hne
    have hR : (a : ℝ) * q' = (a' : ℝ) * q := by
      have := congrArg (fun z : ℤ => (z : ℝ)) heq
      push_cast at this
      linarith
    field_simp
    linarith [hR]
  have hdiff_abs : (1 : ℝ) ≤ |(a : ℝ) * q' - (a' : ℝ) * q| := by
    have hz : 1 ≤ |a * (q' : ℤ) - a' * (q : ℤ)| := Int.one_le_abs hdiff_ne
    have hR : ((|a * (q' : ℤ) - a' * (q : ℤ)| : ℤ) : ℝ) = |(a : ℝ) * q' - (a' : ℝ) * q| := by
      push_cast
      rfl
    rw [← hR]
    exact_mod_cast hz
  have hfrac_ge : 1 / ((q : ℝ) * q') ≤ |(a : ℝ) / q - (a' : ℝ) / q'| := by
    have hrew : (a : ℝ) / q - (a' : ℝ) / q' = ((a : ℝ) * q' - (a' : ℝ) * q) / ((q : ℝ) * q') := by
      field_simp
    rw [hrew, abs_div, abs_of_pos (mul_pos hqR hq'R)]
    exact div_le_div_of_nonneg_right hdiff_abs (mul_pos hqR hq'R).le
  have hsum_le : (q : ℝ) + q' ≤ Real.sqrt Y := by linarith
  have harc :
      1 / (2 * (q : ℝ) * Real.sqrt Y) + 1 / (2 * (q' : ℝ) * Real.sqrt Y) ≤
        1 / ((q : ℝ) * q') := by
    have hrew :
        1 / (2 * (q : ℝ) * Real.sqrt Y) + 1 / (2 * (q' : ℝ) * Real.sqrt Y) =
          ((q : ℝ) + q') / (2 * (q : ℝ) * q' * Real.sqrt Y) := by
      field_simp
      ring
    rw [hrew, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hqR hq'R]
  exact harc.trans hfrac_ge

/-- Integer kernel check `541^8 < 271 * 270^8` plus monotonicity for `p ≥ 271`. -/
theorem ratio_2p_sub_1_le_pow_eighth {p : ℝ} (hp : 271 ≤ p) :
    ((2 * p - 1) / (p - 1)) ^ 8 ≤ p := by
  have hbase : (541 : ℝ) ^ 8 ≤ 271 * (270 : ℝ) ^ 8 := by norm_num
  have hp1 : 0 < p - 1 := by linarith
  have hratio : (2 * p - 1) / (p - 1) ≤ 541 / 270 := by
    rw [div_le_div_iff₀ hp1 (by norm_num)]
    linarith
  have hratio0 : 0 ≤ (2 * p - 1) / (p - 1) := div_nonneg (by linarith) hp1.le
  calc
    ((2 * p - 1) / (p - 1)) ^ 8 ≤ (541 / 270 : ℝ) ^ 8 := by gcongr
    _ = (541 : ℝ) ^ 8 / (270 : ℝ) ^ 8 := by ring
    _ ≤ 271 := by rw [div_le_iff₀ (by positivity)]; exact hbase
    _ ≤ p := hp

private def oddSmallPrimes : Finset ℕ :=
  (Finset.range 60).filter (fun p => 2 < p ∧ Nat.Prime p)

private noncomputable def twinFactor (p : ℕ) : ℝ := 1 - 1 / ((p : ℝ) - 1) ^ 2

private lemma twinFactor_nonneg {p : ℕ} (hp : 2 < p) : 0 ≤ twinFactor p := by
  have h : (2 : ℝ) < p := by exact_mod_cast hp
  unfold twinFactor
  apply sub_nonneg.mpr
  apply (div_le_one (sq_pos_of_pos (by linarith))).mpr
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

private lemma through_fifty_nine :
    (0.66234 : ℝ) < ∏ p ∈ oddSmallPrimes, twinFactor p := by
  have h : oddSmallPrimes = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59} := by decide
  rw [h]
  norm_num [twinFactor, Finset.prod_insert, Finset.prod_singleton]

private lemma reciprocal_square_step (b : ℝ) (hb : 0 < b) :
    1 / (b + 15) ^ 2 ≤ 1 / (30 * b) - 1 / (30 * (b + 30)) := by
  have h : 1 / (30 * b) - 1 / (30 * (b + 30)) = 1 / (b * (b + 30)) := by
    field_simp
    ring
  rw [h]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

private lemma progression_tail (b : ℝ) (hb : 0 < b) (k : ℕ) :
    ∑ j ∈ Finset.range k, 1 / (b + 30 * (j : ℝ) + 15) ^ 2 ≤
      1 / (30 * b) - 1 / (30 * (b + 30 * (k : ℝ))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hs := reciprocal_square_step (b + 30 * (k : ℝ)) (by positivity)
    have h : b + 30 * ((k : ℝ) + 1) = b + 30 * (k : ℝ) + 30 := by ring
    rw [h]
    linarith

private lemma large_prime_residues {p : ℕ} (hp : Nat.Prime p) (h : 59 < p) :
    p % 30 ∈ ({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
  have h2 : ¬ 2 ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with he | he <;> omega
  have h3 : ¬ 3 ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with he | he <;> omega
  have h5 : ¬ 5 ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with he | he <;> omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hm := Nat.mod_lt p (by decide : 0 < 30)
  interval_cases hres : p % 30 <;> omega

private lemma eight_class_tail (k : ℕ) :
    ∑ r ∈ ({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ),
      ∑ j ∈ Finset.range k, 1 / ((44 + (r : ℝ)) + 30 * (j : ℝ) + 15) ^ 2 < 0.004615 := by
  calc
    _ ≤ ∑ r ∈ ({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), 1 / (30 * (44 + (r : ℝ))) := by
      apply Finset.sum_le_sum
      intro r _
      exact (progression_tail (44 + (r : ℝ)) (by positivity) k).trans (sub_le_self _ (by positivity))
    _ < 0.004615 := by norm_num [Finset.sum_insert, Finset.sum_singleton]

private lemma product_loss_bound {ι : Type*} (s : Finset ι) (loss : ι → ℝ)
    (hl : ∀ i ∈ s, 0 ≤ loss i) (hu : ∀ i ∈ s, loss i ≤ 1) :
    1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hlo := hl i (Finset.mem_insert_self i s)
    have hup := hu i (Finset.mem_insert_self i s)
    have hsum : 0 ≤ ∑ j ∈ s, loss j :=
      Finset.sum_nonneg (fun j hj => hl j (Finset.mem_insert_of_mem hj))
    have hind := ih (fun j hj => hl j (Finset.mem_insert_of_mem hj))
      (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    exact le_trans (by nlinarith [mul_nonneg hlo hsum])
      (mul_le_mul_of_nonneg_left hind (sub_nonneg.mpr hup))

private lemma prod_le_one_of_bounds {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi]
    have hi1 := h1 i (Finset.mem_insert_self i t)
    have ht_nn : 0 ≤ ∏ j ∈ t, f j :=
      Finset.prod_nonneg (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
    have ht_le1 : ∏ j ∈ t, f j ≤ 1 :=
      ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    calc
      f i * ∏ j ∈ t, f j ≤ 1 * ∏ j ∈ t, f j := mul_le_mul_of_nonneg_right hi1 ht_nn
      _ = ∏ j ∈ t, f j := one_mul _
      _ ≤ 1 := ht_le1

private lemma prime_square_tail (s : Finset ℕ) (K : ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ 59 < p ∧ p < K) :
    ∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2 < 0.004615 := by
  let encode (p : ℕ) : ℕ × ℕ := (p % 30, p / 30 - 2)
  let residues : Finset ℕ := {1, 7, 11, 13, 17, 19, 23, 29}
  let cost (i : ℕ × ℕ) : ℝ := 1 / ((44 + (i.1 : ℝ)) + 30 * (i.2 : ℝ) + 15) ^ 2
  have decode (p : ℕ) (hp : 59 < p) : 60 + (encode p).1 + 30 * (encode p).2 = p := by
    simp only [encode]
    omega
  have majorize : ∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2 ≤
      ∑ i ∈ residues ×ˢ Finset.range K, cost i := by
    apply Finset.sum_le_sum_of_injOn encode
    · intro p hp q hq he
      rw [← decode p (hs p hp).2.1, ← decode q (hs q hq).2.1, he]
    · intro i hi
      rcases Finset.mem_image.mp hi with ⟨p, hp, rfl⟩
      apply Finset.mem_product.mpr
      refine ⟨large_prime_residues (hs p hp).1 (hs p hp).2.1, Finset.mem_range.mpr ?_⟩
      change p / 30 - 2 < K
      have := (hs p hp).2.2
      omega
    · intro p hp
      have h := congrArg (fun n : ℕ => (n : ℝ)) (decode p (hs p hp).2.1)
      push_cast at h
      have hc : (44 + ((encode p).1 : ℝ)) + 30 * ((encode p).2 : ℝ) + 15 = (p : ℝ) - 1 := by
        linarith
      simp only [cost, hc, le_refl]
    · intro i _ _
      dsimp [cost]
      positivity
  refine lt_of_le_of_lt majorize ?_
  rw [Finset.sum_product]
  exact eight_class_tail K

/-- Unconditional lower bound on every finite odd-prime twin-prime partial product (`> 0.65928`). -/
theorem twin_prime_partial_product_ge (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ 2 < p) :
    (0.65928 : ℝ) < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  let small := s.filter (fun p => p ≤ 59)
  let large := s.filter (fun p => 59 < p)
  have hunion : small ∪ large = s := by
    ext p
    simp only [small, large, Finset.mem_union, Finset.mem_filter]
    by_cases hp : p ≤ 59
    · simp [hp]
    · simp [hp, lt_of_not_ge hp]
  have hdisj : Disjoint small large := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    omega
  have hsplit : ∏ p ∈ s, twinFactor p =
      (∏ p ∈ small, twinFactor p) * ∏ p ∈ large, twinFactor p := by
    rw [← hunion, Finset.prod_union hdisj]
  have hsmall_sub : small ⊆ oddSmallPrimes := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hle⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (hs p hps).2, (hs p hps).1⟩
  have hsmall_ge : (0.66234 : ℝ) < ∏ p ∈ small, twinFactor p := by
    have hle : ∏ p ∈ oddSmallPrimes, twinFactor p ≤ ∏ p ∈ small, twinFactor p := by
      rw [← Finset.prod_sdiff hsmall_sub]
      have hdiff_le_one : ∏ p ∈ oddSmallPrimes \ small, twinFactor p ≤ 1 := by
        apply prod_le_one_of_bounds
        · intro p hp
          exact twinFactor_nonneg (Finset.mem_filter.mp (Finset.sdiff_subset hp)).2.1
        · intro p hp
          have hp2 : 2 < p := (Finset.mem_filter.mp (Finset.sdiff_subset hp)).2.1
          have : (2 : ℝ) < p := by exact_mod_cast hp2
          unfold twinFactor
          linarith [show (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 by positivity]
      have hsmall_nn : 0 ≤ ∏ p ∈ small, twinFactor p :=
        Finset.prod_nonneg (fun p hp => twinFactor_nonneg (hs p (Finset.mem_filter.mp hp).1).2)
      exact mul_le_of_le_one_left hsmall_nn hdiff_le_one
    exact through_fifty_nine.trans_le hle
  let K := s.sup id + 1
  have hlarge_tail : ∑ p ∈ large, 1 / ((p : ℝ) - 1) ^ 2 < 0.004615 := by
    apply prime_square_tail large K
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hgt⟩
    exact ⟨(hs p hps).1, hgt, Nat.lt_succ_of_le (Finset.le_sup (f := id) hps)⟩
  have hlarge_ge : (1 - 0.004615 : ℝ) < ∏ p ∈ large, twinFactor p := by
    have hprod := product_loss_bound large (fun p => 1 / ((p : ℝ) - 1) ^ 2)
      (fun _ _ => by positivity)
      (fun p hp => by
        have hgt : 59 < p := (Finset.mem_filter.mp hp).2
        have h : (59 : ℝ) < p := by exact_mod_cast hgt
        apply (div_le_one (sq_pos_of_pos (by linarith))).mpr
        nlinarith)
    have : ∏ p ∈ large, twinFactor p = ∏ p ∈ large, (1 - 1 / ((p : ℝ) - 1) ^ 2) := rfl
    linarith
  have hprod_ge : (0.66234 : ℝ) * (1 - 0.004615) < ∏ p ∈ s, twinFactor p := by
    rw [hsplit]
    exact mul_lt_mul'' hsmall_ge hlarge_ge (by norm_num) (by norm_num)
  have hnum : (0.65928 : ℝ) < 0.66234 * (1 - 0.004615) := by norm_num
  exact hnum.trans hprod_ge

private lemma odd_prime_pow_totient_sq {p k : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 := by
  rw [Nat.totient_prime_pow hp hk]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpow : (p - 1) ^ 2 ≥ p := by
    rcases Nat.exists_eq_add_of_le hp3 with ⟨q, rfl⟩
    have hsub : 3 + q - 1 = q + 2 := by omega
    rw [hsub]
    nlinarith
  calc
    p ^ k = p ^ (k - 1) * p := by
      cases k with
      | zero => omega
      | succ m => simp [pow_succ]
    _ ≤ p ^ (k - 1) * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hpow
    _ ≤ (p ^ (k - 1)) ^ 2 * (p - 1) ^ 2 := by
      apply Nat.mul_le_mul_right
      exact Nat.le_self_pow (by decide : 2 ≠ 0) (p ^ (k - 1))
    _ = (p ^ (k - 1) * (p - 1)) ^ 2 := by ring

private lemma two_pow_totient_sq (k : ℕ) :
    2 ^ k ≤ 2 * (Nat.totient (2 ^ k)) ^ 2 := by
  cases k with
  | zero => simp
  | succ m =>
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos m)]
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    have hpow : (2 : ℕ) ^ (m + 1) ≤ 2 * (2 ^ m * (2 - 1)) ^ 2 := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
      calc
        2 ^ (m + 1) = 2 * 2 ^ m := by ring
        _ ≤ 2 * (2 ^ m * 2 ^ m) := Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ h1)
        _ = 2 * (2 ^ m * (2 - 1)) ^ 2 := by ring
    exact hpow

private lemma exists_coprime_prime_pow_split {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hd : p ∣ n) :
    ∃ k r : ℕ, 1 ≤ k ∧ 1 ≤ r ∧ ¬ p ∣ r ∧ n = p ^ k * r := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases hd with ⟨m, rfl⟩
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    by_cases hdm : p ∣ m
    · obtain ⟨k, r, hk, hr, hnd, hm_eq⟩ := ih m (lt_mul_of_one_lt_left hm hp.one_lt) hm hdm
      refine ⟨k + 1, r, by omega, hr, hnd, ?_⟩
      rw [hm_eq, pow_succ']
      ring
    · exact ⟨1, m, le_refl 1, hm, hdm, by ring⟩

private lemma odd_totient_sq_ge {m : ℕ} (hm : Odd m) (hm1 : 1 ≤ m) :
    m ≤ m.totient ^ 2 := by
  induction m using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h1 : n = 1
    · subst h1; simp
    have hn2 : 2 ≤ n := by omega
    let p := n.minFac
    have hp : p.Prime := n.minFac_prime (by omega)
    have hpd : p ∣ n := n.minFac_dvd
    have hp2 : p ≠ 2 := by
      intro hp2eq
      have h2n : 2 ∣ n := hp2eq ▸ hpd
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2n)) hm
    obtain ⟨k, r, hk, hr_pos, hnd, hsplit⟩ :=
      exists_coprime_prime_pow_split hp (by omega) hpd
    have hr_odd : Odd r := by
      rw [Nat.odd_iff]
      by_contra hne
      have h2r : 2 ∣ r := by omega
      have h2n : 2 ∣ n := by rw [hsplit]; exact h2r.trans (dvd_mul_left r (p ^ k))
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2n)) hm
    have hcop : Nat.Coprime (p ^ k) r := (hp.coprime_iff_not_dvd.mpr hnd).pow_left k
    have hr_lt : r < n := by
      have hpk_gt1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
      calc
        r < p ^ k * r := lt_mul_of_one_lt_left hr_pos hpk_gt1
        _ = n := hsplit.symm
    have h1_le := odd_prime_pow_totient_sq hp hp2 hk
    have h2_le := ih r hr_lt hr_odd hr_pos
    have htot : n.totient = (p ^ k).totient * r.totient := by
      rw [hsplit]
      exact Nat.totient_mul hcop
    rw [htot, mul_pow, hsplit]
    exact Nat.mul_le_mul h1_le h2_le

/-- Elementary lower bound `q / 2 ≤ φ(q)^2` valid for all `q ≥ 1`. -/
theorem totient_sq_ge_half {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) / 2 ≤ (q.totient : ℝ) ^ 2 := by
  have hNat : q ≤ 2 * q.totient ^ 2 := by
    by_cases h2q : 2 ∣ q
    · obtain ⟨k, m, _, hm_pos, hm_nd2, hsplit⟩ :=
        exists_coprime_prime_pow_split Nat.prime_two hq h2q
      have hm_odd : Odd m := by rw [Nat.odd_iff]; omega
      have hcop : Nat.Coprime (2 ^ k) m := (Nat.prime_two.coprime_iff_not_dvd.mpr hm_nd2).pow_left k
      have htot : q.totient = (2 ^ k).totient * m.totient := by
        rw [hsplit]
        exact Nat.totient_mul hcop
      have h1 := two_pow_totient_sq k
      have h2 := odd_totient_sq_ge hm_odd hm_pos
      calc
        q = 2 ^ k * m := hsplit
        _ ≤ (2 * (2 ^ k).totient ^ 2) * (m.totient ^ 2) := Nat.mul_le_mul h1 h2
        _ = 2 * ((2 ^ k).totient * m.totient) ^ 2 := by ring
        _ = 2 * q.totient ^ 2 := by rw [htot]
    · have hq_odd : Odd q := by rw [Nat.odd_iff]; omega
      exact (odd_totient_sq_ge hq_odd hq).trans (Nat.le_mul_of_pos_left _ (by decide))
  have hR : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by exact_mod_cast hNat
  linarith

private lemma geom_sum_mul_one_sub (r : ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, r ^ k) * (1 - r) = 1 - r ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

/-- Finite geometric series bound `∑_{k < m} (1/√2)^k < 2 + √2`. -/
theorem dyadic_geom_sum_lt (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 / Real.sqrt 2) ^ k < 2 + Real.sqrt 2 := by
  have hr_pos : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
  have hsqrt_gt : (1 : ℝ) < Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr_lt : (1 / Real.sqrt 2 : ℝ) < 1 := (div_lt_one (by positivity)).mpr hsqrt_gt
  have hsub_pos : 0 < 1 - (1 / Real.sqrt 2 : ℝ) := sub_pos.mpr hr_lt
  have hnum_lt : 1 - (1 / Real.sqrt 2 : ℝ) ^ m < 1 := by
    have : 0 < (1 / Real.sqrt 2 : ℝ) ^ m := pow_pos hr_pos m
    linarith
  have hsum_eq :
      ∑ k ∈ Finset.range m, (1 / Real.sqrt 2) ^ k =
        (1 - (1 / Real.sqrt 2 : ℝ) ^ m) / (1 - 1 / Real.sqrt 2) := by
    exact (eq_div_iff hsub_pos.ne').mpr (geom_sum_mul_one_sub (1 / Real.sqrt 2) m)
  rw [hsum_eq]
  calc
    (1 - (1 / Real.sqrt 2) ^ m) / (1 - 1 / Real.sqrt 2) <
        1 / (1 - 1 / Real.sqrt 2) := div_lt_div_of_pos_right hnum_lt hsub_pos
    _ = 2 + Real.sqrt 2 := by
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith

end OnePlusOne.Arithmetic
