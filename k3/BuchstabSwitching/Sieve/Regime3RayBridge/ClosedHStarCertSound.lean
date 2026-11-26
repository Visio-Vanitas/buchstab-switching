import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStar
import BuchstabSwitching.Sieve.Regime3RayBridge.ClosedHStarCertData
import Mathlib.Tactic

namespace BuchstabSwitching

/-!
# Soundness of the Fixed-Point `log` Evaluator, Gap Completeness, and Causal Scan

Proves that the `10^12`-scale integer evaluator in `ClosedHStarCertData` yields certified bounds
on `Real.log`, that `gaps_ok` certifies completeness of `s0List` for primes in `[3, 8000] \ Q0_100`,
and that `scan_chain_ok` establishes `ScanInv s0List stFinal`.
-/

noncomputable section

/-! ## 3. Soundness of Fixed-Point `log`, Gap Completeness, and Causal Scan -/

lemma scaleS_pos : (0 : ℝ) < (scaleS : ℝ) := by unfold scaleS; positivity

lemma floorDiv_le_real {a b : ℕ} (hb : 0 < b) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]; exact_mod_cast Nat.div_mul_le_self a b

private lemma real_le_ceilDiv {a b : ℕ} (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ ((hstarCeilDiv a b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h3 : a ≤ hstarCeilDiv a b * b := by
    by_cases ha : a = 0
    · subst ha; simp
    · unfold hstarCeilDiv; have h1 := Nat.div_add_mod (a + b - 1) b; have h2 := Nat.mod_lt (a + b - 1) hb
      have hcomm : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
      omega
  exact_mod_cast h3

private lemma logLoop2_sound {a b : ℕ} (hb : 0 < b) :
    ∀ (n j tLo tHi sLo sHi : ℕ),
      (tLo : ℝ) / (scaleS : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ (2 * j + 1) →
      ((a : ℝ) / (b : ℝ)) ^ (2 * j + 1) ≤ (tHi : ℝ) / (scaleS : ℝ) →
      let res := logLoop2 n j (a * a) (b * b) tLo tHi sLo sHi
      ((res.1 : ℝ) - (sLo : ℝ)) / (scaleS : ℝ) ≤
        ∑ m ∈ Finset.range n, (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) *
          ((a : ℝ) / (b : ℝ)) ^ (2 * (j + m) + 1) ∧
      ∑ m ∈ Finset.range n, (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) *
          ((a : ℝ) / (b : ℝ)) ^ (2 * (j + m) + 1) ≤
        ((res.2 : ℝ) - (sHi : ℝ)) / (scaleS : ℝ) := by
  intro n
  induction n with
  | zero => intro j tLo tHi sLo sHi _ _; simp [logLoop2]
  | succ n ih =>
    intro j tLo tHi sLo sHi htLo htHi
    set d : ℕ := 2 * j + 1
    set u : ℝ := (a : ℝ) / (b : ℝ)
    have hd_pos : 0 < d := by omega
    have hb2_pos : 0 < b * b := Nat.mul_pos hb hb
    have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
    have hu_nn : 0 ≤ u := by positivity
    have hd_eq : (d : ℝ) = 2 * (j : ℝ) + 1 := by simp [d]
    have hterm_lo : (((2 * tLo) / d : ℕ) : ℝ) / (scaleS : ℝ) ≤
        (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) := by
      have h1 : (((2 * tLo) / d : ℕ) : ℝ) ≤ (2 * (tLo : ℝ)) / (d : ℝ) := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using floorDiv_le_real (a := 2 * tLo) hd_pos
      have h2 : (2 * (tLo : ℝ)) / (d : ℝ) / (scaleS : ℝ) =
          (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * ((tLo : ℝ) / (scaleS : ℝ)) := by rw [hd_eq]; ring
      exact le_trans (div_le_div_of_nonneg_right h1 hS.le) (h2 ▸ by gcongr)
    have hterm_hi : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
        ((hstarCeilDiv (2 * tHi) d : ℕ) : ℝ) / (scaleS : ℝ) := by
      have h1 : (2 * (tHi : ℝ)) / (d : ℝ) ≤ ((hstarCeilDiv (2 * tHi) d : ℕ) : ℝ) := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using real_le_ceilDiv (a := 2 * tHi) hd_pos
      have h2 : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
          (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * ((tHi : ℝ) / (scaleS : ℝ)) := by gcongr
      have h3 : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * ((tHi : ℝ) / (scaleS : ℝ)) =
          (2 * (tHi : ℝ)) / (d : ℝ) / (scaleS : ℝ) := by rw [hd_eq]; ring
      exact le_trans (h3 ▸ h2) (div_le_div_of_nonneg_right h1 hS.le)
    have htLo1 : (((tLo * (a * a)) / (b * b) : ℕ) : ℝ) / (scaleS : ℝ) ≤ u ^ (2 * (j + 1) + 1) := by
      have h1 : (((tLo * (a * a)) / (b * b) : ℕ) : ℝ) ≤
          ((tLo : ℝ) * ((a : ℝ) * (a : ℝ))) / ((b : ℝ) * (b : ℝ)) := by
        simpa [Nat.cast_mul] using floorDiv_le_real (a := tLo * (a * a)) hb2_pos
      have h2 : (((tLo : ℝ) * ((a : ℝ) * (a : ℝ))) / ((b : ℝ) * (b : ℝ))) / (scaleS : ℝ) =
          ((tLo : ℝ) / (scaleS : ℝ)) * (u * u) := by simp [u]; ring
      have h3 : ((tLo : ℝ) / (scaleS : ℝ)) * (u * u) ≤ u ^ (2 * j + 1) * (u * u) :=
        mul_le_mul_of_nonneg_right htLo (mul_nonneg hu_nn hu_nn)
      exact le_trans (div_le_div_of_nonneg_right h1 hS.le)
        (h2 ▸ (show u ^ (2 * j + 1) * (u * u) = u ^ (2 * (j + 1) + 1) by ring) ▸ h3)
    have htHi1 : u ^ (2 * (j + 1) + 1) ≤ ((hstarCeilDiv (tHi * (a * a)) (b * b) : ℕ) : ℝ) / (scaleS : ℝ) := by
      have h1 : ((tHi : ℝ) * ((a : ℝ) * (a : ℝ))) / ((b : ℝ) * (b : ℝ)) ≤
          ((hstarCeilDiv (tHi * (a * a)) (b * b) : ℕ) : ℝ) := by
        simpa [Nat.cast_mul] using real_le_ceilDiv (a := tHi * (a * a)) hb2_pos
      have h3 : u ^ (2 * j + 1) * (u * u) ≤ ((tHi : ℝ) / (scaleS : ℝ)) * (u * u) :=
        mul_le_mul_of_nonneg_right htHi (mul_nonneg hu_nn hu_nn)
      have h4 : ((tHi : ℝ) / (scaleS : ℝ)) * (u * u) =
          (((tHi * (a * a)) : ℝ) / ((b : ℝ) * (b : ℝ))) / (scaleS : ℝ) := by simp [u]; ring
      exact le_trans ((show u ^ (2 * (j + 1) + 1) = u ^ (2 * j + 1) * (u * u) by ring) ▸ h3)
        (h4 ▸ div_le_div_of_nonneg_right h1 hS.le)
    have hrec := ih (j + 1) ((tLo * (a * a)) / (b * b)) (hstarCeilDiv (tHi * (a * a)) (b * b))
      (sLo + (2 * tLo) / d) (sHi + hstarCeilDiv (2 * tHi) d) htLo1 htHi1
    dsimp only [logLoop2] at hrec ⊢
    rw [Finset.sum_range_succ']
    have hshift : ∑ x ∈ Finset.range n, (2 : ℝ) * (1 / (2 * ((j + (x + 1) : ℕ) : ℝ) + 1)) *
        u ^ (2 * (j + (x + 1)) + 1) =
        ∑ m ∈ Finset.range n, (2 : ℝ) * (1 / (2 * (((j + 1 + m : ℕ) : ℝ)) + 1)) *
          u ^ (2 * (j + 1 + m) + 1) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show j + (m + 1) = j + 1 + m by omega]
    rw [hshift]; simp only [Nat.add_zero]
    have hdj : 2 * j + 1 = d := rfl
    rw [hdj] at hterm_lo hterm_hi ⊢; push_cast at hrec ⊢
    set res := logLoop2 n (j + 1) (a * a) (b * b) (tLo * (a * a) / (b * b))
      (hstarCeilDiv (tHi * (a * a)) (b * b)) (sLo + 2 * tLo / d) (sHi + hstarCeilDiv (2 * tHi) d)
    have hs1 : ((res.1 : ℝ) - (sLo : ℝ)) / (scaleS : ℝ) =
        ((res.1 : ℝ) - ((sLo : ℝ) + ((2 * tLo / d : ℕ) : ℝ))) / (scaleS : ℝ) +
          ((2 * tLo / d : ℕ) : ℝ) / (scaleS : ℝ) := by ring
    have hs2 : ((res.2 : ℝ) - (sHi : ℝ)) / (scaleS : ℝ) =
        ((res.2 : ℝ) - ((sHi : ℝ) + ((hstarCeilDiv (2 * tHi) d : ℕ) : ℝ))) / (scaleS : ℝ) +
          ((hstarCeilDiv (2 * tHi) d : ℕ) : ℝ) / (scaleS : ℝ) := by ring
    rw [hs1, hs2]; exact ⟨add_le_add hrec.1 hterm_lo, add_le_add hrec.2 hterm_hi⟩

lemma logRatIv_sound {num den k : ℕ} (hden : 0 < den)
    (hlo : den * 2 ^ k ≤ num) (hhi : num < den * 2 ^ (k + 1)) :
    ((logRatIv num den k).1 : ℝ) / (scaleS : ℝ) ≤ Real.log ((num : ℝ) / (den : ℝ)) ∧
      Real.log ((num : ℝ) / (den : ℝ)) ≤ ((logRatIv num den k).2 : ℝ) / (scaleS : ℝ) := by
  set p2 : ℕ := den * 2 ^ k
  set a : ℕ := num - p2
  set b : ℕ := num + p2
  have hp2_pos : 0 < p2 := Nat.mul_pos hden (pow_pos (by norm_num) k)
  have hb_pos : 0 < b := by omega
  have h2p2 : num < 2 * p2 := by
    have : den * 2 ^ (k + 1) = 2 * p2 := by dsimp [p2]; rw [pow_succ']; ring
    omega
  have ha_lt_b3 : 3 * a < b := by have hp2_le : p2 ≤ num := hlo; omega
  set u : ℝ := (a : ℝ) / (b : ℝ)
  have hu_nn : 0 ≤ u := by positivity
  have hu_lt_third : u < (1 / 3 : ℝ) := by
    rw [div_lt_div_iff₀ (by exact_mod_cast hb_pos) (by norm_num)]; exact_mod_cast (by omega : a * 3 < 1 * b)
  have hu_abs : |u| < 1 := by rw [abs_of_nonneg hu_nn]; linarith
  have hlog_x : Real.log ((num : ℝ) / (den : ℝ)) =
      (k : ℝ) * Real.log 2 + Real.log ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) := by
    have hden_pos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
    have hnum_pos : (0 : ℝ) < (num : ℝ) := by exact_mod_cast lt_of_lt_of_le hp2_pos hlo
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [show (num : ℝ) / (den : ℝ) = (2 : ℝ) ^ k * ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) by field_simp,
      Real.log_mul h2k_pos.ne' (div_pos hnum_pos (mul_pos hden_pos h2k_pos)).ne', Real.log_pow]
  have hlog_y : Real.log ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) =
      Real.log (1 + u) - Real.log (1 - u) := by
    have hb_real : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    have ha_real : (a : ℝ) = (num : ℝ) - (p2 : ℝ) := Nat.cast_sub hlo
    have hb_eq : (b : ℝ) = (num : ℝ) + (p2 : ℝ) := by push_cast [b]; rfl
    have h1pu : 1 + u = (2 * (num : ℝ)) / (b : ℝ) := by
      simp only [u]; rw [one_add_div hb_real.ne', ha_real, hb_eq]; ring
    have h1mu : 1 - u = (2 * (p2 : ℝ)) / (b : ℝ) := by
      simp only [u]; rw [one_sub_div hb_real.ne', ha_real, hb_eq]; ring
    have hnum_pos : (0 : ℝ) < (num : ℝ) := by exact_mod_cast lt_of_lt_of_le hp2_pos hlo
    have hp2_real : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2_pos
    rw [← Real.log_div (by rw [h1pu]; positivity) (by rw [h1mu]; positivity), h1pu, h1mu]
    have hp2_eq : (p2 : ℝ) = (den : ℝ) * (2 : ℝ) ^ k := by push_cast [p2]; rfl
    rw [← hp2_eq]; congr 1; field_simp
  have hhasSum := hlog_y ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  set f : ℕ → ℝ := fun j => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)
  have hf_nn : ∀ j : ℕ, 0 ≤ f j := fun j => by positivity
  have hsum_le : ∑ j ∈ Finset.range 6, f j ≤ Real.log ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) :=
    sum_le_hasSum (Finset.range 6) (fun j _ => hf_nn j) hhasSum
  have hsum_ge : Real.log ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) ≤
      (∑ j ∈ Finset.range 6, f j) + (logTailHi : ℝ) / (scaleS : ℝ) := by
    have hsplit := hhasSum.summable.sum_add_tsum_nat_add 6
    have hu2_lt1 : u ^ 2 < 1 / 9 := by
      have : u ^ 2 < (1 / 3 : ℝ) ^ 2 := sq_lt_sq' (by linarith) hu_lt_third
      linarith
    have hgeom : HasSum (fun m : ℕ => (u ^ 2) ^ m) (1 - u ^ 2)⁻¹ :=
      hasSum_geometric_of_lt_one (sq_nonneg u) (by linarith)
    have htail_le : ∀ m : ℕ, f (m + 6) ≤ ((2 / 13 : ℝ) * u ^ 13) * (u ^ 2) ^ m := by
      intro m
      have hden_le : (1 : ℝ) / (2 * ((m + 6 : ℕ) : ℝ) + 1) ≤ 1 / 13 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
      dsimp only [f]; rw [show u ^ (2 * (m + 6) + 1) = u ^ 13 * (u ^ 2) ^ m by ring]
      linarith [show (2 : ℝ) * (1 / (2 * ((m + 6 : ℕ) : ℝ) + 1)) * (u ^ 13 * (u ^ 2) ^ m) ≤
        (2 : ℝ) * (1 / 13) * (u ^ 13 * (u ^ 2) ^ m) by gcongr]
    have htsum_bound : ∑' m : ℕ, f (m + 6) ≤ ((2 / 13 : ℝ) * u ^ 13) * (1 - u ^ 2)⁻¹ := by
      have hsum_m := hhasSum.summable.comp_injective (add_left_injective 6)
      have h1 := Summable.tsum_le_tsum htail_le hsum_m (hgeom.summable.mul_left _)
      rwa [tsum_mul_left, hgeom.tsum_eq] at h1
    have hnum_tail : ((2 / 13 : ℝ) * u ^ 13) * (1 - u ^ 2)⁻¹ ≤ (logTailHi : ℝ) / (scaleS : ℝ) := by
      have hu13 : u ^ 13 ≤ (1 / 3 : ℝ) ^ 13 := pow_le_pow_left₀ hu_nn hu_lt_third.le 13
      have hinv : (1 - u ^ 2)⁻¹ ≤ (9 / 8 : ℝ) := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have hu13_nn : 0 ≤ (2 / 13 : ℝ) * u ^ 13 := mul_nonneg (by norm_num) (pow_nonneg hu_nn 13)
      have hmul : ((2 / 13 : ℝ) * u ^ 13) * (1 - u ^ 2)⁻¹ ≤ ((2 / 13 : ℝ) * (1 / 3 : ℝ) ^ 13) * (9 / 8 : ℝ) :=
        mul_le_mul (by gcongr) hinv (inv_nonneg.mpr (by linarith)) (by positivity)
      exact hmul.trans (by unfold logTailHi scaleS; norm_num)
    linarith [hsplit, hhasSum.tsum_eq]
  have htLo0 : (((scaleS * a) / b : ℕ) : ℝ) / (scaleS : ℝ) ≤ u ^ (2 * 0 + 1) := by
    have h1 := floorDiv_le_real (a := scaleS * a) hb_pos; rw [Nat.cast_mul] at h1
    have h2 : ((scaleS : ℝ) * (a : ℝ) / (b : ℝ)) / (scaleS : ℝ) = u := by simp [u]; field_simp [scaleS_pos.ne']
    exact (div_le_div_of_nonneg_right h1 scaleS_pos.le).trans (by simp [h2])
  have htHi0 : u ^ (2 * 0 + 1) ≤ ((hstarCeilDiv (scaleS * a) b : ℕ) : ℝ) / (scaleS : ℝ) := by
    have h1 := real_le_ceilDiv (a := scaleS * a) hb_pos; rw [Nat.cast_mul] at h1
    have h2 : u = ((scaleS : ℝ) * (a : ℝ) / (b : ℝ)) / (scaleS : ℝ) := by simp [u]; field_simp [scaleS_pos.ne']
    exact (by simp [h2] : u ^ (2 * 0 + 1) = _).le.trans (div_le_div_of_nonneg_right h1 scaleS_pos.le)
  have hloop := logLoop2_sound hb_pos 6 0 ((scaleS * a) / b) (hstarCeilDiv (scaleS * a) b) 0 0 htLo0 htHi0
  simp only [Nat.zero_add, Nat.cast_zero, sub_zero] at hloop
  have hlog2_lo : (log2Lo : ℝ) / (scaleS : ℝ) ≤ Real.log 2 := by unfold log2Lo scaleS; linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 ≤ (log2Hi : ℝ) / (scaleS : ℝ) := by unfold log2Hi scaleS; linarith [Real.log_two_lt_d9]
  dsimp only [logRatIv]
  change (↑(k * log2Lo + (logLoop2 6 0 (a * a) (b * b) ((scaleS * a) / b) (hstarCeilDiv (scaleS * a) b) 0 0).1) : ℝ) / ↑scaleS ≤ _ ∧
    _ ≤ (↑(k * log2Hi + (logLoop2 6 0 (a * a) (b * b) ((scaleS * a) / b) (hstarCeilDiv (scaleS * a) b) 0 0).2 + logTailHi) : ℝ) / ↑scaleS
  push_cast; rw [add_div, add_div, add_div, mul_div_assoc, mul_div_assoc]
  constructor
  · have := mul_le_mul_of_nonneg_left hlog2_lo (Nat.cast_nonneg k); linarith [hlog_x, hloop.1, hsum_le]
  · have := mul_le_mul_of_nonneg_left hlog2_hi (Nat.cast_nonneg k); linarith [hlog_x, hloop.2, hsum_ge]

private lemma log2Aux_bounds : ∀ (k n : ℕ), 1 ≤ n → n < 2 ^ (k + 1) →
    2 ^ log2Aux n k ≤ n ∧ n < 2 ^ (log2Aux n k + 1)
  | 0, n, h1, h2 => by simp [log2Aux]; omega
  | k + 1, n, h1, h2 => by
    dsimp only [log2Aux]; split_ifs with hle
    · exact ⟨hle, h2⟩
    · exact log2Aux_bounds k n h1 (by omega)

lemma logNatIv_sound {n : ℕ} (hn2 : 2 ≤ n) (hn8000 : n ≤ 8000) :
    ((logNatIv n).1 : ℝ) / (scaleS : ℝ) ≤ Real.log (n : ℝ) ∧
      Real.log (n : ℝ) ≤ ((logNatIv n).2 : ℝ) / (scaleS : ℝ) := by
  have hb := log2Aux_bounds 13 n (by omega) (by omega)
  change 2 ^ log2Pow n ≤ n ∧ n < 2 ^ (log2Pow n + 1) at hb
  simpa [logNatIv] using logRatIv_sound (num := n) (den := 1) (k := log2Pow n)
    Nat.one_pos (by simpa using hb.1) (by simpa using hb.2)

private lemma prime_of_not_hasSmallFactor {n : ℕ} (hn2 : 2 ≤ n) (hn8000 : n ≤ 8000)
    (hsf : hasSmallFactor n = false) : n.Prime := by
  by_contra hnp
  have hm_pr := Nat.minFac_prime (by omega : n ≠ 1)
  have hm_lt : n.minFac < n := lt_of_le_of_ne (Nat.minFac_le (by omega)) (fun h => hnp (h ▸ hm_pr))
  have hm_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hall := List.all_eq_true.mp small90_check n.minFac (List.mem_range.mpr (by nlinarith))
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hall
  have hm_mem : n.minFac ∈ smallPrimes89 := by
    rcases hall with (hm | h2) | ⟨d, hdm, hdl, hmod⟩
    · exact hm
    · exact absurd hm_pr.two_le (by omega)
    · have hd2 : 2 ≤ d := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hdm
        rcases hdm with rfl | rfl | rfl | rfl <;> omega
      rcases hm_pr.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with rfl | rfl <;> omega
  have hbad := List.any_eq_false.mp hsf n.minFac hm_mem
  simp [hm_lt, Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n)] at hbad

private lemma hasSmallFactor_not_prime {n : ℕ} (hsf : hasSmallFactor n = true) : ¬ n.Prime := by
  intro hpr
  rcases List.any_eq_true.mp hsf with ⟨d, hd_mem, hd_prop⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd_prop
  have hd2 := smallPrimes89_ge2 d hd_mem
  rcases hpr.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd_prop.2) with rfl | rfl <;> omega

private lemma checkGapCount_sound : ∀ (c lo : ℕ), checkGapCount lo c = true →
    ∀ n : ℕ, lo ≤ n → n < lo + c → n = 2 ∨ n ∈ q0List ∨ ¬ n.Prime := by
  intro c
  induction c with
  | zero => intro lo _ n h1 h2; omega
  | succ c ih =>
    intro lo h n h1 h2; simp only [checkGapCount, Bool.and_eq_true] at h
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h.1 with (hsf | rfl) | ⟨_, hq⟩
      · exact Or.inr (Or.inr (hasSmallFactor_not_prime hsf))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hq)
    · exact ih (lo + 1) h.2 n (by omega) (by omega)

private lemma checkGapsLoop_sound : ∀ (ps : List ℕ) (prev : ℕ),
    1 ≤ prev → (checkGapsLoop prev ps).1 = true →
    prev ≤ (checkGapsLoop prev ps).2 ∧ ps.Pairwise (· < ·) ∧
    (∀ p ∈ ps, prev < p ∧ p ≤ (checkGapsLoop prev ps).2 ∧ p ≤ 8000 ∧ p.Prime ∧ p ∉ q0List) ∧
    (∀ n : ℕ, prev < n → n ≤ (checkGapsLoop prev ps).2 → n ∉ ps → n = 2 ∨ n ∈ q0List ∨ ¬ n.Prime) := by
  intro ps; induction ps with
  | nil =>
    intro prev _ _; simp only [checkGapsLoop]
    exact ⟨le_rfl, List.Pairwise.nil, (fun _ h => by cases h), fun n h1 h2 _ => by omega⟩
  | cons p ps ih =>
    intro prev hprev h; simp only [checkGapsLoop] at h
    split_ifs at h with hcond
    · have hres : checkGapsLoop prev (p :: ps) = checkGapsLoop p ps := by
        simp only [checkGapsLoop, hcond, ↓reduceIte]
      rw [hres]; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨⟨⟨hp_gt, hp_le⟩, hsf⟩, hnq0⟩, hgap⟩
      have hp_pr := prime_of_not_hasSmallFactor (by omega) hp_le hsf
      have hp_nq0 : p ∉ q0List := fun hm => by
        have hp227 := (Q0_100_mem_props p (q0_eq_toFinset ▸ List.mem_toFinset.mpr hm)).2.2
        simp [hp227, hm] at hnq0
      have hrec := ih p (by omega) h
      refine ⟨(hp_gt.le).trans hrec.1, List.pairwise_cons.mpr ⟨fun q hq => (hrec.2.2.1 q hq).1, hrec.2.1⟩,
        fun q hq => ?_, fun n hn1 hn2 hn_mem => ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hp_gt, hrec.1, hp_le, hp_pr, hp_nq0⟩
        · exact ⟨hp_gt.trans (hrec.2.2.1 q hq).1, (hrec.2.2.1 q hq).2⟩
      · simp only [List.mem_cons, not_or] at hn_mem
        rcases lt_or_gt_of_ne hn_mem.1 with hnp | hpn
        · exact checkGapCount_sound (p - prev - 1) (prev + 1) hgap n (by omega) (by omega)
        · exact hrec.2.2.2 n hpn hn2 hn_mem.2

private lemma checkGapsChunks_sound : ∀ (cs : List (List ℕ)) (prev : ℕ),
    1 ≤ prev → checkGapsChunks prev cs = true →
    cs.flatten.Pairwise (· < ·) ∧
    (∀ p ∈ cs.flatten, prev < p ∧ p ≤ 8000 ∧ p.Prime ∧ p ∉ q0List) ∧
    (∀ n : ℕ, prev < n → n ≤ 8000 → n ∉ cs.flatten → n = 2 ∨ n ∈ q0List ∨ ¬ n.Prime) := by
  intro cs; induction cs with
  | nil =>
    intro prev _ h; simp only [checkGapsChunks] at h
    exact ⟨List.Pairwise.nil, (fun _ h1 => by cases h1), fun n h1 h2 _ =>
      checkGapCount_sound (8000 - prev) (prev + 1) h n (by omega) (by omega)⟩
  | cons c cs ih =>
    intro prev hprev h; simp only [checkGapsChunks, Bool.and_eq_true] at h
    have hloop := checkGapsLoop_sound c prev hprev h.1
    have hrec := ih (checkGapsLoop prev c).2 (hprev.trans hloop.1) h.2
    refine ⟨?_, fun p hp => ?_, fun n h1 h2 hmem => ?_⟩
    · simp only [List.flatten_cons]
      exact List.pairwise_append.mpr ⟨hloop.2.1, hrec.1, fun a ha b hb =>
        lt_of_le_of_lt (hloop.2.2.1 a ha).2.1 (hrec.2.1 b hb).1⟩
    · simp only [List.flatten_cons, List.mem_append] at hp
      exact hp.elim (fun h => ⟨(hloop.2.2.1 p h).1, (hloop.2.2.1 p h).2.2⟩)
        (fun h => ⟨lt_of_le_of_lt hloop.1 (hrec.2.1 p h).1, (hrec.2.1 p h).2⟩)
    · simp only [List.flatten_cons, List.mem_append, not_or] at hmem
      exact (le_or_gt n (checkGapsLoop prev c).2).elim
        (fun hn => hloop.2.2.2 n h1 hn hmem.1) (fun hn => hrec.2.2 n hn h2 hmem.2)

lemma s0List_props :
    s0List.Pairwise (· < ·) ∧ (∀ p ∈ s0List, 3 ≤ p ∧ p ≤ 8000 ∧ p.Prime ∧ p ∉ Q0_100) ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ 8000 → p ∉ Q0_100 → p ∈ s0List) := by
  have hs := checkGapsChunks_sound s0Chunks 2 (by norm_num) gaps_ok
  refine ⟨hs.1, fun p hp => ?_, fun p hp_pr hp3 hp8000 hpQ0 => ?_⟩
  · have h1 := hs.2.1 p hp
    exact ⟨h1.1, h1.2.1, h1.2.2.1, by rw [q0_eq_toFinset, List.mem_toFinset]; exact h1.2.2.2⟩
  · by_contra hmem
    rcases hs.2.2 p (by omega) hp8000 hmem with rfl | hq | hnp
    · omega
    · exact hpQ0 (q0_eq_toFinset ▸ List.mem_toFinset.mpr hq)
    · exact hnp hp_pr

def listProd (qs : List ℕ) : ℝ := (qs.map (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2))).prod
lemma listProd_append (as bs : List ℕ) : listProd (as ++ bs) = listProd as * listProd bs := by simp [listProd]
lemma listProd_pos {qs : List ℕ} (hqs : ∀ p ∈ qs, 3 ≤ p) : 0 < listProd qs := by
  induction qs with
  | nil => simp [listProd]
  | cons p qs ih =>
    simp only [listProd, List.map_cons, List.prod_cons]
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqs p List.mem_cons_self
    exact mul_pos (div_pos (by linarith) (by linarith)) (ih fun q hq => hqs q (List.mem_cons_of_mem p hq))
lemma listProd_eq_finset_prod {qs : List ℕ} (hnodup : qs.Nodup) :
    listProd qs = ∏ p ∈ qs.toFinset, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [listProd, ← List.prod_toFinset _ hnodup]

def ScanInv (pref : List ℕ) (st : ScanState) : Prop :=
  0 < st.prodLo ∧ (st.prodLo : ℝ) / (scaleS : ℝ) ≤ listProd pref ∧
  listProd pref ≤ (st.prodHi : ℝ) / (scaleS : ℝ) ∧
  (∀ x ∈ pref, Real.log (x : ℝ) / listProd (pref.filter (fun q => decide (q < x))) ≤
    (st.maxInvHi : ℝ) / (scaleS : ℝ)) ∧
  (st.ok = true → ∀ x ∈ pref, ∀ y ∈ pref, x ≤ y →
    (Real.log (x : ℝ) / listProd (pref.filter (fun q => decide (q < x)))) *
      (listProd (pref.filter (fun q => decide (q ≤ y))) / Real.log (y : ℝ)) ≤ (101 : ℝ) / 100)

private lemma scanStep_sound {pref : List ℕ} {p : ℕ} {st : ScanState}
    (hpref_3 : ∀ q ∈ pref, 3 ≤ q) (hpref_lt : ∀ q ∈ pref, q < p)
    (hp3 : 3 ≤ p) (hp8000 : p ≤ 8000) (hinv : ScanInv pref st) :
    ScanInv (pref ++ [p]) (scanStep st p) := by
  rcases hinv with ⟨hprodLo_pos, hlo, hhi, hmax, hok⟩
  set ln := logNatIv p
  set st' := scanStep st p
  have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
  have hlog_bd := logNatIv_sound (by omega) hp8000
  have hpm2_pos : 0 < p - 2 := by omega
  have hp_sub_cast : (((p - 1 : ℕ) : ℝ) / ((p - 2 : ℕ) : ℝ)) = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)]; push_cast; rfl
  have hpref_pos : 0 < listProd pref := listProd_pos hpref_3
  have hp_rat_pos : (0 : ℝ) < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    exact div_pos (by linarith) (by linarith)
  have hprodLo'_pos : 0 < st'.prodLo := by
    dsimp [st', scanStep]
    have : st.prodLo ≤ (st.prodLo * (p - 1)) / (p - 2) := by
      rw [Nat.le_div_iff_mul_le hpm2_pos]; exact Nat.mul_le_mul_left st.prodLo (by omega)
    omega
  have hlp_eq : listProd [p] = ((p - 1 : ℕ) : ℝ) / ((p - 2 : ℕ) : ℝ) := by simp [listProd, hp_sub_cast]
  have hlo' : (st'.prodLo : ℝ) / (scaleS : ℝ) ≤ listProd (pref ++ [p]) := by
    dsimp [st', scanStep]; rw [listProd_append, hlp_eq]
    have h1 : (((st.prodLo * (p - 1)) / (p - 2) : ℕ) : ℝ) ≤
        ((st.prodLo : ℝ) * ((p - 1 : ℕ) : ℝ)) / ((p - 2 : ℕ) : ℝ) := by
      simpa [Nat.cast_mul] using floorDiv_le_real (a := st.prodLo * (p - 1)) hpm2_pos
    have h2 : ((st.prodLo : ℝ) * ((p - 1 : ℕ) : ℝ)) / ((p - 2 : ℕ) : ℝ) / (scaleS : ℝ) =
        ((st.prodLo : ℝ) / (scaleS : ℝ)) * (((p - 1 : ℕ) : ℝ) / ((p - 2 : ℕ) : ℝ)) := by ring
    exact le_trans (div_le_div_of_nonneg_right h1 hS.le)
      (h2 ▸ mul_le_mul_of_nonneg_right hlo (hp_sub_cast ▸ hp_rat_pos.le))
  have hhi' : listProd (pref ++ [p]) ≤ (st'.prodHi : ℝ) / (scaleS : ℝ) := by
    dsimp [st', scanStep]; rw [listProd_append, hlp_eq]
    have h1 : ((st.prodHi : ℝ) * ((p - 1 : ℕ) : ℝ)) / ((p - 2 : ℕ) : ℝ) ≤
        ((hstarCeilDiv (st.prodHi * (p - 1)) (p - 2) : ℕ) : ℝ) := by
      simpa [Nat.cast_mul] using real_le_ceilDiv (a := st.prodHi * (p - 1)) hpm2_pos
    have h2 : listProd pref * (((p - 1 : ℕ) : ℝ) / ((p - 2 : ℕ) : ℝ)) ≤
        ((st.prodHi : ℝ) * ((p - 1 : ℕ) : ℝ)) / ((p - 2 : ℕ) : ℝ) / (scaleS : ℝ) :=
      (mul_le_mul_of_nonneg_right hhi (hp_sub_cast ▸ hp_rat_pos.le)).trans_eq (by ring)
    exact h2.trans (div_le_div_of_nonneg_right h1 hS.le)
  have hmax' : ∀ x ∈ pref ++ [p],
      Real.log (x : ℝ) / listProd ((pref ++ [p]).filter (fun q => decide (q < x))) ≤
        (st'.maxInvHi : ℝ) / (scaleS : ℝ) := by
    intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hxp
    · rw [show (pref ++ [p]).filter (fun q => decide (q < x)) = pref.filter (fun q => decide (q < x)) by
          simp [List.filter_append, (hpref_lt x hx).not_gt]]
      exact (hmax x hx).trans (div_le_div_of_nonneg_right
        (by exact_mod_cast (le_max_left _ _ : st.maxInvHi ≤ st'.maxInvHi)) hS.le)
    · subst x
      rw [show (pref ++ [p]).filter (fun q => decide (q < p)) = pref by
          rw [List.filter_append, List.filter_eq_self.mpr fun q hq => decide_eq_true (hpref_lt q hq)]; simp]
      have h1 : Real.log (p : ℝ) / listProd pref ≤
          ((ln.2 : ℝ) / (scaleS : ℝ)) / ((st.prodLo : ℝ) / (scaleS : ℝ)) :=
        (div_le_div_of_nonneg_right hlog_bd.2 hpref_pos.le).trans
          (div_le_div_of_nonneg_left (by positivity) (div_pos (by exact_mod_cast hprodLo_pos) hS) hlo)
      have h2 : ((ln.2 : ℝ) / (scaleS : ℝ)) / ((st.prodLo : ℝ) / (scaleS : ℝ)) =
          ((ln.2 : ℝ) * (scaleS : ℝ)) / (st.prodLo : ℝ) / (scaleS : ℝ) := by
        field_simp [hS.ne', (by exact_mod_cast hprodLo_pos : (0 : ℝ) < st.prodLo).ne']
      have h3 : ((ln.2 : ℝ) * (scaleS : ℝ)) / (st.prodLo : ℝ) ≤
          ((hstarCeilDiv (ln.2 * scaleS) st.prodLo : ℕ) : ℝ) := by
        simpa [Nat.cast_mul] using real_le_ceilDiv (a := ln.2 * scaleS) hprodLo_pos
      exact h1.trans (h2 ▸ (div_le_div_of_nonneg_right h3 hS.le).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast (le_max_right _ _ :
          hstarCeilDiv (ln.2 * scaleS) st.prodLo ≤ st'.maxInvHi)) hS.le))
  refine ⟨hprodLo'_pos, hlo', hhi', hmax', fun hst'_ok x hx y hy hxy => ?_⟩
  have hok_conj : st.ok = true ∧ 100 * st'.maxInvHi * st'.prodHi ≤ 101 * scaleS * ln.1 ∧ 0 < ln.1 := by
    dsimp [st', scanStep, ln] at hst'_ok ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hst'_ok
    exact ⟨hst'_ok.1.1, hst'_ok.1.2, hst'_ok.2⟩
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | hyp
  · have hx_lt : x < p := lt_of_le_of_lt hxy (hpref_lt y hy)
    have hx_pref : x ∈ pref := (List.mem_append.mp hx).elim id
      (fun h => absurd ((List.mem_singleton.mp h) ▸ hx_lt) (lt_irrefl p))
    rw [show (pref ++ [p]).filter (fun q => decide (q < x)) = pref.filter (fun q => decide (q < x)) by
        simp [List.filter_append, hx_lt.not_gt],
      show (pref ++ [p]).filter (fun q => decide (q ≤ y)) = pref.filter (fun q => decide (q ≤ y)) by
        simp [List.filter_append, (hpref_lt y hy).not_ge]]
    exact hok hok_conj.1 x hx_pref y hy hxy
  · subst y
    have hfl : (pref ++ [p]).filter (fun q => decide (q ≤ p)) = pref ++ [p] :=
      List.filter_eq_self.mpr fun q hq => by
        simp only [List.mem_append, List.mem_singleton] at hq
        exact decide_eq_true (hq.elim (fun h => (hpref_lt q h).le) (fun h => h ▸ le_rfl))
    rw [hfl]
    have hlnLo_pos : (0 : ℝ) < (ln.1 : ℝ) / (scaleS : ℝ) := div_pos (by exact_mod_cast hok_conj.2.2) hS
    have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
    have hprod_le_div : listProd (pref ++ [p]) / Real.log (p : ℝ) ≤
        ((st'.prodHi : ℝ) / (scaleS : ℝ)) / ((ln.1 : ℝ) / (scaleS : ℝ)) :=
      (div_le_div_of_nonneg_right hhi' hlogp_pos.le).trans
        (div_le_div_of_nonneg_left (by positivity) hlnLo_pos hlog_bd.1)
    have hmul_bd := mul_le_mul (hmax' x hx) hprod_le_div
      (div_nonneg (listProd_pos fun q hq => by
        simp only [List.mem_append, List.mem_singleton] at hq
        exact hq.elim (hpref_3 q) (fun h => h ▸ hp3)).le hlogp_pos.le) (by positivity)
    have hrat_eq : ((st'.maxInvHi : ℝ) / (scaleS : ℝ)) *
        (((st'.prodHi : ℝ) / (scaleS : ℝ)) / ((ln.1 : ℝ) / (scaleS : ℝ))) =
        ((st'.maxInvHi : ℝ) * (st'.prodHi : ℝ)) / ((scaleS : ℝ) * (ln.1 : ℝ)) := by
      field_simp [hS.ne', (by exact_mod_cast hok_conj.2.2 : (0 : ℝ) < ln.1).ne']
    have hrat_le : ((st'.maxInvHi : ℝ) * (st'.prodHi : ℝ)) / ((scaleS : ℝ) * (ln.1 : ℝ)) ≤
        (101 : ℝ) / 100 := by
      rw [div_le_div_iff₀ (mul_pos hS (by exact_mod_cast hok_conj.2.2)) (by norm_num)]
      exact_mod_cast (by nlinarith [hok_conj.2.1] : st'.maxInvHi * st'.prodHi * 100 ≤ 101 * (scaleS * ln.1))
    exact hmul_bd.trans (hrat_eq ▸ hrat_le)

private lemma scanList_sound : ∀ (suf pref : List ℕ) (st : ScanState),
    (pref ++ suf).Pairwise (· < ·) → (∀ q ∈ pref ++ suf, 3 ≤ q ∧ q ≤ 8000) →
    ScanInv pref st → ScanInv (pref ++ suf) (scanList suf st) := by
  intro suf; induction suf with
  | nil => intro pref st _ _ hinv; simpa [scanList] using hinv
  | cons p suf ih =>
    intro pref st hpw hbd hinv
    have hpref_lt : ∀ q ∈ pref, q < p := fun q hq =>
      (List.pairwise_append.mp hpw).2.2 q hq p List.mem_cons_self
    have hp_mem : p ∈ pref ++ (p :: suf) := List.mem_append_right pref List.mem_cons_self
    have hinv1 := scanStep_sound (fun q hq => (hbd q (List.mem_append_left _ hq)).1) hpref_lt
      (hbd p hp_mem).1 (hbd p hp_mem).2 hinv
    have hrew : (pref ++ [p]) ++ suf = pref ++ (p :: suf) := by simp
    simpa [scanList, hrew] using ih (pref ++ [p]) (scanStep st p) (hrew ▸ hpw) (hrew ▸ hbd) hinv1

private def chainLast (st : ScanState) : List (List ℕ × ScanState) → ScanState
  | [] => st
  | (_, stNext) :: rest => chainLast stNext rest

private lemma checkScanChain_sound : ∀ (chain : List (List ℕ × ScanState)) (st : ScanState),
    checkScanChain st chain = true →
    scanList (chain.map Prod.fst).flatten st = chainLast st chain ∧ (chainLast st chain).ok = true := by
  intro chain; induction chain with
  | nil => intro st h; simpa [checkScanChain, scanList, chainLast] using h
  | cons hd tl ih =>
    intro st h; rcases hd with ⟨ps, stNext⟩
    simp only [checkScanChain, Bool.and_eq_true, beq_iff_eq] at h
    have hrec := ih stNext h.2
    simp only [List.map_cons, List.flatten_cons, scanList, List.foldl_append, chainLast]
    change scanList (tl.map Prod.fst).flatten (scanList ps st) = chainLast stNext tl ∧
      (chainLast stNext tl).ok = true
    rw [h.1]; exact hrec

lemma s0List_scanInv : ScanInv s0List stFinal ∧ stFinal.ok = true := by
  let st0 : ScanState := ⟨scaleS, scaleS, 0, true⟩
  have hinv0 : ScanInv [] st0 := ⟨by dsimp [st0]; unfold scaleS; positivity,
    by simp [st0, listProd, scaleS_pos.ne'], by simp [st0, listProd, scaleS_pos.ne'],
    (fun _ h => by cases h), fun _ _ hx _ _ _ => by cases hx⟩
  have hs := s0List_props
  have hinv := scanList_sound s0List [] st0 (by simpa using hs.1)
    (fun q hq => ⟨(hs.2.1 q hq).1, (hs.2.1 q hq).2.1⟩) hinv0
  simp only [List.nil_append] at hinv
  have hc := checkScanChain_sound s0Chain st0 scan_chain_ok
  change scanList s0List st0 = stFinal ∧ stFinal.ok = true at hc
  exact ⟨hc.1 ▸ hinv, hc.2⟩

end

end BuchstabSwitching
