import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstDefs
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Binary Proof-by-Reflection Arithmetic and `sqrt` Soundness

Provides division-free `Dyadic` soundness lemmas (`<<<`/`>>>` only), single-multiply
square-root checkers (`checkSqrtLb`, `checkSqrtUb`), and Q64 multiplication helpers.
-/

namespace BuchstabSwitching.SieveInst

section

/-! ## 1. `Dyadic` Bitshift, Comparison, Arithmetic, and `sqrt` Soundness -/

namespace Dyadic

private lemma two_pow_bias_pos : (0 : ℝ) < twoPowBias := twoPowBias_pos

private lemma two_pow_split {a b : ℕ} (h : a ≤ b) :
    (2 : ℝ) ^ b = (2 : ℝ) ^ a * (2 : ℝ) ^ (b - a) := by
  rw [← pow_add, Nat.add_sub_of_le h]

lemma q64Scale_real_eq : (q64Scale : ℝ) = (2 : ℝ) ^ 64 := by
  unfold q64Scale; rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat]

lemma zero_toReal : zero.toReal = 0 := by
  unfold zero toReal; simp only [Nat.cast_zero, zero_mul, zero_div]
lemma one_toReal : one.toReal = 1 := by
  unfold one toReal; simp only [Nat.cast_one, one_mul, twoPowBias_eq]; exact div_self (by positivity)
lemma ofNat_toReal (n : ℕ) : (ofNat n).toReal = (n : ℝ) := by
  unfold ofNat toReal; rw [twoPowBias_eq, mul_div_assoc, div_self (by positivity), mul_one]

lemma ofQ64_toReal (m : ℕ) : (ofQ64 m).toReal = (m : ℝ) / (q64Scale : ℝ) := by
  unfold ofQ64 toReal; rw [q64Scale_real_eq, twoPowBias_eq]; unfold dyadicBias
  rw [show (8192 : ℕ) = 8128 + 64 by norm_num, pow_add]
  field_simp

lemma ofQ48_toReal (m : ℕ) : (ofQ48 m).toReal = (m : ℝ) / (2 : ℝ) ^ 48 := by
  unfold ofQ48 toReal; rw [twoPowBias_eq]; unfold dyadicBias
  rw [show (8192 : ℕ) = 8144 + 48 by norm_num, pow_add]
  field_simp

lemma ceilShr_ge (n k : ℕ) : (n : ℝ) / (2 : ℝ) ^ k ≤ (ceilShr n k : ℝ) := by
  unfold ceilShr
  rw [div_le_iff₀ (by positivity), Nat.shiftRight_eq_div_pow]
  dsimp only
  split_ifs with heq
  · have hq : (n / 2 ^ k) * 2 ^ k = n := by
      rw [← Nat.shiftLeft_eq]; exact beq_iff_eq.mp heq
    exact_mod_cast hq.ge
  · have hmod := Nat.div_add_mod n (2 ^ k)
    have hlt := Nat.mod_lt n (pow_pos (by norm_num : (0 : ℕ) < 2) k)
    exact_mod_cast (by nlinarith : n ≤ (n / 2 ^ k + 1) * 2 ^ k)

lemma floorShr_le (n k : ℕ) : ((n >>> k : ℕ) : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ k := by
  rw [Nat.shiftRight_eq_div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast Nat.div_mul_le_self n (2 ^ k)

lemma shrLb_le (a : Dyadic) (k : ℕ) : (a.shrLb k).toReal ≤ a.toReal := by
  unfold shrLb toReal
  refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
  rw [pow_add]
  calc ((a.m >>> k : ℕ) : ℝ) * ((2 : ℝ) ^ a.e * (2 : ℝ) ^ k)
      ≤ ((a.m : ℝ) / (2 : ℝ) ^ k) * ((2 : ℝ) ^ a.e * (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right (floorShr_le a.m k) (by positivity)
    _ = (a.m : ℝ) * (2 : ℝ) ^ a.e := by field_simp [(by positivity : (2 : ℝ) ^ k ≠ 0)]

lemma le_shrUb (a : Dyadic) (k : ℕ) : a.toReal ≤ (a.shrUb k).toReal := by
  unfold shrUb toReal
  refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
  rw [pow_add]
  calc (a.m : ℝ) * (2 : ℝ) ^ a.e
      = ((a.m : ℝ) / (2 : ℝ) ^ k) * ((2 : ℝ) ^ a.e * (2 : ℝ) ^ k) := by
        field_simp [(by positivity : (2 : ℝ) ^ k ≠ 0)]
    _ ≤ (ceilShr a.m k : ℝ) * ((2 : ℝ) ^ a.e * (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right (ceilShr_ge a.m k) (by positivity)

lemma trimLb_le (a : Dyadic) (keep : ℕ := 80) : (a.trimLb keep).toReal ≤ a.toReal := by
  unfold trimLb
  split_ifs with h0
  · rw [zero_toReal]; exact a.toReal_nonneg
  · exact shrLb_le a (trimShift a.m keep)

lemma le_trimUb (a : Dyadic) (keep : ℕ := 80) : a.toReal ≤ (a.trimUb keep).toReal := by
  unfold trimUb
  split_ifs with h0
  · have hm : a.m = 0 := beq_iff_eq.mp h0
    rw [zero_toReal]; simp [toReal, hm]
  · exact le_shrUb a (trimShift a.m keep)

lemma mulPow2_toReal (a : Dyadic) (k : ℕ) :
    (a.mulPow2 k).toReal = a.toReal * (2 : ℝ) ^ k := by
  unfold mulPow2 toReal; rw [pow_add]; ring

lemma divPow2Lb_le (a : Dyadic) (k : ℕ) :
    (a.divPow2Lb k).toReal ≤ a.toReal / (2 : ℝ) ^ k := by
  unfold divPow2Lb toReal
  split_ifs with hk
  · refine le_of_eq ?_
    calc (a.m : ℝ) * (2 : ℝ) ^ (a.e - k) / twoPowBias
        = (a.m : ℝ) * ((2 : ℝ) ^ a.e / (2 : ℝ) ^ k) / twoPowBias := by
          rw [two_pow_split hk, mul_div_cancel_left₀ _ (by positivity)]
      _ = (a.m : ℝ) * (2 : ℝ) ^ a.e / twoPowBias / (2 : ℝ) ^ k := by ring
  · have hk' : a.e ≤ k := le_of_not_ge hk
    have hfl := floorShr_le a.m (k - a.e)
    rw [pow_zero, mul_one]
    calc ((a.m >>> (k - a.e) : ℕ) : ℝ) / twoPowBias
        ≤ ((a.m : ℝ) / (2 : ℝ) ^ (k - a.e)) / twoPowBias :=
          div_le_div_of_nonneg_right hfl two_pow_bias_pos.le
      _ = (a.m : ℝ) * (2 : ℝ) ^ a.e / twoPowBias / (2 : ℝ) ^ k := by
          rw [two_pow_split hk']; field_simp [(by positivity : (2 : ℝ) ^ a.e ≠ 0), (by positivity : (2 : ℝ) ^ (k - a.e) ≠ 0)]

lemma le_divPow2Ub (a : Dyadic) (k : ℕ) :
    a.toReal / (2 : ℝ) ^ k ≤ (a.divPow2Ub k).toReal := by
  unfold divPow2Ub toReal
  split_ifs with hk
  · refine le_of_eq ?_
    calc (a.m : ℝ) * (2 : ℝ) ^ a.e / twoPowBias / (2 : ℝ) ^ k
        = (a.m : ℝ) * ((2 : ℝ) ^ a.e / (2 : ℝ) ^ k) / twoPowBias := by ring
      _ = (a.m : ℝ) * (2 : ℝ) ^ (a.e - k) / twoPowBias := by
          rw [two_pow_split hk, mul_div_cancel_left₀ _ (by positivity)]
  · have hk' : a.e ≤ k := le_of_not_ge hk
    have hceil := ceilShr_ge a.m (k - a.e)
    rw [pow_zero, mul_one]
    calc (a.m : ℝ) * (2 : ℝ) ^ a.e / twoPowBias / (2 : ℝ) ^ k
        = ((a.m : ℝ) / (2 : ℝ) ^ (k - a.e)) / twoPowBias := by
          rw [two_pow_split hk']; field_simp [(by positivity : (2 : ℝ) ^ a.e ≠ 0), (by positivity : (2 : ℝ) ^ (k - a.e) ≠ 0)]
      _ ≤ (ceilShr a.m (k - a.e) : ℝ) / twoPowBias :=
          div_le_div_of_nonneg_right hceil two_pow_bias_pos.le

lemma ble_sound {a b : Dyadic} (h : a.ble b = true) : a.toReal ≤ b.toReal := by
  unfold ble at h
  split_ifs at h with ha0 hb0 he
  · have hm : a.m = 0 := beq_iff_eq.mp ha0
    simpa [toReal, hm] using b.toReal_nonneg
  · have hm : (a.m : ℝ) ≤ (b.m : ℝ) * (2 : ℝ) ^ (b.e - a.e) := by
      have h' := decide_eq_true_eq.mp h
      rw [Nat.shiftLeft_eq] at h'; exact_mod_cast h'
    unfold toReal
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he, mul_comm ((2 : ℝ) ^ a.e), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  · have he' : b.e ≤ a.e := le_of_not_ge he
    have hm : (a.m : ℝ) * (2 : ℝ) ^ (a.e - b.e) ≤ (b.m : ℝ) := by
      have h' := decide_eq_true_eq.mp h
      rw [Nat.shiftLeft_eq] at h'; exact_mod_cast h'
    unfold toReal
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he', mul_comm ((2 : ℝ) ^ b.e), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hm (by positivity)

lemma blt_sound {a b : Dyadic} (h : a.blt b = true) : a.toReal < b.toReal := by
  unfold blt at h
  by_cases hb0 : (b.m == 0) = true
  · simp only [hb0, ite_true] at h; exact absurd h (by native_decide)
  · simp only [hb0, Bool.false_eq_true, ite_false] at h
    by_cases ha0 : (a.m == 0) = true
    · have hm : a.m = 0 := beq_iff_eq.mp ha0
      have hbn : 0 < b.m := Nat.pos_of_ne_zero (fun h0 => hb0 (beq_iff_eq.mpr h0))
      unfold toReal; rw [hm, Nat.cast_zero, zero_mul, zero_div]
      exact div_pos (mul_pos (by exact_mod_cast hbn) (by positivity)) two_pow_bias_pos
    · simp only [ha0, Bool.false_eq_true, ite_false] at h
      by_cases he : a.e ≤ b.e
      · simp only [he, ite_true, decide_eq_true_eq, Nat.shiftLeft_eq] at h
        have hm : (a.m : ℝ) < (b.m : ℝ) * (2 : ℝ) ^ (b.e - a.e) := by exact_mod_cast h
        unfold toReal
        refine div_lt_div_of_pos_right ?_ two_pow_bias_pos
        rw [two_pow_split he, mul_comm ((2 : ℝ) ^ a.e), ← mul_assoc]
        exact mul_lt_mul_of_pos_right hm (by positivity)
      · have he' : b.e ≤ a.e := le_of_not_ge he
        simp only [he, ite_false, decide_eq_true_eq, Nat.shiftLeft_eq] at h
        have hm : (a.m : ℝ) * (2 : ℝ) ^ (a.e - b.e) < (b.m : ℝ) := by exact_mod_cast h
        unfold toReal
        refine div_lt_div_of_pos_right ?_ two_pow_bias_pos
        rw [two_pow_split he', mul_comm ((2 : ℝ) ^ b.e), ← mul_assoc]
        exact mul_lt_mul_of_pos_right hm (by positivity)

lemma ble_false_le {a b : Dyadic} (h : a.ble b = false) : b.toReal ≤ a.toReal := by
  unfold ble at h
  split_ifs at h with ha0 hb0 he
  · have hbm : b.m = 0 := beq_iff_eq.mp hb0
    simpa [toReal, hbm] using a.toReal_nonneg
  · rw [decide_eq_false_iff_not, not_le, Nat.shiftLeft_eq] at h
    have hm : (b.m : ℝ) * (2 : ℝ) ^ (b.e - a.e) ≤ (a.m : ℝ) := by exact_mod_cast h.le
    unfold toReal
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he, mul_comm ((2 : ℝ) ^ a.e), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  · have he' : b.e ≤ a.e := le_of_not_ge he
    rw [decide_eq_false_iff_not, not_le, Nat.shiftLeft_eq] at h
    have hm : (b.m : ℝ) ≤ (a.m : ℝ) * (2 : ℝ) ^ (a.e - b.e) := by exact_mod_cast h.le
    unfold toReal
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he', mul_comm ((2 : ℝ) ^ b.e), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hm (by positivity)

lemma blt_false_le {a b : Dyadic} (h : a.blt b = false) : b.toReal ≤ a.toReal := by
  unfold blt at h
  split_ifs at h with hb0 ha0 he
  · have hbm : b.m = 0 := beq_iff_eq.mp hb0
    simpa [toReal, hbm] using a.toReal_nonneg
  · rw [decide_eq_false_iff_not, not_lt, Nat.shiftLeft_eq] at h
    have hm : (b.m : ℝ) * (2 : ℝ) ^ (b.e - a.e) ≤ (a.m : ℝ) := by exact_mod_cast h
    unfold toReal
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he, mul_comm ((2 : ℝ) ^ a.e), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  · have he' : b.e ≤ a.e := le_of_not_ge he
    rw [decide_eq_false_iff_not, not_lt, Nat.shiftLeft_eq] at h
    have hm : (b.m : ℝ) ≤ (a.m : ℝ) * (2 : ℝ) ^ (a.e - b.e) := by exact_mod_cast h
    unfold toReal
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he', mul_comm ((2 : ℝ) ^ b.e), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hm (by positivity)

lemma add_toReal (a b : Dyadic) : (a.add b).toReal = a.toReal + b.toReal := by
  unfold add
  split_ifs with ha0 hb0 he
  · have hm : a.m = 0 := beq_iff_eq.mp ha0; simp [toReal, hm]
  · have hm : b.m = 0 := beq_iff_eq.mp hb0; simp [toReal, hm]
  · unfold toReal; rw [← add_div]; congr 1
    rw [Nat.shiftLeft_eq, two_pow_split he]; push_cast; ring
  · have he' : b.e ≤ a.e := le_of_not_ge he
    unfold toReal; rw [← add_div]; congr 1
    rw [Nat.shiftLeft_eq, two_pow_split he']; push_cast; ring

lemma sub_le_subLb_toReal (a b : Dyadic) : a.toReal - b.toReal ≤ (a.subLb b).toReal := by
  unfold subLb
  split_ifs with hb0 ha0 he
  · have hm : b.m = 0 := beq_iff_eq.mp hb0; simp [toReal, hm]
  · have hm : a.m = 0 := beq_iff_eq.mp ha0
    rw [zero_toReal, toReal_eq_zero_of_m hm]; linarith [b.toReal_nonneg]
  · unfold toReal; rw [← sub_div]
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he]
    rcases le_or_gt (b.m <<< (b.e - a.e)) a.m with hle | hlt
    · rw [Nat.cast_sub hle, Nat.shiftLeft_eq]; push_cast; ring_nf; exact le_rfl
    · rw [Nat.sub_eq_zero_of_le hlt.le, Nat.cast_zero, zero_mul]
      rw [Nat.shiftLeft_eq] at hlt
      have hr : (a.m : ℝ) < (b.m : ℝ) * (2 : ℝ) ^ (b.e - a.e) := by exact_mod_cast hlt
      have hmul : (a.m : ℝ) * (2 : ℝ) ^ a.e ≤ (b.m : ℝ) * ((2 : ℝ) ^ a.e * (2 : ℝ) ^ (b.e - a.e)) := by
        rw [mul_comm ((2 : ℝ) ^ a.e), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hr.le (by positivity)
      linarith
  · have he' : b.e ≤ a.e := le_of_not_ge he
    unfold toReal; rw [← sub_div]
    refine div_le_div_of_nonneg_right ?_ two_pow_bias_pos.le
    rw [two_pow_split he']
    rcases le_or_gt b.m (a.m <<< (a.e - b.e)) with hle | hlt
    · rw [Nat.cast_sub hle, Nat.shiftLeft_eq]; push_cast; ring_nf; exact le_rfl
    · rw [Nat.sub_eq_zero_of_le hlt.le, Nat.cast_zero, zero_mul]
      rw [Nat.shiftLeft_eq] at hlt
      have hr : (a.m : ℝ) * (2 : ℝ) ^ (a.e - b.e) < (b.m : ℝ) := by exact_mod_cast hlt
      have hmul : (a.m : ℝ) * ((2 : ℝ) ^ b.e * (2 : ℝ) ^ (a.e - b.e)) ≤ (b.m : ℝ) * (2 : ℝ) ^ b.e := by
        rw [mul_comm ((2 : ℝ) ^ b.e), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hr.le (by positivity)
      linarith

lemma subLb_eq {a b : Dyadic} (h : b.toReal ≤ a.toReal) :
    (a.subLb b).toReal = a.toReal - b.toReal := by
  unfold subLb
  split_ifs with hb0 ha0 he
  · have hm : b.m = 0 := beq_iff_eq.mp hb0; simp [toReal, hm]
  · have hm : a.m = 0 := beq_iff_eq.mp ha0
    have ha0r : a.toReal = 0 := by simp [toReal, hm]
    have hb0r : b.toReal = 0 := le_antisymm (ha0r ▸ h) b.toReal_nonneg
    rw [zero_toReal, ha0r, hb0r, sub_zero]
  · unfold toReal at h ⊢; rw [two_pow_split he] at h
    have hnum : (b.m : ℝ) * (2 : ℝ) ^ (b.e - a.e) * (2 : ℝ) ^ a.e ≤ (a.m : ℝ) * (2 : ℝ) ^ a.e := by
      have h1 := mul_le_mul_of_nonneg_right h two_pow_bias_pos.le
      rw [div_mul_cancel₀ _ two_pow_bias_pos.ne', div_mul_cancel₀ _ two_pow_bias_pos.ne'] at h1
      rw [mul_assoc, mul_comm ((2 : ℝ) ^ (b.e - a.e))]; exact h1
    have hm : b.m * 2 ^ (b.e - a.e) ≤ a.m := by
      exact_mod_cast le_of_mul_le_mul_right hnum (by positivity)
    rw [← Nat.shiftLeft_eq] at hm
    rw [← sub_div]; congr 1; rw [two_pow_split he, Nat.cast_sub hm, Nat.shiftLeft_eq]; push_cast; ring
  · have he' : b.e ≤ a.e := le_of_not_ge he
    unfold toReal at h ⊢; rw [two_pow_split he'] at h
    have hnum : (b.m : ℝ) * (2 : ℝ) ^ b.e ≤ (a.m : ℝ) * (2 : ℝ) ^ (a.e - b.e) * (2 : ℝ) ^ b.e := by
      have h1 := mul_le_mul_of_nonneg_right h two_pow_bias_pos.le
      rw [div_mul_cancel₀ _ two_pow_bias_pos.ne', div_mul_cancel₀ _ two_pow_bias_pos.ne'] at h1
      rw [mul_assoc, mul_comm ((2 : ℝ) ^ (a.e - b.e))]; exact h1
    have hm : b.m ≤ a.m * 2 ^ (a.e - b.e) := by
      exact_mod_cast le_of_mul_le_mul_right hnum (by positivity)
    rw [← Nat.shiftLeft_eq] at hm
    rw [← sub_div]; congr 1; rw [two_pow_split he', Nat.cast_sub hm, Nat.shiftLeft_eq]; push_cast; ring

lemma subLb_le {a b : Dyadic} (h : b.toReal ≤ a.toReal) :
    (a.subLb b).toReal ≤ a.toReal - b.toReal :=
  (subLb_eq h).le

private lemma dyadic_mul_eq_abstract {m1 m2 e1 e2 c B : ℝ} (hB : B ≠ 0) (hp : c * B = e1 * e2) :
    (m1 * m2) * c / B = (m1 * e1 / B) * (m2 * e2 / B) := by
  field_simp [hB]
  calc m1 * m2 * c * B = (m1 * m2) * (c * B) := by ring
    _ = (m1 * m2) * (e1 * e2) := by rw [hp]
    _ = m1 * m2 * e1 * e2 := by ring

private lemma dyadic_div_eq_abstract {m1 m2 e1 e2 c B : ℝ} (hc : c ≠ 0)
    (hB : B ≠ 0) (hp : e1 * e2 * c = B) :
    (m1 * m2 / c) / B = (m1 * e1 / B) * (m2 * e2 / B) := by
  have h1 : e1 * e2 * c ≠ 0 := hp.symm ▸ hB
  have he1 : e1 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h1)
  have he2 : e2 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h1)
  field_simp [hc, he1, he2, hB]
  calc m1 * m2 * B = m1 * m2 * (e1 * e2 * c) := by rw [hp]
    _ = m1 * e1 * (m2 * e2) * c := by ring
    _ = m1 * m2 * c * e1 * e2 := by ring

private lemma q64_mul_eq_abstract {m B1 B2 E S : ℝ} (hB1 : B1 ≠ 0) (hB2 : B2 ≠ 0)
    (hp : B1 * S = E) : m * S / B2 = m * E / (B1 * B2) := by
  field_simp [hB1, hB2]
  calc m * S * B1 = m * (B1 * S) := by ring
    _ = m * E := by rw [hp]

lemma subLb_le_max_zero {a b : Dyadic} {A B : ℝ} (ha : a.toReal ≤ A) (hb : B ≤ b.toReal) :
    (a.subLb b).toReal ≤ max 0 (A - B) := by
  by_cases hba : b.toReal ≤ a.toReal
  · exact (subLb_le hba).trans (le_trans (by linarith) (le_max_right _ _))
  · have hba' : a.toReal < b.toReal := not_le.mp hba
    have hzero : (a.subLb b).toReal = 0 := by
      unfold subLb
      by_cases hb0 : (b.m == 0) = true
      · exfalso; have hbm : b.m = 0 := beq_iff_eq.mp hb0
        have hb0r : b.toReal = 0 := by unfold toReal; rw [hbm, Nat.cast_zero, zero_mul, zero_div]
        linarith [a.toReal_nonneg]
      · simp only [hb0, Bool.false_eq_true, ite_false]
        by_cases ha0 : (a.m == 0) = true
        · simp only [ha0, ite_true]; exact zero_toReal
        · simp only [ha0, Bool.false_eq_true, ite_false]
          by_cases he : a.e ≤ b.e
          · simp only [he, ite_true]
            unfold toReal at hba' ⊢; rw [two_pow_split he] at hba'
            have hnum : (a.m : ℝ) * (2 : ℝ) ^ a.e < (b.m : ℝ) * (2 : ℝ) ^ (b.e - a.e) * (2 : ℝ) ^ a.e := by
              have h1 := mul_lt_mul_of_pos_right hba' two_pow_bias_pos
              rw [div_mul_cancel₀ _ two_pow_bias_pos.ne', div_mul_cancel₀ _ two_pow_bias_pos.ne'] at h1
              rw [mul_assoc, mul_comm ((2 : ℝ) ^ (b.e - a.e))]; exact h1
            have hm : a.m < b.m * 2 ^ (b.e - a.e) := by
              exact_mod_cast lt_of_mul_lt_mul_right hnum (by positivity)
            rw [← Nat.shiftLeft_eq] at hm
            dsimp only
            rw [Nat.sub_eq_zero_of_le hm.le, Nat.cast_zero, zero_mul, zero_div]
          · have he' : b.e ≤ a.e := le_of_not_ge he
            simp only [he, ite_false]
            unfold toReal at hba' ⊢; rw [two_pow_split he'] at hba'
            have hnum : (a.m : ℝ) * (2 : ℝ) ^ (a.e - b.e) * (2 : ℝ) ^ b.e < (b.m : ℝ) * (2 : ℝ) ^ b.e := by
              have h1 := mul_lt_mul_of_pos_right hba' two_pow_bias_pos
              rw [div_mul_cancel₀ _ two_pow_bias_pos.ne', div_mul_cancel₀ _ two_pow_bias_pos.ne'] at h1
              rw [mul_assoc, mul_comm ((2 : ℝ) ^ (a.e - b.e))]; exact h1
            have hm : a.m * 2 ^ (a.e - b.e) < b.m := by
              exact_mod_cast lt_of_mul_lt_mul_right hnum (by positivity)
            rw [← Nat.shiftLeft_eq] at hm
            dsimp only
            rw [Nat.sub_eq_zero_of_le hm.le, Nat.cast_zero, zero_mul, zero_div]
    rw [hzero]; exact le_max_left _ _

lemma mulRawLb_le (a b : Dyadic) : (mulRawLb a b).toReal ≤ a.toReal * b.toReal := by
  unfold mulRawLb
  split_ifs with h0 hge
  · rcases Bool.or_eq_true_iff.mp h0 with ha | hb
    · rw [zero_toReal]; unfold toReal; rw [beq_iff_eq.mp ha]; simp
    · rw [zero_toReal]; unfold toReal; rw [beq_iff_eq.mp hb]; simp
  · refine le_of_eq ?_
    unfold toReal; dsimp only; rw [Nat.cast_mul]
    exact dyadic_mul_eq_abstract two_pow_bias_pos.ne'
      (by rw [twoPowBias_eq, ← pow_add, Nat.sub_add_cancel hge, pow_add])
  · have hlt : a.e + b.e ≤ dyadicBias := (not_le.mp hge).le
    unfold toReal; dsimp only
    have hfl := floorShr_le (a.m * b.m) (dyadicBias - (a.e + b.e))
    have hmul : (((a.m * b.m) >>> (dyadicBias - (a.e + b.e)) : ℕ) : ℝ) * (2 : ℝ) ^ 0 / twoPowBias ≤
        (((a.m * b.m : ℕ) : ℝ) / (2 : ℝ) ^ (dyadicBias - (a.e + b.e))) / twoPowBias := by
      rw [pow_zero, mul_one]; exact div_le_div_of_nonneg_right hfl two_pow_bias_pos.le
    refine hmul.trans_eq ?_
    rw [Nat.cast_mul]
    exact dyadic_div_eq_abstract (by positivity) two_pow_bias_pos.ne'
      (by rw [twoPowBias_eq, two_pow_split hlt, pow_add])

lemma le_mulRawUb (a b : Dyadic) : a.toReal * b.toReal ≤ (mulRawUb a b).toReal := by
  unfold mulRawUb
  split_ifs with h0 hge
  · rcases Bool.or_eq_true_iff.mp h0 with ha | hb
    · rw [zero_toReal]; unfold toReal; rw [beq_iff_eq.mp ha]; simp
    · rw [zero_toReal]; unfold toReal; rw [beq_iff_eq.mp hb]; simp
  · refine le_of_eq ?_
    unfold toReal; dsimp only; rw [Nat.cast_mul]
    exact (dyadic_mul_eq_abstract two_pow_bias_pos.ne'
      (by rw [twoPowBias_eq, ← pow_add, Nat.sub_add_cancel hge, pow_add])).symm
  · have hlt : a.e + b.e ≤ dyadicBias := (not_le.mp hge).le
    unfold toReal; dsimp only
    have hceil := ceilShr_ge (a.m * b.m) (dyadicBias - (a.e + b.e))
    have heq : ((a.m : ℝ) * (2 : ℝ) ^ a.e / twoPowBias) * ((b.m : ℝ) * (2 : ℝ) ^ b.e / twoPowBias) =
        (((a.m * b.m : ℕ) : ℝ) / (2 : ℝ) ^ (dyadicBias - (a.e + b.e))) / twoPowBias := by
      rw [Nat.cast_mul]
      exact (dyadic_div_eq_abstract (by positivity) two_pow_bias_pos.ne'
        (by rw [twoPowBias_eq, two_pow_split hlt, pow_add])).symm
    refine heq.trans_le ?_
    rw [pow_zero, mul_one]
    exact div_le_div_of_nonneg_right hceil two_pow_bias_pos.le

lemma mulLb_le (a b : Dyadic) : (a.mulLb b).toReal ≤ a.toReal * b.toReal :=
  (trimLb_le _ 80).trans (mulRawLb_le a b)

lemma le_mulUb (a b : Dyadic) : a.toReal * b.toReal ≤ (a.mulUb b).toReal :=
  (le_mulRawUb a b).trans (le_trimUb _ 80)

lemma powUb_sound (a : Dyadic) (k : ℕ) : a.toReal ^ k ≤ (powUb a k).toReal := by
  induction k with
  | zero => simp [powUb, one_toReal]
  | succ k ih =>
    unfold powUb
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih a.toReal_nonneg).trans (le_mulUb _ _)

lemma toQ64Lb_le (a : Dyadic) : ((a.toQ64Lb : ℝ) / (q64Scale : ℝ)) ≤ a.toReal := by
  unfold toQ64Lb toReal
  rw [q64Scale_real_eq, twoPowBias_eq]; unfold dyadicBias
  rw [show (8192 : ℕ) = 8128 + 64 by norm_num, pow_add]
  have hq8 : (8192 : ℕ) - 64 = 8128 := rfl
  rw [hq8]
  split_ifs with he
  · rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (q64_mul_eq_abstract (by positivity) (by positivity) (two_pow_split he).symm)
  · have he' : a.e ≤ 8128 := le_of_not_ge he
    have hfl := floorShr_le a.m (8128 - a.e)
    calc ((a.m >>> (8128 - a.e) : ℕ) : ℝ) / (2 : ℝ) ^ 64
        ≤ ((a.m : ℝ) / (2 : ℝ) ^ (8128 - a.e)) / (2 : ℝ) ^ 64 :=
          div_le_div_of_nonneg_right hfl (by positivity)
      _ = (a.m : ℝ) * (2 : ℝ) ^ a.e / ((2 : ℝ) ^ 8128 * (2 : ℝ) ^ 64) := by
          rw [two_pow_split he']; field_simp [(by positivity : (2 : ℝ) ^ a.e ≠ 0), (by positivity : (2 : ℝ) ^ (8128 - a.e) ≠ 0)]

lemma le_toQ64Ub (a : Dyadic) : a.toReal ≤ ((a.toQ64Ub : ℝ) / (q64Scale : ℝ)) := by
  unfold toQ64Ub toReal
  rw [q64Scale_real_eq, twoPowBias_eq]; unfold dyadicBias
  rw [show (8192 : ℕ) = 8128 + 64 by norm_num, pow_add]
  have hq8 : (8192 : ℕ) - 64 = 8128 := rfl
  rw [hq8]
  split_ifs with he
  · rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact le_of_eq (q64_mul_eq_abstract (by positivity) (by positivity) (two_pow_split he).symm).symm
  · have he' : a.e ≤ 8128 := le_of_not_ge he
    have hceil := ceilShr_ge a.m (8128 - a.e)
    calc (a.m : ℝ) * (2 : ℝ) ^ a.e / ((2 : ℝ) ^ 8128 * (2 : ℝ) ^ 64)
        = ((a.m : ℝ) / (2 : ℝ) ^ (8128 - a.e)) / (2 : ℝ) ^ 64 := by
          rw [two_pow_split he']; field_simp [(by positivity : (2 : ℝ) ^ a.e ≠ 0), (by positivity : (2 : ℝ) ^ (8128 - a.e) ≠ 0)]
      _ ≤ (ceilShr a.m (8128 - a.e) : ℝ) / (2 : ℝ) ^ 64 :=
          div_le_div_of_nonneg_right hceil (by positivity)

lemma div_le_of_ble_mulLb {num den qUb : Dyadic} {N D : ℝ}
    (hN : N ≤ num.toReal) (hD_pos : 0 < D) (hD : den.toReal ≤ D)
    (hchk : num.ble (qUb.mulLb den) = true) :
    N / D ≤ qUb.toReal := by
  have h1 : num.toReal ≤ qUb.toReal * den.toReal := (ble_sound hchk).trans (mulLb_le qUb den)
  exact (div_le_iff₀ hD_pos).mpr (hN.trans (h1.trans (mul_le_mul_of_nonneg_left hD qUb.toReal_nonneg)))

lemma le_div_of_mulUb_ble {num den qLb : Dyadic} {N D : ℝ}
    (hN : num.toReal ≤ N) (hD_pos : 0 < D) (hD : D ≤ den.toReal)
    (hchk : (qLb.mulUb den).ble num = true) :
    qLb.toReal ≤ N / D := by
  have h1 : qLb.toReal * den.toReal ≤ num.toReal := (le_mulUb qLb den).trans (ble_sound hchk)
  exact (le_div_iff₀ hD_pos).mpr ((mul_le_mul_of_nonneg_left hD qLb.toReal_nonneg).trans (h1.trans hN))

end Dyadic

lemma fastChoose_eq_choose (n k : ℕ) : fastChoose n k = n.choose k := by
  unfold fastChoose
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.mul_div_cancel_left (n.choose k) (Nat.factorial_pos k)

def checkSqrtLb (x sLb : Dyadic) : Bool := (sLb.mulUb sLb).ble x
def checkSqrtUb (x sUb : Dyadic) : Bool := x.ble (sUb.mulLb sUb)

lemma checkSqrtLb_sound {x sLb : Dyadic} {r : ℝ} (hxr : x.toReal ≤ r)
    (h : checkSqrtLb x sLb = true) : sLb.toReal ≤ Real.sqrt r := by
  apply Real.le_sqrt_of_sq_le; rw [sq]
  exact (Dyadic.le_mulUb sLb sLb).trans ((Dyadic.ble_sound h).trans hxr)

lemma checkSqrtUb_sound {x sUb : Dyadic} {r : ℝ} (hrx : r ≤ x.toReal)
    (h : checkSqrtUb x sUb = true) : Real.sqrt r ≤ sUb.toReal := by
  rw [Real.sqrt_le_iff]; refine ⟨sUb.toReal_nonneg, ?_⟩; rw [sq]
  exact hrx.trans ((Dyadic.ble_sound h).trans (Dyadic.mulLb_le sUb sUb))

/-! ## 2. Precomputed Q64 Rational Constants and Division-Free `log` Checker -/

lemma q64Scale_pos : (0 : ℝ) < (q64Scale : ℝ) := by
  rw [Dyadic.q64Scale_real_eq]; positivity

lemma q64MulLb_le (a b : ℕ) :
    (((a * b) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤
      ((a : ℝ) / (q64Scale : ℝ)) * ((b : ℝ) / (q64Scale : ℝ)) := by
  have hfl := Dyadic.floorShr_le (a * b) 64
  rw [← Dyadic.q64Scale_real_eq] at hfl
  calc (((a * b) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ)
      ≤ (((a * b : ℕ) : ℝ) / (q64Scale : ℝ)) / (q64Scale : ℝ) :=
        div_le_div_of_nonneg_right hfl q64Scale_pos.le
    _ = ((a : ℝ) / (q64Scale : ℝ)) * ((b : ℝ) / (q64Scale : ℝ)) := by push_cast; ring

lemma le_q64MulUb (a b : ℕ) :
    ((a : ℝ) / (q64Scale : ℝ)) * ((b : ℝ) / (q64Scale : ℝ)) ≤
      (Dyadic.ceilShr (a * b) 64 : ℝ) / (q64Scale : ℝ) := by
  have hceil := Dyadic.ceilShr_ge (a * b) 64
  rw [← Dyadic.q64Scale_real_eq] at hceil
  calc ((a : ℝ) / (q64Scale : ℝ)) * ((b : ℝ) / (q64Scale : ℝ))
      = (((a * b : ℕ) : ℝ) / (q64Scale : ℝ)) / (q64Scale : ℝ) := by push_cast; ring
    _ ≤ (Dyadic.ceilShr (a * b) 64 : ℝ) / (q64Scale : ℝ) :=
        div_le_div_of_nonneg_right hceil q64Scale_pos.le

end

end BuchstabSwitching.SieveInst
