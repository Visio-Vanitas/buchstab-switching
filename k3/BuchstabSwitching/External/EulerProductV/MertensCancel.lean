import BuchstabSwitching.External.NumericalConstants.CanonicalDefs
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import Mathlib.Tactic

/-!
# Mertens-Product Cancellation & Middle-Range Bound (`27000 ≤ x ≤ 10^12`)

Defines `eulerR3 x = (log x / exp(-γ)) * ∏_{p < ⌈x⌉} (1 - 1/p)` and proves:
1. `eulerR3_mem_Icc_of_mertens_err`: general reduction from two-sided bounds on
   `∑_{p < ⌈x⌉} 1/p - log(log x) - meisselMertensConst` to
   `1 - 1/(2 (log x)^2) ≤ eulerR3 x ≤ 1 + 1/(2 (log x)^2)` by cancelling `meisselMertensConst`
   against `∑_{p < ⌈x⌉} (log(1 - 1/p) + 1/p)`;
2. `eulerR3_mem_Icc_mid`: unconditional proof on `27000 ≤ x ≤ 10^12` from
   `MertensPrimeSumPremise meisselMertensConst`.
-/

namespace BuchstabSwitching.External

/-- Normalized Mertens Euler-product ratio `(log x / e^{-γ}) * ∏_{p < ⌈x⌉} (1 - 1/p)`. -/
noncomputable def eulerR3 (x : ℝ) : ℝ :=
  (Real.log x / Real.exp (-Real.eulerMascheroniConstant)) *
    ∏ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 - 1 / (p : ℝ))

private noncomputable def mmNegTermNat (n : ℕ) : ℝ :=
  if n.Prime then -(Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)) else 0

private lemma mmNegTermNat_nonneg (n : ℕ) : 0 ≤ mmNegTermNat n := by
  unfold mmNegTermNat
  split_ifs with hp
  · exact (neg_log_one_sub_inv_add_inv_bounds (by exact_mod_cast hp.two_le)).1
  · exact le_rfl

private lemma mmNegTermNat_le {n : ℕ} (hn : 2 ≤ n) :
    mmNegTermNat n ≤ (1 / 2 : ℝ) * (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
  have hn_r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have htele : (1 / 2 : ℝ) * (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
      1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp [hn0.ne', hn1.ne']
    ring
  unfold mmNegTermNat
  split_ifs with hp
  · rw [htele]
    exact (neg_log_one_sub_inv_add_inv_bounds hn_r).2
  · rw [htele]; positivity

private lemma summable_mmNegTermNat : Summable mmNegTermNat := by
  have hp2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine Summable.of_nonneg_of_le mmNegTermNat_nonneg (fun n => ?_) hp2
  unfold mmNegTermNat
  split_ifs with hp
  · have hn_r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hbd := (neg_log_one_sub_inv_add_inv_bounds hn_r).2
    have hden : (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    exact hbd.trans (one_div_le_one_div_of_le (by positivity) hden)
  · positivity

private lemma tsum_mmNegTermNat_eq :
    (∑' n : ℕ, mmNegTermNat n) = Real.eulerMascheroniConstant - meisselMertensConst := by
  have hind : mmNegTermNat =
      Set.indicator {n : ℕ | n.Prime} (fun n : ℕ => -(Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))) := by
    ext n; simp [mmNegTermNat, Set.indicator_apply]
  have hsub : (∑' p : {n : ℕ | n.Prime}, -(Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))) =
      ∑' n : ℕ, mmNegTermNat n := by
    rw [hind]
    exact tsum_subtype {n : ℕ | n.Prime}
      (fun n : ℕ => -(Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)))
  have hpr : (∑' p : Nat.Primes, -(Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))) =
      ∑' n : ℕ, mmNegTermNat n := hsub
  rw [← hpr, tsum_neg]
  unfold meisselMertensConst
  ring

private lemma mm_tail_bounds {z : ℕ} (hz : 2 ≤ z) :
    0 ≤ ∑' k : ℕ, mmNegTermNat (k + z) ∧
      (∑' k : ℕ, mmNegTermNat (k + z)) ≤ 1 / (2 * ((z : ℝ) - 1)) := by
  have hsum_shift : Summable (fun k : ℕ => mmNegTermNat (k + z)) :=
    summable_mmNegTermNat.comp_injective (add_left_injective z)
  refine ⟨tsum_nonneg fun k => mmNegTermNat_nonneg (k + z), ?_⟩
  refine Real.tsum_le_of_sum_range_le (fun k => mmNegTermNat_nonneg (k + z)) fun M => ?_
  have hle : ∑ k ∈ Finset.range M, mmNegTermNat (k + z) ≤
      ∑ k ∈ Finset.range M,
        (1 / 2 : ℝ) * (1 / (((k + z : ℕ) : ℝ) - 1) - 1 / ((k + z : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun k _ => mmNegTermNat_le (by omega)
  have htele : ∀ m : ℕ,
      ∑ k ∈ Finset.range m,
        (1 / 2 : ℝ) * (1 / (((k + z : ℕ) : ℝ) - 1) - 1 / ((k + z : ℕ) : ℝ)) =
      (1 / 2 : ℝ) * (1 / ((z : ℝ) - 1) - 1 / (((m + z : ℕ) : ℝ) - 1)) := by
    intro m
    induction m with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [htele M] at hle
  have hz_r : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hmz_pos : (0 : ℝ) < ((M + z : ℕ) : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ((M + z : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ M + z)
    linarith
  have hnn : (0 : ℝ) ≤ 1 / (((M + z : ℕ) : ℝ) - 1) := div_nonneg zero_le_one hmz_pos.le
  have hhalf : (1 / 2 : ℝ) * (1 / ((z : ℝ) - 1)) = 1 / (2 * ((z : ℝ) - 1)) := by
    rw [one_div_mul_one_div]
  linarith

/-- Master reduction from two-sided Mertens sum bounds at `x ≥ 285` to `eulerR3 x` bounds. -/
theorem eulerR3_mem_Icc_of_mertens_err {x E_lo E_hi : ℝ} (hx : 285 ≤ x)
    (h_lo : Real.log (Real.log x) + meisselMertensConst - E_lo ≤
      ∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    (h_hi : (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
      Real.log (Real.log x) + meisselMertensConst + E_hi)
    (hE_lo_nn : 0 ≤ E_lo)
    (h_hi_bd : E_hi ≤ 1 / (2 * (Real.log x) ^ 2))
    (h_lo_bd : E_lo + 1 / (2 * (x - 1)) ≤ (9 / 20 : ℝ) / (Real.log x) ^ 2) :
    1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
      eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2) := by
  set z : ℕ := Nat.ceil x
  have hz_ge : x ≤ (z : ℝ) := Nat.le_ceil x
  have hz285 : 285 ≤ z := by exact_mod_cast hx.trans hz_ge
  have hx1 : 1 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx1
  have hsplit := summable_mmNegTermNat.sum_add_tsum_nat_add z
  rw [tsum_mmNegTermNat_eq] at hsplit
  have hfin_eq : ∑ n ∈ Finset.range z, mmNegTermNat n =
      -(∑ p ∈ (Finset.range z).filter Nat.Prime,
        (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) := by
    rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold mmNegTermNat
    split_ifs <;> simp
  have hprod_pos : ∀ p ∈ (Finset.range z).filter Nat.Prime, 0 < 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hprod_exp : ∏ p ∈ (Finset.range z).filter Nat.Prime, (1 - 1 / (p : ℝ)) =
      Real.exp (∑ p ∈ (Finset.range z).filter Nat.Prime, Real.log (1 - 1 / (p : ℝ))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun p hp => (Real.exp_log (hprod_pos p hp)).symm
  have hr3_exp : eulerR3 x =
      Real.exp (Real.log (Real.log x) + Real.eulerMascheroniConstant +
        ∑ p ∈ (Finset.range z).filter Nat.Prime, Real.log (1 - 1 / (p : ℝ))) := by
    unfold eulerR3
    rw [hprod_exp, Real.exp_add, Real.exp_add, Real.exp_log hlogx_pos, div_eq_mul_inv,
      ← Real.exp_neg, neg_neg]
  have hsum_log : ∑ p ∈ (Finset.range z).filter Nat.Prime, Real.log (1 - 1 / (p : ℝ)) =
      (∑ p ∈ (Finset.range z).filter Nat.Prime, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
        ∑ p ∈ (Finset.range z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.sum_add_distrib, add_sub_cancel_right]
  set T : ℝ := ∑' k : ℕ, mmNegTermNat (k + z)
  have hT := mm_tail_bounds (z := z) (by omega)
  have hT_le_x : T ≤ 1 / (2 * (x - 1)) :=
    hT.2.trans (one_div_le_one_div_of_le (by linarith) (by linarith))
  set L : ℝ := Real.log (Real.log x) + Real.eulerMascheroniConstant +
    ∑ p ∈ (Finset.range z).filter Nat.Prime, Real.log (1 - 1 / (p : ℝ))
  have hL_id : L = T - ((∑ p ∈ (Finset.range z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
      Real.log (Real.log x) - meisselMertensConst) := by
    dsimp only [L]
    rw [hsum_log]
    linarith [hsplit, hfin_eq]
  have hL_lo : -E_hi ≤ L := by linarith [hL_id, hT.1, h_hi]
  have hL_hi : L ≤ E_lo + 1 / (2 * (x - 1)) := by linarith [hL_id, hT_le_x, h_lo]
  rw [hr3_exp]
  change 1 - 1 / (2 * (Real.log x) ^ 2) ≤ Real.exp L ∧
    Real.exp L ≤ 1 + 1 / (2 * (Real.log x) ^ 2)
  constructor
  · have h1 : 1 - E_hi ≤ Real.exp (-E_hi) := by linarith [Real.add_one_le_exp (-E_hi)]
    have h2 : Real.exp (-E_hi) ≤ Real.exp L := Real.exp_le_exp.mpr hL_lo
    linarith
  · set u : ℝ := E_lo + 1 / (2 * (x - 1))
    have hu_nn : 0 ≤ u := add_nonneg hE_lo_nn (by positivity)
    have hexp5 : Real.exp 5 ≤ x := by
      have h1 : Real.exp 1 < 3 := by
        have hbd := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by omega : 0 < 4)
        norm_num [Finset.sum_range_succ, Nat.factorial] at hbd
        linarith [le_of_abs_le hbd]
      have h5 : Real.exp 5 < 3 ^ 5 := by
        rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        exact pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by omega)
      norm_num at h5; linarith
    have hlog5 : 5 ≤ Real.log x := by
      calc (5 : ℝ) = Real.log (Real.exp 5) := (Real.log_exp 5).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 5) hexp5
    have hlog_sq : 25 ≤ (Real.log x) ^ 2 := by nlinarith
    have hu_lt : u ≤ 1 / 10 := by
      have : (9 / 20 : ℝ) / (Real.log x) ^ 2 ≤ (9 / 20 : ℝ) / 25 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog_sq
      linarith
    have hexp_u : Real.exp u ≤ 1 + (10 / 9 : ℝ) * u := by
      have hneg : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
      rw [Real.exp_neg, ← one_div] at hneg
      have hsub_pos : 0 < 1 - u := by linarith
      have hinv := one_div_le_one_div_of_le hsub_pos hneg
      rw [one_div_one_div] at hinv
      have hlin : 1 / (1 - u) ≤ 1 + (10 / 9 : ℝ) * u := by
        rw [div_le_iff₀ hsub_pos]
        nlinarith
      exact hinv.trans hlin
    have h10_9 : (10 / 9 : ℝ) * u ≤ 1 / (2 * (Real.log x) ^ 2) := by
      calc (10 / 9 : ℝ) * u ≤ (10 / 9 : ℝ) * ((9 / 20 : ℝ) / (Real.log x) ^ 2) :=
            mul_le_mul_of_nonneg_left h_lo_bd (by norm_num)
        _ = 1 / (2 * (Real.log x) ^ 2) := by ring
    exact (Real.exp_le_exp.mpr hL_hi).trans (hexp_u.trans (by linarith))

private lemma four_log_le_sqrt_of_ge_27000 {x : ℝ} (hx : 27000 ≤ x) :
    4 * Real.log x ≤ Real.sqrt x := by
  have hx_pos : 0 < x := by linarith
  set s : ℝ := Real.sqrt (Real.sqrt x)
  have hs_sq : s ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hs4 : s ^ 4 = x := by
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = Real.sqrt x ^ 2 := by rw [hs_sq]
      _ = x := Real.sq_sqrt hx_pos.le
  have hsq1 : (144 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx_pos.le]; linarith
  have hs12 : (12 : ℝ) ≤ s := by
    dsimp only [s]; rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg x)]; linarith
  have hs_pos : 0 < s := by linarith
  have hlog_x : Real.log x = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]; norm_num
  have hlog_s6 : Real.log (s / 6) ≤ s / 6 - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hs_pos (by norm_num))
  have hlog6 : Real.log 6 < 2 := by
    have he1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
      have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
      norm_num [Finset.sum_range_succ, Nat.factorial] at hs; linarith
    have he2 : (6 : ℝ) < Real.exp 2 := by
      have hp : (5 / 2 : ℝ) ^ 2 ≤ Real.exp 2 := by
        rw [show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
        exact pow_le_pow_left₀ (by norm_num) he1 2
      linarith [show (6 : ℝ) < (5 / 2 : ℝ) ^ 2 by norm_num]
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr he2
  rw [Real.log_div hs_pos.ne' (by norm_num)] at hlog_s6
  rw [hlog_x, ← hs_sq]
  nlinarith [sq_nonneg (s - 12)]

/-- Middle-range bound (`27000 ≤ x ≤ 10^12`) proved from `MertensPrimeSumPremise`. -/
theorem eulerR3_mem_Icc_mid (hMert : MertensPrimeSumPremise meisselMertensConst)
    {x : ℝ} (hx_lo : 27000 ≤ x) (hx_hi : x ≤ (10 : ℝ) ^ 12) :
    1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
      eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2) := by
  have hmb := hMert.mertensSumBounds x (by linarith)
  have hexp10 : Real.exp 10 < x := by
    have he1 : Real.exp 1 < 272 / 100 := by
      have hbd := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by omega : 0 < 5)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hbd
      linarith [le_of_abs_le hbd]
    have he10 : Real.exp 10 < (272 / 100 : ℝ) ^ 10 := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by omega)
    have hnum : (272 / 100 : ℝ) ^ 10 < 27000 := by norm_num
    linarith
  have hlog10 : 10 < Real.log x :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr hexp10
  have hhi_eq := jsMertensHiErr_eq_bjv hx_hi hlog10
  refine eulerR3_mem_Icc_of_mertens_err (by linarith) hmb.1 hmb.2
    (jsMertensLoErr_nonneg (by linarith)) ?_ ?_
  · rw [hhi_eq]
    have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hlog_pos : 0 < Real.log x := by linarith
    rw [div_le_div_iff₀ (mul_pos hsq_pos hlog_pos) (by positivity)]
    have h4 := four_log_le_sqrt_of_ge_27000 hx_lo
    nlinarith
  · unfold jsMertensLoErr
    have hlog_pos : 0 < Real.log x := by linarith
    have hlog_ub : Real.log x < 30 := by
      have he30 : (10 : ℝ) ^ 12 < Real.exp 30 := by
        have h27 : (27 / 10 : ℝ) ≤ Real.exp 1 := by
          have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 5
          norm_num [Finset.sum_range_succ, Nat.factorial] at hs; linarith
        have hp30 : (27 / 10 : ℝ) ^ 30 ≤ Real.exp 30 := by
          rw [show (30 : ℝ) = ((30 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
          exact pow_le_pow_left₀ (by norm_num) h27 30
        have hnum : (10 : ℝ) ^ 12 < (27 / 10 : ℝ) ^ 30 := by norm_num
        linarith
      exact (Real.log_lt_iff_lt_exp (by linarith)).mpr (hx_hi.trans_lt he30)
    have h4 := four_log_le_sqrt_of_ge_27000 hx_lo
    have hlog_sq_le : (Real.log x) ^ 2 ≤ x / 16 := by
      have hsq : (4 * Real.log x) ^ 2 ≤ (Real.sqrt x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h4 2
      rw [Real.sq_sqrt (by linarith)] at hsq
      linarith
    have ht1 : (2.964e-6 : ℝ) / Real.log x ≤ (0.09 : ℝ) / (Real.log x) ^ 2 := by
      rw [div_le_div_iff₀ hlog_pos (by positivity)]
      nlinarith
    have ht2 : 1 / (2 * (x - 1)) ≤ (0.04 : ℝ) / (Real.log x) ^ 2 := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
    have hsum_c : (0.09 : ℝ) / (Real.log x) ^ 2 + (0.04 : ℝ) / (Real.log x) ^ 2 ≤
        (9 / 20 : ℝ) / (Real.log x) ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
    linarith

end BuchstabSwitching.External
