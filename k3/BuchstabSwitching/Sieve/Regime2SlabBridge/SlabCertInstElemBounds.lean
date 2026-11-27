import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstEpdLi
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTree
import BuchstabSwitching.Sieve.Regime2SlabBridge.LowerAndMaster
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import Mathlib.Tactic

/-!
# Certified Analytic Range, Slice, Mertens Tail, and `vFullLb2c` Checkers (`Dyadic`)

Replaces `SciNat` 24-digit decimal arithmetic in `ElemBounds` with witness-checked
`Dyadic` inequalities (`AnalyticRangeWitness`, `MertensTailWitness`) and $O(\log N)$
segment-tree queries on `oddPrimeTree`.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

private lemma exp_ten_lt_27000 : Real.exp 10 < (27000 : ℝ) := by
  have hpow := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num : 10 ≠ 0)
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow; linarith

private lemma inv_log_integrable_Icc {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b :=
  (ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono fun t ht => by
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht; exact ne_of_gt (by linarith)) fun t ht => by
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht; exact (Real.log_pos (by linarith)).ne').intervalIntegrable

lemma sum_Ico_primes_inv_pred_sq_le (a b : ℕ) (ha : 3 ≤ a) :
    ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 ≤
      1 / ((a : ℝ) - 2) := by
  rcases le_or_gt a b with hab | hba
  · have hsub : ((Finset.Ico a b).filter Nat.Prime).image (fun q : ℕ => q - 1) ⊆
        Finset.Ico (a - 1) (b - 1) := by
      intro m hm; rcases Finset.mem_image.mp hm with ⟨q, hq, rfl⟩
      have hqico := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hsum_eq : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 =
        ∑ m ∈ ((Finset.Ico a b).filter Nat.Prime).image (fun q : ℕ => q - 1), (1 : ℝ) / (m : ℝ) ^ 2 := by
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun q hq => ?_
        have hqa := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
        rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
      · intro x hx y hy hxy
        have hx1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).1
        have hy1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).1
        dsimp only at hxy; omega
    have hsub_le : ∑ m ∈ ((Finset.Ico a b).filter Nat.Prime).image (fun q : ℕ => q - 1),
          (1 : ℝ) / (m : ℝ) ^ 2 ≤
        ∑ m ∈ Finset.Ico (a - 1) (b - 1), (1 : ℝ) / (m : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hIco := BuchstabSwitching.sum_Ico_inv_sq_le (a - 1) (b - 1) (by omega) (by omega)
    rw [hsum_eq]
    refine (hsub_le.trans hIco).trans_eq ?_
    rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one]; ring
  · simp only [Finset.Ico_eq_empty_of_le hba.le, Finset.filter_empty, Finset.sum_empty]
    have ha3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have : (0 : ℝ) < (a : ℝ) - 2 := by linarith
    positivity

lemma sum_gTot_eq_inv_sub_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, BuchstabSwitching.gTot p = ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) :=
  Finset.sum_congr rfl fun p hp => BuchstabSwitching.gTot_prime (hS p hp)

lemma sum_gTot_sq_eq_inv_pred_sq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (BuchstabSwitching.gTot p) ^ 2 = ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 :=
  Finset.sum_congr rfl fun p hp => by rw [BuchstabSwitching.gTot_prime (hS p hp), one_div_pow]

/-- Verify `AnalyticRangeWitness` against `[a, b)` with `27000 ≤ a < b`, certifying `∑ 1/(q-1) ≤ sqUb` and `π([a,b)) ≤ cntUb`. -/
def checkAnalyticRange (a b : ℕ) (aLogLo aLogHi bLogLo bLogHi sqUb cntUb : Dyadic)
    (w : AnalyticRangeWitness) : Bool :=
  let okHi :=
    if 10 ^ 12 < b then dy6836Ub.ble (w.hiErrUb.mulLb bLogLo)
    else checkSqrtLb (Dyadic.ofNat b) w.bSqrtLb && decide (0 < w.bSqrtLb.m) &&
      dyTwo.ble (w.hiErrUb.mulLb (w.bSqrtLb.mulLb bLogLo))
  let okPi :=
    if !w.piUseSingle then
      (Dyadic.ofNat (b - a)).ble (w.piMainUb.mulLb aLogLo) &&
      ((w.bSqrtUb.mulUb bLogHi).add (w.aSqrtUb.mulUb aLogHi)).ble (w.piRemUb.mulLb dy8PiLo4) &&
      (w.piMainUb.add (w.piRemUb.add dyOne)).ble cntUb
    else
      decide (0 < (bLogLo.subLb dyTwo).m) &&
      (Dyadic.ofNat b).ble (w.piMainUb.mulLb (bLogLo.subLb dyTwo)) &&
      (w.bSqrtUb.mulUb bLogHi).ble (w.piRemUb.mulLb dy8PiLo4) &&
      (w.piMainUb.add (dyLi2Ub.add w.piRemUb)).ble cntUb
  decide (27000 ≤ a) && decide (a < b) && dyThree.blt aLogLo &&
  aLogLo.ble aLogHi && bLogLo.ble bLogHi && dyThree.blt bLogLo &&
  dyOne.ble w.ratioUb && bLogHi.ble (w.ratioUb.mulLb aLogLo) &&
  checkLogDyadic w.ratioUb w.wLL Dyadic.zero w.llRatioUb &&
  checkSqrtUb (Dyadic.ofNat a) w.aSqrtUb &&
  checkSqrtUb (Dyadic.ofNat b) w.bSqrtUb &&
  dy2964Ub.ble (w.loErrUb.mulLb aLogLo) &&
  okHi &&
  dyOne.ble (w.tailPredUb.mulLb (Dyadic.ofNat (a - 1))) &&
  (w.llRatioUb.add (w.hiErrUb.add (w.loErrUb.add w.tailPredUb))).ble sqUb &&
  okPi

lemma checkAnalyticRange_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0) {a b : ℕ}
    {aLogLo aLogHi bLogLo bLogHi sqUb cntUb : Dyadic} {w : AnalyticRangeWitness}
    (haLog : aLogLo.toReal ≤ Real.log (a : ℝ) ∧ Real.log (a : ℝ) ≤ aLogHi.toReal)
    (hbLog : bLogLo.toReal ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ bLogHi.toReal)
    (h : checkAnalyticRange a b aLogLo aLogHi bLogLo bLogHi sqUb cntUb w = true) :
    27000 ≤ a ∧ a < b ∧
      ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤ sqUb.toReal ∧
      (((Finset.Ico a b).filter Nat.Prime).card : ℝ) ≤ cntUb.toReal := by
  unfold checkAnalyticRange at h; dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨ha27, hab, haL3, _, _, hbL3, hrat1, hratMul, hll, hsqA, hsqB, hlo, hhi, htailB, hsqSum, hpi⟩
  have haL_pos : (0 : ℝ) < aLogLo.toReal := by
    have := Dyadic.blt_sound haL3; rw [dyThree_toReal] at this; linarith
  have hbL_gt3 : (3 : ℝ) < bLogLo.toReal := by
    have := Dyadic.blt_sound hbL3; rw [dyThree_toReal] at this; linarith
  have h1_sum : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) =
      (∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / (q : ℝ)) +
        ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun q hq => ?_
    have hq27 : (27000 : ℝ) ≤ (q : ℝ) :=
      by exact_mod_cast ha27.trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  have hM := BuchstabSwitching.mertens_sum_Ico_le hMert.mertensSumBounds
    (by exact_mod_cast (by omega : 2 ≤ a)) (by exact_mod_cast hab : (a : ℝ) < (b : ℝ))
  simp only [Nat.ceil_natCast] at hM
  have hlog_ratio : Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) ≤ w.llRatioUb.toReal := by
    have hrat_pos : 0 < w.ratioUb.toReal := by
      have := Dyadic.ble_sound hrat1; rw [dyOne_toReal] at this; linarith
    have hdiv : Real.log (b : ℝ) / Real.log (a : ℝ) ≤ w.ratioUb.toReal := by
      have hdiv0 := div_le_div₀ bLogHi.toReal_nonneg hbLog.2 haL_pos haLog.1
      have hdiv1 := Dyadic.div_le_of_ble_mulLb le_rfl haL_pos le_rfl hratMul
      exact hdiv0.trans hdiv1
    exact (Real.log_le_log (div_pos (by linarith) (by linarith)) hdiv).trans
      ((checkLogDyadic_sound consts hll).2.trans_eq (by rfl))
  have hlo_err : External.jsMertensLoErr (a : ℝ) ≤ w.loErrUb.toReal := by
    unfold External.jsMertensLoErr
    exact Dyadic.div_le_of_ble_mulLb le_dy2964Ub (lt_of_lt_of_le haL_pos haLog.1) haLog.1 hlo
  have hhi_err : External.jsMertensHiErr (b : ℝ) ≤ w.hiErrUb.toReal := by
    split_ifs at hhi with hb12
    · rw [External.jsMertensHiErr_eq_tail (by exact_mod_cast hb12)]
      exact Dyadic.div_le_of_ble_mulLb le_dy6836Ub (by linarith [hbLog.1]) hbLog.1 hhi
    · simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hhi
      rcases hhi with ⟨hbsLb, _, hhiBle⟩
      have hbr : (27000 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 27000 < b)
      have hlog10 : (10 : ℝ) < Real.log (b : ℝ) :=
        (Real.lt_log_iff_exp_lt (by linarith)).mpr (exp_ten_lt_27000.trans hbr)
      rw [External.jsMertensHiErr_eq_bjv (by exact_mod_cast le_of_not_gt hb12) hlog10]
      have hsqb := checkSqrtLb_sound (by rw [Dyadic.ofNat_toReal]) hbsLb
      have hden_le : (w.bSqrtLb.mulLb bLogLo).toReal ≤ Real.sqrt (b : ℝ) * Real.log (b : ℝ) :=
        (Dyadic.mulLb_le _ _).trans (mul_le_mul hsqb hbLog.1 (by linarith) (Real.sqrt_nonneg _))
      exact Dyadic.div_le_of_ble_mulLb (by rw [dyTwo_toReal])
        (mul_pos (Real.sqrt_pos.mpr (by linarith)) (by linarith)) hden_le hhiBle
  have htail : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤
      w.tailPredUb.toReal := by
    have htp := BuchstabSwitching.sum_Ico_primes_inv_mul_pred_le a b (by omega)
    have ha_sub : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one]
    have ha_pos : (0 : ℝ) < (a : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < a))
    exact htp.trans (Dyadic.div_le_of_ble_mulLb (by rw [dyOne_toReal]) ha_pos
      (by rw [Dyadic.ofNat_toReal, ha_sub]) htailB)
  have hsq_le : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤ sqUb.toReal := by
    have hs1 : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ≤
        Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
          External.jsMertensHiErr (b : ℝ) + External.jsMertensLoErr (a : ℝ) := by convert hM using 2
    have hsum_ble := Dyadic.ble_sound hsqSum
    simp only [Dyadic.add_toReal] at hsum_ble
    linarith only [h1_sum, hs1, hlog_ratio, hlo_err, hhi_err, htail, hsum_ble]
  have hS := hCls.schoenfeld hGRH
  have hpi_b := External.primeCounting_le_of_schoenfeld (x := (b : ℝ)) hS
    (by exact_mod_cast (by omega : 2657 ≤ b))
  have hpi_a := External.le_primeCounting_of_schoenfeld (x := (a : ℝ)) hS
    (by exact_mod_cast (by omega : 2657 ≤ a))
  have hcard_le_pi_diff : (((Finset.Ico a b).filter Nat.Prime).card : ℝ) ≤
      (External.primeCounting (b : ℝ) : ℝ) - (External.primeCounting (a : ℝ) : ℝ) + 1 := by
    have h1 : (Finset.Ico a b).filter Nat.Prime ⊆
        (Finset.range (b + 1)).filter Nat.Prime \ (Finset.range a).filter Nat.Prime := by
      intro p hp; rcases Finset.mem_filter.mp hp with ⟨hpico, hpr⟩
      rw [Finset.mem_Ico] at hpico
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpr⟩,
        fun hm => by have := Finset.mem_range.mp (Finset.mem_filter.mp hm).1; omega⟩
    have hsub : ((Finset.range a).filter Nat.Prime) ⊆ ((Finset.range (b + 1)).filter Nat.Prime) := by
      intro p hp; rcases Finset.mem_filter.mp hp with ⟨hpa, hpr⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hpa; omega), hpr⟩
    have hnat_bound : ((Finset.Ico a b).filter Nat.Prime).card +
        ((Finset.range (a + 1)).filter Nat.Prime).card ≤
        ((Finset.range (b + 1)).filter Nat.Prime).card + 1 := by
      have ha_succ : ((Finset.range (a + 1)).filter Nat.Prime).card ≤
          ((Finset.range a).filter Nat.Prime).card + 1 := by
        have ha_not : a ∉ (Finset.range a).filter Nat.Prime := by simp
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs
        · rw [Finset.card_insert_of_notMem ha_not]
        · omega
      have hc := Finset.card_le_card h1
      rw [Finset.card_sdiff_of_subset hsub] at hc
      have := Finset.card_le_card hsub; omega
    rw [← External.primeCounting_nat b, ← External.primeCounting_nat a] at hnat_bound
    have hr : (((Finset.Ico a b).filter Nat.Prime).card : ℝ) + (External.primeCounting (a : ℝ) : ℝ) ≤
        (External.primeCounting (b : ℝ) : ℝ) + 1 := by exact_mod_cast hnat_bound
    linarith
  have hcard_le_pi_b : (((Finset.Ico a b).filter Nat.Prime).card : ℝ) ≤
      (External.primeCounting (b : ℝ) : ℝ) := by
    have hsub : (Finset.Ico a b).filter Nat.Prime ⊆ (Finset.range (b + 1)).filter Nat.Prime := by
      intro p hp; rcases Finset.mem_filter.mp hp with ⟨hpico, hpr⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [Finset.mem_Ico] at hpico; omega), hpr⟩
    rw [External.primeCounting_nat]; exact_mod_cast Finset.card_le_card hsub
  have hsqrtA : Real.sqrt (a : ℝ) ≤ w.aSqrtUb.toReal := checkSqrtUb_sound (by rw [Dyadic.ofNat_toReal]) hsqA
  have hsqrtB : Real.sqrt (b : ℝ) ≤ w.bSqrtUb.toReal := checkSqrtUb_sound (by rw [Dyadic.ofNat_toReal]) hsqB
  have h8pi_pos : 0 < 8 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have h8pi_le : dy8PiLo4.toReal ≤ 8 * Real.pi := dy8PiLo4_lt.le
  refine ⟨ha27, hab, hsq_le, ?_⟩
  split_ifs at hpi with hpus
  · simp only [Bool.and_eq_true, and_assoc] at hpi
    rcases hpi with ⟨hpm, hpr, hcnt⟩
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 2 ≤ a)
    have habr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
    have hsub_int : External.offsetLogIntegral (b : ℝ) - External.offsetLogIntegral (a : ℝ) =
        ∫ t in (a : ℝ)..(b : ℝ), 1 / Real.log t := by
      unfold External.offsetLogIntegral
      linarith [intervalIntegral.integral_add_adjacent_intervals
        (inv_log_integrable_Icc (le_refl 2) ha2) (inv_log_integrable_Icc ha2 habr)]
    have hint_ub : ∫ t in (a : ℝ)..(b : ℝ), 1 / Real.log t ≤ ((b - a : ℕ) : ℝ) / aLogLo.toReal := by
      calc ∫ t in (a : ℝ)..(b : ℝ), 1 / Real.log t
          ≤ ∫ _ in (a : ℝ)..(b : ℝ), (1 / aLogLo.toReal : ℝ) := by
            refine intervalIntegral.integral_mono_on habr (inv_log_integrable_Icc ha2 habr)
              intervalIntegrable_const fun t ht => one_div_le_one_div_of_le haL_pos
                (haLog.1.trans (Real.log_le_log (by linarith) ht.1))
        _ = ((b - a : ℕ) : ℝ) / aLogLo.toReal := by
            rw [intervalIntegral.integral_const, smul_eq_mul, Nat.cast_sub hab.le]; ring
    have ht1 : ((b - a : ℕ) : ℝ) / aLogLo.toReal ≤ w.piMainUb.toReal :=
      Dyadic.div_le_of_ble_mulLb (by rw [Dyadic.ofNat_toReal]) haL_pos le_rfl hpm
    have hnum2 : Real.sqrt (b : ℝ) * Real.log (b : ℝ) + Real.sqrt (a : ℝ) * Real.log (a : ℝ) ≤
        ((w.bSqrtUb.mulUb bLogHi).add (w.aSqrtUb.mulUb aLogHi)).toReal := by
      rw [Dyadic.add_toReal]
      have hba := (mul_le_mul hsqrtB hbLog.2 (by linarith) w.bSqrtUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
      have haa := (mul_le_mul hsqrtA haLog.2 (by linarith) w.aSqrtUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
      linarith
    have ht2 : (Real.sqrt (b : ℝ) * Real.log (b : ℝ) + Real.sqrt (a : ℝ) * Real.log (a : ℝ)) / (8 * Real.pi) ≤
        w.piRemUb.toReal :=
      Dyadic.div_le_of_ble_mulLb hnum2 h8pi_pos h8pi_le hpr
    have hcnt_r := Dyadic.ble_sound hcnt
    simp only [Dyadic.add_toReal, dyOne_toReal] at hcnt_r
    simp only [External.logIntegral] at hpi_b hpi_a
    have hdiv_add : Real.sqrt (b : ℝ) * Real.log (b : ℝ) / (8 * Real.pi) +
        Real.sqrt (a : ℝ) * Real.log (a : ℝ) / (8 * Real.pi) =
        (Real.sqrt (b : ℝ) * Real.log (b : ℝ) + Real.sqrt (a : ℝ) * Real.log (a : ℝ)) / (8 * Real.pi) :=
      (add_div _ _ _).symm
    linarith only [hcard_le_pi_diff, hpi_b, hpi_a, hsub_int, hint_ub, ht1, ht2, hcnt_r, hdiv_add]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hpi
    rcases hpi with ⟨_, hpm, hpr, hcnt⟩
    have hbr : (27000 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 27000 < b)
    have hexp5 : Real.exp 5 ≤ (b : ℝ) :=
      (Real.exp_le_exp.mpr (by norm_num : (5 : ℝ) ≤ 10)).trans (exp_ten_lt_27000.trans hbr).le
    have hli_lt := BuchstabSwitching.offsetLogIntegral_lt_div_log_sub_two hexp5
    have hsub_eq := Dyadic.subLb_eq (a := bLogLo) (b := dyTwo) (by rw [dyTwo_toReal]; linarith)
    rw [dyTwo_toReal] at hsub_eq
    have hden_le : (bLogLo.subLb dyTwo).toReal ≤ Real.log (b : ℝ) - 2 := by linarith [hbLog.1]
    have ht1 : (b : ℝ) / (Real.log (b : ℝ) - 2) ≤ w.piMainUb.toReal :=
      Dyadic.div_le_of_ble_mulLb (by rw [Dyadic.ofNat_toReal]) (by linarith [hbLog.1]) hden_le hpm
    have hnum2 : Real.sqrt (b : ℝ) * Real.log (b : ℝ) ≤ (w.bSqrtUb.mulUb bLogHi).toReal :=
      (mul_le_mul hsqrtB hbLog.2 (by linarith) w.bSqrtUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
    have ht2 : Real.sqrt (b : ℝ) * Real.log (b : ℝ) / (8 * Real.pi) ≤ w.piRemUb.toReal :=
      Dyadic.div_le_of_ble_mulLb hnum2 h8pi_pos h8pi_le hpr
    have hli2 : consts.li2 ≤ dyLi2Ub.toReal := li2_le_dyLi2Ub consts
    have hcnt_r := Dyadic.ble_sound hcnt
    simp only [Dyadic.add_toReal] at hcnt_r
    simp only [External.logIntegral] at hpi_b
    have hli_eq : External.offsetLogIntegral (b : ℝ) = ∫ t in (2 : ℝ)..(b : ℝ), 1 / Real.log t := rfl
    linarith only [hcard_le_pi_b, hpi_b, hli_lt, hli_eq, ht1, ht2, hli2, hcnt_r]

private lemma ico_split_27000 (u v : ℕ) (hu : u < 27000) (hv : 27000 < v) :
    (Finset.Ico u v).filter Nat.Prime =
      (Finset.Ico u 27000).filter Nat.Prime ∪ (Finset.Ico 27000 v).filter Nat.Prime ∧
      Disjoint ((Finset.Ico u 27000).filter Nat.Prime) ((Finset.Ico 27000 v).filter Nat.Prime) := by
  refine ⟨?_, ?_⟩
  · ext q; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hqu, hqv⟩, hpr⟩
      rcases lt_or_ge q 27000 with hq27 | hq27
      · exact Or.inl ⟨⟨hqu, hq27⟩, hpr⟩
      · exact Or.inr ⟨⟨hq27, hqv⟩, hpr⟩
    · rintro (⟨⟨hqu, hq27⟩, hpr⟩ | ⟨⟨hq27, hqv⟩, hpr⟩)
      · exact ⟨⟨hqu, lt_trans hq27 hv⟩, hpr⟩
      · exact ⟨⟨hu.le.trans hq27, hqv⟩, hpr⟩
  · rw [Finset.disjoint_left]; intro q h1 h2
    have a1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1).2
    have a2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega

/-- Check slice bounds `∑ 1/(q-1) ≤ sqUb` and `π([q0, q1)) ≤ cntUb` using `OddPrimeTree` or `AnalyticRangeWitness`. -/
def checkSlice2abOr2cBounds (q0 q1 : ℕ) (log0Lo log0Hi log1Lo log1Hi sqUb cntUb : Dyadic)
    (anW : Option AnalyticRangeWitness) : Bool :=
  if q1 ≤ q0 then true
  else if q1 ≤ 27000 then
    (exactInvSubOneSumUb q0 q1).ble sqUb && (Dyadic.ofNat (exactPrimeCount q0 q1)).ble cntUb
  else if 27000 ≤ q0 then
    match anW with
    | none => false
    | some aw => checkAnalyticRange q0 q1 log0Lo log0Hi log1Lo log1Hi sqUb cntUb aw
  else
    match anW with
    | none => false
    | some aw =>
      let sqEx := exactInvSubOneSumUb q0 27000
      let cntEx := Dyadic.ofNat (exactPrimeCount q0 27000)
      let sqAn := aw.llRatioUb.add (aw.hiErrUb.add (aw.loErrUb.add aw.tailPredUb))
      let cntAn :=
        if !aw.piUseSingle then aw.piMainUb.add (aw.piRemUb.add dyOne)
        else aw.piMainUb.add (dyLi2Ub.add aw.piRemUb)
      checkAnalyticRange 27000 q1 log27000Lo log27000Hi log1Lo log1Hi sqAn cntAn aw &&
      (sqEx.add sqAn).ble sqUb && (cntEx.add cntAn).ble cntUb

lemma checkSlice2abOr2cBounds_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {q0 q1 : ℕ} {log0Lo log0Hi log1Lo log1Hi sqUb cntUb : Dyadic}
    {anW : Option AnalyticRangeWitness}
    (hLog0 : 27000 ≤ q0 → log0Lo.toReal ≤ Real.log (q0 : ℝ) ∧ Real.log (q0 : ℝ) ≤ log0Hi.toReal)
    (hLog1 : 27000 < q1 → log1Lo.toReal ≤ Real.log (q1 : ℝ) ∧ Real.log (q1 : ℝ) ≤ log1Hi.toReal)
    (h : checkSlice2abOr2cBounds q0 q1 log0Lo log0Hi log1Lo log1Hi sqUb cntUb anW = true) :
    ∑ q ∈ (Finset.Ico q0 q1).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤ sqUb.toReal ∧
      (((Finset.Ico q0 q1).filter Nat.Prime).card : ℝ) ≤ cntUb.toReal := by
  unfold checkSlice2abOr2cBounds at h; split_ifs at h with h1 h2 h3
  · simp [Finset.Ico_eq_empty_of_le h1, sqUb.toReal_nonneg, cntUb.toReal_nonneg]
  · simp only [Bool.and_eq_true] at h
    refine ⟨(sum_inv_sub_one_le_exact h2).trans (Dyadic.ble_sound h.1), ?_⟩
    rw [card_ico_primes_eq_exact h2, ← Dyadic.ofNat_toReal]; exact Dyadic.ble_sound h.2
  · cases anW with
    | none => simp at h
    | some aw =>
      have hs := checkAnalyticRange_sound consts hGRH hCls hMert (hLog0 h3) (hLog1 (by omega)) h
      exact ⟨hs.2.2.1, hs.2.2.2⟩
  · cases anW with
    | none => simp at h
    | some aw =>
      dsimp only at h
      simp only [Bool.and_eq_true, and_assoc] at h
      have hs := checkAnalyticRange_sound consts hGRH hCls hMert (log27000_bounds consts) (hLog1 (by omega)) h.1
      have hsplit := ico_split_27000 q0 q1 (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · rw [hsplit.1, Finset.sum_union hsplit.2]
        have hsq_ex := sum_inv_sub_one_le_exact (q0 := q0) (q1 := 27000) le_rfl
        have hble := Dyadic.ble_sound h.2.1; rw [Dyadic.add_toReal] at hble
        linarith only [hsq_ex, hs.2.2.1, hble]
      · rw [hsplit.1, Finset.card_union_of_disjoint hsplit.2, Nat.cast_add,
          card_ico_primes_eq_exact (q0 := q0) (q1 := 27000) le_rfl]
        have hble := Dyadic.ble_sound h.2.2; rw [Dyadic.add_toReal, Dyadic.ofNat_toReal] at hble
        linarith only [hs.2.2.2, hble]

/-- Check Mertens sums `(s1Ub, s2Ub, piUb)` over `[u, v)` and (when `3 ≤ u ∧ 0 < w.gLb.m`) lower bound `w.gLb ≤ V2 [u, v)`. -/
def checkMertensTailWithLogs (u v : ℕ) (uLogLo uLogHi vLogLo vLogHi : Dyadic)
    (w : MertensTailWitness) : Bool :=
  if v ≤ u then w.gLb.ble dyOne
  else if v ≤ 27000 then
    (exactInvSubOneSumUb u v).ble w.s1Ub &&
    (exactInvPredSqSumUb u v).ble w.s2Ub &&
    decide (exactPrimeCount u v ≤ w.piUb) &&
    (if 3 ≤ u ∧ 0 < w.gLb.m then w.gLb.ble (exactProdOneSubInvPredLb u v) else true)
  else if 27000 ≤ u then
    match w.anW with
    | none => false
    | some aw =>
      checkAnalyticRange u v uLogLo uLogHi vLogLo vLogHi w.s1Ub (Dyadic.ofNat w.piUb) aw &&
      dyOne.ble (w.s2Ub.mulLb (Dyadic.ofNat (u - 2))) &&
      (if 0 < w.gLb.m then
        (Dyadic.ofNat (u - 1)).ble (w.c2Ub.mulLb (Dyadic.ofNat (2 * (u - 2)))) &&
        let (okExp, eUb) := expUbDyadic (w.s1Ub.add (w.c2Ub.mulUb w.s2Ub))
        okExp && (w.gLb.mulUb eUb).ble dyOne
       else true)
  else
    match w.anW with
    | none => false
    | some aw =>
      let s1Ex := exactInvSubOneSumUb u 27000
      let s2Ex := exactInvPredSqSumUb u 27000
      let cntEx := exactPrimeCount u 27000
      let s1An := aw.llRatioUb.add (aw.hiErrUb.add (aw.loErrUb.add aw.tailPredUb))
      let cntAn :=
        if !aw.piUseSingle then aw.piMainUb.add (aw.piRemUb.add dyOne)
        else aw.piMainUb.add (dyLi2Ub.add aw.piRemUb)
      checkAnalyticRange 27000 v log27000Lo log27000Hi vLogLo vLogHi s1An cntAn aw &&
      (s1Ex.add s1An).ble w.s1Ub &&
      (s2Ex.add (w.s2Ub.subLb s2Ex)).ble w.s2Ub &&
      dyOne.ble ((w.s2Ub.subLb s2Ex).mulLb (Dyadic.ofNat 26998)) &&
      ((Dyadic.ofNat cntEx).add cntAn).ble (Dyadic.ofNat w.piUb) &&
      (if 3 ≤ u ∧ 0 < w.gLb.m then
        (Dyadic.ofNat 26999).ble (w.c2Ub.mulLb (Dyadic.ofNat 53996)) &&
        let (okExp, eUb) := expUbDyadic (s1An.add (w.c2Ub.mulUb (w.s2Ub.subLb s2Ex)))
        okExp && (w.gLb.mulUb eUb).ble (exactProdOneSubInvPredLb u 27000)
       else true)

lemma checkMertensTailWithLogs_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {u v : ℕ} {uLogLo uLogHi vLogLo vLogHi : Dyadic} {w : MertensTailWitness}
    (hLogU : 27000 ≤ u → uLogLo.toReal ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ uLogHi.toReal)
    (hLogV : 27000 < v → vLogLo.toReal ≤ Real.log (v : ℝ) ∧ Real.log (v : ℝ) ≤ vLogHi.toReal)
    (h : checkMertensTailWithLogs u v uLogLo uLogHi vLogLo vLogHi w = true) :
    ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, BuchstabSwitching.gTot p ≤ w.s1Ub.toReal ∧
      ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, (BuchstabSwitching.gTot p) ^ 2 ≤ w.s2Ub.toReal ∧
      (((Finset.Ico u v).filter Nat.Prime).card : ℝ) ≤ (w.piUb : ℝ) ∧
      (3 ≤ u → w.gLb.toReal ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico u v).filter Nat.Prime)) := by
  have hpr : ∀ S : Finset ℕ, S ⊆ (Finset.Ico u v).filter Nat.Prime → ∀ p ∈ S, p.Prime :=
    fun _ hS p hp => (Finset.mem_filter.mp (hS hp)).2
  rw [sum_gTot_eq_inv_sub_one _ (hpr _ Finset.Subset.rfl),
    sum_gTot_sq_eq_inv_pred_sq _ (hpr _ Finset.Subset.rfl)]
  have hv2_eq : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 3 ≤ p) →
      BuchstabSwitching.V2 BuchstabSwitching.gTot S = ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1)) := fun S hS => by
    unfold BuchstabSwitching.V2
    exact Finset.prod_congr rfl fun p hp => by rw [BuchstabSwitching.gTot_prime (hS p hp).1]
  have hv2_nn : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 0 ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot S :=
    fun S hS => Finset.prod_nonneg fun p hp => by
      rw [BuchstabSwitching.gTot_prime (hS p hp)]
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  unfold checkMertensTailWithLogs at h
  by_cases h1 : v ≤ u
  · simp only [h1, ↓reduceIte] at h
    simp [Finset.Ico_eq_empty_of_le h1, w.s1Ub.toReal_nonneg, w.s2Ub.toReal_nonneg]
    intro _; exact (Dyadic.ble_sound h).trans_eq dyOne_toReal
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : v ≤ 27000
    · simp only [h2, ↓reduceIte] at h
      rcases (Bool.and_eq_true _ _).mp h with ⟨h123, hgv⟩
      rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hpi_b⟩
      rcases (Bool.and_eq_true _ _).mp h12 with ⟨hs1, hs2⟩
      have hpi : exactPrimeCount u v ≤ w.piUb := decide_eq_true_eq.mp hpi_b
      refine ⟨(sum_inv_sub_one_le_exact h2).trans (Dyadic.ble_sound hs1),
        (sum_inv_pred_sq_le_exact h2).trans (Dyadic.ble_sound hs2),
        by rw [card_ico_primes_eq_exact h2]; exact_mod_cast hpi, fun hu3 => ?_⟩
      rw [hv2_eq _ (fun p hp => ⟨(Finset.mem_filter.mp hp).2, hu3.trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1⟩)]
      split_ifs at hgv with hgpos
      · exact (Dyadic.ble_sound hgv).trans (exactProdOneSubInvPredLb_le hu3 h2)
      · have hm0 : w.gLb.m = 0 := Nat.eq_zero_of_not_pos fun hpos => hgpos ⟨hu3, hpos⟩
        rw [Dyadic.toReal_eq_zero_of_m hm0]
        exact Finset.prod_nonneg fun p hp => by
          have hp3 := hu3.trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
          have hp1 : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
            rw [div_le_one (sub_pos.mpr (by exact_mod_cast (by omega : 1 < p)))]
            have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 2 ≤ p)
            linarith
          exact sub_nonneg.mpr hp1
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : 27000 ≤ u
      · simp only [h3, ↓reduceIte] at h
        cases haw : w.anW with
        | none => rw [haw] at h; simp at h
        | some aw =>
          rw [haw] at h
          rcases (Bool.and_eq_true _ _).mp h with ⟨h12, hgv⟩
          rcases (Bool.and_eq_true _ _).mp h12 with ⟨han, hs2⟩
          have ha := checkAnalyticRange_sound consts hGRH hCls hMert (hLogU h3) (hLogV (by omega)) han
          have hs2_le : ∑ q ∈ (Finset.Ico u v).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 ≤ w.s2Ub.toReal := by
            have htp := sum_Ico_primes_inv_pred_sq_le u v (by omega)
            have hu2 : ((u - 2 : ℕ) : ℝ) = (u : ℝ) - 2 := by rw [Nat.cast_sub (by omega : 2 ≤ u), Nat.cast_two]
            have hu_pos : (0 : ℝ) < (u : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast (by omega : 2 < u))
            exact htp.trans (Dyadic.div_le_of_ble_mulLb (by rw [dyOne_toReal]) hu_pos
              (by rw [Dyadic.ofNat_toReal, hu2]) hs2)
          refine ⟨ha.2.2.1, hs2_le, by simpa [Dyadic.ofNat_toReal] using ha.2.2.2, fun hu3 => ?_⟩
          split_ifs at hgv with hgpos
          · rcases (Bool.and_eq_true _ _).mp hgv with ⟨hc2, hexp_all⟩
            rcases (Bool.and_eq_true _ _).mp hexp_all with ⟨hokExp, hmul1⟩
            have hc2_le : 1 / (2 * (1 - 1 / ((u : ℝ) - 1))) ≤ w.c2Ub.toReal := by
              have heq : 1 / (2 * (1 - 1 / ((u : ℝ) - 1))) = ((u - 1 : ℕ) : ℝ) / ((2 * (u - 2) : ℕ) : ℝ) := by
                rw [Nat.cast_sub (by omega : 1 ≤ u), Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ u),
                  Nat.cast_one, Nat.cast_ofNat]
                have hu_r : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
                have h1' : (u : ℝ) - 1 ≠ 0 := by linarith
                have h2' : (u : ℝ) - 2 ≠ 0 := by linarith
                have h1m : 1 - 1 / ((u : ℝ) - 1) = ((u : ℝ) - 2) / ((u : ℝ) - 1) := by
                  field_simp [h1']; ring
                rw [h1m]; field_simp [h1', h2']
              have hden_pos : (0 : ℝ) < ((2 * (u - 2) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * (u - 2))
              rw [heq]
              exact Dyadic.div_le_of_ble_mulLb (by rw [Dyadic.ofNat_toReal]) hden_pos
                (by rw [Dyadic.ofNat_toReal]) hc2
            have hS1 : ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, BuchstabSwitching.gTot p ≤ w.s1Ub.toReal := by
              rw [sum_gTot_eq_inv_sub_one _ (hpr _ Finset.Subset.rfl)]; exact ha.2.2.1
            have hS2 : ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, (BuchstabSwitching.gTot p) ^ 2 ≤ w.s2Ub.toReal := by
              rw [sum_gTot_sq_eq_inv_pred_sq _ (hpr _ Finset.Subset.rfl)]; exact hs2_le
            have hbonf := BuchstabSwitching.analytic_bonf_V2_lb (P₂ := (Finset.Ico u v).filter Nat.Prime)
              (p_min := u) (by omega) (fun p hp => ⟨(Finset.mem_filter.mp hp).2,
                (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1⟩) hS1 hS2
            set eUb := (expUbDyadic (w.s1Ub.add (w.c2Ub.mulUb w.s2Ub))).2
            have hexp := (expUbDyadic_sound hokExp).1
            have he_pos : 0 < eUb.toReal := lt_of_lt_of_le (Real.exp_pos _) hexp
            have hmul_le : w.gLb.toReal * eUb.toReal ≤ 1 :=
              (Dyadic.le_mulUb w.gLb eUb).trans ((Dyadic.ble_sound hmul1).trans_eq dyOne_toReal)
            have hinv : w.gLb.toReal ≤ 1 / eUb.toReal := (le_div_iff₀ he_pos).mpr hmul_le
            have harg : -(w.s1Ub.add (w.c2Ub.mulUb w.s2Ub)).toReal ≤
                -(w.s1Ub.toReal + (1 / (2 * (1 - 1 / ((u : ℝ) - 1)))) * w.s2Ub.toReal) := by
              rw [Dyadic.add_toReal]
              have hc2s := (mul_le_mul_of_nonneg_right hc2_le w.s2Ub.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
              linarith
            exact hinv.trans (by
              rw [one_div]; exact (inv_anti₀ (Real.exp_pos _) hexp).trans
                (by rw [← Real.exp_neg]; exact (Real.exp_le_exp.mpr harg).trans hbonf))
          · have hm0 : w.gLb.m = 0 := Nat.eq_zero_of_not_pos hgpos
            rw [Dyadic.toReal_eq_zero_of_m hm0]
            exact hv2_nn _ (hpr _ Finset.Subset.rfl)
      · simp only [h3, ↓reduceIte] at h
        cases haw : w.anW with
        | none => rw [haw] at h; simp at h
        | some aw =>
          rw [haw] at h
          rcases (Bool.and_eq_true _ _).mp h with ⟨h12345, hgv⟩
          rcases (Bool.and_eq_true _ _).mp h12345 with ⟨h1234, hpi⟩
          rcases (Bool.and_eq_true _ _).mp h1234 with ⟨h123, hs2An⟩
          rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hs2Add⟩
          rcases (Bool.and_eq_true _ _).mp h12 with ⟨han, hs1⟩
          have ha := checkAnalyticRange_sound consts hGRH hCls hMert (log27000_bounds consts) (hLogV (by omega)) han
          have hsplit := ico_split_27000 u v (by omega) (by omega)
          have hs1_ex := sum_inv_sub_one_le_exact (q0 := u) (q1 := 27000) le_rfl
          have hs1_le : ∑ q ∈ (Finset.Ico u v).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤ w.s1Ub.toReal := by
            rw [hsplit.1, Finset.sum_union hsplit.2]
            have hb := Dyadic.ble_sound hs1; rw [Dyadic.add_toReal] at hb
            linarith only [hs1_ex, ha.2.2.1, hb]
          set s2Ex := exactInvPredSqSumUb u 27000
          have hs2_ex := sum_inv_pred_sq_le_exact (q0 := u) (q1 := 27000) le_rfl
          have hs2_an : ∑ q ∈ (Finset.Ico 27000 v).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 ≤
              (w.s2Ub.subLb s2Ex).toReal := by
            have htp := sum_Ico_primes_inv_pred_sq_le 27000 v (by norm_num)
            have hpos : (0 : ℝ) < ((27000 : ℕ) : ℝ) - 2 := by norm_num
            exact htp.trans (Dyadic.div_le_of_ble_mulLb (by rw [dyOne_toReal]) hpos
              (by rw [Dyadic.ofNat_toReal]; norm_num) hs2An)
          have hs2_le : ∑ q ∈ (Finset.Ico u v).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 ≤ w.s2Ub.toReal := by
            rw [hsplit.1, Finset.sum_union hsplit.2]
            have hb := Dyadic.ble_sound hs2Add; rw [Dyadic.add_toReal] at hb
            linarith only [hs2_ex, hs2_an, hb]
          have hcnt_le : (((Finset.Ico u v).filter Nat.Prime).card : ℝ) ≤ (w.piUb : ℝ) := by
            rw [hsplit.1, Finset.card_union_of_disjoint hsplit.2, Nat.cast_add,
              card_ico_primes_eq_exact (q0 := u) (q1 := 27000) le_rfl]
            have hpi_r := Dyadic.ble_sound hpi
            rw [Dyadic.add_toReal, Dyadic.ofNat_toReal, Dyadic.ofNat_toReal] at hpi_r
            linarith only [ha.2.2.2, hpi_r]
          refine ⟨hs1_le, hs2_le, hcnt_le, fun hu3 => ?_⟩
          split_ifs at hgv with hgpos
          · rcases (Bool.and_eq_true _ _).mp hgv with ⟨hc2, hexp_all⟩
            rcases (Bool.and_eq_true _ _).mp hexp_all with ⟨hokExp, hmulEx⟩
            have hc2_le : 1 / (2 * (1 - 1 / ((27000 : ℝ) - 1))) ≤ w.c2Ub.toReal := by
              have heq : 1 / (2 * (1 - 1 / ((27000 : ℝ) - 1))) = ((26999 : ℕ) : ℝ) / ((53996 : ℕ) : ℝ) := by norm_num
              have hden_pos : (0 : ℝ) < ((53996 : ℕ) : ℝ) := by norm_num
              rw [heq]
              exact Dyadic.div_le_of_ble_mulLb (by rw [Dyadic.ofNat_toReal]) hden_pos
                (by rw [Dyadic.ofNat_toReal]) hc2
            set s1An := aw.llRatioUb.add (aw.hiErrUb.add (aw.loErrUb.add aw.tailPredUb))
            have hS1_an : ∑ p ∈ (Finset.Ico 27000 v).filter Nat.Prime, BuchstabSwitching.gTot p ≤ s1An.toReal := by
              rw [sum_gTot_eq_inv_sub_one _ (fun p hp => (Finset.mem_filter.mp hp).2)]; exact ha.2.2.1
            have hS2_an : ∑ p ∈ (Finset.Ico 27000 v).filter Nat.Prime, (BuchstabSwitching.gTot p) ^ 2 ≤
                (w.s2Ub.subLb s2Ex).toReal := by
              rw [sum_gTot_sq_eq_inv_pred_sq _ (fun p hp => (Finset.mem_filter.mp hp).2)]; exact hs2_an
            have hbonf := BuchstabSwitching.analytic_bonf_V2_lb (P₂ := (Finset.Ico 27000 v).filter Nat.Prime)
              (p_min := 27000) (by norm_num) (fun p hp => ⟨(Finset.mem_filter.mp hp).2,
                (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1⟩) hS1_an hS2_an
            set eUb := (expUbDyadic (s1An.add (w.c2Ub.mulUb (w.s2Ub.subLb s2Ex)))).2
            have hexp := (expUbDyadic_sound hokExp).1
            have he_pos : 0 < eUb.toReal := lt_of_lt_of_le (Real.exp_pos _) hexp
            have hmul_le : w.gLb.toReal * eUb.toReal ≤ (exactProdOneSubInvPredLb u 27000).toReal :=
              (Dyadic.le_mulUb w.gLb eUb).trans (Dyadic.ble_sound hmulEx)
            have hV_ex : (exactProdOneSubInvPredLb u 27000).toReal ≤
                BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico u 27000).filter Nat.Prime) := by
              rw [hv2_eq _ (fun p hp => ⟨(Finset.mem_filter.mp hp).2,
                hu3.trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1⟩)]
              exact exactProdOneSubInvPredLb_le hu3 le_rfl
            have hV_split : BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico u v).filter Nat.Prime) =
                BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico u 27000).filter Nat.Prime) *
                  BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico 27000 v).filter Nat.Prime) := by
              rw [hsplit.1]; unfold BuchstabSwitching.V2; exact Finset.prod_union hsplit.2
            have harg : -(s1An.add (w.c2Ub.mulUb (w.s2Ub.subLb s2Ex))).toReal ≤
                -(s1An.toReal + (1 / (2 * (1 - 1 / ((27000 : ℝ) - 1)))) * (w.s2Ub.subLb s2Ex).toReal) := by
              rw [Dyadic.add_toReal]
              have hc2s := (mul_le_mul_of_nonneg_right hc2_le (w.s2Ub.subLb s2Ex).toReal_nonneg).trans (Dyadic.le_mulUb _ _)
              linarith
            have hV_an : 1 / eUb.toReal ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico 27000 v).filter Nat.Prime) := by
              rw [one_div]; refine (inv_anti₀ (Real.exp_pos _) hexp).trans ?_
              rw [← Real.exp_neg]; exact (Real.exp_le_exp.mpr harg).trans hbonf
            rw [hV_split]
            calc w.gLb.toReal ≤ (exactProdOneSubInvPredLb u 27000).toReal * (1 / eUb.toReal) :=
                  by rw [mul_one_div, le_div_iff₀ he_pos]; exact hmul_le
              _ ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico u 27000).filter Nat.Prime) *
                    BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico 27000 v).filter Nat.Prime) :=
                  mul_le_mul hV_ex hV_an (by positivity)
                    (hv2_nn _ (fun p hp => (Finset.mem_filter.mp hp).2))
          · have hm0 : w.gLb.m = 0 := Nat.eq_zero_of_not_pos fun hpos => hgpos ⟨hu3, hpos⟩
            rw [Dyadic.toReal_eq_zero_of_m hm0]
            exact hv2_nn _ (hpr _ Finset.Subset.rfl)

/-- Verify `vLb ≤ VN 2 z` using `exactProdOneSubInvPredLb 3 z` (`z ≤ 27000`) or `vPrefix27000Lb` + `vFullW`. -/
def checkVFullLb2c (z : ℕ) (zLogLo zLogHi vLb : Dyadic) (vW : Option MertensTailWitness) : Bool :=
  if z ≤ 27000 then vLb.ble (exactProdOneSubInvPredLb 3 z)
  else
    match vW with
    | none => false
    | some tw =>
      decide (0 < tw.gLb.m) &&
      checkMertensTailWithLogs 27000 z log27000Lo log27000Hi zLogLo zLogHi tw &&
      vLb.ble (vPrefix27000Lb.mulLb tw.gLb)

lemma checkVFullLb2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {z : ℕ} {zLogLo zLogHi vLb : Dyadic} {vW : Option MertensTailWitness}
    (hzLog : 27000 < z → zLogLo.toReal ≤ Real.log (z : ℝ) ∧ Real.log (z : ℝ) ≤ zLogHi.toReal)
    (h : checkVFullLb2c z zLogLo zLogHi vLb vW = true) :
    vLb.toReal ≤ External.VN 2 z := by
  unfold checkVFullLb2c at h; split_ifs at h with hz
  · exact (Dyadic.ble_sound h).trans (exactProdOneSubInvPredLb_le_VN_two hz)
  · cases vW with
    | none => simp at h
    | some tw =>
      have hz27 : 27000 < z := lt_of_not_ge hz
      simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
      rcases h with ⟨_, htail, hble⟩
      have hmt := (checkMertensTailWithLogs_sound consts hGRH hCls hMert
        (fun _ => log27000_bounds consts) hzLog htail).2.2.2 (by norm_num)
      have hdisj : Disjoint (BuchstabSwitching.fullOddPrimesBelow 27000) ((Finset.Ico 27000 z).filter Nat.Prime) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        have a1 := (BuchstabSwitching.fullOddPrimesBelow_mem_iff.mp h1).1
        have a2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega
      have hunion : BuchstabSwitching.fullOddPrimesBelow z =
          BuchstabSwitching.fullOddPrimesBelow 27000 ∪ (Finset.Ico 27000 z).filter Nat.Prime := by
        ext p; simp only [Finset.mem_union, BuchstabSwitching.fullOddPrimesBelow_mem_iff,
          Finset.mem_filter, Finset.mem_Ico]
        constructor
        · rintro ⟨hpz, hpr, hp2⟩; by_cases hp27 : p < 27000
          · exact Or.inl ⟨hp27, hpr, hp2⟩
          · exact Or.inr ⟨⟨by omega, hpz⟩, hpr⟩
        · rintro (⟨hp27, hpr, hp2⟩ | ⟨⟨hp27, hpz⟩, hpr⟩)
          · exact ⟨lt_trans hp27 hz27, hpr, hp2⟩
          · exact ⟨hpz, hpr, by omega⟩
      have hV_split : External.VN 2 z = External.VN 2 27000 *
          BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico 27000 z).filter Nat.Prime) := by
        rw [← BuchstabSwitching.V2_gTot_fullOddPrimesBelow_eq_VN_two z,
          ← BuchstabSwitching.V2_gTot_fullOddPrimesBelow_eq_VN_two 27000, hunion]
        exact Finset.prod_union hdisj
      have hprod_le : (vPrefix27000Lb.mulLb tw.gLb).toReal ≤ External.VN 2 z := by
        rw [hV_split]
        exact (Dyadic.mulLb_le _ _).trans (mul_le_mul vPrefix27000Lb_le_VN_two hmt
          tw.gLb.toReal_nonneg (External.VN_nonneg 2 27000))
      exact (Dyadic.ble_sound hble).trans hprod_le

end

end BuchstabSwitching.SieveInst
