import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstEpdLi
import BuchstabSwitching.Sieve.Regime2SlabBridge.LowerAndMaster
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import Mathlib.Tactic

/-!
# Certified Slice, Mertens Tail, and `vFullLb2c` Bounds for Regime 2 Slab Instantiation

Provides computable `Bool` checkers and soundness theorems (against `CertifiedConstants`,
`ClassicalPrimePremises consts.li2`, and `MertensPrimeSumPremise consts.M0`):
- `checkSlice2abOr2cBounds`, `checkMertensTailSums`, `checkVFullLb2c`;
- `checkEpdUb`, `checkLiRatioUb` (re-exported via `SlabCertInstEpdLi`).
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

/-! ## 2. Certified Slice, Mertens Tail, and `vFullLb2c` Checkers -/

private lemma exp_ten_lt_27000 : Real.exp 10 < (27000 : ℝ) := by
  have hpow := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num : 10 ≠ 0)
  rw [← Real.exp_natCast_mul] at hpow
  norm_num at hpow; linarith

private lemma inv_log_integrable_Icc {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  refine (ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono fun t ht => by
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht; exact ne_of_gt (by linarith)) fun t ht => by
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht; exact (Real.log_pos (by linarith)).ne').intervalIntegrable

private lemma sum_Ico_primes_inv_pred_sq_le (a b : ℕ) (ha : 3 ≤ a) :
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

private def analyticSliceAux (a b : ℕ) (aLogLo aLogHi bLogLo bLogHi : SciNat) :
    Bool × SciNat × SciNat × SciNat :=
  let ratioUb := divUbSig bLogHi aLogLo 24
  let (okLL, _, llRatioUb) := sciLogBounds ratioUb
  let (okSa, _, aSqrtUb) := sqrtSciBounds a 18
  let (okSb2, _, bSqrtUb) := sqrtSciBounds b 18
  let (okSb, bSqrtLb, _) := sqrtSciBounds b 12
  let okBase := decide (27000 ≤ a) && decide (a < b) && sci3.blt aLogLo &&
    aLogLo.ble aLogHi && bLogLo.ble bLogHi && sci3.blt bLogLo &&
    sci1.ble ratioUb && okLL && okSa && okSb2
  if !okBase then (false, (⟨0, 0⟩ : SciNat), (⟨0, 0⟩ : SciNat), (⟨0, 0⟩ : SciNat))
  else
    let loErrUb := divUbSig sci2964 aLogLo 24
    let (okHi, hiErrUb) :=
      if 10 ^ 12 < b then (true, divUbSig sci6836 bLogLo 24)
      else (okSb && decide (0 < bSqrtLb.m), divUbSig sci2 (bSqrtLb.mul bLogLo) 24)
    let tailPredUb := divUbSig sci1 (SciNat.ofNat (a - 1)) 24
    let sqUb := llRatioUb.add (hiErrUb.add (loErrUb.add tailPredUb))
    let piDiffUb := (divUbSig (SciNat.ofNat (b - a)) aLogLo 24).add
      ((divUbSig ((bSqrtUb.mul bLogHi).add (aSqrtUb.mul aLogHi)) (sci8.mul piLo4) 24).add sci1)
    let piSingleUb := (divUbSig (SciNat.ofNat b) (bLogLo.subLb sci2) 24).add
      (sciLi2Ub.add (divUbSig (bSqrtUb.mul bLogHi) (sci8.mul piLo4) 24))
    (okHi, sqUb, piDiffUb, piSingleUb)

private lemma analyticSliceAux_sq_sound (consts : External.CertifiedConstants)
    (hMert : External.MertensPrimeSumPremise consts.M0) {a b : ℕ}
    {aLogLo aLogHi bLogLo bLogHi : SciNat}
    (haLog : aLogLo.toReal ≤ Real.log (a : ℝ) ∧ Real.log (a : ℝ) ≤ aLogHi.toReal)
    (hbLog : bLogLo.toReal ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ bLogHi.toReal)
    (h : (analyticSliceAux a b aLogLo aLogHi bLogLo bLogHi).1 = true) :
    27000 ≤ a ∧ a < b ∧
      ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤
        (analyticSliceAux a b aLogLo aLogHi bLogLo bLogHi).2.1.toReal := by
  cases hok : decide (27000 ≤ a) && decide (a < b) && sci3.blt aLogLo &&
      aLogLo.ble aLogHi && bLogLo.ble bLogHi && sci3.blt bLogLo &&
      sci1.ble (divUbSig bLogHi aLogLo 24) && (sciLogBounds (divUbSig bLogHi aLogLo 24)).1 &&
      (sqrtSciBounds a 18).1 && (sqrtSciBounds b 18).1 with
  | false =>
    unfold analyticSliceAux at h
    dsimp only at h
    simp [hok] at h
  | true =>
    unfold analyticSliceAux at h ⊢
    dsimp only at h ⊢
    simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha27, hab⟩, haL3⟩, _⟩, _⟩, hbL3⟩, _⟩, hll_ok⟩, _⟩, _⟩
    set ratioUb := divUbSig bLogHi aLogLo 24
    refine ⟨ha27, hab, ?_⟩
    have h3r : sci3.toReal = 3 := by unfold sci3 SciNat.toReal; norm_num
    have haL_pos : (0 : ℝ) < aLogLo.toReal := by have := SciProofs.blt_sound haL3; linarith
    have hbL_pos : (0 : ℝ) < bLogLo.toReal := by have := SciProofs.blt_sound hbL3; linarith
    have h1_sum : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) =
        (∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / (q : ℝ)) +
          ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun q hq => ?_
      have hq27 : (27000 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast ha27.trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
      have hq0 : (q : ℝ) ≠ 0 := by linarith
      have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    have hM := BuchstabSwitching.mertens_sum_Ico_le hMert.mertensSumBounds
      (by exact_mod_cast (by omega : 2 ≤ a)) (by exact_mod_cast hab : (a : ℝ) < (b : ℝ))
    simp only [Nat.ceil_natCast] at hM
    have hlog_ratio : Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) ≤
        (sciLogBounds ratioUb).2.2.toReal := by
      have hdiv : Real.log (b : ℝ) / Real.log (a : ℝ) ≤ ratioUb.toReal :=
        (div_le_div₀ (SciNat.toReal_nonneg _) hbLog.2 haL_pos haLog.1).trans (divUbSig_le bLogHi aLogLo 24)
      exact (Real.log_le_log (div_pos (by linarith) (by linarith)) hdiv).trans
        (sciLogBounds_sound consts hll_ok).2
    have hlo_err : External.jsMertensLoErr (a : ℝ) ≤ (divUbSig sci2964 aLogLo 24).toReal := by
      unfold External.jsMertensLoErr
      have hc : (2.964e-6 : ℝ) ≤ sci2964.toReal := by unfold sci2964 SciNat.toReal; norm_num
      exact (div_le_div₀ (SciNat.toReal_nonneg _) hc haL_pos haLog.1).trans (divUbSig_le sci2964 aLogLo 24)
    have hhi_err : External.jsMertensHiErr (b : ℝ) ≤
        (if 10 ^ 12 < b then (true, divUbSig sci6836 bLogLo 24)
         else ((sqrtSciBounds b 12).1 && decide (0 < (sqrtSciBounds b 12).2.1.m),
           divUbSig sci2 ((sqrtSciBounds b 12).2.1.mul bLogLo) 24)).2.toReal := by
      split_ifs at h ⊢ with hb12
      · rw [External.jsMertensHiErr_eq_tail (by exact_mod_cast hb12)]
        have hc : (6.836e-6 : ℝ) ≤ sci6836.toReal := by unfold sci6836 SciNat.toReal; norm_num
        exact (div_le_div₀ (SciNat.toReal_nonneg _) hc hbL_pos hbLog.1).trans (divUbSig_le sci6836 bLogLo 24)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have hbr : (27000 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 27000 < b)
        have hlog10 : (10 : ℝ) < Real.log (b : ℝ) :=
          (Real.lt_log_iff_exp_lt (by linarith)).mpr (exp_ten_lt_27000.trans hbr)
        rw [External.jsMertensHiErr_eq_bjv (by exact_mod_cast le_of_not_gt hb12) hlog10]
        have hsqb := (sqrtSciBounds_sound h.1).1
        have hsqb_pos : 0 < (sqrtSciBounds b 12).2.1.toReal := by
          unfold SciNat.toReal; exact div_pos (by exact_mod_cast h.2) (by positivity)
        have hden := mul_le_mul hsqb hbLog.1 hbL_pos.le (Real.sqrt_nonneg _)
        have h2r : (2 : ℝ) ≤ sci2.toReal := by unfold sci2 SciNat.toReal; norm_num
        have hd := div_le_div₀ (SciNat.toReal_nonneg _) h2r (mul_pos hsqb_pos hbL_pos) hden
        have hdiv := divUbSig_le sci2 ((sqrtSciBounds b 12).2.1.mul bLogLo) 24
        rw [SciProofs.mul_toReal] at hdiv; exact hd.trans hdiv
    have htail : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤
        (divUbSig sci1 (SciNat.ofNat (a - 1)) 24).toReal := by
      have htp := BuchstabSwitching.sum_Ico_primes_inv_mul_pred_le a b (by omega)
      have ha_sub : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one]
      have h1r : sci1.toReal = 1 := by unfold sci1 SciNat.toReal; norm_num
      have hd := divUbSig_le sci1 (SciNat.ofNat (a - 1)) 24
      rw [h1r, SciProofs.ofNat_toReal, ha_sub] at hd
      exact htp.trans hd
    have hM' : ∑ q ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / (q : ℝ) ≤
        Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
          External.jsMertensHiErr (b : ℝ) + External.jsMertensLoErr (a : ℝ) := by
      convert hM using 2
    rw [h1_sum]; simp only [SciProofs.add_toReal]
    have hstep1 := add_le_add hM' htail
    have hstep2 : Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
        External.jsMertensHiErr (b : ℝ) + External.jsMertensLoErr (a : ℝ) +
        (divUbSig sci1 (SciNat.ofNat (a - 1)) 24).toReal ≤
        (sciLogBounds ratioUb).2.2.toReal +
          ((if 10 ^ 12 < b then (true, divUbSig sci6836 bLogLo 24)
            else ((sqrtSciBounds b 12).1 && decide (0 < (sqrtSciBounds b 12).2.1.m),
              divUbSig sci2 ((sqrtSciBounds b 12).2.1.mul bLogLo) 24)).2.toReal +
            ((divUbSig sci2964 aLogLo 24).toReal +
              (divUbSig sci1 (SciNat.ofNat (a - 1)) 24).toReal)) := by
      have h12 : Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) +
          External.jsMertensHiErr (b : ℝ) + External.jsMertensLoErr (a : ℝ) ≤
          (sciLogBounds ratioUb).2.2.toReal +
            ((if 10 ^ 12 < b then (true, divUbSig sci6836 bLogLo 24)
              else ((sqrtSciBounds b 12).1 && decide (0 < (sqrtSciBounds b 12).2.1.m),
                divUbSig sci2 ((sqrtSciBounds b 12).2.1.mul bLogLo) 24)).2.toReal +
              (divUbSig sci2964 aLogLo 24).toReal) := by
        convert add_le_add (add_le_add hlog_ratio hhi_err) hlo_err using 1
        ring
      linarith only [h12]
    exact hstep1.trans hstep2

private lemma analyticSliceAux_cnt_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2) {a b : ℕ}
    {aLogLo aLogHi bLogLo bLogHi : SciNat}
    (haLog : aLogLo.toReal ≤ Real.log (a : ℝ) ∧ Real.log (a : ℝ) ≤ aLogHi.toReal)
    (hbLog : bLogLo.toReal ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ bLogHi.toReal)
    (h : (analyticSliceAux a b aLogLo aLogHi bLogLo bLogHi).1 = true) :
    (((Finset.Ico a b).filter Nat.Prime).card : ℝ) ≤
        (analyticSliceAux a b aLogLo aLogHi bLogLo bLogHi).2.2.1.toReal ∧
      (((Finset.Ico a b).filter Nat.Prime).card : ℝ) ≤
        (analyticSliceAux a b aLogLo aLogHi bLogLo bLogHi).2.2.2.toReal := by
  cases hok : decide (27000 ≤ a) && decide (a < b) && sci3.blt aLogLo &&
      aLogLo.ble aLogHi && bLogLo.ble bLogHi && sci3.blt bLogLo &&
      sci1.ble (divUbSig bLogHi aLogLo 24) && (sciLogBounds (divUbSig bLogHi aLogLo 24)).1 &&
      (sqrtSciBounds a 18).1 && (sqrtSciBounds b 18).1 with
  | false =>
    unfold analyticSliceAux at h
    dsimp only at h
    simp [hok] at h
  | true =>
    unfold analyticSliceAux at h ⊢
    dsimp only at h ⊢
    simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha27, hab⟩, haL3⟩, _⟩, _⟩, hbL3⟩, _⟩, _⟩, hsqA⟩, hsqB⟩
    have h3r : sci3.toReal = 3 := by unfold sci3 SciNat.toReal; norm_num
    have haL_pos : (0 : ℝ) < aLogLo.toReal := by have := SciProofs.blt_sound haL3; linarith
    have hbL_gt3 : (3 : ℝ) < bLogLo.toReal := by have := SciProofs.blt_sound hbL3; linarith
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
      have hcard_nat : ((Finset.Ico a b).filter Nat.Prime).card ≤
          ((Finset.range (b + 1)).filter Nat.Prime).card - ((Finset.range a).filter Nat.Prime).card := by
        rw [← Finset.card_sdiff_of_subset hsub]; exact Finset.card_le_card h1
      have ha_succ : ((Finset.range (a + 1)).filter Nat.Prime).card ≤
          ((Finset.range a).filter Nat.Prime).card + 1 := by
        have ha_not : a ∉ (Finset.range a).filter Nat.Prime := by simp
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs
        · rw [Finset.card_insert_of_notMem ha_not]
        · omega
      have hnat_bound : ((Finset.Ico a b).filter Nat.Prime).card +
          ((Finset.range (a + 1)).filter Nat.Prime).card ≤
          ((Finset.range (b + 1)).filter Nat.Prime).card + 1 := by
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
    have hsqrtA := (sqrtSciBounds_sound hsqA).2; have hsqrtB := (sqrtSciBounds_sound hsqB).2
    have h8pi_pos : 0 < (sci8.mul piLo4).toReal := by rw [SciProofs.mul_toReal, sci8_toReal]; linarith [piLo4_pos]
    have h8pi_le : (sci8.mul piLo4).toReal ≤ 8 * Real.pi := by rw [SciProofs.mul_toReal, sci8_toReal]; linarith [piLo4_lt_pi]
    constructor
    · have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 2 ≤ a)
      have habr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
      have hsub_int : External.offsetLogIntegral (b : ℝ) - External.offsetLogIntegral (a : ℝ) =
          ∫ t in (a : ℝ)..(b : ℝ), 1 / Real.log t := by
        unfold External.offsetLogIntegral
        linarith [intervalIntegral.integral_add_adjacent_intervals
          (inv_log_integrable_Icc (le_refl 2) ha2) (inv_log_integrable_Icc ha2 habr)]
      have hint_ub : ∫ t in (a : ℝ)..(b : ℝ), 1 / Real.log t ≤
          ((b - a : ℕ) : ℝ) / aLogLo.toReal := by
        calc ∫ t in (a : ℝ)..(b : ℝ), 1 / Real.log t
            ≤ ∫ _ in (a : ℝ)..(b : ℝ), (1 / aLogLo.toReal : ℝ) := by
              refine intervalIntegral.integral_mono_on habr (inv_log_integrable_Icc ha2 habr)
                intervalIntegrable_const fun t ht => one_div_le_one_div_of_le haL_pos
                  (haLog.1.trans (Real.log_le_log (by linarith) ht.1))
          _ = ((b - a : ℕ) : ℝ) / aLogLo.toReal := by
              rw [intervalIntegral.integral_const, smul_eq_mul, Nat.cast_sub hab.le]; ring
      have ht1 : ((b - a : ℕ) : ℝ) / aLogLo.toReal ≤
          (divUbSig (SciNat.ofNat (b - a)) aLogLo 24).toReal := by
        simpa [SciProofs.ofNat_toReal] using divUbSig_le (SciNat.ofNat (b - a)) aLogLo 24
      have ht2 : (Real.sqrt (b : ℝ) * Real.log (b : ℝ) + Real.sqrt (a : ℝ) * Real.log (a : ℝ)) /
            (8 * Real.pi) ≤
          (divUbSig (((sqrtSciBounds b 18).2.2.mul bLogHi).add ((sqrtSciBounds a 18).2.2.mul aLogHi))
            (sci8.mul piLo4) 24).toReal := by
        have hnum : Real.sqrt (b : ℝ) * Real.log (b : ℝ) + Real.sqrt (a : ℝ) * Real.log (a : ℝ) ≤
            (((sqrtSciBounds b 18).2.2.mul bLogHi).add ((sqrtSciBounds a 18).2.2.mul aLogHi)).toReal := by
          rw [SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal]
          have hba := mul_le_mul hsqrtB hbLog.2 (Real.log_nonneg (by linarith))
            ((sqrtSciBounds b 18).2.2.toReal_nonneg)
          have haa := mul_le_mul hsqrtA haLog.2 (Real.log_nonneg (by linarith))
            ((sqrtSciBounds a 18).2.2.toReal_nonneg)
          linarith
        exact (div_le_div₀ (SciNat.toReal_nonneg _) hnum h8pi_pos h8pi_le).trans (divUbSig_le _ _ 24)
      simp only [External.logIntegral] at hpi_b hpi_a
      simp only [SciProofs.add_toReal]
      have h1r : (1 : ℝ) = sci1.toReal := by unfold sci1 SciNat.toReal; norm_num
      have hdiv_add : Real.sqrt (b : ℝ) * Real.log (b : ℝ) / (8 * Real.pi) +
          Real.sqrt (a : ℝ) * Real.log (a : ℝ) / (8 * Real.pi) =
          (Real.sqrt (b : ℝ) * Real.log (b : ℝ) + Real.sqrt (a : ℝ) * Real.log (a : ℝ)) /
            (8 * Real.pi) := (add_div _ _ _).symm
      linarith [hsub_int, hint_ub, ht1, ht2, h1r, hdiv_add]
    · have hbr : (27000 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 27000 < b)
      have hexp5 : Real.exp 5 ≤ (b : ℝ) :=
        (Real.exp_le_exp.mpr (by norm_num : (5 : ℝ) ≤ 10)).trans (exp_ten_lt_27000.trans hbr).le
      have hli_lt := BuchstabSwitching.offsetLogIntegral_lt_div_log_sub_two hexp5
      have hsub_eq := SciNat.subLb_eq (a := bLogLo) (b := sci2) (by linarith [sci2_toReal])
      have hden_pos : 0 < (bLogLo.subLb sci2).toReal := by linarith [sci2_toReal]
      have hden_le : (bLogLo.subLb sci2).toReal ≤ Real.log (b : ℝ) - 2 := by linarith [hbLog.1, sci2_toReal]
      have ht1 : (b : ℝ) / (Real.log (b : ℝ) - 2) ≤
          (divUbSig (SciNat.ofNat b) (bLogLo.subLb sci2) 24).toReal :=
        (div_le_div₀ (SciNat.toReal_nonneg _) (le_of_eq (SciProofs.ofNat_toReal b).symm)
          hden_pos hden_le).trans (divUbSig_le _ _ 24)
      have ht2 : Real.sqrt (b : ℝ) * Real.log (b : ℝ) / (8 * Real.pi) ≤
          (divUbSig ((sqrtSciBounds b 18).2.2.mul bLogHi) (sci8.mul piLo4) 24).toReal := by
        have hnum : Real.sqrt (b : ℝ) * Real.log (b : ℝ) ≤
            ((sqrtSciBounds b 18).2.2.mul bLogHi).toReal := by
          rw [SciProofs.mul_toReal]
          exact mul_le_mul hsqrtB hbLog.2 (Real.log_nonneg (by linarith))
            ((sqrtSciBounds b 18).2.2.toReal_nonneg)
        exact (div_le_div₀ (SciNat.toReal_nonneg _) hnum h8pi_pos h8pi_le).trans (divUbSig_le _ _ 24)
      have hli2 : consts.li2 ≤ sciLi2Ub.toReal :=
        consts.li2_bounds.2.trans (by unfold sciLi2Ub SciNat.toReal; norm_num)
      simp only [External.logIntegral] at hpi_b
      simp only [SciProofs.add_toReal]
      have hli_eq : External.offsetLogIntegral (b : ℝ) = ∫ t in (2 : ℝ)..(b : ℝ), 1 / Real.log t := rfl
      linarith [hli_eq]

def checkSlice2abOr2cBounds (q0 q1 : ℕ) (log0Lo log0Hi log1Lo log1Hi sqUb cntUb : SciNat)
    (_m0Known : Bool := true) : Bool :=
  if q1 ≤ q0 then true
  else if q1 ≤ 27000 then
    (exactInvSubOneSumUb q0 q1 24).ble sqUb && (SciNat.ofNat (exactPrimeCount q0 q1)).ble cntUb
  else if 27000 ≤ q0 then
    let (ok, sUb, pDiff, pSingle) := analyticSliceAux q0 q1 log0Lo log0Hi log1Lo log1Hi
    ok && sUb.ble sqUb && (pDiff.ble cntUb || pSingle.ble cntUb)
  else
    let sqEx := exactInvSubOneSumUb q0 27000 24
    let cntEx := SciNat.ofNat (exactPrimeCount q0 27000)
    let (ok, sUb, pDiff, pSingle) := analyticSliceAux 27000 q1 log27000Lo log27000Hi log1Lo log1Hi
    ok && (sqEx.add sUb).ble sqUb &&
      ((cntEx.add pDiff).ble cntUb || (cntEx.add pSingle).ble cntUb)

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
    have a2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1
    omega

lemma checkSlice2abOr2cBounds_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {q0 q1 : ℕ} {log0Lo log0Hi log1Lo log1Hi sqUb cntUb : SciNat} {m0Known : Bool}
    (hLog0 : 27000 ≤ q0 → log0Lo.toReal ≤ Real.log (q0 : ℝ) ∧ Real.log (q0 : ℝ) ≤ log0Hi.toReal)
    (hLog1 : 27000 < q1 → log1Lo.toReal ≤ Real.log (q1 : ℝ) ∧ Real.log (q1 : ℝ) ≤ log1Hi.toReal)
    (h : checkSlice2abOr2cBounds q0 q1 log0Lo log0Hi log1Lo log1Hi sqUb cntUb m0Known = true) :
    ∑ q ∈ (Finset.Ico q0 q1).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤ sqUb.toReal ∧
      (((Finset.Ico q0 q1).filter Nat.Prime).card : ℝ) ≤ cntUb.toReal := by
  unfold checkSlice2abOr2cBounds at h; split_ifs at h with h1 h2 h3
  · simp [Finset.Ico_eq_empty_of_le h1, sqUb.toReal_nonneg, cntUb.toReal_nonneg]
  · simp only [Bool.and_eq_true] at h
    refine ⟨(sum_inv_sub_one_le_exact h2 24).trans (SciProofs.ble_sound h.1), ?_⟩
    rw [card_ico_primes_eq_exact h2, ← SciProofs.ofNat_toReal]; exact SciProofs.ble_sound h.2
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    have ha := analyticSliceAux_sq_sound consts hMert (hLog0 h3) (hLog1 (by omega)) h.1.1
    have hc := analyticSliceAux_cnt_sound consts hGRH hCls (hLog0 h3) (hLog1 (by omega)) h.1.1
    refine ⟨ha.2.2.trans (SciProofs.ble_sound h.1.2), ?_⟩
    rcases h.2 with hcd | hcs
    · exact hc.1.trans (SciProofs.ble_sound hcd)
    · exact hc.2.trans (SciProofs.ble_sound hcs)
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    have hsplit := ico_split_27000 q0 q1 (by omega) (by omega)
    have ha := analyticSliceAux_sq_sound consts hMert (log27000_bounds consts) (hLog1 (by omega)) h.1.1
    have hc := analyticSliceAux_cnt_sound consts hGRH hCls (log27000_bounds consts) (hLog1 (by omega)) h.1.1
    refine ⟨?_, ?_⟩
    · rw [hsplit.1, Finset.sum_union hsplit.2]
      have hsq_ex := sum_inv_sub_one_le_exact (q0 := q0) (q1 := 27000) le_rfl 24
      have hble := SciProofs.ble_sound h.1.2; rw [SciProofs.add_toReal] at hble; linarith [ha.2.2]
    · rw [hsplit.1, Finset.card_union_of_disjoint hsplit.2, Nat.cast_add,
        card_ico_primes_eq_exact (q0 := q0) (q1 := 27000) le_rfl]
      rcases h.2 with hcd | hcs
      · have hble := SciProofs.ble_sound hcd; rw [SciProofs.add_toReal, SciProofs.ofNat_toReal] at hble; linarith [hc.1]
      · have hble := SciProofs.ble_sound hcs; rw [SciProofs.add_toReal, SciProofs.ofNat_toReal] at hble; linarith [hc.2]

def checkMertensTailSums (u v : ℕ) (uLogLo uLogHi vLogLo vLogHi s1Ub s2Ub piVUb : SciNat) : Bool :=
  if v ≤ u then true
  else if v ≤ 27000 then
    (exactInvSubOneSumUb u v 24).ble s1Ub && (exactInvPredSqSumUb u v 24).ble s2Ub &&
      (SciNat.ofNat (exactPrimeCount u v)).ble piVUb
  else if 27000 ≤ u then
    let (ok, s1, pDiff, pSingle) := analyticSliceAux u v uLogLo uLogHi vLogLo vLogHi
    let s2 := divUbSig sci1 (SciNat.ofNat (u - 2)) 24
    ok && s1.ble s1Ub && s2.ble s2Ub && (pDiff.ble piVUb || pSingle.ble piVUb)
  else
    let s1Ex := exactInvSubOneSumUb u 27000 24
    let s2Ex := exactInvPredSqSumUb u 27000 24
    let cntEx := SciNat.ofNat (exactPrimeCount u 27000)
    let (ok, s1An, pDiff, pSingle) := analyticSliceAux 27000 v log27000Lo log27000Hi vLogLo vLogHi
    let s2An := divUbSig sci1 (SciNat.ofNat 26998) 24
    ok && (s1Ex.add s1An).ble s1Ub && (s2Ex.add s2An).ble s2Ub &&
      ((cntEx.add pDiff).ble piVUb || (cntEx.add pSingle).ble piVUb)

private lemma sum_gTot_eq_inv_sub_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, BuchstabSwitching.gTot p = ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) :=
  Finset.sum_congr rfl fun p hp => BuchstabSwitching.gTot_prime (hS p hp)

private lemma sum_gTot_sq_eq_inv_pred_sq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (BuchstabSwitching.gTot p) ^ 2 = ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 :=
  Finset.sum_congr rfl fun p hp => by rw [BuchstabSwitching.gTot_prime (hS p hp), one_div_pow]

lemma checkMertensTailSums_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {u v : ℕ} {uLogLo uLogHi vLogLo vLogHi s1Ub s2Ub piVUb : SciNat}
    (hLogU : 27000 ≤ u → uLogLo.toReal ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ uLogHi.toReal)
    (hLogV : 27000 < v → vLogLo.toReal ≤ Real.log (v : ℝ) ∧ Real.log (v : ℝ) ≤ vLogHi.toReal)
    (h : checkMertensTailSums u v uLogLo uLogHi vLogLo vLogHi s1Ub s2Ub piVUb = true) :
    ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, BuchstabSwitching.gTot p ≤ s1Ub.toReal ∧
      ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, (BuchstabSwitching.gTot p) ^ 2 ≤ s2Ub.toReal ∧
      (((Finset.Ico u v).filter Nat.Prime).card : ℝ) ≤ piVUb.toReal := by
  have hpr : ∀ S : Finset ℕ, S ⊆ (Finset.Ico u v).filter Nat.Prime → ∀ p ∈ S, p.Prime :=
    fun _ hS p hp => (Finset.mem_filter.mp (hS hp)).2
  rw [sum_gTot_eq_inv_sub_one _ (hpr _ Finset.Subset.rfl),
    sum_gTot_sq_eq_inv_pred_sq _ (hpr _ Finset.Subset.rfl)]
  unfold checkMertensTailSums at h; split_ifs at h with h1 h2 h3
  · simp [Finset.Ico_eq_empty_of_le h1, s1Ub.toReal_nonneg, s2Ub.toReal_nonneg, piVUb.toReal_nonneg]
  · simp only [Bool.and_eq_true] at h
    refine ⟨(sum_inv_sub_one_le_exact h2 24).trans (SciProofs.ble_sound h.1.1),
      (sum_inv_pred_sq_le_exact h2 24).trans (SciProofs.ble_sound h.1.2), ?_⟩
    rw [card_ico_primes_eq_exact h2, ← SciProofs.ofNat_toReal]; exact SciProofs.ble_sound h.2
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    have ha := analyticSliceAux_sq_sound consts hMert (hLogU h3) (hLogV (by omega)) h.1.1.1
    have hc := analyticSliceAux_cnt_sound consts hGRH hCls (hLogU h3) (hLogV (by omega)) h.1.1.1
    have hs2 : ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ s2Ub.toReal := by
      have hsub := sum_Ico_primes_inv_pred_sq_le u v (by omega)
      have hdiv := divUbSig_le sci1 (SciNat.ofNat (u - 2)) 24
      rw [sci1_toReal, SciProofs.ofNat_toReal, Nat.cast_sub (by omega : 2 ≤ u)] at hdiv
      have h2r : (1 : ℝ) / ((u : ℝ) - 2) = 1 / ((u : ℝ) - ((2 : ℕ) : ℝ)) := by norm_num
      exact hsub.trans ((h2r ▸ hdiv).trans (SciProofs.ble_sound h.1.2))
    refine ⟨ha.2.2.trans (SciProofs.ble_sound h.1.1.2), hs2, ?_⟩
    rcases h.2 with hcd | hcs
    · exact hc.1.trans (SciProofs.ble_sound hcd)
    · exact hc.2.trans (SciProofs.ble_sound hcs)
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    have hsplit := ico_split_27000 u v (by omega) (by omega)
    have ha := analyticSliceAux_sq_sound consts hMert (log27000_bounds consts) (hLogV (by omega)) h.1.1.1
    have hc := analyticSliceAux_cnt_sound consts hGRH hCls (log27000_bounds consts) (hLogV (by omega)) h.1.1.1
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit.1, Finset.sum_union hsplit.2]
      have hsq_ex := sum_inv_sub_one_le_exact (q0 := u) (q1 := 27000) le_rfl 24
      have hble := SciProofs.ble_sound h.1.1.2; rw [SciProofs.add_toReal] at hble; linarith [ha.2.2]
    · rw [hsplit.1, Finset.sum_union hsplit.2]
      have hs2_ex := sum_inv_pred_sq_le_exact (q0 := u) (q1 := 27000) le_rfl 24
      have hs2_an : ∑ p ∈ (Finset.Ico 27000 v).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤
          (divUbSig sci1 (SciNat.ofNat 26998) 24).toReal := by
        have h1 := sum_Ico_primes_inv_pred_sq_le 27000 v (by norm_num)
        have h2 := divUbSig_le sci1 (SciNat.ofNat 26998) 24
        rw [sci1_toReal, SciProofs.ofNat_toReal] at h2
        exact h1.trans ((by norm_num : (1 : ℝ) / ((27000 : ℝ) - 2) ≤ 1 / ((26998 : ℕ) : ℝ)).trans h2)
      have hble := SciProofs.ble_sound h.1.2; rw [SciProofs.add_toReal] at hble; linarith
    · rw [hsplit.1, Finset.card_union_of_disjoint hsplit.2, Nat.cast_add,
        card_ico_primes_eq_exact (q0 := u) (q1 := 27000) le_rfl]
      rcases h.2 with hcd | hcs
      · have hble := SciProofs.ble_sound hcd; rw [SciProofs.add_toReal, SciProofs.ofNat_toReal] at hble; linarith [hc.1]
      · have hble := SciProofs.ble_sound hcs; rw [SciProofs.add_toReal, SciProofs.ofNat_toReal] at hble; linarith [hc.2]

def vPrefix27000Lb : SciNat := ⟨72601774652157303544786, 24⟩

private def prodListTree : List ℕ → ℕ → SciNat
  | [], _ => ⟨1, 0⟩
  | [p], _ => SciNat.divLb (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24
  | _, 0 => ⟨0, 0⟩
  | xs, fuel + 1 =>
    let h := xs.length / 2
    ((prodListTree (xs.take h) fuel).mul (prodListTree (xs.drop h) fuel)).trimLb 24

private def prodChunksTree : List (List ℕ) → ℕ → SciNat
  | [], _ => ⟨1, 0⟩
  | [c], _ => prodListTree (c.filter (fun p => 3 ≤ p ∧ p < 27000)) 10
  | _, 0 => ⟨0, 0⟩
  | cs, fuel + 1 =>
    let h := cs.length / 2
    ((prodChunksTree (cs.take h) fuel).mul (prodChunksTree (cs.drop h) fuel)).trimLb 24

private lemma one_sub_inv_pred_eq_elem {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 : ℝ) - 1 / ((p : ℝ) - 1) ∧
      (1 : ℝ) - 1 / ((p : ℝ) - 1) = ((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p := by omega
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · have : 1 / ((p : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  · rw [Nat.cast_sub hp2, Nat.cast_sub hp1]; push_cast; field_simp [hden]; ring

private lemma prodListTree_le :
    ∀ (fuel : ℕ) (xs : List ℕ), (∀ p ∈ xs, p.Prime) →
      (prodListTree xs fuel).toReal ≤
        (xs.map (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod
  | fuel, [], _ => by simp [prodListTree, SciNat.toReal]
  | fuel, [p], hpr => by
    simp only [prodListTree, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hp := hpr p (by simp)
    have hprop := one_sub_inv_pred_eq_elem hp
    have hdiv := SciNat.divLb_le (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24
    rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, ← hprop.2] at hdiv
    exact hdiv
  | 0, a :: b :: rest, hpr => by
    simp only [prodListTree]
    have h0 : (⟨0, 0⟩ : SciNat).toReal = 0 := by simp [SciNat.toReal]
    rw [h0]
    exact List.prod_nonneg (fun x hx => by
      rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
      exact (one_sub_inv_pred_eq_elem (hpr p hp)).1)
  | fuel + 1, a :: b :: rest, hpr => by
    set xs := a :: b :: rest
    set h := xs.length / 2
    have hsplit : xs = xs.take h ++ xs.drop h := (List.take_append_drop h xs).symm
    have hpl := prodListTree_le fuel (xs.take h) (fun p hp => hpr p (List.mem_of_mem_take hp))
    have hpr_r := prodListTree_le fuel (xs.drop h) (fun p hp => hpr p (List.mem_of_mem_drop hp))
    have hmul : (prodListTree xs (fuel + 1)).toReal ≤
        (prodListTree (xs.take h) fuel).toReal * (prodListTree (xs.drop h) fuel).toReal :=
      (SciProofs.trimLb_le _ 24).trans (le_of_eq (SciProofs.mul_toReal _ _))
    have hprod_eq : (xs.map (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod =
        ((xs.take h).map (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod *
          ((xs.drop h).map (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod := by
      conv_lhs => rw [hsplit, List.map_append, List.prod_append]
    rw [hprod_eq]
    exact hmul.trans (mul_le_mul hpl hpr_r (SciNat.toReal_nonneg _)
      (List.prod_nonneg fun x hx => by
        rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
        exact (one_sub_inv_pred_eq_elem (hpr p (List.mem_of_mem_take hp))).1))

private lemma prodChunksTree_le :
    ∀ (fuel : ℕ) (cs : List (List ℕ)), (∀ p ∈ cs.flatten, p.Prime) →
      (prodChunksTree cs fuel).toReal ≤
        ((cs.flatten.filter (fun p => decide (3 ≤ p ∧ p < 27000))).map
          (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod
  | fuel, [], _ => by simp [prodChunksTree, SciNat.toReal]
  | fuel, [c], hpr => by
    simp only [prodChunksTree, List.flatten_singleton]
    exact prodListTree_le 10 _ (fun p hp => hpr p (by simpa using (List.mem_filter.mp hp).1))
  | 0, a :: b :: rest, hpr => by
    simp only [prodChunksTree]
    have h0 : (⟨0, 0⟩ : SciNat).toReal = 0 := by simp [SciNat.toReal]
    rw [h0]
    exact List.prod_nonneg (fun x hx => by
      rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
      exact (one_sub_inv_pred_eq_elem (hpr p (List.mem_of_mem_filter hp))).1)
  | fuel + 1, a :: b :: rest, hpr => by
    set cs := a :: b :: rest
    set h := cs.length / 2
    have hsplit : cs = cs.take h ++ cs.drop h := (List.take_append_drop h cs).symm
    have hpl := prodChunksTree_le fuel (cs.take h) (fun p hp => hpr p (by
      rw [hsplit, List.flatten_append]; exact List.mem_append_left _ hp))
    have hpr_r := prodChunksTree_le fuel (cs.drop h) (fun p hp => hpr p (by
      rw [hsplit, List.flatten_append]; exact List.mem_append_right _ hp))
    have hmul : (prodChunksTree cs (fuel + 1)).toReal ≤
        (prodChunksTree (cs.take h) fuel).toReal * (prodChunksTree (cs.drop h) fuel).toReal :=
      (SciProofs.trimLb_le _ 24).trans (le_of_eq (SciProofs.mul_toReal _ _))
    have hprod_eq : ((cs.flatten.filter (fun p => decide (3 ≤ p ∧ p < 27000))).map
          (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod =
        (((cs.take h).flatten.filter (fun p => decide (3 ≤ p ∧ p < 27000))).map
          (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod *
          (((cs.drop h).flatten.filter (fun p => decide (3 ≤ p ∧ p < 27000))).map
            (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod := by
      conv_lhs => rw [hsplit, List.flatten_append, List.filter_append, List.map_append, List.prod_append]
    rw [hprod_eq]
    exact hmul.trans (mul_le_mul hpl hpr_r (SciNat.toReal_nonneg _)
      (List.prod_nonneg fun x hx => by
        rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
        exact (one_sub_inv_pred_eq_elem (hpr p (by
          rw [hsplit, List.flatten_append]; exact List.mem_append_left _ (List.mem_of_mem_filter hp)))).1))

private lemma vPrefix27000Lb_ok :
    vPrefix27000Lb.ble (prodChunksTree primeChunks 10) = true := by decide

lemma vPrefix27000Lb_le_VN_two : vPrefix27000Lb.toReal ≤ External.VN 2 27000 := by
  have hble := SciProofs.ble_sound vPrefix27000Lb_ok
  have htree := prodChunksTree_le 10 primeChunks (fun p hp =>
    (mem_primesLt27000_iff.mp hp).2)
  have hfilt : (primesLt27000.filter (fun p => decide (3 ≤ p ∧ p < 27000))).toFinset =
      (Finset.Ico 3 27000).filter Nat.Prime := by
    ext p
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_primesLt27000_iff,
      Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨_, hpr⟩, h3, h27⟩; exact ⟨⟨h3, h27⟩, hpr⟩
    · rintro ⟨⟨h3, h27⟩, hpr⟩; exact ⟨⟨h27, hpr⟩, h3, h27⟩
  have hprod : ((primeChunks.flatten.filter (fun p => decide (3 ≤ p ∧ p < 27000))).map
        (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod =
      ∏ p ∈ (Finset.Ico 3 27000).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) := by
    change ((primesLt27000.filter (fun p => decide (3 ≤ p ∧ p < 27000))).map
        (fun (p : ℕ) => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod = _
    rw [← hfilt, List.prod_toFinset _ (primesLt27000_nodup.filter _)]
  rw [VN_two_eq_prod_Ico, ← hprod]
  exact hble.trans htree

def checkVFullLb2c (z : ℕ) (zLogLo zLogHi vLb : SciNat) : Bool :=
  if z ≤ 27000 then vLb.ble (exactProdOneSubInvPredLb 3 z 24)
  else
    let (ok, s1, _, _) := analyticSliceAux 27000 z log27000Lo log27000Hi zLogLo zLogHi
    let c2S2 := divUbSig (⟨26999, 0⟩ : SciNat) (⟨1457784008, 0⟩ : SciNat) 24
    let argUb := s1.add c2S2
    let (okExp, eUb) := expUbBounds argUb
    let expLb := divLbSig sci1 eUb 24
    ok && okExp && vLb.ble (vPrefix27000Lb.mul expLb)

lemma checkVFullLb2c_sound (consts : External.CertifiedConstants)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {z : ℕ} {zLogLo zLogHi vLb : SciNat}
    (hzLog : 27000 < z → zLogLo.toReal ≤ Real.log (z : ℝ) ∧ Real.log (z : ℝ) ≤ zLogHi.toReal)
    (h : checkVFullLb2c z zLogLo zLogHi vLb = true) :
    vLb.toReal ≤ External.VN 2 z := by
  unfold checkVFullLb2c at h; split_ifs at h with hz
  · exact (SciProofs.ble_sound h).trans (exactProdOneSubInvPredLb_le_VN_two hz 24)
  · simp only [Bool.and_eq_true] at h
    have hz27 : 27000 < z := lt_of_not_ge hz
    have ha := analyticSliceAux_sq_sound consts hMert (log27000_bounds consts) (hzLog hz27) h.1.1
    set s1 := (analyticSliceAux 27000 z log27000Lo log27000Hi zLogLo zLogHi).2.1
    set c2S2 := divUbSig (⟨26999, 0⟩ : SciNat) (⟨1457784008, 0⟩ : SciNat) 24
    set argUb := s1.add c2S2
    have he := expUbBounds_sound h.1.2
    set P_lo := BuchstabSwitching.fullOddPrimesBelow 27000
    set P_hi := (Finset.Ico 27000 z).filter Nat.Prime
    have hdisj : Disjoint P_lo P_hi := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have a1 := (BuchstabSwitching.fullOddPrimesBelow_mem_iff.mp h1).1
      have a2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega
    have hunion : BuchstabSwitching.fullOddPrimesBelow z = P_lo ∪ P_hi := by
      ext p; simp only [P_lo, P_hi, Finset.mem_union, BuchstabSwitching.fullOddPrimesBelow_mem_iff,
        Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨hpz, hpr, hp2⟩; by_cases hp27 : p < 27000
        · exact Or.inl ⟨hp27, hpr, hp2⟩
        · exact Or.inr ⟨⟨by omega, hpz⟩, hpr⟩
      · rintro (⟨hp27, hpr, hp2⟩ | ⟨⟨hp27, hpz⟩, hpr⟩)
        · exact ⟨lt_trans hp27 hz27, hpr, hp2⟩
        · exact ⟨hpz, hpr, by omega⟩
    have hV_split : External.VN 2 z = External.VN 2 27000 * BuchstabSwitching.V2 BuchstabSwitching.gTot P_hi := by
      rw [← BuchstabSwitching.V2_gTot_fullOddPrimesBelow_eq_VN_two z,
        ← BuchstabSwitching.V2_gTot_fullOddPrimesBelow_eq_VN_two 27000, hunion]
      exact Finset.prod_union hdisj
    have hS1 : ∑ p ∈ P_hi, BuchstabSwitching.gTot p ≤ s1.toReal := by
      rw [sum_gTot_eq_inv_sub_one P_hi (fun p hp => (Finset.mem_filter.mp hp).2)]; exact ha.2.2
    have hS2 : ∑ p ∈ P_hi, (BuchstabSwitching.gTot p) ^ 2 ≤ (1 : ℝ) / 26998 := by
      rw [sum_gTot_sq_eq_inv_pred_sq P_hi (fun p hp => (Finset.mem_filter.mp hp).2)]
      exact (sum_Ico_primes_inv_pred_sq_le 27000 z (by norm_num)).trans_eq (by norm_num)
    have hbonf := BuchstabSwitching.analytic_bonf_V2_lb (P₂ := P_hi) (p_min := 27000)
      (by norm_num) (fun p hp => ⟨(Finset.mem_filter.mp hp).2,
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1⟩) hS1 hS2
    have hc2_eq : (1 / (2 * (1 - 1 / ((27000 : ℝ) - 1)))) * ((1 : ℝ) / 26998) ≤ c2S2.toReal := by
      have hdiv := divUbSig_le (⟨26999, 0⟩ : SciNat) (⟨1457784008, 0⟩ : SciNat) 24
      have hnum : (1 / (2 * (1 - 1 / ((27000 : ℝ) - 1)))) * ((1 : ℝ) / 26998) =
          (⟨26999, 0⟩ : SciNat).toReal / (⟨1457784008, 0⟩ : SciNat).toReal := by
        unfold SciNat.toReal; norm_num
      exact hnum ▸ hdiv
    have hexp_lb : (divLbSig sci1 (expUbBounds argUb).2 24).toReal ≤
        BuchstabSwitching.V2 BuchstabSwitching.gTot P_hi := by
      have hdiv := divLbSig_le sci1 (expUbBounds argUb).2 24; rw [sci1_toReal] at hdiv
      have hinv : 1 / (expUbBounds argUb).2.toReal ≤ Real.exp (-argUb.toReal) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos _) he.1
      have harg_le : -(argUb.toReal) ≤ -(s1.toReal +
          (1 / (2 * (1 - 1 / ((27000 : ℝ) - 1)))) * ((1 : ℝ) / 26998)) := by
        dsimp only [argUb]; rw [SciProofs.add_toReal]; linarith
      exact hdiv.trans (hinv.trans ((Real.exp_le_exp.mpr harg_le).trans hbonf))
    have hprod_le : (vPrefix27000Lb.mul (divLbSig sci1 (expUbBounds argUb).2 24)).toReal ≤
        External.VN 2 z := by
      rw [hV_split, SciProofs.mul_toReal]
      exact mul_le_mul vPrefix27000Lb_le_VN_two hexp_lb (SciNat.toReal_nonneg _)
        (External.VN_nonneg 2 27000)
    exact (SciProofs.ble_sound h.2).trans hprod_le

end

end BuchstabSwitching.SieveInst
