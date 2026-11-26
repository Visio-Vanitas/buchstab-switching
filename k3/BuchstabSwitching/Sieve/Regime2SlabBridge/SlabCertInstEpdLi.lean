import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSciProofs
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.MainTermAndLiRatio
import Mathlib.Tactic

/-!
# Certified `epdNormFn` and `liRatioUb` Checkers for Regime 2 Slab Instantiation

Provides shared fixed-point constants (`piLo4`, `sci1`, ...) together with computable `Bool`
checkers `checkEpdUb` and `checkLiRatioUb` and their soundness theorems.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

def piLo4 : SciNat := ⟨31415, 4⟩
def sci1 : SciNat := ⟨1, 0⟩
def sci2 : SciNat := ⟨2, 0⟩
def sci3 : SciNat := ⟨3, 0⟩
def sci6 : SciNat := ⟨6, 0⟩
def sci7 : SciNat := ⟨7, 0⟩
def sci8 : SciNat := ⟨8, 0⟩
def sci16 : SciNat := ⟨16, 0⟩
def sci13841 : SciNat := ⟨13841, 4⟩
def sciLi2Ub : SciNat := ⟨1045163780117493, 15⟩
def sci2964 : SciNat := ⟨2964, 9⟩
def sci6836 : SciNat := ⟨6836, 9⟩

lemma sci1_toReal : sci1.toReal = 1 := by unfold sci1 SciNat.toReal; norm_num
lemma sci2_toReal : sci2.toReal = 2 := by unfold sci2 SciNat.toReal; norm_num
lemma sci3_toReal : sci3.toReal = 3 := by unfold sci3 SciNat.toReal; norm_num
lemma sci8_toReal : sci8.toReal = 8 := by unfold sci8 SciNat.toReal; norm_num
lemma piLo4_lt_pi : piLo4.toReal < Real.pi := by unfold piLo4 SciNat.toReal; linarith [Real.pi_gt_d4]
lemma piLo4_pos : 0 < piLo4.toReal := by unfold piLo4 SciNat.toReal; norm_num

def checkEpdUb (X_lo : ℕ) (logLo logHi epdUb : SciNat) : Bool :=
  let (okSq, sqrtLb, _) := sqrtSciBounds X_lo 18
  let (okLL, llxLb, _) := sciLogBounds logLo
  if !(decide (4 * 10 ^ 18 ≤ X_lo) && sci3.ble logLo && logLo.ble logHi &&
      okSq && okLL && decide (0 < sqrtLb.m) && decide (0 < llxLb.m)) then false
  else
    let tPi := divUbSig sci7 (sci16.mul piLo4) 24
    let tLog1 := divUbSig (sci6.add (divUbSig sci1 piLo4 24)) ((SciNat.ofNat 4).mul logLo) 24
    let tLog2 := divUbSig sci6 (logLo.mul logLo) 24
    let tLi2 := divUbSig sciLi2Ub (sqrtLb.mul logLo) 24
    let cSum := tPi.add (tLog1.add (tLog2.add tLi2))
    let epd1 := divUbSig (cSum.mul (logHi.mul logHi)) sqrtLb 24
    let epd2 := divUbSig (sci13841.mul (logHi.mul logHi)) ((SciNat.ofNat X_lo).mul llxLb) 24
    (epd1.add epd2).ble epdUb

lemma checkEpdUb_sound (consts : External.CertifiedConstants) {X_lo : ℕ}
    {logLo logHi epdUb : SciNat}
    (hLog : logLo.toReal ≤ Real.log (X_lo : ℝ) ∧ Real.log (X_lo : ℝ) ≤ logHi.toReal)
    (h : checkEpdUb X_lo logLo logHi epdUb = true) :
    BuchstabSwitching.epdNormFn (X_lo : ℝ) consts.li2 (X_lo : ℝ) ≤ epdUb.toReal := by
  unfold checkEpdUb at h
  dsimp only at h
  split_ifs at h with hcond
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hcond
  rcases hcond with ⟨⟨⟨⟨⟨⟨hX, hlog3⟩, _⟩, hsq_ok⟩, hll_ok⟩, hsq_pos⟩, hll_pos⟩
  set sqrtLb := (sqrtSciBounds X_lo 18).2.1
  set llxLb := (sciLogBounds logLo).2.1
  have hsqrtLb := (sqrtSciBounds_sound hsq_ok).1
  have hlogLo3 : (3 : ℝ) ≤ logLo.toReal := by
    have h3 := SciProofs.ble_sound hlog3
    have h3r : sci3.toReal = 3 := by unfold sci3 SciNat.toReal; norm_num
    linarith
  have hlog_pos : 0 < Real.log (X_lo : ℝ) := by linarith
  have hsqrt_pos : 0 < sqrtLb.toReal := by
    unfold SciNat.toReal; exact div_pos (by exact_mod_cast hsq_pos) (by positivity)
  have hllx_pos : 0 < llxLb.toReal := by
    unfold SciNat.toReal; exact div_pos (by exact_mod_cast hll_pos) (by positivity)
  have hllx_le : llxLb.toReal ≤ Real.log (Real.log (X_lo : ℝ)) :=
    (sciLogBounds_sound consts hll_ok).1.trans (Real.log_le_log (by linarith) hLog.1)
  have hpi_lt := piLo4_lt_pi
  have h1 : 3 / (8 * Real.pi) + 1 / (16 * Real.pi) ≤
      (divUbSig sci7 (sci16.mul piLo4) 24).toReal := by
    have hsum : 3 / (8 * Real.pi) + 1 / (16 * Real.pi) = sci7.toReal / (16 * Real.pi) := by
      unfold sci7 SciNat.toReal; norm_num; ring
    have hd : sci7.toReal / (16 * Real.pi) ≤ sci7.toReal / (sci16.mul piLo4).toReal := by
      rw [SciProofs.mul_toReal]
      have h16 : sci16.toReal = 16 := by unfold sci16 SciNat.toReal; norm_num
      rw [h16]
      exact div_le_div_of_nonneg_left (SciNat.toReal_nonneg _) (mul_pos (by norm_num) piLo4_pos)
        (by linarith)
    exact hsum ▸ hd.trans (divUbSig_le sci7 (sci16.mul piLo4) 24)
  have h2 : (6 + 1 / Real.pi) / (4 * Real.log (X_lo : ℝ)) ≤
      (divUbSig (sci6.add (divUbSig sci1 piLo4 24)) ((SciNat.ofNat 4).mul logLo) 24).toReal := by
    have hinv_pi : 1 / Real.pi ≤ (divUbSig sci1 piLo4 24).toReal := by
      have h1r : sci1.toReal = 1 := by unfold sci1 SciNat.toReal; norm_num
      exact (one_div_le_one_div_of_le piLo4_pos hpi_lt.le).trans
        (by rw [← h1r]; exact divUbSig_le sci1 piLo4 24)
    have hnum : 6 + 1 / Real.pi ≤ (sci6.add (divUbSig sci1 piLo4 24)).toReal := by
      rw [SciProofs.add_toReal]
      have h6r : sci6.toReal = 6 := by unfold sci6 SciNat.toReal; norm_num
      linarith
    have hd : (6 + 1 / Real.pi) / (4 * Real.log (X_lo : ℝ)) ≤
        (sci6.add (divUbSig sci1 piLo4 24)).toReal / ((SciNat.ofNat 4).mul logLo).toReal := by
      have h4r : (SciNat.ofNat 4).toReal = 4 := by rw [SciProofs.ofNat_toReal]; norm_num
      rw [SciProofs.mul_toReal, h4r]
      exact div_le_div₀ (SciNat.toReal_nonneg _) hnum
        (by linarith : 0 < 4 * logLo.toReal) (mul_le_mul_of_nonneg_left hLog.1 (by norm_num))
    exact hd.trans (divUbSig_le _ _ 24)
  have h3 : 6 / (Real.log (X_lo : ℝ)) ^ 2 ≤ (divUbSig sci6 (logLo.mul logLo) 24).toReal := by
    have h6r : sci6.toReal = 6 := by unfold sci6 SciNat.toReal; norm_num
    have hd : 6 / (Real.log (X_lo : ℝ)) ^ 2 ≤ sci6.toReal / (logLo.mul logLo).toReal := by
      rw [h6r, SciProofs.mul_toReal]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by rw [← sq]; exact pow_le_pow_left₀ (by linarith) hLog.1 2)
    exact hd.trans (divUbSig_le sci6 (logLo.mul logLo) 24)
  have h4 : consts.li2 / (Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ)) ≤
      (divUbSig sciLi2Ub (sqrtLb.mul logLo) 24).toReal := by
    have hli : consts.li2 ≤ sciLi2Ub.toReal := by
      exact consts.li2_bounds.2.trans (by unfold sciLi2Ub SciNat.toReal; norm_num)
    have hden := mul_le_mul hsqrtLb hLog.1 (by linarith) (Real.sqrt_nonneg _)
    have hd : consts.li2 / (Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ)) ≤
        sciLi2Ub.toReal / (sqrtLb.mul logLo).toReal := by
      rw [SciProofs.mul_toReal]
      exact div_le_div₀ (SciNat.toReal_nonneg _) hli (mul_pos hsqrt_pos (by linarith)) hden
    exact hd.trans (divUbSig_le sciLi2Ub (sqrtLb.mul logLo) 24)
  set cSum := (divUbSig sci7 (sci16.mul piLo4) 24).add
    ((divUbSig (sci6.add (divUbSig sci1 piLo4 24)) ((SciNat.ofNat 4).mul logLo) 24).add
      ((divUbSig sci6 (logLo.mul logLo) 24).add (divUbSig sciLi2Ub (sqrtLb.mul logLo) 24)))
  have hcSum : External.c_pi (X_lo : ℝ) consts.li2 + 1 / (16 * Real.pi) ≤ cSum.toReal := by
    unfold External.c_pi; simp only [cSum, SciProofs.add_toReal]; linarith
  have hX1 : (1 : ℝ) < (X_lo : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 4 * 10 ^ 18) hX
  have hX_pos : (0 : ℝ) < (X_lo : ℝ) := lt_trans zero_lt_one hX1
  have hlog2 : (Real.log (X_lo : ℝ)) ^ 2 ≤ (logHi.mul logHi).toReal := by
    rw [SciProofs.mul_toReal, ← sq]; exact pow_le_pow_left₀ hlog_pos.le hLog.2 2
  have hep1 : (External.c_pi (X_lo : ℝ) consts.li2 + 1 / (16 * Real.pi)) *
        (Real.log (X_lo : ℝ)) ^ 2 / Real.sqrt (X_lo : ℝ) ≤
      (divUbSig (cSum.mul (logHi.mul logHi)) sqrtLb 24).toReal := by
    have _hc_nn : 0 ≤ External.c_pi (X_lo : ℝ) consts.li2 + 1 / (16 * Real.pi) := by
      have := External.c_pi_nonneg hX1 (consts.li2_bounds.1.trans' (by norm_num))
      have := Real.pi_pos; positivity
    have hnum := mul_le_mul hcSum hlog2 (sq_nonneg _) cSum.toReal_nonneg
    rw [← SciProofs.mul_toReal] at hnum
    exact (div_le_div₀ (SciNat.toReal_nonneg _) hnum hsqrt_pos hsqrtLb).trans
      (divUbSig_le _ sqrtLb 24)
  have hep2 : External.omegaUpperFn (X_lo : ℝ) * Real.log (X_lo : ℝ) / (X_lo : ℝ) ≤
      (divUbSig (sci13841.mul (logHi.mul logHi)) ((SciNat.ofNat X_lo).mul llxLb) 24).toReal := by
    have hrew : External.omegaUpperFn (X_lo : ℝ) * Real.log (X_lo : ℝ) / (X_lo : ℝ) =
        sci13841.toReal * (Real.log (X_lo : ℝ)) ^ 2 /
          ((X_lo : ℝ) * Real.log (Real.log (X_lo : ℝ))) := by
      unfold External.omegaUpperFn sci13841 SciNat.toReal; norm_num; ring
    rw [hrew]
    have hnum : sci13841.toReal * (Real.log (X_lo : ℝ)) ^ 2 ≤
        (sci13841.mul (logHi.mul logHi)).toReal := by
      rw [SciProofs.mul_toReal]; exact mul_le_mul_of_nonneg_left hlog2 (SciNat.toReal_nonneg _)
    have hden : ((SciNat.ofNat X_lo).mul llxLb).toReal ≤
        (X_lo : ℝ) * Real.log (Real.log (X_lo : ℝ)) := by
      rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal]; exact mul_le_mul_of_nonneg_left hllx_le hX_pos.le
    have hden_pos : 0 < ((SciNat.ofNat X_lo).mul llxLb).toReal := by
      rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal]; exact mul_pos hX_pos hllx_pos
    exact (div_le_div₀ (SciNat.toReal_nonneg _) hnum hden_pos hden).trans
      (divUbSig_le _ _ 24)
  unfold BuchstabSwitching.epdNormFn
  have hble := SciProofs.ble_sound h
  rw [SciProofs.add_toReal] at hble
  linarith

def checkLiRatioUb (X_lo : ℕ) (logLo logHi liRUb : SciNat) : Bool :=
  let (okSq, _, sqrtUb) := sqrtSciBounds X_lo 18
  let (okLL, llxLb, _) := sciLogBounds logLo
  if !(decide (4 * 10 ^ 18 ≤ X_lo) && sci3.ble logLo && logLo.ble logHi &&
      okSq && okLL && decide (0 < llxLb.m)) then false
  else
    let loss1 := divUbSig (sqrtUb.mul (logHi.mul logHi)) (sci8.mul piLo4) 24
    let loss2 := divUbSig (sci13841.mul (logHi.mul logHi)) llxLb 24
    let relLossUb := divUbSig (loss1.add loss2) (SciNat.ofNat X_lo) 24
    if !(relLossUb.blt sci1) then false
    else
      let denLb := sci1.subLb relLossUb
      decide (0 < denLb.m) && (divUbSig sci1 denLb 24).ble liRUb

lemma checkLiRatioUb_sound (consts : External.CertifiedConstants) {X_lo : ℕ}
    {logLo logHi liRUb : SciNat}
    (hLog : logLo.toReal ≤ Real.log (X_lo : ℝ) ∧ Real.log (X_lo : ℝ) ≤ logHi.toReal)
    (h : checkLiRatioUb X_lo logLo logHi liRUb = true) :
    External.liRatioUb (X_lo : ℝ) ≤ liRUb.toReal := by
  unfold checkLiRatioUb at h
  dsimp only at h
  split_ifs at h with hcond hlt1
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hcond hlt1 h
  rcases hcond with ⟨⟨⟨⟨⟨hX, hlog3⟩, _⟩, hsq_ok⟩, hll_ok⟩, hll_pos⟩
  rcases h with ⟨hden_pos_nat, hble⟩
  set sqrtUb := (sqrtSciBounds X_lo 18).2.2
  set llxLb := (sciLogBounds logLo).2.1
  set loss1 := divUbSig (sqrtUb.mul (logHi.mul logHi)) (sci8.mul piLo4) 24
  set loss2 := divUbSig (sci13841.mul (logHi.mul logHi)) llxLb 24
  set relLossUb := divUbSig (loss1.add loss2) (SciNat.ofNat X_lo) 24
  have hsqrtUb := (sqrtSciBounds_sound hsq_ok).2
  have hlogLo3 : (3 : ℝ) ≤ logLo.toReal := by have h3 := SciProofs.ble_sound hlog3; linarith [sci3_toReal]
  have hlog_pos : 0 < Real.log (X_lo : ℝ) := by linarith
  have hllx_pos : 0 < llxLb.toReal := by
    unfold SciNat.toReal; exact div_pos (by exact_mod_cast hll_pos) (by positivity)
  have hllx_le : llxLb.toReal ≤ Real.log (Real.log (X_lo : ℝ)) :=
    (sciLogBounds_sound consts hll_ok).1.trans (Real.log_le_log (by linarith) hLog.1)
  have hlog2 : (Real.log (X_lo : ℝ)) ^ 2 ≤ (logHi.mul logHi).toReal := by
    rw [SciProofs.mul_toReal, ← sq]; exact pow_le_pow_left₀ hlog_pos.le hLog.2 2
  have hl1 : Real.sqrt (X_lo : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / (8 * Real.pi) ≤ loss1.toReal := by
    have hnum := mul_le_mul hsqrtUb hlog2 (sq_nonneg _) sqrtUb.toReal_nonneg
    rw [← SciProofs.mul_toReal] at hnum
    have hden : (sci8.mul piLo4).toReal ≤ 8 * Real.pi := by rw [SciProofs.mul_toReal, sci8_toReal]; linarith [piLo4_lt_pi]
    have hd_pos : 0 < (sci8.mul piLo4).toReal := by rw [SciProofs.mul_toReal, sci8_toReal]; linarith [piLo4_pos]
    exact (div_le_div₀ (SciNat.toReal_nonneg _) hnum hd_pos hden).trans
      (divUbSig_le _ _ 24)
  have hl2 : (1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / Real.log (Real.log (X_lo : ℝ)) ≤ loss2.toReal := by
    have h138 : (1.3841 : ℝ) ≤ sci13841.toReal := by unfold sci13841 SciNat.toReal; norm_num
    have hnum := mul_le_mul h138 hlog2 (sq_nonneg _) (by positivity)
    rw [← SciProofs.mul_toReal] at hnum
    exact (div_le_div₀ (SciNat.toReal_nonneg _) hnum hllx_pos hllx_le).trans
      (divUbSig_le _ _ 24)
  have hX_pos : (0 : ℝ) < (X_lo : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 4 * 10 ^ 18) hX
  have hrel : (Real.sqrt (X_lo : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / (8 * Real.pi) +
        (1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / Real.log (Real.log (X_lo : ℝ))) / (X_lo : ℝ) ≤
      relLossUb.toReal := by
    have hnum : Real.sqrt (X_lo : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / (8 * Real.pi) +
          (1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / Real.log (Real.log (X_lo : ℝ)) ≤
        (loss1.add loss2).toReal := by
      rw [SciProofs.add_toReal]; exact add_le_add hl1 hl2
    exact (div_le_div₀ (SciNat.toReal_nonneg _) hnum
      (by rw [SciProofs.ofNat_toReal]; exact hX_pos)
      (le_of_eq (SciProofs.ofNat_toReal X_lo))).trans (divUbSig_le _ _ 24)
  have hrel_lt1 : relLossUb.toReal < 1 := by
    have hlt := SciProofs.blt_sound hlt1
    linarith only [hlt, sci1_toReal]
  set denLb := sci1.subLb relLossUb
  have hden_eq : denLb.toReal = 1 - relLossUb.toReal := by
    have heq := SciNat.subLb_eq (a := sci1) (b := relLossUb)
      (by linarith only [hrel_lt1, sci1_toReal])
    linarith only [heq, sci1_toReal]
  have hden_pos : 0 < denLb.toReal := by
    unfold SciNat.toReal; exact div_pos (by exact_mod_cast hden_pos_nat) (by positivity)
  have hinv : External.liRatioUb (X_lo : ℝ) ≤ 1 / denLb.toReal := by
    unfold External.liRatioUb; rw [one_div]; refine inv_anti₀ hden_pos ?_
    rw [hden_eq]; exact sub_le_sub_left hrel 1
  have hdiv := divUbSig_le sci1 denLb 24; rw [sci1_toReal] at hdiv
  exact hinv.trans (hdiv.trans (SciProofs.ble_sound hble))

end

end BuchstabSwitching.SieveInst
