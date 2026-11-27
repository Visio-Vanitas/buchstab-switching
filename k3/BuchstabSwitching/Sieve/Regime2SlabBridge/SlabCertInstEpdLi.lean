import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstExpProofs
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.MainTermAndLiRatio
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder.SquaresAndMonotonicity
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Certified `epdNormFn` and `liRatioUb` Checkers (Binary Dyadic + `EpdWitness`)

Replaces `SciNat` 24-digit division loops with pure bit-shifted `Dyadic` constants,
`checkSqrtLb`/`checkSqrtUb`, `checkLogDyadic`, and cleared-denominator witness checks.
-/

namespace BuchstabSwitching.SieveInst

section

def dyZero : Dyadic := Dyadic.zero
def dyOne : Dyadic := Dyadic.one
def dyTwo : Dyadic := Dyadic.ofNat 2
def dyThree : Dyadic := Dyadic.ofNat 3
def dyFour : Dyadic := Dyadic.ofNat 4
def dySix : Dyadic := Dyadic.ofNat 6
def dySeven : Dyadic := Dyadic.ofNat 7
def dyEight : Dyadic := Dyadic.ofNat 8
def dySixteen : Dyadic := Dyadic.ofNat 16

/-- Q64 lower bound `< 31415 / 10000 < π`. -/
def dyPiLo4 : Dyadic := Dyadic.ofQ64 57950446507558556401
/-- Q64 lower bound `< 8 * 31415 / 10000 < 8 * π`. -/
def dy8PiLo4 : Dyadic := Dyadic.ofQ64 463603572060468451213
/-- Q64 lower bound `< 16 * 31415 / 10000 < 16 * π`. -/
def dy16PiLo4 : Dyadic := Dyadic.ofQ64 927207144120936902426
/-- Q64 upper bound `≥ 13841 / 10000`. -/
def dy13841Ub : Dyadic := Dyadic.ofQ64 25532138472421390392
/-- Q64 upper bound `≥ 1045163780117493 / 10^15 ≥ consts.li2`. -/
def dyLi2Ub : Dyadic := Dyadic.ofQ64 19279868766938236891
/-- Q64 upper bound `≥ 2964 / 10^9 = 2.964e-6`. -/
def dy2964Ub : Dyadic := Dyadic.ofQ64 54676149434476
/-- Q64 upper bound `≥ 6836 / 10^9 = 6.836e-6`. -/
def dy6836Ub : Dyadic := Dyadic.ofQ64 126101942487879

lemma dyZero_toReal : dyZero.toReal = 0 := Dyadic.zero_toReal
lemma dyOne_toReal : dyOne.toReal = 1 := Dyadic.one_toReal
lemma dyTwo_toReal : dyTwo.toReal = 2 := by simpa [dyTwo] using Dyadic.ofNat_toReal 2
lemma dyThree_toReal : dyThree.toReal = 3 := by simpa [dyThree] using Dyadic.ofNat_toReal 3
lemma dyFour_toReal : dyFour.toReal = 4 := by simpa [dyFour] using Dyadic.ofNat_toReal 4
lemma dySix_toReal : dySix.toReal = 6 := by simpa [dySix] using Dyadic.ofNat_toReal 6
lemma dySeven_toReal : dySeven.toReal = 7 := by simpa [dySeven] using Dyadic.ofNat_toReal 7
lemma dyEight_toReal : dyEight.toReal = 8 := by simpa [dyEight] using Dyadic.ofNat_toReal 8
lemma dySixteen_toReal : dySixteen.toReal = 16 := by simpa [dySixteen] using Dyadic.ofNat_toReal 16

private lemma dyPiLo4_nat_ok : 57950446507558556401 * 10000 ≤ 31415 * q64Scale := by native_decide
private lemma dy8PiLo4_nat_ok : 463603572060468451213 * 10000 ≤ 8 * 31415 * q64Scale := by native_decide
private lemma dy16PiLo4_nat_ok : 927207144120936902426 * 10000 ≤ 16 * 31415 * q64Scale := by native_decide
private lemma dy13841Ub_nat_ok : 13841 * q64Scale ≤ 25532138472421390392 * 10000 := by native_decide
private lemma dyLi2Ub_nat_ok : 1045163780117493 * q64Scale ≤ 19279868766938236891 * 10 ^ 15 := by native_decide
private lemma dy2964Ub_nat_ok : 2964 * q64Scale ≤ 54676149434476 * 10 ^ 9 := by native_decide
private lemma dy6836Ub_nat_ok : 6836 * q64Scale ≤ 126101942487879 * 10 ^ 9 := by native_decide

lemma dyPiLo4_lt_pi : dyPiLo4.toReal < Real.pi := by
  have h : dyPiLo4.toReal ≤ (3.1415 : ℝ) := by
    rw [dyPiLo4, Dyadic.ofQ64_toReal, show (3.1415 : ℝ) = (31415 : ℝ) / 10000 by norm_num,
      div_le_div_iff₀ q64Scale_pos (by norm_num)]
    exact_mod_cast dyPiLo4_nat_ok
  exact lt_of_le_of_lt h Real.pi_gt_d4

lemma dy8PiLo4_lt : dy8PiLo4.toReal < 8 * Real.pi := by
  have h : dy8PiLo4.toReal ≤ 8 * (3.1415 : ℝ) := by
    rw [dy8PiLo4, Dyadic.ofQ64_toReal, show 8 * (3.1415 : ℝ) = (8 * 31415 : ℝ) / 10000 by norm_num,
      div_le_div_iff₀ q64Scale_pos (by norm_num)]
    exact_mod_cast dy8PiLo4_nat_ok
  exact lt_of_le_of_lt h (by linarith [Real.pi_gt_d4])

lemma dy16PiLo4_lt : dy16PiLo4.toReal < 16 * Real.pi := by
  have h : dy16PiLo4.toReal ≤ 16 * (3.1415 : ℝ) := by
    rw [dy16PiLo4, Dyadic.ofQ64_toReal, show 16 * (3.1415 : ℝ) = (16 * 31415 : ℝ) / 10000 by norm_num,
      div_le_div_iff₀ q64Scale_pos (by norm_num)]
    exact_mod_cast dy16PiLo4_nat_ok
  exact lt_of_le_of_lt h (by linarith [Real.pi_gt_d4])

lemma le_dy13841Ub : (1.3841 : ℝ) ≤ dy13841Ub.toReal := by
  rw [dy13841Ub, Dyadic.ofQ64_toReal, show (1.3841 : ℝ) = 13841 / 10000 by norm_num,
    div_le_div_iff₀ (by norm_num) q64Scale_pos]
  exact_mod_cast dy13841Ub_nat_ok

lemma li2_le_dyLi2Ub (consts : External.CertifiedConstants) : consts.li2 ≤ dyLi2Ub.toReal := by
  have h : (1.045163780117493 : ℝ) ≤ dyLi2Ub.toReal := by
    rw [dyLi2Ub, Dyadic.ofQ64_toReal,
      show (1.045163780117493 : ℝ) = (1045163780117493 : ℝ) / (10 ^ 15 : ℝ) by norm_num,
      div_le_div_iff₀ (by norm_num) q64Scale_pos]
    exact_mod_cast dyLi2Ub_nat_ok
  exact consts.li2_bounds.2.trans h

lemma le_dy2964Ub : (2.964e-6 : ℝ) ≤ dy2964Ub.toReal := by
  rw [dy2964Ub, Dyadic.ofQ64_toReal,
    show (2.964e-6 : ℝ) = (2964 : ℝ) / (10 : ℝ) ^ 9 by norm_num,
    div_le_div_iff₀ (by positivity) q64Scale_pos]
  exact_mod_cast dy2964Ub_nat_ok

lemma le_dy6836Ub : (6.836e-6 : ℝ) ≤ dy6836Ub.toReal := by
  rw [dy6836Ub, Dyadic.ofQ64_toReal,
    show (6.836e-6 : ℝ) = (6836 : ℝ) / (10 : ℝ) ^ 9 by norm_num,
    div_le_div_iff₀ (by positivity) q64Scale_pos]
  exact_mod_cast dy6836Ub_nat_ok

/-- Heuristic 80-bit `Dyadic` ceiling quotient hint `num / den` (always re-checked via `ble (qUb.mulLb den)`). -/
def dyDivUb (num den : Dyadic) : Dyadic :=
  if den.m == 0 || num.m == 0 then Dyadic.zero
  else
    let num' := num.trimUb 80
    let den' := den.trimLb 80
    if den'.m == 0 then Dyadic.zero
    else
      let eDiff : ℤ := (num'.e : ℤ) - (den'.e : ℤ) + (dyadicBias : ℤ) - 80
      let shNum : ℕ := if 0 ≤ eDiff then 80 else Int.toNat (80 - eDiff)
      let eOut : ℕ := if 0 ≤ eDiff then Int.toNat eDiff else 0
      let qm := (num'.m <<< shNum + den'.m - 1) / den'.m
      Dyadic.trimUb ⟨qm + (qm >>> 72) + 1, eOut⟩ 80

/-- Heuristic 80-bit `Dyadic` floor quotient hint `num / den` (always re-checked via `(qLb.mulUb den).ble num`). -/
def dyDivLb (num den : Dyadic) : Dyadic :=
  if den.m == 0 || num.m == 0 then Dyadic.zero
  else
    let num' := num.trimLb 80
    let den' := den.trimUb 80
    let eDiff : ℤ := (num'.e : ℤ) - (den'.e : ℤ) + (dyadicBias : ℤ) - 80
    let shNum : ℕ := if 0 ≤ eDiff then 80 else Int.toNat (80 - eDiff)
    let eOut : ℕ := if 0 ≤ eDiff then Int.toNat eDiff else 0
    let qm := (num'.m <<< shNum) / den'.m
    Dyadic.trimLb ⟨qm - (qm >>> 72) - 1, eOut⟩ 80

/-- Check `EpdWitness` cleanly with cleared denominators, bit-shifted bounds, and `Dyadic` arithmetic. -/
def checkEpdWitness (X_lo : ℕ) (logLo logHi epdUb : Dyadic) (w : EpdWitness) : Bool :=
  let llxUb := w.llxLb.add dyOne
  let cSum := w.tPi.add (w.tLog1.add (w.tLog2.add w.tLi2))
  let logHi2 := logHi.mulUb logHi
  decide (4 * 10 ^ 18 ≤ X_lo) && dyThree.ble logLo && logLo.ble logHi &&
  checkSqrtLb (Dyadic.ofNat X_lo) w.xLoSqrtLb && decide (0 < w.xLoSqrtLb.m) &&
  checkSqrtUb (Dyadic.ofNat X_lo) w.xLoSqrtUb &&
  checkLogDyadic logLo w.wLLX w.llxLb llxUb && decide (0 < w.llxLb.m) &&
  dySeven.ble (w.tPi.mulLb dy16PiLo4) &&
  dyOne.ble (w.tInvPi.mulLb dyPiLo4) &&
  (dySix.add w.tInvPi).ble (w.tLog1.mulLb (dyFour.mulLb logLo)) &&
  dySix.ble (w.tLog2.mulLb (logLo.mulLb logLo)) &&
  dyLi2Ub.ble (w.tLi2.mulLb (w.xLoSqrtLb.mulLb logLo)) &&
  (cSum.mulUb logHi2).ble (w.epd1.mulLb w.xLoSqrtLb) &&
  (dy13841Ub.mulUb logHi2).ble (w.epd2.mulLb ((Dyadic.ofNat X_lo).mulLb w.llxLb)) &&
  (w.epd1.add w.epd2).ble epdUb

lemma checkEpdWitness_sound (consts : External.CertifiedConstants) {X_lo : ℕ}
    {logLo logHi epdUb : Dyadic} {w : EpdWitness}
    (hLog : logLo.toReal ≤ Real.log (X_lo : ℝ) ∧ Real.log (X_lo : ℝ) ≤ logHi.toReal)
    (h : checkEpdWitness X_lo logLo logHi epdUb w = true) :
    BuchstabSwitching.epdNormFn (X_lo : ℝ) consts.li2 (X_lo : ℝ) ≤ epdUb.toReal := by
  unfold checkEpdWitness at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hX, h3l, _, hsqLb, hsqLbPos, _, hll, hllPos, htPi, htInv, htL1, htL2, htLi2, hepd1, hepd2, hble⟩
  have h3r : (3 : ℝ) ≤ logLo.toReal := by
    have := Dyadic.ble_sound h3l; rwa [dyThree_toReal] at this
  have hlog_pos : 0 < Real.log (X_lo : ℝ) := by linarith
  have hXpos : (0 : ℝ) < (X_lo : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hX
  have hsqrt_real_pos : 0 < Real.sqrt (X_lo : ℝ) := Real.sqrt_pos.mpr hXpos
  have hsqrtLb : w.xLoSqrtLb.toReal ≤ Real.sqrt (X_lo : ℝ) :=
    checkSqrtLb_sound (by rw [Dyadic.ofNat_toReal]) hsqLb
  have hllx_le : w.llxLb.toReal ≤ Real.log (Real.log (X_lo : ℝ)) :=
    (checkLogDyadic_sound consts hll).1.trans (Real.log_le_log (by linarith) hLog.1)
  have hllx_real_pos : 0 < Real.log (Real.log (X_lo : ℝ)) :=
    lt_of_lt_of_le (Dyadic.toReal_pos_of_m hllPos) hllx_le
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h1 : 3 / (8 * Real.pi) + 1 / (16 * Real.pi) ≤ w.tPi.toReal := by
    rw [show 3 / (8 * Real.pi) + 1 / (16 * Real.pi) = 7 / (16 * Real.pi) by ring]
    exact Dyadic.div_le_of_ble_mulLb (by rw [dySeven_toReal]) (by positivity) dy16PiLo4_lt.le htPi
  have h2 : (6 + 1 / Real.pi) / (4 * Real.log (X_lo : ℝ)) ≤ w.tLog1.toReal := by
    have hinv_pi : 1 / Real.pi ≤ w.tInvPi.toReal :=
      Dyadic.div_le_of_ble_mulLb (by rw [dyOne_toReal]) hpi_pos dyPiLo4_lt_pi.le htInv
    have hnum : 6 + 1 / Real.pi ≤ (dySix.add w.tInvPi).toReal := by
      rw [Dyadic.add_toReal, dySix_toReal]; linarith
    have hden_le : (dyFour.mulLb logLo).toReal ≤ 4 * Real.log (X_lo : ℝ) :=
      (Dyadic.mulLb_le _ _).trans (by rw [dyFour_toReal]; linarith)
    exact Dyadic.div_le_of_ble_mulLb hnum (by positivity) hden_le htL1
  have h3 : 6 / (Real.log (X_lo : ℝ)) ^ 2 ≤ w.tLog2.toReal := by
    have hden_le : (logLo.mulLb logLo).toReal ≤ (Real.log (X_lo : ℝ)) ^ 2 :=
      (Dyadic.mulLb_le _ _).trans (by rw [← sq]; exact pow_le_pow_left₀ (by linarith) hLog.1 2)
    exact Dyadic.div_le_of_ble_mulLb (by rw [dySix_toReal]) (sq_pos_of_pos hlog_pos) hden_le htL2
  have h4 : consts.li2 / (Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ)) ≤ w.tLi2.toReal := by
    have hden_le : (w.xLoSqrtLb.mulLb logLo).toReal ≤ Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ) :=
      (Dyadic.mulLb_le _ _).trans (mul_le_mul hsqrtLb hLog.1 (by linarith) hsqrt_real_pos.le)
    exact Dyadic.div_le_of_ble_mulLb (li2_le_dyLi2Ub consts) (mul_pos hsqrt_real_pos hlog_pos) hden_le htLi2
  have hlog2 : (Real.log (X_lo : ℝ)) ^ 2 ≤ (logHi.mulUb logHi).toReal :=
    (pow_le_pow_left₀ hlog_pos.le hLog.2 2).trans (by rw [sq]; exact Dyadic.le_mulUb _ _)
  have hcSum : (3 / (8 * Real.pi) + 1 / (16 * Real.pi) +
        (6 + 1 / Real.pi) / (4 * Real.log (X_lo : ℝ)) +
        6 / (Real.log (X_lo : ℝ)) ^ 2 + consts.li2 / (Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ))) *
        (Real.log (X_lo : ℝ)) ^ 2 ≤
      ((w.tPi.add (w.tLog1.add (w.tLog2.add w.tLi2))).mulUb (logHi.mulUb logHi)).toReal := by
    have hleft : 3 / (8 * Real.pi) + 1 / (16 * Real.pi) +
          (6 + 1 / Real.pi) / (4 * Real.log (X_lo : ℝ)) +
          6 / (Real.log (X_lo : ℝ)) ^ 2 + consts.li2 / (Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ)) ≤
        (w.tPi.add (w.tLog1.add (w.tLog2.add w.tLi2))).toReal := by
      simp only [Dyadic.add_toReal]; linarith
    exact (mul_le_mul hleft hlog2 (sq_nonneg _) (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)
  have he1 : ((3 / (8 * Real.pi) + 1 / (16 * Real.pi) +
        (6 + 1 / Real.pi) / (4 * Real.log (X_lo : ℝ)) +
        6 / (Real.log (X_lo : ℝ)) ^ 2 + consts.li2 / (Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ))) *
        (Real.log (X_lo : ℝ)) ^ 2) / Real.sqrt (X_lo : ℝ) ≤ w.epd1.toReal :=
    Dyadic.div_le_of_ble_mulLb hcSum hsqrt_real_pos hsqrtLb hepd1
  have he2 : ((1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2) / ((X_lo : ℝ) * Real.log (Real.log (X_lo : ℝ))) ≤
      w.epd2.toReal := by
    have hnum : (1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 ≤ (dy13841Ub.mulUb (logHi.mulUb logHi)).toReal :=
      (mul_le_mul le_dy13841Ub hlog2 (sq_nonneg _) (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)
    have hden_le : ((Dyadic.ofNat X_lo).mulLb w.llxLb).toReal ≤ (X_lo : ℝ) * Real.log (Real.log (X_lo : ℝ)) :=
      (Dyadic.mulLb_le _ _).trans (by
        rw [Dyadic.ofNat_toReal]
        exact mul_le_mul_of_nonneg_left hllx_le (Nat.cast_nonneg _))
    exact Dyadic.div_le_of_ble_mulLb hnum (mul_pos hXpos hllx_real_pos) hden_le hepd2
  have hadd : w.epd1.toReal + w.epd2.toReal ≤ epdUb.toReal := by
    simpa [Dyadic.add_toReal] using Dyadic.ble_sound hble
  unfold BuchstabSwitching.epdNormFn External.c_pi External.omegaUpperFn
  have heqc : (External.c_pi (X_lo : ℝ) consts.li2 + 1 / (16 * Real.pi)) * (Real.log (X_lo : ℝ)) ^ 2 / Real.sqrt (X_lo : ℝ) +
      External.omegaUpperFn (X_lo : ℝ) * Real.log (X_lo : ℝ) / (X_lo : ℝ) =
      ((3 / (8 * Real.pi) + 1 / (16 * Real.pi) +
        (6 + 1 / Real.pi) / (4 * Real.log (X_lo : ℝ)) +
        6 / (Real.log (X_lo : ℝ)) ^ 2 + consts.li2 / (Real.sqrt (X_lo : ℝ) * Real.log (X_lo : ℝ))) *
        (Real.log (X_lo : ℝ)) ^ 2) / Real.sqrt (X_lo : ℝ) +
      ((1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2) / ((X_lo : ℝ) * Real.log (Real.log (X_lo : ℝ))) := by
    unfold External.c_pi External.omegaUpperFn; ring
  unfold External.c_pi External.omegaUpperFn at heqc
  linarith only [he1, he2, hadd, heqc]

private def checkLiRatioUbAux (X_lo : ℕ) (logLo logHi sqrtUb llxLb loss1 loss2 relLossUb denLb liUb : Dyadic) : Bool :=
  let log2 := logHi.mulUb logHi
  decide (4 * 10 ^ 18 ≤ X_lo) && dyThree.ble logLo && logLo.ble logHi &&
  decide (0 < llxLb.m) &&
  (sqrtUb.mulUb log2).ble (loss1.mulLb dy8PiLo4) &&
  (dy13841Ub.mulUb log2).ble (loss2.mulLb llxLb) &&
  (loss1.add loss2).ble (relLossUb.mulLb (Dyadic.ofNat X_lo)) &&
  relLossUb.blt dyOne &&
  decide (0 < denLb.m) &&
  denLb.ble (dyOne.subLb relLossUb) &&
  dyOne.ble (liUb.mulLb denLb)

/-- Check `liRatioUb (X_lo : ℝ) ≤ liUb.toReal` using pre-verified `sqrtUb ≥ √X_lo` and `llxLb ≤ log log X_lo`. -/
def checkLiRatioUb (X_lo : ℕ) (logLo logHi sqrtUb llxLb liUb : Dyadic) : Bool :=
  let log2 := logHi.mulUb logHi
  let loss1 := dyDivUb (sqrtUb.mulUb log2) dy8PiLo4
  let loss2 := dyDivUb (dy13841Ub.mulUb log2) llxLb
  let relLossUb := dyDivUb (loss1.add loss2) (Dyadic.ofNat X_lo)
  let denLb := dyOne.subLb relLossUb
  checkLiRatioUbAux X_lo logLo logHi sqrtUb llxLb loss1 loss2 relLossUb denLb liUb

private lemma checkLiRatioUbAux_sound {X_lo : ℕ}
    {logLo logHi sqrtUb llxLb loss1 loss2 relLossUb denLb liUb : Dyadic}
    (hLog : logLo.toReal ≤ Real.log (X_lo : ℝ) ∧ Real.log (X_lo : ℝ) ≤ logHi.toReal)
    (hsqrtUb : Real.sqrt (X_lo : ℝ) ≤ sqrtUb.toReal)
    (hllxPos : 0 < Real.log (Real.log (X_lo : ℝ)))
    (hllxLe : llxLb.toReal ≤ Real.log (Real.log (X_lo : ℝ)))
    (h : checkLiRatioUbAux X_lo logLo logHi sqrtUb llxLb loss1 loss2 relLossUb denLb liUb = true) :
    External.liRatioUb (X_lo : ℝ) ≤ liUb.toReal := by
  unfold checkLiRatioUbAux at h; dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hX, h3l, _, _, hl1, hl2, hrel, hlt1, hdenPos, hdenSub, hble⟩
  set log2 := logHi.mulUb logHi
  have h3r : (3 : ℝ) ≤ logLo.toReal := by
    have := Dyadic.ble_sound h3l; rwa [dyThree_toReal] at this
  have hlog_pos : 0 < Real.log (X_lo : ℝ) := by linarith
  have hlog2 : (Real.log (X_lo : ℝ)) ^ 2 ≤ log2.toReal :=
    (pow_le_pow_left₀ hlog_pos.le hLog.2 2).trans (by rw [sq]; exact Dyadic.le_mulUb _ _)
  have hnum1 : Real.sqrt (X_lo : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 ≤ (sqrtUb.mulUb log2).toReal :=
    (mul_le_mul hsqrtUb hlog2 (sq_nonneg _) (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)
  have h8pi_pos : 0 < 8 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hL1 : Real.sqrt (X_lo : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / (8 * Real.pi) ≤ loss1.toReal :=
    Dyadic.div_le_of_ble_mulLb hnum1 h8pi_pos dy8PiLo4_lt.le hl1
  have hnum2 : (1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 ≤ (dy13841Ub.mulUb log2).toReal :=
    (mul_le_mul le_dy13841Ub hlog2 (sq_nonneg _) (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)
  have hL2 : (1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / Real.log (Real.log (X_lo : ℝ)) ≤ loss2.toReal :=
    Dyadic.div_le_of_ble_mulLb hnum2 hllxPos hllxLe hl2
  have hXpos : (0 : ℝ) < (X_lo : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hX
  have hrel_le : (Real.sqrt (X_lo : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / (8 * Real.pi) +
        (1.3841 : ℝ) * (Real.log (X_lo : ℝ)) ^ 2 / Real.log (Real.log (X_lo : ℝ))) / (X_lo : ℝ) ≤
      relLossUb.toReal :=
    Dyadic.div_le_of_ble_mulLb (by rw [Dyadic.add_toReal]; linarith) hXpos
      (le_of_eq (Dyadic.ofNat_toReal X_lo)) hrel
  have hrel_lt1 : relLossUb.toReal < 1 := by
    have := Dyadic.blt_sound hlt1; rwa [dyOne_toReal] at this
  have hden_le : denLb.toReal ≤ 1 - relLossUb.toReal := by
    have heq := Dyadic.subLb_eq (a := dyOne) (b := relLossUb) (by rw [dyOne_toReal]; exact hrel_lt1.le)
    rw [dyOne_toReal] at heq
    exact (Dyadic.ble_sound hdenSub).trans heq.le
  have hden_pos : 0 < denLb.toReal := Dyadic.toReal_pos_of_m hdenPos
  have hinv : External.liRatioUb (X_lo : ℝ) ≤ 1 / denLb.toReal := by
    unfold External.liRatioUb; rw [one_div]; refine inv_anti₀ hden_pos ?_
    exact hden_le.trans (sub_le_sub_left hrel_le 1)
  exact hinv.trans (Dyadic.div_le_of_ble_mulLb (le_of_eq dyOne_toReal.symm) hden_pos le_rfl hble)

lemma checkLiRatioUb_sound {X_lo : ℕ} {logLo logHi sqrtUb llxLb liUb : Dyadic}
    (hLog : logLo.toReal ≤ Real.log (X_lo : ℝ) ∧ Real.log (X_lo : ℝ) ≤ logHi.toReal)
    (hsqrtUb : Real.sqrt (X_lo : ℝ) ≤ sqrtUb.toReal)
    (hllxPos : 0 < Real.log (Real.log (X_lo : ℝ)))
    (hllxLe : llxLb.toReal ≤ Real.log (Real.log (X_lo : ℝ)))
    (h : checkLiRatioUb X_lo logLo logHi sqrtUb llxLb liUb = true) :
    External.liRatioUb (X_lo : ℝ) ≤ liUb.toReal :=
  checkLiRatioUbAux_sound hLog hsqrtUb hllxPos hllxLe h

end

end BuchstabSwitching.SieveInst
