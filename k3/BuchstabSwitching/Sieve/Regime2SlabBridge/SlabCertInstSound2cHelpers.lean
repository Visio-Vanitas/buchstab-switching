import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstEpdLi
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstJOddSmall
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.DiscreteJFull
import BuchstabSwitching.Sieve.OddSquarefreeBounds.ConstantBounds
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstCJ
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Shared Regime `2c` `Dyadic` Helpers, `α₀` Bound, `J_odd`, & `jFullTerm1`

Provides:
1. Outward-rounded 80-bit `divDyadicLb` / `divDyadicUb`, `dyLogBounds`, and `sumDyadicFin`;
2. `alpha0_ge_63518`, Q64 `expGeDyadic` / `expNegUbDyadic`, `jOddLbDyadic`, `jOddUbDyadic`,
   `jOddHybridUbDyadic`, `jsMertLoUbDyadic`, `jsMertHiUbDyadic`;
3. `jFullTerm1` and `jFullTerm1_sound` for the 12-point single-prime quadrature in `J_full`.
-/

namespace BuchstabSwitching.SieveInst

section

section ExtraDyadicHelpers

/-- Outward 80-bit lower quotient `⌊(a * 2^sh) / b⌋ * 2^(a.e - b.e - sh)` (`sh = 80 + msbPos b.m`). -/
def divDyadicLb (a b : Dyadic) : Dyadic :=
  if b.m == 0 || a.m == 0 then Dyadic.zero
  else
    let sh := 80 + Dyadic.msbPos b.m
    let qm := (a.m <<< sh) / b.m
    if b.e + sh ≤ a.e + dyadicBias then
      (Dyadic.mk qm (a.e + dyadicBias - (b.e + sh))).trimLb 80
    else
      Dyadic.mk (qm >>> ((b.e + sh) - (a.e + dyadicBias))) 0

/-- Outward 80-bit upper quotient `⌈(a * 2^sh) / b⌉ * 2^(a.e - b.e - sh)` (`sh = 80 + msbPos b.m`). -/
def divDyadicUb (a b : Dyadic) : Dyadic :=
  if b.m == 0 || a.m == 0 then Dyadic.zero
  else
    let sh := 80 + Dyadic.msbPos b.m
    let qm := ((a.m <<< sh) + b.m - 1) / b.m
    if b.e + sh ≤ a.e + dyadicBias then
      (Dyadic.mk qm (a.e + dyadicBias - (b.e + sh))).trimUb 80
    else
      Dyadic.mk (Dyadic.ceilShr qm ((b.e + sh) - (a.e + dyadicBias))) 0

private lemma dyadic_div_eq {a b : Dyadic} (hb : b.m ≠ 0) :
    a.toReal / b.toReal = ((a.m : ℝ) / (b.m : ℝ)) * ((2 : ℝ) ^ a.e / (2 : ℝ) ^ b.e) := by
  unfold Dyadic.toReal
  have hbm : (b.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have h2b : (2 : ℝ) ^ b.e ≠ 0 := by positivity
  have hbias : Dyadic.twoPowBias ≠ 0 := Dyadic.twoPowBias_pos.ne'
  field_simp [hbm, h2b, hbias]

lemma divDyadicLb_le (a b : Dyadic) : (divDyadicLb a b).toReal ≤ a.toReal / b.toReal := by
  unfold divDyadicLb
  by_cases h0 : (b.m == 0 || a.m == 0) = true
  · simp only [h0, ↓reduceIte, Dyadic.zero_toReal]
    exact div_nonneg a.toReal_nonneg b.toReal_nonneg
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h0
    rcases h0 with ⟨hb0, _⟩
    have hb_pos : (0 : ℝ) < (b.m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb0
    set sh := 80 + Dyadic.msbPos b.m
    set qm := (a.m <<< sh) / b.m
    have hqm : (qm : ℝ) / (2 : ℝ) ^ sh ≤ (a.m : ℝ) / (b.m : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hb_pos]
      have hmul : qm * b.m ≤ a.m * 2 ^ sh := by
        simpa [qm, Nat.shiftLeft_eq] using Nat.div_mul_le_self (a.m <<< sh) b.m
      exact_mod_cast hmul
    rw [dyadic_div_eq hb0]
    split_ifs with he
    · refine (Dyadic.trimLb_le _ 80).trans ?_
      have hexp : (Dyadic.mk qm (a.e + dyadicBias - (b.e + sh))).toReal =
          ((qm : ℝ) / (2 : ℝ) ^ sh) * ((2 : ℝ) ^ a.e / (2 : ℝ) ^ b.e) := by
        unfold Dyadic.toReal; dsimp only; rw [Dyadic.twoPowBias_eq]
        have hp : (2 : ℝ) ^ (a.e + dyadicBias - (b.e + sh)) * (2 : ℝ) ^ b.e * (2 : ℝ) ^ sh =
            (2 : ℝ) ^ a.e * (2 : ℝ) ^ dyadicBias := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1; omega
        field_simp; linarith [congrArg ((qm : ℝ) * ·) hp]
      rw [hexp]
      exact mul_le_mul_of_nonneg_right hqm (by positivity)
    · set k := (b.e + sh) - (a.e + dyadicBias)
      have hfl : (Dyadic.mk (qm >>> k) 0).toReal ≤ ((qm : ℝ) / (2 : ℝ) ^ k) / (2 : ℝ) ^ dyadicBias := by
        unfold Dyadic.toReal; dsimp only; rw [pow_zero, mul_one, Dyadic.twoPowBias_eq]
        exact div_le_div_of_nonneg_right (Dyadic.floorShr_le qm k) (by positivity)
      have hexp : ((qm : ℝ) / (2 : ℝ) ^ k) / (2 : ℝ) ^ dyadicBias =
          ((qm : ℝ) / (2 : ℝ) ^ sh) * ((2 : ℝ) ^ a.e / (2 : ℝ) ^ b.e) := by
        have hp : (2 : ℝ) ^ k * (2 : ℝ) ^ dyadicBias * (2 : ℝ) ^ a.e =
            (2 : ℝ) ^ b.e * (2 : ℝ) ^ sh := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1; omega
        field_simp; linarith [congrArg ((qm : ℝ) * ·) hp.symm]
      exact hfl.trans (hexp.trans_le (mul_le_mul_of_nonneg_right hqm (by positivity)))

lemma le_divDyadicUb {a b : Dyadic} (hb : 0 < b.toReal) :
    a.toReal / b.toReal ≤ (divDyadicUb a b).toReal := by
  have hb0 : b.m ≠ 0 := fun h => hb.ne' (Dyadic.toReal_eq_zero_of_m h)
  unfold divDyadicUb
  by_cases ha0 : a.m = 0
  · simp [ha0, Dyadic.toReal_eq_zero_of_m ha0, Dyadic.zero_toReal]
  · have hcond : (b.m == 0 || a.m == 0) = false := by simp [hb0, ha0]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hb_pos_nat : 0 < b.m := Nat.pos_of_ne_zero hb0
    have hb_pos : (0 : ℝ) < (b.m : ℝ) := by exact_mod_cast hb_pos_nat
    set sh := 80 + Dyadic.msbPos b.m
    set qm := ((a.m <<< sh) + b.m - 1) / b.m
    have hqm : (a.m : ℝ) / (b.m : ℝ) ≤ (qm : ℝ) / (2 : ℝ) ^ sh := by
      rw [div_le_div_iff₀ hb_pos (by positivity)]
      have hmul : a.m * 2 ^ sh ≤ qm * b.m := by
        have hd := Nat.div_add_mod ((a.m <<< sh) + b.m - 1) b.m
        have hm := Nat.mod_lt ((a.m <<< sh) + b.m - 1) hb_pos_nat
        rw [Nat.mul_comm] at hd
        have hsh : a.m <<< sh = a.m * 2 ^ sh := Nat.shiftLeft_eq a.m sh
        dsimp only [qm]; omega
      exact_mod_cast hmul
    rw [dyadic_div_eq hb0]
    split_ifs with he
    · refine le_trans ?_ (Dyadic.le_trimUb _ 80)
      have hexp : (Dyadic.mk qm (a.e + dyadicBias - (b.e + sh))).toReal =
          ((qm : ℝ) / (2 : ℝ) ^ sh) * ((2 : ℝ) ^ a.e / (2 : ℝ) ^ b.e) := by
        unfold Dyadic.toReal; dsimp only; rw [Dyadic.twoPowBias_eq]
        have hp : (2 : ℝ) ^ (a.e + dyadicBias - (b.e + sh)) * (2 : ℝ) ^ b.e * (2 : ℝ) ^ sh =
            (2 : ℝ) ^ a.e * (2 : ℝ) ^ dyadicBias := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1; omega
        field_simp; linarith [congrArg ((qm : ℝ) * ·) hp]
      rw [hexp]
      exact mul_le_mul_of_nonneg_right hqm (by positivity)
    · set k := (b.e + sh) - (a.e + dyadicBias)
      have hcl : ((qm : ℝ) / (2 : ℝ) ^ k) / (2 : ℝ) ^ dyadicBias ≤
          (Dyadic.mk (Dyadic.ceilShr qm k) 0).toReal := by
        unfold Dyadic.toReal; dsimp only; rw [pow_zero, mul_one, Dyadic.twoPowBias_eq]
        exact div_le_div_of_nonneg_right (Dyadic.ceilShr_ge qm k) (by positivity)
      have hexp : ((qm : ℝ) / (2 : ℝ) ^ k) / (2 : ℝ) ^ dyadicBias =
          ((qm : ℝ) / (2 : ℝ) ^ sh) * ((2 : ℝ) ^ a.e / (2 : ℝ) ^ b.e) := by
        have hp : (2 : ℝ) ^ k * (2 : ℝ) ^ dyadicBias * (2 : ℝ) ^ a.e =
            (2 : ℝ) ^ b.e * (2 : ℝ) ^ sh := by
          rw [← pow_add, ← pow_add, ← pow_add]
          congr 1; omega
        field_simp; linarith [congrArg ((qm : ℝ) * ·) hp.symm]
      exact (mul_le_mul_of_nonneg_right hqm (by positivity)).trans (hexp.symm.trans_le hcl)

/-- Deterministic Q64 log interval for `x : Dyadic` (`1 ≤ x`), verified via `checkLogDyadic`. -/
def dyLogBounds (x : Dyadic) : Bool × Dyadic × Dyadic :=
  if x.m == 0 then (false, Dyadic.zero, Dyadic.zero)
  else
    let b := Dyadic.msbPos x.m
    if !(dyadicBias ≤ b + x.e) then (false, Dyadic.zero, Dyadic.zero)
    else
      let p2 := 1 <<< b
      let a := x.m - p2
      let den := x.m + p2
      let mU := (a <<< 64) / den
      let k := b + x.e - dyadicBias
      let u2Lo := (mU * mU) >>> 64
      let u2Hi := Dyadic.ceilShr ((mU + 1) * (mU + 1)) 64
      let s := logLoopList64 u2Lo u2Hi inv2OddPairs64 mU (mU + 1) 0 0
      let lo := Dyadic.ofQ64 (k * ln2Lo64 + s.1)
      let hi := Dyadic.ofQ64 (k * ln2Hi64 + s.2 + 256)
      (checkLogDyadic x ⟨b, mU⟩ lo hi, lo, hi)

lemma dyLogBounds_sound (consts : External.CertifiedConstants) {x : Dyadic}
    (h : (dyLogBounds x).1 = true) :
    (dyLogBounds x).2.1.toReal ≤ Real.log x.toReal ∧
      Real.log x.toReal ≤ (dyLogBounds x).2.2.toReal := by
  unfold dyLogBounds at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢
  dsimp only
  exact checkLogDyadic_sound consts h

def sumDyadicFin {n : ℕ} (f : Fin n → Dyadic) : Dyadic :=
  (List.finRange n).foldl (fun a i => a.add (f i)) Dyadic.zero

lemma sumDyadicFin_toReal {n : ℕ} (f : Fin n → Dyadic) :
    (sumDyadicFin f).toReal = ∑ i : Fin n, (f i).toReal := by
  have hgen : ∀ (L : List (Fin n)) (acc : Dyadic),
      (L.foldl (fun a i => a.add (f i)) acc).toReal =
        acc.toReal + (L.map (fun i => (f i).toReal)).sum := by
    intro L; induction L with
    | nil => intro acc; simp
    | cons i tl ih =>
      intro acc; rw [List.foldl_cons, ih, Dyadic.add_toReal, List.map_cons, List.sum_cons]; ring
  have h1 := hgen (List.finRange n) Dyadic.zero
  have hsum : (List.map (fun i => (f i).toReal) (List.finRange n)).sum = ∑ i : Fin n, (f i).toReal := by
    rw [← List.sum_toFinset _ (List.nodup_finRange n)]; simp
  rw [sumDyadicFin, h1, hsum, Dyadic.zero_toReal, zero_add]

lemma sum_fin_le_sumDyadicFin {n : ℕ} (f : Fin n → Dyadic) (g : Fin n → ℝ)
    (hg : ∀ i : Fin n, g i ≤ (f i).toReal) :
    ∑ i : Fin n, g i ≤ (sumDyadicFin f).toReal := by
  rw [sumDyadicFin_toReal]; exact Finset.sum_le_sum fun i _ => hg i

lemma sumDyadicFin_le_sum_fin {n : ℕ} (f : Fin n → Dyadic) (g : Fin n → ℝ)
    (hg : ∀ i : Fin n, (f i).toReal ≤ g i) :
    (sumDyadicFin f).toReal ≤ ∑ i : Fin n, g i := by
  rw [sumDyadicFin_toReal]; exact Finset.sum_le_sum fun i _ => hg i

end ExtraDyadicHelpers

section JOddAndMertHelpers

private lemma floorDiv_le_real_local {a b : ℕ} (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

private def harmChunk2c (lo len : ℕ) : ℕ :=
  (List.range len).foldl (fun s k => s + BuchstabSwitching.scaleS / (lo + k + 1)) 0

private lemma harmChunk2c_le_sum (lo len : ℕ) :
    ((harmChunk2c lo len : ℕ) : ℝ) / (BuchstabSwitching.scaleS : ℝ) ≤
      ∑ k ∈ Finset.Ico lo (lo + len), (1 : ℝ) / ((k : ℝ) + 1) := by
  induction len with
  | zero => simp [harmChunk2c]
  | succ m ih =>
    have heq : harmChunk2c lo (m + 1) = harmChunk2c lo m + BuchstabSwitching.scaleS / (lo + m + 1) := by
      simp [harmChunk2c, List.range_succ, List.foldl_append]
    have hdiv : ((BuchstabSwitching.scaleS / (lo + m + 1) : ℕ) : ℝ) / (BuchstabSwitching.scaleS : ℝ) ≤
        (1 : ℝ) / (((lo + m : ℕ) : ℝ) + 1) := by
      have h1 := floorDiv_le_real_local (a := BuchstabSwitching.scaleS) (b := lo + m + 1) (by omega)
      have h2 : ((BuchstabSwitching.scaleS : ℝ) / ((lo + m + 1 : ℕ) : ℝ)) / (BuchstabSwitching.scaleS : ℝ) =
          (1 : ℝ) / (((lo + m : ℕ) : ℝ) + 1) := by
        push_cast; field_simp [BuchstabSwitching.scaleS_pos.ne']
      exact (div_le_div_of_nonneg_right h1 BuchstabSwitching.scaleS_pos.le).trans_eq h2
    rw [heq, show lo + (m + 1) = (lo + m) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    push_cast at hdiv ⊢; rw [add_div]; exact add_le_add ih hdiv

private lemma harmonic_eq_sum_range (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [harmonic_succ, Rat.cast_add, Finset.sum_range_succ, ih, ← one_div]
    push_cast; rfl

private lemma hc2c_0 : harmChunk2c 0 32 = 4058495195428 := by native_decide
private lemma hc2c_1 : harmChunk2c 32 32 = 685395708257 := by native_decide
private lemma hc2c_2 : harmChunk2c 64 32 = 402872243836 := by native_decide
private lemma hc2c_3 : harmChunk2c 96 32 = 286383945022 := by native_decide
private lemma hc2c_4 : harmChunk2c 128 32 = 222364132337 := by native_decide
private lemma hc2c_5 : harmChunk2c 160 32 = 181801718088 := by native_decide
private lemma hc2c_6 : harmChunk2c 192 32 = 153779255741 := by native_decide
private lemma hc2c_7 : harmChunk2c 224 32 = 133252764007 := by native_decide

private lemma sum_Ico_split_256 :
    ∑ k ∈ Finset.Ico (0 : ℕ) 256, (1 : ℝ) / ((k : ℝ) + 1) =
      (∑ k ∈ Finset.Ico (0 : ℕ) 32, (1 : ℝ) / ((k : ℝ) + 1)) +
      (∑ k ∈ Finset.Ico (32 : ℕ) 64, (1 : ℝ) / ((k : ℝ) + 1)) +
      (∑ k ∈ Finset.Ico (64 : ℕ) 96, (1 : ℝ) / ((k : ℝ) + 1)) +
      (∑ k ∈ Finset.Ico (96 : ℕ) 128, (1 : ℝ) / ((k : ℝ) + 1)) +
      (∑ k ∈ Finset.Ico (128 : ℕ) 160, (1 : ℝ) / ((k : ℝ) + 1)) +
      (∑ k ∈ Finset.Ico (160 : ℕ) 192, (1 : ℝ) / ((k : ℝ) + 1)) +
      (∑ k ∈ Finset.Ico (192 : ℕ) 224, (1 : ℝ) / ((k : ℝ) + 1)) +
      (∑ k ∈ Finset.Ico (224 : ℕ) 256, (1 : ℝ) / ((k : ℝ) + 1)) := by
  let f : ℕ → ℝ := fun k => (1 : ℝ) / ((k : ℝ) + 1)
  rw [← Finset.sum_Ico_consecutive f (by omega : 0 ≤ 224) (by omega : 224 ≤ 256)]
  rw [← Finset.sum_Ico_consecutive f (by omega : 0 ≤ 192) (by omega : 192 ≤ 224)]
  rw [← Finset.sum_Ico_consecutive f (by omega : 0 ≤ 160) (by omega : 160 ≤ 192)]
  rw [← Finset.sum_Ico_consecutive f (by omega : 0 ≤ 128) (by omega : 128 ≤ 160)]
  rw [← Finset.sum_Ico_consecutive f (by omega : 0 ≤ 96) (by omega : 96 ≤ 128)]
  rw [← Finset.sum_Ico_consecutive f (by omega : 0 ≤ 64) (by omega : 64 ≤ 96)]
  rw [← Finset.sum_Ico_consecutive f (by omega : 0 ≤ 32) (by omega : 32 ≤ 64)]

lemma alpha0_ge_63518 : (63518 / 100000 : ℝ) ≤ BuchstabSwitching.alpha0 := by
  have h256 := (harmonic_sub_log_sub_eulerMascheroni_bounds 256 (by norm_num)).2
  have hlog256 : Real.log ((256 : ℕ) : ℝ) = 8 * Real.log 2 := by
    rw [show ((256 : ℕ) : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.log_pow]; ring
  rw [hlog256, show (1 : ℝ) / (2 * ((256 : ℕ) : ℝ)) = 1 / 512 by norm_num] at h256
  have c0 := harmChunk2c_le_sum 0 32; rw [hc2c_0] at c0
  have c1 := harmChunk2c_le_sum 32 32; rw [hc2c_1] at c1
  have c2 := harmChunk2c_le_sum 64 32; rw [hc2c_2] at c2
  have c3 := harmChunk2c_le_sum 96 32; rw [hc2c_3] at c3
  have c4 := harmChunk2c_le_sum 128 32; rw [hc2c_4] at c4
  have c5 := harmChunk2c_le_sum 160 32; rw [hc2c_5] at c5
  have c6 := harmChunk2c_le_sum 192 32; rw [hc2c_6] at c6
  have c7 := harmChunk2c_le_sum 224 32; rw [hc2c_7] at c7
  have hsum : (6124344962716 : ℝ) / (BuchstabSwitching.scaleS : ℝ) =
      (4058495195428 : ℝ) / (BuchstabSwitching.scaleS : ℝ) +
      (685395708257 : ℝ) / (BuchstabSwitching.scaleS : ℝ) +
      (402872243836 : ℝ) / (BuchstabSwitching.scaleS : ℝ) +
      (286383945022 : ℝ) / (BuchstabSwitching.scaleS : ℝ) +
      (222364132337 : ℝ) / (BuchstabSwitching.scaleS : ℝ) +
      (181801718088 : ℝ) / (BuchstabSwitching.scaleS : ℝ) +
      (153779255741 : ℝ) / (BuchstabSwitching.scaleS : ℝ) +
      (133252764007 : ℝ) / (BuchstabSwitching.scaleS : ℝ) := by
    unfold BuchstabSwitching.scaleS; norm_num
  have hharm : (6124344962716 : ℝ) / (BuchstabSwitching.scaleS : ℝ) ≤ (harmonic 256 : ℝ) := by
    rw [harmonic_eq_sum_range, ← Nat.Ico_zero_eq_range, sum_Ico_split_256]
    linarith only [c0, c1, c2, c3, c4, c5, c6, c7, hsum]
  have hsc : (BuchstabSwitching.scaleS : ℝ) = (10 : ℝ) ^ 12 := by
    unfold BuchstabSwitching.scaleS; norm_num
  rw [hsc] at hharm
  have hlog2_lt : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hnum : (63518 : ℝ) / 100000 ≤
      ((6124344962716 : ℝ) / (10 : ℝ) ^ 12 - 8 * (0.6931471808 : ℝ) - 1 / 512 + (0.6931471803 : ℝ)) / 2 := by
    norm_num
  unfold BuchstabSwitching.alpha0
  linarith only [h256, hharm, hlog2_lt, hlog2_gt, hnum]

private def h0LoDy : Dyadic := Dyadic.ofQ64 27932727089960614046
private def h0HiDy : Dyadic := Dyadic.ofQ64 27967774427758222114
private def cjUbDy : Dyadic := Dyadic.ofQ64 148137153875374043203
private def a0LbDy : Dyadic := Dyadic.ofQ64 11717002900738832995
def a0UbDy : Dyadic := Dyadic.ofQ64 11732129230879274828
private def log10e12HiDy : Dyadic := Dyadic.ofQ64 509702391329038242312

private lemma h0Lo_ok : 27932727089960614046 * 10 ^ 12 ≤ 1514236169719 * q64Scale := by native_decide
private lemma h0Hi_ok : 1516136089708 * q64Scale ≤ 27967774427758222114 * 10 ^ 12 := by native_decide
private lemma cjUb_ok : 8030531202875 * q64Scale ≤ 148137153875374043203 * 10 ^ 12 := by native_decide
private lemma a0Lb_ok : 11717002900738832995 * 100000 ≤ 63518 * q64Scale := by native_decide
private lemma a0Ub_ok : 636 * q64Scale ≤ 11732129230879274828 * 1000 := by native_decide

private lemma scaleS_eq_12 : (BuchstabSwitching.scaleS : ℝ) = (10 : ℝ) ^ 12 := by
  unfold BuchstabSwitching.scaleS; norm_num

private lemma h0LoDy_le : h0LoDy.toReal ≤ BuchstabSwitching.H_0 := by
  refine (le_trans ?_ BuchstabSwitching.H_0_bounds_cert.1)
  rw [h0LoDy, Dyadic.ofQ64_toReal, scaleS_eq_12, div_le_div_iff₀ q64Scale_pos (by positivity)]
  exact_mod_cast h0Lo_ok

private lemma le_h0HiDy : BuchstabSwitching.H_0 ≤ h0HiDy.toReal := by
  refine BuchstabSwitching.H_0_bounds_cert.2.trans ?_
  rw [h0HiDy, Dyadic.ofQ64_toReal, scaleS_eq_12, div_le_div_iff₀ (by positivity) q64Scale_pos]
  exact_mod_cast h0Hi_ok

private lemma le_cjUbDy : BuchstabSwitching.C_J ≤ cjUbDy.toReal := by
  refine BuchstabSwitching.C_J_le_cert.trans ?_
  rw [cjUbDy, Dyadic.ofQ64_toReal, scaleS_eq_12, div_le_div_iff₀ (by positivity) q64Scale_pos]
  exact_mod_cast cjUb_ok

private lemma a0LbDy_le : a0LbDy.toReal ≤ BuchstabSwitching.alpha0 := by
  refine le_trans ?_ alpha0_ge_63518
  rw [a0LbDy, Dyadic.ofQ64_toReal, div_le_div_iff₀ q64Scale_pos (by norm_num)]
  exact_mod_cast a0Lb_ok

lemma le_a0UbDy : BuchstabSwitching.alpha0 ≤ a0UbDy.toReal := by
  refine BuchstabSwitching.alpha0_le_636_div_1000.trans ?_
  rw [a0UbDy, Dyadic.ofQ64_toReal, div_le_div_iff₀ (by norm_num) q64Scale_pos]
  exact_mod_cast a0Ub_ok

/-- Q64 lower bound `exp(t)` via `expGeQ64`. -/
def expGeDyadic (t : Dyadic) : Dyadic :=
  Dyadic.ofQ64 (expGeQ64 t.toQ64Lb)

lemma expGeDyadic_sound (t : Dyadic) :
    0 < (expGeDyadic t).toReal ∧ (expGeDyadic t).toReal ≤ Real.exp t.toReal := by
  have he := expGeQ64_sound t.toReal_nonneg (Dyadic.toQ64Lb_le t)
  rw [expGeDyadic, Dyadic.ofQ64_toReal]
  refine ⟨div_pos (lt_of_lt_of_le q64Scale_pos he.1) q64Scale_pos, he.2⟩

/-- Q64 upper bound `exp(-x)` for `t.toReal ≤ x` via `1 / expGeQ64(t)`. -/
def expNegUbDyadic (t : Dyadic) : Dyadic :=
  let e64 := expGeQ64 t.toQ64Lb
  Dyadic.ofQ64 ((q64Scale * q64Scale + e64 - 1) / e64)

lemma expNegUbDyadic_sound {t : Dyadic} {x : ℝ} (ht : t.toReal ≤ x) :
    Real.exp (-x) ≤ (expNegUbDyadic t).toReal := by
  set e64 := expGeQ64 t.toQ64Lb
  have he := expGeQ64_sound t.toReal_nonneg (Dyadic.toQ64Lb_le t)
  have he_pos_nat : 0 < e64 := by
    have hq : 0 < q64Scale := by native_decide
    have hle : q64Scale ≤ e64 := by exact_mod_cast he.1
    omega
  have he_pos : (0 : ℝ) < (e64 : ℝ) := by exact_mod_cast he_pos_nat
  have h1 : Real.exp (-x) ≤ (q64Scale : ℝ) / (e64 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    have h2 : (e64 : ℝ) / (q64Scale : ℝ) ≤ Real.exp x := he.2.trans (Real.exp_le_exp.mpr ht)
    have hinv := one_div_le_one_div_of_le (div_pos he_pos q64Scale_pos) h2
    rwa [one_div_div] at hinv
  refine h1.trans ?_
  rw [expNegUbDyadic, Dyadic.ofQ64_toReal, div_le_div_iff₀ he_pos q64Scale_pos]
  have hmul : q64Scale * q64Scale ≤ ((q64Scale * q64Scale + e64 - 1) / e64) * e64 := by
    have hd := Nat.div_add_mod (q64Scale * q64Scale + e64 - 1) e64
    have hm := Nat.mod_lt (q64Scale * q64Scale + e64 - 1) he_pos_nat
    rw [Nat.mul_comm] at hd; omega
  exact_mod_cast hmul

def jOddLbDyadic (logLo : Dyadic) : Dyadic :=
  let mainLb := h0LoDy.mulLb ((logLo.divPow2Lb 1).add a0LbDy)
  let errUb := cjUbDy.mulUb (expNegUbDyadic (logLo.divPow2Lb 2))
  if errUb.ble mainLb then mainLb.subLb errUb else Dyadic.zero

lemma jOddLbDyadic_sound {logLo : Dyadic} {X : ℝ} (hX1 : 1 ≤ X) (hlog : logLo.toReal ≤ Real.log X) :
    (jOddLbDyadic logLo).toReal ≤ BuchstabSwitching.J_odd_lb_asym X := by
  unfold jOddLbDyadic; dsimp only; split_ifs with hcmp
  · have hXpos : 0 < X := by linarith
    have hneg : X ^ (-(1 / 4 : ℝ)) ≤ (expNegUbDyadic (logLo.divPow2Lb 2)).toReal := by
      rw [Real.rpow_def_of_pos hXpos, mul_neg, mul_one_div]
      exact expNegUbDyadic_sound ((Dyadic.divPow2Lb_le logLo 2).trans (by
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num]; linarith))
    have hm_le : (h0LoDy.mulLb ((logLo.divPow2Lb 1).add a0LbDy)).toReal ≤
        BuchstabSwitching.H_0 * ((1 / 2 : ℝ) * Real.log X + BuchstabSwitching.alpha0) := by
      refine (Dyadic.mulLb_le _ _).trans ?_
      rw [Dyadic.add_toReal]
      have hhalf := Dyadic.divPow2Lb_le logLo 1
      rw [pow_one] at hhalf
      exact mul_le_mul h0LoDy_le (by linarith [a0LbDy_le])
        (add_nonneg (Dyadic.toReal_nonneg _) a0LbDy.toReal_nonneg)
        (h0LoDy.toReal_nonneg.trans h0LoDy_le)
    have herr_le : BuchstabSwitching.C_J * X ^ (-(1 / 4 : ℝ)) ≤
        (cjUbDy.mulUb (expNegUbDyadic (logLo.divPow2Lb 2))).toReal :=
      (mul_le_mul le_cjUbDy hneg (Real.rpow_nonneg hXpos.le _) cjUbDy.toReal_nonneg).trans
        (Dyadic.le_mulUb _ _)
    exact (Dyadic.subLb_le (Dyadic.ble_sound hcmp)).trans (le_trans (by linarith) (le_max_right _ _))
  · rw [Dyadic.zero_toReal]; exact BuchstabSwitching.J_odd_lb_asym_nonneg X

def jOddUbDyadic (logLo logHi : Dyadic) : Dyadic :=
  (h0HiDy.mulUb ((logHi.divPow2Ub 1).add a0UbDy)).add
    (cjUbDy.mulUb (expNegUbDyadic (logLo.divPow2Lb 2)))

lemma jOddUbDyadic_sound {logLo logHi : Dyadic} {X : ℝ} (hX1 : 1 ≤ X)
    (hlo : logLo.toReal ≤ Real.log X) (hhi : Real.log X ≤ logHi.toReal) :
    BuchstabSwitching.J_odd_ub_asym X ≤ (jOddUbDyadic logLo logHi).toReal := by
  have hXpos : 0 < X := by linarith
  have hneg : X ^ (-(1 / 4 : ℝ)) ≤ (expNegUbDyadic (logLo.divPow2Lb 2)).toReal := by
    rw [Real.rpow_def_of_pos hXpos, mul_neg, mul_one_div]
    exact expNegUbDyadic_sound ((Dyadic.divPow2Lb_le logLo 2).trans (by
      rw [show (2 : ℝ) ^ 2 = 4 by norm_num]; linarith))
  have hmain : BuchstabSwitching.H_0 * ((1 / 2 : ℝ) * Real.log X + BuchstabSwitching.alpha0) ≤
      (h0HiDy.mulUb ((logHi.divPow2Ub 1).add a0UbDy)).toReal := by
    have hhalf := Dyadic.le_divPow2Ub logHi 1
    rw [pow_one] at hhalf
    have h1 : (1 / 2 : ℝ) * Real.log X + BuchstabSwitching.alpha0 ≤
        ((logHi.divPow2Ub 1).add a0UbDy).toReal := by
      rw [Dyadic.add_toReal]; linarith [le_a0UbDy]
    exact (mul_le_mul le_h0HiDy h1 (by have := Real.log_nonneg hX1; linarith [alpha0_ge_63518])
      h0HiDy.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
  have herr : BuchstabSwitching.C_J * X ^ (-(1 / 4 : ℝ)) ≤
      (cjUbDy.mulUb (expNegUbDyadic (logLo.divPow2Lb 2))).toReal :=
    (mul_le_mul le_cjUbDy hneg (Real.rpow_nonneg hXpos.le _) cjUbDy.toReal_nonneg).trans
      (Dyadic.le_mulUb _ _)
  unfold jOddUbDyadic BuchstabSwitching.J_odd_ub_asym
  rw [Dyadic.add_toReal]; linarith

def jOddHybridUbDyadic (logLo logHi : Dyadic) : Dyadic :=
  jOddStepMin logHi (jOddUbDyadic logLo logHi)

lemma jOddHybridUbDyadic_sound (consts : External.CertifiedConstants) {logLo logHi : Dyadic} {X : ℝ}
    (hX1 : 1 ≤ X) (hlo : logLo.toReal ≤ Real.log X) (hhi : Real.log X ≤ logHi.toReal) :
    BuchstabSwitching.J_odd X ≤ (jOddHybridUbDyadic logLo logHi).toReal :=
  jOddStepMin_sound consts hX1 hhi
    ((BuchstabSwitching.le_J_odd_ub_asym hX1).trans (jOddUbDyadic_sound hX1 hlo hhi))

def jsMertLoUbDyadic (logLo : Dyadic) : Dyadic := divDyadicUb dy2964Ub logLo

lemma jsMertLoUbDyadic_sound {logLo : Dyadic} {x : ℝ} (hpos : 0 < logLo.toReal)
    (hx : logLo.toReal ≤ Real.log x) : External.jsMertensLoErr x ≤ (jsMertLoUbDyadic logLo).toReal := by
  unfold External.jsMertensLoErr jsMertLoUbDyadic
  exact (div_le_div₀ dy2964Ub.toReal_nonneg le_dy2964Ub hpos hx).trans (le_divDyadicUb hpos)

def jsMertHiUbDyadic (logLo : Dyadic) : Dyadic :=
  let t1 := divDyadicUb dy6836Ub logLo
  if log10e12HiDy.ble logLo then t1
  else
    let sqLb := expGeDyadic (logLo.divPow2Lb 1)
    let t2 := divDyadicUb (divDyadicUb dyTwo sqLb) logLo
    if t1.ble t2 then t2 else t1

private lemma log10_hi_ok :
    checkLogNat 10 ⟨3, 2049638230412172401⟩ Dyadic.zero (Dyadic.ofQ64 42475197918399907507) = true ∧
    ((Dyadic.ofQ64 42475197918399907507).mulUb (Dyadic.ofNat 12)).blt log10e12HiDy = true := by native_decide

private lemma exp_log10e12_gt (consts : External.CertifiedConstants) :
    (10 : ℝ) ^ 12 < Real.exp log10e12HiDy.toReal := by
  have hr := (checkLogNat_sound consts log10_hi_ok.1).2
  rw [Nat.cast_ofNat] at hr
  have hlt := Dyadic.blt_sound log10_hi_ok.2
  have hmul := (mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ 12)).trans
    (by simpa [Dyadic.ofNat_toReal] using Dyadic.le_mulUb (Dyadic.ofQ64 42475197918399907507) (Dyadic.ofNat 12))
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (10 : ℝ) ^ 12), Real.exp_lt_exp, Real.log_pow]
  push_cast; linarith

def dyTen : Dyadic := Dyadic.ofNat 10
lemma dyTen_toReal : dyTen.toReal = 10 := by simpa [dyTen] using Dyadic.ofNat_toReal 10

lemma jsMertHiUbDyadic_sound (consts : External.CertifiedConstants) {logLo : Dyadic} {x : ℝ}
    (hx_pos : 0 < x) (h10 : dyTen.blt logLo = true)
    (hx : logLo.toReal ≤ Real.log x) : External.jsMertensHiErr x ≤ (jsMertHiUbDyadic logLo).toReal := by
  have h10r : (10 : ℝ) < logLo.toReal := by have := Dyadic.blt_sound h10; rwa [dyTen_toReal] at this
  have hlog_pos : 0 < logLo.toReal := by linarith
  have hx_log10 : 10 < Real.log x := h10r.trans_le hx
  have h6836 : (6.836e-6 : ℝ) / Real.log x ≤ (divDyadicUb dy6836Ub logLo).toReal :=
    (div_le_div₀ dy6836Ub.toReal_nonneg le_dy6836Ub hlog_pos hx).trans (le_divDyadicUb hlog_pos)
  set sqLb := expGeDyadic (logLo.divPow2Lb 1)
  have hbjv : ¬ x > (10 : ℝ) ^ 12 →
      External.jsMertensHiErr x ≤ (divDyadicUb (divDyadicUb dyTwo sqLb) logLo).toReal := by
    intro hx12; rw [External.jsMertensHiErr_eq_bjv (not_lt.mp hx12) hx_log10, ← div_div]
    have hsq : 0 < sqLb.toReal ∧ sqLb.toReal ≤ Real.sqrt x := by
      refine ⟨(expGeDyadic_sound _).1, (expGeDyadic_sound _).2.trans ?_⟩
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]
      refine Real.exp_le_exp.mpr ((Dyadic.divPow2Lb_le logLo 1).trans ?_)
      rw [pow_one]; linarith
    have hstep1 : 2 / Real.sqrt x ≤ (divDyadicUb dyTwo sqLb).toReal :=
      (div_le_div₀ dyTwo.toReal_nonneg dyTwo_toReal.symm.le hsq.1 hsq.2).trans (le_divDyadicUb hsq.1)
    exact (div_le_div₀ (Dyadic.toReal_nonneg _) hstep1 hlog_pos hx).trans (le_divDyadicUb hlog_pos)
  unfold jsMertHiUbDyadic; dsimp only; split_ifs with hbig hcmp
  · have hx12 : (10 : ℝ) ^ 12 < x := by
      simpa [Real.exp_log hx_pos] using
        (exp_log10e12_gt consts).trans_le (Real.exp_le_exp.mpr ((Dyadic.ble_sound hbig).trans hx))
    rw [External.jsMertensHiErr_eq_tail hx12]; exact h6836
  · by_cases hx12 : x > (10 : ℝ) ^ 12
    · rw [External.jsMertensHiErr_eq_tail hx12]; exact h6836.trans (Dyadic.ble_sound hcmp)
    · exact hbjv hx12
  · by_cases hx12 : x > (10 : ℝ) ^ 12
    · rw [External.jsMertensHiErr_eq_tail hx12]; exact h6836
    · exact (hbjv hx12).trans (Dyadic.ble_false_le (Bool.eq_false_iff.mpr hcmp))

end JOddAndMertHelpers

section JFullTerm1Helpers

private def linCombLog (a b d : ℕ) (sLo sHi tLo tHi : Dyadic) : Dyadic × Dyadic :=
  (divDyadicLb (((Dyadic.ofNat a).mulLb sLo).add ((Dyadic.ofNat b).mulLb tLo)) (Dyadic.ofNat d),
   divDyadicUb (((Dyadic.ofNat a).mulUb sHi).add ((Dyadic.ofNat b).mulUb tHi)) (Dyadic.ofNat d))

private lemma linCombLog_sound {a b d : ℕ} (hd : 0 < d) {sLo sHi tLo tHi : Dyadic} {s t : ℝ}
    (hs : sLo.toReal ≤ s ∧ s ≤ sHi.toReal) (ht : tLo.toReal ≤ t ∧ t ≤ tHi.toReal) :
    (linCombLog a b d sLo sHi tLo tHi).1.toReal ≤ ((a : ℝ) * s + (b : ℝ) * t) / (d : ℝ) ∧
      ((a : ℝ) * s + (b : ℝ) * t) / (d : ℝ) ≤ (linCombLog a b d sLo sHi tLo tHi).2.toReal := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_dy_pos : 0 < (Dyadic.ofNat d).toReal := by rwa [Dyadic.ofNat_toReal]
  constructor
  · have h1 := divDyadicLb_le (((Dyadic.ofNat a).mulLb sLo).add ((Dyadic.ofNat b).mulLb tLo)) (Dyadic.ofNat d)
    rw [Dyadic.ofNat_toReal, Dyadic.add_toReal] at h1
    refine h1.trans (div_le_div_of_nonneg_right ?_ hd_pos.le)
    have ha0 : (Dyadic.ofNat a).toReal * sLo.toReal ≤ (a : ℝ) * s := by
      rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left hs.1 (Nat.cast_nonneg _)
    have hb0 : (Dyadic.ofNat b).toReal * tLo.toReal ≤ (b : ℝ) * t := by
      rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg _)
    exact add_le_add ((Dyadic.mulLb_le _ _).trans ha0) ((Dyadic.mulLb_le _ _).trans hb0)
  · have h2 := le_divDyadicUb (a := (((Dyadic.ofNat a).mulUb sHi).add ((Dyadic.ofNat b).mulUb tHi))) hd_dy_pos
    rw [Dyadic.ofNat_toReal, Dyadic.add_toReal] at h2
    refine (div_le_div_of_nonneg_right ?_ hd_pos.le).trans h2
    have ha0 : (a : ℝ) * s ≤ (Dyadic.ofNat a).toReal * sHi.toReal := by
      rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left hs.2 (Nat.cast_nonneg _)
    have hb0 : (b : ℝ) * t ≤ (Dyadic.ofNat b).toReal * tHi.toReal := by
      rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg _)
    exact add_le_add (ha0.trans (Dyadic.le_mulUb _ _)) (hb0.trans (Dyadic.le_mulUb _ _))

def jFullTerm1 (zLogLo zLogHi xiLogLo xiLogHi xiLb : Dyadic) (k : Fin 12) : Bool × Dyadic :=
  let w0 := linCombLog (12 - k.1) k.1 12 zLogLo zLogHi xiLogLo xiLogHi
  let w1 := linCombLog (11 - k.1) (k.1 + 1) 12 zLogLo zLogHi xiLogLo xiLogHi
  let w1pHi := if k.1 + 1 == 12 then w1.2.add (divDyadicUb dyOne xiLb) else w1.2
  let rUb := divDyadicUb w1pHi w0.1
  let rLog := dyLogBounds rUb
  let w0Lb := expGeDyadic w0.1
  let den2 := w0Lb.subLb dyTwo
  let mertUb := ((rLog.2.2.add (jsMertHiUbDyadic w1.1)).add (jsMertLoUbDyadic w0.1)).add (divDyadicUb dyTwo den2)
  let ok := dyTen.blt w0.1 && dyTen.blt w1.1 && dyTwo.ble w0Lb && dyOne.ble den2 && rLog.1
  (ok, (jOddHybridUbDyadic (xiLogLo.subLb w0.2) (xiLogHi.subLb w0.1)).mulUb mertUb)

private lemma jFullTerm1_sound_aux (consts : External.CertifiedConstants) {z_nat : ℕ} {xi : ℝ}
    (hz_pos : (0 : ℝ) < (z_nat : ℝ)) (hzxi : (z_nat : ℝ) < xi)
    {xiLogLo xiLogHi xiLb : Dyadic}
    (hxiL : xiLogLo.toReal ≤ Real.log xi ∧ Real.log xi ≤ xiLogHi.toReal)
    (hxiLbPos : 0 < xiLb.toReal) (hxiLb : xiLb.toReal ≤ xi) (k : Fin 12)
    {w0Lo w0Hi w1Lo w1Hi w1pHi rUb rLogUb w0Lb den2 : Dyadic}
    (hw0_b : w0Lo.toReal ≤ ((12 - k.1 : ℕ) * Real.log (z_nat : ℝ) + (k.1 : ℕ) * Real.log xi) / 12 ∧
      ((12 - k.1 : ℕ) * Real.log (z_nat : ℝ) + (k.1 : ℕ) * Real.log xi) / 12 ≤ w0Hi.toReal)
    (hw1_b : w1Lo.toReal ≤ ((11 - k.1 : ℕ) * Real.log (z_nat : ℝ) + ((k.1 + 1 : ℕ) : ℝ) * Real.log xi) / 12 ∧
      ((11 - k.1 : ℕ) * Real.log (z_nat : ℝ) + ((k.1 + 1 : ℕ) : ℝ) * Real.log xi) / 12 ≤ w1Hi.toReal)
    (hw010 : dyTen.blt w0Lo = true) (hw110 : dyTen.blt w1Lo = true)
    (hw0Lb_eq : w0Lb = expGeDyadic w0Lo) (hden2_eq : den2 = w0Lb.subLb dyTwo)
    (hw02 : dyTwo.ble w0Lb = true) (hden1 : dyOne.ble den2 = true)
    (hw1pHi_eq : w1pHi = if k.1 + 1 == 12 then w1Hi.add (divDyadicUb dyOne xiLb) else w1Hi)
    (hrUb_eq : rUb = divDyadicUb w1pHi w0Lo)
    (hokL : (dyLogBounds rUb).1 = true)
    (hrLog_eq : rLogUb = (dyLogBounds rUb).2.2) :
    let w : Fin 13 → ℝ := fun j =>
      Real.exp (((12 - j.1 : ℕ) * Real.log (z_nat : ℝ) + (j.1 : ℕ) * Real.log xi) / 12)
    let w0 := w k.castSucc
    let w1p := if k.val + 1 = 12 then w k.succ + 1 else w k.succ
    BuchstabSwitching.J_odd (xi / w0) *
        (max 0 (Real.log (Real.log w1p / Real.log w0) +
          External.jsMertensHiErr w1p + External.jsMertensLoErr w0) + 2 / (w0 - 2)) ≤
      ((jOddHybridUbDyadic (xiLogLo.subLb w0Hi) (xiLogHi.subLb w0Lo)).mulUb
        (((rLogUb.add (jsMertHiUbDyadic w1Lo)).add (jsMertLoUbDyadic w0Lo)).add
          (divDyadicUb dyTwo den2))).toReal := by
  intro w w0 w1p
  have hxi_pos : 0 < xi := hz_pos.trans hzxi
  have hw_log : ∀ j : Fin 13, Real.log (w j) =
      ((12 - j.1 : ℕ) * Real.log (z_nat : ℝ) + (j.1 : ℕ) * Real.log xi) / 12 := fun j => Real.log_exp _
  have hlogw0_eq : Real.log w0 = ((12 - k.1 : ℕ) * Real.log (z_nat : ℝ) + (k.1 : ℕ) * Real.log xi) / 12 :=
    hw_log k.castSucc
  have hlogw1_eq : Real.log (w k.succ) = ((11 - k.1 : ℕ) * Real.log (z_nat : ℝ) + ((k.1 + 1 : ℕ) : ℝ) * Real.log xi) / 12 := by
    rw [hw_log k.succ]; simp [Fin.val_succ, show 12 - (k.1 + 1) = 11 - k.1 by omega]
  rw [← hlogw0_eq] at hw0_b; rw [← hlogw1_eq] at hw1_b
  have hw0_pos : 0 < w0 := Real.exp_pos _
  have hw1_pos : 0 < w k.succ := Real.exp_pos _
  have hs_lt_t : Real.log (z_nat : ℝ) < Real.log xi := Real.log_lt_log hz_pos hzxi
  have hw0_le_xi : w0 ≤ xi := by
    rw [← Real.exp_log hxi_pos]; refine Real.exp_le_exp.mpr ?_
    have hsub : ((12 - k.1 : ℕ) : ℝ) = 12 - (k.1 : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
    have hk12 : (k.1 : ℝ) ≤ 12 := by exact_mod_cast k.isLt.le
    dsimp [w0, w]; rw [hsub]; nlinarith
  have hw0_le_w1 : w0 ≤ w k.succ := by
    refine Real.exp_le_exp.mpr ?_
    have h12 : ((12 - k.1 : ℕ) : ℝ) = 12 - (k.1 : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
    have h11 : ((12 - (k.1 + 1) : ℕ) : ℝ) = 11 - (k.1 : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    dsimp [w0, w]; rw [h12, h11]; push_cast; nlinarith
  have hw1_le_w1p : w k.succ ≤ w1p := by dsimp [w1p]; split_ifs <;> linarith
  have hw1p_pos : 0 < w1p := lt_of_lt_of_le hw1_pos hw1_le_w1p
  have hw1p_b : w1Lo.toReal ≤ Real.log w1p ∧ Real.log w1p ≤ w1pHi.toReal := by
    refine ⟨hw1_b.1.trans (Real.log_le_log hw1_pos hw1_le_w1p), ?_⟩
    rw [hw1pHi_eq]; dsimp [w1p]
    by_cases hk12 : k.1 + 1 = 12
    · have hk12v : k.val + 1 = 12 := hk12
      simp only [hk12v, beq_self_eq_true, ↓reduceIte]
      have hw1_xi : w k.succ = xi := by
        dsimp [w]; rw [hk12]; simp [Real.exp_log hxi_pos]
      rw [hw1_xi, Dyadic.add_toReal, show xi + 1 = xi * (1 + 1 / xi) by field_simp [hxi_pos.ne'],
        Real.log_mul hxi_pos.ne' (by positivity)]
      have hlog_1 : Real.log (1 + 1 / xi) ≤ 1 / xi := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / xi)]
      have hinv : 1 / xi ≤ (divDyadicUb dyOne xiLb).toReal :=
        (one_div_le_one_div_of_le hxiLbPos hxiLb).trans
          (by simpa [dyOne_toReal] using le_divDyadicUb (a := dyOne) hxiLbPos)
      have hlogxi : Real.log xi ≤ w1Hi.toReal := by rw [← hw1_xi]; exact hw1_b.2
      linarith
    · have hk12v : k.val + 1 ≠ 12 := hk12
      have hk12b : (k.1 + 1 == 12) = false := beq_false_of_ne hk12
      simp only [hk12v, ↓reduceIte, hk12b, Bool.false_eq_true]
      exact hw1_b.2
  have hw0_10r : (10 : ℝ) < w0Lo.toReal := by
    have h := Dyadic.blt_sound hw010; rwa [dyTen_toReal] at h
  have hr_le : Real.log (Real.log w1p / Real.log w0) ≤ rLogUb.toReal := by
    have hlogw0_pos : 0 < Real.log w0 := by linarith [hw0_b.1]
    have hlogw1p_pos : 0 < Real.log w1p := lt_of_lt_of_le hlogw0_pos
      ((Real.log_le_log hw0_pos hw0_le_w1).trans (Real.log_le_log hw1_pos hw1_le_w1p))
    have hratio : Real.log w1p / Real.log w0 ≤ rUb.toReal := by
      rw [hrUb_eq]
      exact (div_le_div₀ w1pHi.toReal_nonneg hw1p_b.2 (by linarith : 0 < w0Lo.toReal) hw0_b.1).trans
        (le_divDyadicUb (by linarith : 0 < w0Lo.toReal))
    have hrat := (dyLogBounds_sound consts hokL).2
    rw [hrLog_eq]
    exact (Real.log_le_log (div_pos hlogw1p_pos hlogw0_pos) hratio).trans hrat
  have h2_ge_dy : dyTwo.toReal ≤ w0Lb.toReal := Dyadic.ble_sound hw02
  have h2_ge : (2 : ℝ) ≤ w0Lb.toReal := by rwa [dyTwo_toReal] at h2_ge_dy
  have hw0_ge_w0Lb : w0Lb.toReal ≤ w0 := by
    rw [hw0Lb_eq]
    have h := (expGeDyadic_sound w0Lo).2.trans (Real.exp_le_exp.mpr hw0_b.1)
    rwa [Real.exp_log hw0_pos] at h
  have hw0_2_le : 2 / (w0 - 2) ≤ (divDyadicUb dyTwo den2).toReal := by
    have h1_dy : dyOne.toReal ≤ den2.toReal := Dyadic.ble_sound hden1
    have h1 : (1 : ℝ) ≤ den2.toReal := by rwa [dyOne_toReal] at h1_dy
    have hsub : den2.toReal ≤ w0Lb.toReal - 2 := by
      rw [hden2_eq]
      have h := Dyadic.subLb_le h2_ge_dy
      rwa [dyTwo_toReal] at h
    exact (div_le_div₀ dyTwo.toReal_nonneg dyTwo_toReal.symm.le (by linarith : 0 < den2.toReal)
      (by linarith : den2.toReal ≤ w0 - 2)).trans (le_divDyadicUb (by linarith : 0 < den2.toReal))
  have hJub : BuchstabSwitching.J_odd (xi / w0) ≤
      (jOddHybridUbDyadic (xiLogLo.subLb w0Hi) (xiLogHi.subLb w0Lo)).toReal := by
    refine jOddHybridUbDyadic_sound consts ((one_le_div hw0_pos).mpr hw0_le_xi) ?_ ?_
    · rw [Real.log_div hxi_pos.ne' hw0_pos.ne']
      exact (Dyadic.subLb_le_max_zero hxiL.1 hw0_b.2).trans
        (by rw [max_eq_right (sub_nonneg.mpr (Real.log_le_log hw0_pos hw0_le_xi))])
    · rw [Real.log_div hxi_pos.ne' hw0_pos.ne']
      exact (by linarith [hxiL.2, hw0_b.1] : Real.log xi - Real.log w0 ≤ xiLogHi.toReal - w0Lo.toReal).trans
        (Dyadic.sub_le_subLb_toReal _ _)
  have hmert_le : max 0 (Real.log (Real.log w1p / Real.log w0) + External.jsMertensHiErr w1p + External.jsMertensLoErr w0) +
      2 / (w0 - 2) ≤ (((rLogUb.add (jsMertHiUbDyadic w1Lo)).add (jsMertLoUbDyadic w0Lo)).add (divDyadicUb dyTwo den2)).toReal := by
    have hhi := jsMertHiUbDyadic_sound consts hw1p_pos hw110 hw1p_b.1
    have hlo := jsMertLoUbDyadic_sound (by linarith) hw0_b.1
    rw [Dyadic.add_toReal, Dyadic.add_toReal, Dyadic.add_toReal]
    have hnn : 0 ≤ rLogUb.toReal + (jsMertHiUbDyadic w1Lo).toReal + (jsMertLoUbDyadic w0Lo).toReal :=
      add_nonneg (add_nonneg rLogUb.toReal_nonneg (Dyadic.toReal_nonneg _)) (Dyadic.toReal_nonneg _)
    have hmax : max 0 (Real.log (Real.log w1p / Real.log w0) + External.jsMertensHiErr w1p + External.jsMertensLoErr w0) ≤
        rLogUb.toReal + (jsMertHiUbDyadic w1Lo).toReal + (jsMertLoUbDyadic w0Lo).toReal :=
      max_le hnn (by linarith)
    linarith
  exact (mul_le_mul hJub hmert_le (add_nonneg (le_max_left _ _) (div_nonneg (by norm_num) (by linarith)))
    (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)

lemma jFullTerm1_sound (consts : External.CertifiedConstants) {z_nat : ℕ} {xi : ℝ}
    (_hz3 : 3 ≤ z_nat) (hzxi : (z_nat : ℝ) < xi) {zLogLo zLogHi xiLogLo xiLogHi xiLb : Dyadic}
    (hzL : zLogLo.toReal ≤ Real.log (z_nat : ℝ) ∧ Real.log (z_nat : ℝ) ≤ zLogHi.toReal)
    (hxiL : xiLogLo.toReal ≤ Real.log xi ∧ Real.log xi ≤ xiLogHi.toReal)
    (hxiLbPos : 0 < xiLb.toReal) (hxiLb : xiLb.toReal ≤ xi) (k : Fin 12)
    (hk : (jFullTerm1 zLogLo zLogHi xiLogLo xiLogHi xiLb k).1 = true) :
    let w : Fin 13 → ℝ := fun j =>
      Real.exp (((12 - j.1 : ℕ) * Real.log (z_nat : ℝ) + (j.1 : ℕ) * Real.log xi) / 12)
    let w0 := w k.castSucc
    let w1p := if k.val + 1 = 12 then w k.succ + 1 else w k.succ
    BuchstabSwitching.J_odd (xi / w0) *
        (max 0 (Real.log (Real.log w1p / Real.log w0) +
          External.jsMertensHiErr w1p + External.jsMertensLoErr w0) + 2 / (w0 - 2)) ≤
      (jFullTerm1 zLogLo zLogHi xiLogLo xiLogHi xiLb k).2.toReal := by
  unfold jFullTerm1 at hk ⊢
  dsimp only at hk ⊢
  rcases (Bool.and_eq_true _ _).mp hk with ⟨hk4, hokL⟩
  rcases (Bool.and_eq_true _ _).mp hk4 with ⟨hk3, hden1⟩
  rcases (Bool.and_eq_true _ _).mp hk3 with ⟨hk2, hw02⟩
  rcases (Bool.and_eq_true _ _).mp hk2 with ⟨hw010, hw110⟩
  have hz_pos : (0 : ℝ) < (z_nat : ℝ) := by exact_mod_cast (by omega : 0 < z_nat)
  have hw0_b := linCombLog_sound (a := 12 - k.1) (b := k.1) (d := 12) (by norm_num) hzL hxiL
  have hw1_b := linCombLog_sound (a := 11 - k.1) (b := k.1 + 1) (d := 12) (by norm_num) hzL hxiL
  rw [Nat.cast_ofNat] at hw0_b hw1_b
  exact jFullTerm1_sound_aux consts hz_pos hzxi hxiL hxiLbPos hxiLb k hw0_b hw1_b hw010 hw110
    rfl rfl hw02 hden1 rfl rfl hokL rfl

end JFullTerm1Helpers

end

end BuchstabSwitching.SieveInst
