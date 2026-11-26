import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTable
import BuchstabSwitching.Sieve.BonferroniEstimates
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import Mathlib.Tactic

/-!
# Certified `SciNat` Operations, `sqrt`, `log`, `exp`, and `elemSymInterval` for Regime 2

Provides:
- `SciProofs` namespace with `ble_sound`, `blt_sound`, `mul_toReal`, `add_toReal`, `ofNat_toReal`,
  `subLb_le`, `divUb_le`, `divLb_le`, `trimUb_le`, `trimLb_le`;
- Relative-precision `divUbSig` / `divLbSig` and `sqrtSciBounds`;
- `ratLogBounds`, `checkRatLogBounds`, `checkLogNat` (`x` up to `10^600+`, using binary power
  reduction + 14-term `artanh` at `10^16` scale + `consts.ln2_bounds`);
- `expUbBounds`, `checkExpPos`, `checkExpNeg` (halving + 12-term Taylor upper bound at `10^16`);
- `elemSymInterval` (outward-rounded DP for `elemSym gTot ps.toFinset j`).
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

/-! ## 1. `SciProofs` Soundness Lemmas, Significant-Digit Division, and `sqrtSciBounds` -/

namespace SciProofs

lemma ofNat_toReal (n : ℕ) : (SciNat.ofNat n).toReal = (n : ℝ) := by simp [SciNat.ofNat, SciNat.toReal]

lemma mul_toReal (a b : SciNat) : (a.mul b).toReal = a.toReal * b.toReal := by
  simp only [SciNat.mul, SciNat.toReal, Nat.cast_mul, pow_add]; ring

private lemma pow10_split {e₁ e₂ : ℕ} (h : e₁ ≤ e₂) :
    (10 : ℝ) ^ e₂ = (10 : ℝ) ^ e₁ * (10 : ℝ) ^ (e₂ - e₁) := by rw [← pow_add, Nat.add_sub_of_le h]

lemma add_toReal (a b : SciNat) : (a.add b).toReal = a.toReal + b.toReal := by
  unfold SciNat.add SciNat.toReal
  split_ifs with he
  · have ha : (0 : ℝ) < (10 : ℝ) ^ a.e := by positivity
    have hd : (0 : ℝ) < (10 : ℝ) ^ (b.e - a.e) := by positivity
    push_cast; rw [pow10_split he]; field_simp [ha.ne', hd.ne']
  · have he' : b.e ≤ a.e := le_of_not_ge he
    have hb : (0 : ℝ) < (10 : ℝ) ^ b.e := by positivity
    have hd : (0 : ℝ) < (10 : ℝ) ^ (a.e - b.e) := by positivity
    push_cast; rw [pow10_split he']; field_simp [hb.ne', hd.ne']

lemma ble_sound {a b : SciNat} (h : a.ble b = true) : a.toReal ≤ b.toReal := by
  unfold SciNat.ble at h; unfold SciNat.toReal
  split_ifs at h with he
  · have hm : (a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e) ≤ (b.m : ℝ) := by exact_mod_cast decide_eq_true_eq.mp h
    have ha : (0 : ℝ) < (10 : ℝ) ^ a.e := by positivity
    rw [div_le_div_iff₀ ha (by positivity), pow10_split he]
    calc (a.m : ℝ) * ((10 : ℝ) ^ a.e * (10 : ℝ) ^ (b.e - a.e))
        = ((a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e)) * (10 : ℝ) ^ a.e := by ring
      _ ≤ (b.m : ℝ) * (10 : ℝ) ^ a.e := mul_le_mul_of_nonneg_right hm ha.le
  · have he' : b.e ≤ a.e := le_of_not_ge he
    have hm : (a.m : ℝ) ≤ (b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e) := by exact_mod_cast decide_eq_true_eq.mp h
    have hb : (0 : ℝ) < (10 : ℝ) ^ b.e := by positivity
    rw [div_le_div_iff₀ (by positivity) hb, pow10_split he']
    calc (a.m : ℝ) * (10 : ℝ) ^ b.e
        ≤ ((b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e)) * (10 : ℝ) ^ b.e := mul_le_mul_of_nonneg_right hm hb.le
      _ = (b.m : ℝ) * ((10 : ℝ) ^ b.e * (10 : ℝ) ^ (a.e - b.e)) := by ring

lemma blt_sound {a b : SciNat} (h : a.blt b = true) : a.toReal < b.toReal := by
  unfold SciNat.blt at h; unfold SciNat.toReal
  split_ifs at h with he
  · have hm : (a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e) < (b.m : ℝ) := by exact_mod_cast decide_eq_true_eq.mp h
    have ha : (0 : ℝ) < (10 : ℝ) ^ a.e := by positivity
    rw [div_lt_div_iff₀ ha (by positivity), pow10_split he]
    calc (a.m : ℝ) * ((10 : ℝ) ^ a.e * (10 : ℝ) ^ (b.e - a.e))
        = ((a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e)) * (10 : ℝ) ^ a.e := by ring
      _ < (b.m : ℝ) * (10 : ℝ) ^ a.e := mul_lt_mul_of_pos_right hm ha
  · have he' : b.e ≤ a.e := le_of_not_ge he
    have hm : (a.m : ℝ) < (b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e) := by exact_mod_cast decide_eq_true_eq.mp h
    have hb : (0 : ℝ) < (10 : ℝ) ^ b.e := by positivity
    rw [div_lt_div_iff₀ (by positivity) hb, pow10_split he']
    calc (a.m : ℝ) * (10 : ℝ) ^ b.e
        < ((b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e)) * (10 : ℝ) ^ b.e := mul_lt_mul_of_pos_right hm hb
      _ = (b.m : ℝ) * ((10 : ℝ) ^ b.e * (10 : ℝ) ^ (a.e - b.e)) := by ring

lemma subLb_le {a b : SciNat} (h : b.toReal ≤ a.toReal) : (a.subLb b).toReal ≤ a.toReal - b.toReal :=
  SciNat.subLb_le h
lemma divUb_le (a b : SciNat) (prec : ℕ := 24) : a.toReal / b.toReal ≤ (a.divUb b prec).toReal :=
  SciNat.divUb_le a b prec
lemma divLb_le (a b : SciNat) (prec : ℕ := 24) : (a.divLb b prec).toReal ≤ a.toReal / b.toReal :=
  SciNat.divLb_le a b prec
lemma trimUb_le (a : SciNat) (maxExp : ℕ := 30) : a.toReal ≤ (a.trimUb maxExp).toReal :=
  SciNat.trimUb_le a maxExp
lemma trimLb_le (a : SciNat) (maxExp : ℕ := 30) : (a.trimLb maxExp).toReal ≤ a.toReal :=
  SciNat.trimLb_le a maxExp

lemma ceilDiv_ge {n d : ℕ} (hd : 0 < d) : (n : ℝ) / (d : ℝ) ≤ (SciNat.ceilDiv n d : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have hnat : n ≤ SciNat.ceilDiv n d * d := by
    by_cases hn : n = 0
    · subst hn; simp
    · unfold SciNat.ceilDiv; simp only [hd.ne', ↓reduceIte]
      have h1 := Nat.div_add_mod (n + d - 1) d; have h2 := Nat.mod_lt (n + d - 1) hd
      have hcomm : d * ((n + d - 1) / d) = (n + d - 1) / d * d := Nat.mul_comm _ _
      omega
  exact_mod_cast hnat

end SciProofs

private def numDigits10Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else 1 + numDigits10Aux k (n / 10)

def divSigPrec (b : SciNat) (sig : ℕ := 24) : ℕ := (numDigits10Aux 1000 b.m - b.e) + sig
def divUbSig (a b : SciNat) (sig : ℕ := 24) : SciNat := a.divUb b (divSigPrec b sig)
def divLbSig (a b : SciNat) (sig : ℕ := 24) : SciNat := a.divLb b (divSigPrec b sig)
lemma divUbSig_le (a b : SciNat) (sig : ℕ := 24) : a.toReal / b.toReal ≤ (divUbSig a b sig).toReal :=
  SciNat.divUb_le a b (divSigPrec b sig)
lemma divLbSig_le (a b : SciNat) (sig : ℕ := 24) : (divLbSig a b sig).toReal ≤ a.toReal / b.toReal :=
  SciNat.divLb_le a b (divSigPrec b sig)

private def findPow2Mul256 (num : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, p2, k => (p2, k)
  | fuel + 1, p2, k =>
    if p2 * 256 ≤ num then findPow2Mul256 num fuel (p2 * 256) (k + 8) else (p2, k)

private def findPow2Mul2 (num : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k
  | fuel + 1, p2, k =>
    if p2 * 2 ≤ num then findPow2Mul2 num fuel (p2 * 2) (k + 1) else k

private def findPow2 (num den : ℕ) : ℕ :=
  if den = 0 then 0
  else
    let (p2, k) := findPow2Mul256 num 512 den 0
    findPow2Mul2 num 8 p2 k

private def sqrtNewtonAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | steps + 1, g =>
    if g = 0 then 0
    else
      let g' := (g + n / g) / 2
      if g' ≥ g then g else sqrtNewtonAux n steps g'

private def sqrtFast (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let k := findPow2 n 1
    sqrtNewtonAux n 16 (2 ^ (k / 2 + 1))

def sqrtSciBounds (n : ℕ) (prec : ℕ := 18) : Bool × SciNat × SciNat :=
  let scaled := n * 10 ^ (2 * prec)
  let s := sqrtFast scaled
  let ok := decide (s ^ 2 ≤ scaled) && decide (scaled < (s + 1) ^ 2)
  (ok, ⟨s, prec⟩, ⟨s + 1, prec⟩)

lemma sqrtSciBounds_sound {n prec : ℕ} (h : (sqrtSciBounds n prec).1 = true) :
    (sqrtSciBounds n prec).2.1.toReal ≤ Real.sqrt (n : ℝ) ∧
      Real.sqrt (n : ℝ) ≤ (sqrtSciBounds n prec).2.2.toReal := by
  unfold sqrtSciBounds at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  dsimp only
  set s := sqrtFast (n * 10 ^ (2 * prec))
  have h1 : (s : ℝ) ^ 2 ≤ (n : ℝ) * ((10 : ℝ) ^ prec) ^ 2 := by
    have hnat : (s : ℝ) ^ 2 ≤ ((n * 10 ^ (2 * prec) : ℕ) : ℝ) := by exact_mod_cast h.1
    push_cast at hnat
    rwa [show (10 : ℝ) ^ (2 * prec) = ((10 : ℝ) ^ prec) ^ 2 by rw [← pow_mul, mul_comm]] at hnat
  have h2 : (n : ℝ) * ((10 : ℝ) ^ prec) ^ 2 ≤ ((s + 1 : ℕ) : ℝ) ^ 2 := by
    have hnat : ((n * 10 ^ (2 * prec) : ℕ) : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast h.2.le
    push_cast at hnat ⊢
    rwa [show (10 : ℝ) ^ (2 * prec) = ((10 : ℝ) ^ prec) ^ 2 by rw [← pow_mul, mul_comm]] at hnat
  have hpow_pos : (0 : ℝ) < (10 : ℝ) ^ prec := by positivity
  unfold SciNat.toReal
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hpow_pos)]
    exact h1
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hpow_pos)]
    exact h2

/-! ## 2. Certified `log` Checker (`checkRatLogBounds`, `checkLogNat`) -/

private def logScale16 : ℕ := 10 ^ 16
private def ln2Lo16 : ℕ := 6931471805599450
private def ln2Hi16 : ℕ := 6931471805599460
private def logTail16 : ℕ := 12

private lemma logScale16_pos : (0 : ℝ) < (logScale16 : ℝ) := by
  unfold logScale16; positivity

private def logLoop16 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, _, _, _, _, sLo, sHi => (sLo, sHi)
  | n + 1, j, a2, b2, tLo, tHi, sLo, sHi =>
    let d := 2 * j + 1
    logLoop16 n (j + 1) a2 b2 ((tLo * a2) / b2) (SciNat.ceilDiv (tHi * a2) b2)
      (sLo + (2 * tLo) / d) (sHi + SciNat.ceilDiv (2 * tHi) d)

private lemma logLoop16_sound {a b : ℕ} (hb : 0 < b) :
    ∀ (n j tLo tHi sLo sHi : ℕ),
      (tLo : ℝ) / (logScale16 : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ (2 * j + 1) →
      ((a : ℝ) / (b : ℝ)) ^ (2 * j + 1) ≤ (tHi : ℝ) / (logScale16 : ℝ) →
      let res := logLoop16 n j (a * a) (b * b) tLo tHi sLo sHi
      ((res.1 : ℝ) - (sLo : ℝ)) / (logScale16 : ℝ) ≤
        ∑ m ∈ Finset.range n, (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) *
          ((a : ℝ) / (b : ℝ)) ^ (2 * (j + m) + 1) ∧
      ∑ m ∈ Finset.range n, (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) *
          ((a : ℝ) / (b : ℝ)) ^ (2 * (j + m) + 1) ≤
        ((res.2 : ℝ) - (sHi : ℝ)) / (logScale16 : ℝ) := by
  intro n
  induction n with
  | zero => intro j tLo tHi sLo sHi _ _; simp [logLoop16]
  | succ n ih =>
    intro j tLo tHi sLo sHi htLo htHi
    set d : ℕ := 2 * j + 1
    set u : ℝ := (a : ℝ) / (b : ℝ)
    have hd_pos : 0 < d := by omega
    have hb2_pos : 0 < b * b := Nat.mul_pos hb hb
    have hS : (0 : ℝ) < (logScale16 : ℝ) := logScale16_pos
    have hu_nn : 0 ≤ u := by positivity
    have hd_eq : (d : ℝ) = 2 * (j : ℝ) + 1 := by simp [d]
    have hterm_lo : (((2 * tLo) / d : ℕ) : ℝ) / (logScale16 : ℝ) ≤
        (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) := by
      have h1 : (((2 * tLo) / d : ℕ) : ℝ) ≤ (2 * (tLo : ℝ)) / (d : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hd_pos)]
        exact_mod_cast Nat.div_mul_le_self (2 * tLo) d
      have h2 : (2 * (tLo : ℝ)) / (d : ℝ) / (logScale16 : ℝ) =
          (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * ((tLo : ℝ) / (logScale16 : ℝ)) := by
        rw [hd_eq]; ring
      exact le_trans (div_le_div_of_nonneg_right h1 hS.le) (h2 ▸ by gcongr)
    have hterm_hi : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
        ((SciNat.ceilDiv (2 * tHi) d : ℕ) : ℝ) / (logScale16 : ℝ) := by
      have h1 : (2 * (tHi : ℝ)) / (d : ℝ) ≤ ((SciNat.ceilDiv (2 * tHi) d : ℕ) : ℝ) := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using SciProofs.ceilDiv_ge (n := 2 * tHi) hd_pos
      have h2 : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
          (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * ((tHi : ℝ) / (logScale16 : ℝ)) := by gcongr
      have h3 : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * ((tHi : ℝ) / (logScale16 : ℝ)) =
          (2 * (tHi : ℝ)) / (d : ℝ) / (logScale16 : ℝ) := by rw [hd_eq]; ring
      exact le_trans (h3 ▸ h2) (div_le_div_of_nonneg_right h1 hS.le)
    have htLo1 : (((tLo * (a * a)) / (b * b) : ℕ) : ℝ) / (logScale16 : ℝ) ≤
        u ^ (2 * (j + 1) + 1) := by
      have h1 : (((tLo * (a * a)) / (b * b) : ℕ) : ℝ) ≤
          ((tLo : ℝ) * ((a : ℝ) * (a : ℝ))) / ((b : ℝ) * (b : ℝ)) := by
        rw [le_div_iff₀ (by exact_mod_cast hb2_pos)]
        exact_mod_cast Nat.div_mul_le_self (tLo * (a * a)) (b * b)
      have h2 : (((tLo : ℝ) * ((a : ℝ) * (a : ℝ))) / ((b : ℝ) * (b : ℝ))) / (logScale16 : ℝ) =
          ((tLo : ℝ) / (logScale16 : ℝ)) * (u * u) := by simp [u]; ring
      have h3 : ((tLo : ℝ) / (logScale16 : ℝ)) * (u * u) ≤ u ^ (2 * j + 1) * (u * u) :=
        mul_le_mul_of_nonneg_right htLo (mul_nonneg hu_nn hu_nn)
      exact le_trans (div_le_div_of_nonneg_right h1 hS.le)
        (h2 ▸ (show u ^ (2 * j + 1) * (u * u) = u ^ (2 * (j + 1) + 1) by ring) ▸ h3)
    have htHi1 : u ^ (2 * (j + 1) + 1) ≤
        ((SciNat.ceilDiv (tHi * (a * a)) (b * b) : ℕ) : ℝ) / (logScale16 : ℝ) := by
      have h1 : ((tHi : ℝ) * ((a : ℝ) * (a : ℝ))) / ((b : ℝ) * (b : ℝ)) ≤
          ((SciNat.ceilDiv (tHi * (a * a)) (b * b) : ℕ) : ℝ) := by
        simpa [Nat.cast_mul] using SciProofs.ceilDiv_ge (n := tHi * (a * a)) hb2_pos
      have h3 : u ^ (2 * j + 1) * (u * u) ≤ ((tHi : ℝ) / (logScale16 : ℝ)) * (u * u) :=
        mul_le_mul_of_nonneg_right htHi (mul_nonneg hu_nn hu_nn)
      have h4 : ((tHi : ℝ) / (logScale16 : ℝ)) * (u * u) =
          (((tHi * (a * a)) : ℝ) / ((b : ℝ) * (b : ℝ))) / (logScale16 : ℝ) := by simp [u]; ring
      exact le_trans ((show u ^ (2 * (j + 1) + 1) = u ^ (2 * j + 1) * (u * u) by ring) ▸ h3)
        (h4 ▸ div_le_div_of_nonneg_right h1 hS.le)
    have hrec := ih (j + 1) ((tLo * (a * a)) / (b * b)) (SciNat.ceilDiv (tHi * (a * a)) (b * b))
      (sLo + (2 * tLo) / d) (sHi + SciNat.ceilDiv (2 * tHi) d) htLo1 htHi1
    dsimp only [logLoop16] at hrec ⊢
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
    set res := logLoop16 n (j + 1) (a * a) (b * b) (tLo * (a * a) / (b * b))
      (SciNat.ceilDiv (tHi * (a * a)) (b * b)) (sLo + 2 * tLo / d) (sHi + SciNat.ceilDiv (2 * tHi) d)
    have hs1 : ((res.1 : ℝ) - (sLo : ℝ)) / (logScale16 : ℝ) =
        ((res.1 : ℝ) - ((sLo : ℝ) + ((2 * tLo / d : ℕ) : ℝ))) / (logScale16 : ℝ) +
          ((2 * tLo / d : ℕ) : ℝ) / (logScale16 : ℝ) := by ring
    have hs2 : ((res.2 : ℝ) - (sHi : ℝ)) / (logScale16 : ℝ) =
        ((res.2 : ℝ) - ((sHi : ℝ) + ((SciNat.ceilDiv (2 * tHi) d : ℕ) : ℝ))) / (logScale16 : ℝ) +
          ((SciNat.ceilDiv (2 * tHi) d : ℕ) : ℝ) / (logScale16 : ℝ) := by ring
    rw [hs1, hs2]; exact ⟨add_le_add hrec.1 hterm_lo, add_le_add hrec.2 hterm_hi⟩

private def ratLogBoundsWithK (num den k : ℕ) : Bool × SciNat × SciNat :=
  let p2 := den * 2 ^ k
  let ok := decide (0 < den) && decide (p2 ≤ num) && decide (num < 2 * p2)
  if !ok then (false, ⟨0, 0⟩, ⟨0, 0⟩)
  else
    let a := num - p2
    let b := num + p2
    let (sLo, sHi) :=
      logLoop16 14 0 (a * a) (b * b) ((logScale16 * a) / b) (SciNat.ceilDiv (logScale16 * a) b) 0 0
    (true, ⟨k * ln2Lo16 + sLo, 16⟩, ⟨k * ln2Hi16 + sHi + logTail16, 16⟩)

def ratLogBounds (num den : ℕ) : Bool × SciNat × SciNat :=
  ratLogBoundsWithK num den (findPow2 num den)

private lemma ratLogBoundsWithK_sound (consts : External.CertifiedConstants) {num den k : ℕ}
    (h : (ratLogBoundsWithK num den k).1 = true) :
    (ratLogBoundsWithK num den k).2.1.toReal ≤ Real.log ((num : ℝ) / (den : ℝ)) ∧
      Real.log ((num : ℝ) / (den : ℝ)) ≤ (ratLogBoundsWithK num den k).2.2.toReal := by
  unfold ratLogBoundsWithK at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hbad
  have hok_true : decide (0 < den) && decide (den * 2 ^ k ≤ num) &&
      decide (num < 2 * (den * 2 ^ k)) = true := by
    by_contra hfalse
    have hbt : (!(decide (0 < den) && decide (den * 2 ^ k ≤ num) &&
        decide (num < 2 * (den * 2 ^ k)))) = true := by
      cases hb : (decide (0 < den) && decide (den * 2 ^ k ≤ num) &&
          decide (num < 2 * (den * 2 ^ k))) <;> simp_all
    exact hbad hbt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok_true
  rcases hok_true with ⟨⟨hden, hlo⟩, hhi⟩
  set p2 : ℕ := den * 2 ^ k
  set a : ℕ := num - p2
  set b : ℕ := num + p2
  set lp := logLoop16 14 0 (a * a) (b * b) ((logScale16 * a) / b) (SciNat.ceilDiv (logScale16 * a) b) 0 0
  have hp2_pos : 0 < p2 := Nat.mul_pos hden (pow_pos (by norm_num) k)
  have hb_pos : 0 < b := by omega
  set u : ℝ := (a : ℝ) / (b : ℝ)
  have hu_nn : 0 ≤ u := by positivity
  have hu_lt_third : u < (1 / 3 : ℝ) := by
    rw [div_lt_div_iff₀ (by exact_mod_cast hb_pos) (by norm_num)]
    exact_mod_cast (by omega : a * 3 < 1 * b)
  have hu_abs : |u| < 1 := by rw [abs_of_nonneg hu_nn]; linarith
  have hlog_x : Real.log ((num : ℝ) / (den : ℝ)) =
      (k : ℝ) * Real.log 2 + Real.log ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) := by
    have hden_pos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
    have hnum_pos : (0 : ℝ) < (num : ℝ) := by exact_mod_cast lt_of_lt_of_le hp2_pos hlo
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [show (num : ℝ) / (den : ℝ) = (2 : ℝ) ^ k * ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) by
        field_simp [h2k_pos.ne', hden_pos.ne'],
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
    have hp2_real : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2_pos
    have hnum_pos : (0 : ℝ) < (num : ℝ) := by exact_mod_cast lt_of_lt_of_le hp2_pos hlo
    rw [← Real.log_div (by rw [h1pu]; positivity) (by rw [h1mu]; positivity), h1pu, h1mu]
    have hp2_eq : (p2 : ℝ) = (den : ℝ) * (2 : ℝ) ^ k := by push_cast [p2]; rfl
    rw [← hp2_eq]; congr 1; field_simp [hb_real.ne', hp2_real.ne']
  have hhasSum := hlog_y ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  set f : ℕ → ℝ := fun j => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)
  have hsum_le : ∑ j ∈ Finset.range 14, f j ≤ Real.log ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) :=
    sum_le_hasSum (Finset.range 14) (fun j _ => by positivity) hhasSum
  have hsum_ge : Real.log ((num : ℝ) / ((den : ℝ) * (2 : ℝ) ^ k)) ≤
      (∑ j ∈ Finset.range 14, f j) + (logTail16 : ℝ) / (logScale16 : ℝ) := by
    have hsplit := hhasSum.summable.sum_add_tsum_nat_add 14
    have hu2_lt1 : u ^ 2 < 1 / 9 := by
      have : u ^ 2 < (1 / 3 : ℝ) ^ 2 := sq_lt_sq' (by linarith) hu_lt_third
      linarith
    have hgeom : HasSum (fun m : ℕ => (u ^ 2) ^ m) (1 - u ^ 2)⁻¹ :=
      hasSum_geometric_of_lt_one (sq_nonneg u) (by linarith)
    have htail_le : ∀ m : ℕ, f (m + 14) ≤ ((2 / 29 : ℝ) * u ^ 29) * (u ^ 2) ^ m := by
      intro m
      have hden_le : (1 : ℝ) / (2 * ((m + 14 : ℕ) : ℝ) + 1) ≤ 1 / 29 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
      dsimp only [f]; rw [show u ^ (2 * (m + 14) + 1) = u ^ 29 * (u ^ 2) ^ m by ring]
      linarith [show (2 : ℝ) * (1 / (2 * ((m + 14 : ℕ) : ℝ) + 1)) * (u ^ 29 * (u ^ 2) ^ m) ≤
        (2 : ℝ) * (1 / 29) * (u ^ 29 * (u ^ 2) ^ m) by gcongr]
    have htsum_bound : ∑' m : ℕ, f (m + 14) ≤ ((2 / 29 : ℝ) * u ^ 29) * (1 - u ^ 2)⁻¹ := by
      have hsum_m := hhasSum.summable.comp_injective (add_left_injective 14)
      have h1 := Summable.tsum_le_tsum htail_le hsum_m (hgeom.summable.mul_left _)
      rwa [tsum_mul_left, hgeom.tsum_eq] at h1
    have hnum_tail : ((2 / 29 : ℝ) * u ^ 29) * (1 - u ^ 2)⁻¹ ≤ (logTail16 : ℝ) / (logScale16 : ℝ) := by
      have hu29 : u ^ 29 ≤ (1 / 3 : ℝ) ^ 29 := pow_le_pow_left₀ hu_nn hu_lt_third.le 29
      have hinv : (1 - u ^ 2)⁻¹ ≤ (9 / 8 : ℝ) := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have hu29_nn : 0 ≤ (2 / 29 : ℝ) * u ^ 29 := mul_nonneg (by norm_num) (pow_nonneg hu_nn 29)
      have hmul : ((2 / 29 : ℝ) * u ^ 29) * (1 - u ^ 2)⁻¹ ≤
          ((2 / 29 : ℝ) * (1 / 3 : ℝ) ^ 29) * (9 / 8 : ℝ) :=
        mul_le_mul (by gcongr) hinv (inv_nonneg.mpr (by linarith)) (by positivity)
      exact hmul.trans (by unfold logTail16 logScale16; norm_num)
    linarith [hsplit, hhasSum.tsum_eq]
  have htLo0 : (((logScale16 * a) / b : ℕ) : ℝ) / (logScale16 : ℝ) ≤ u ^ (2 * 0 + 1) := by
    have h1 : (((logScale16 * a) / b : ℕ) : ℝ) ≤ ((logScale16 : ℝ) * (a : ℝ)) / (b : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hb_pos)]
      exact_mod_cast Nat.div_mul_le_self (logScale16 * a) b
    have h2 : ((logScale16 : ℝ) * (a : ℝ) / (b : ℝ)) / (logScale16 : ℝ) = u := by
      simp [u]; field_simp [logScale16_pos.ne']
    exact (div_le_div_of_nonneg_right h1 logScale16_pos.le).trans (by simp [h2])
  have htHi0 : u ^ (2 * 0 + 1) ≤
      ((SciNat.ceilDiv (logScale16 * a) b : ℕ) : ℝ) / (logScale16 : ℝ) := by
    have h1 := SciProofs.ceilDiv_ge (n := logScale16 * a) hb_pos
    rw [Nat.cast_mul] at h1
    have h2 : u = ((logScale16 : ℝ) * (a : ℝ) / (b : ℝ)) / (logScale16 : ℝ) := by
      simp [u]; field_simp [logScale16_pos.ne']
    exact (by simp [h2] : u ^ (2 * 0 + 1) = _).le.trans (div_le_div_of_nonneg_right h1 logScale16_pos.le)
  have hloop : ((lp.1 : ℝ) - 0) / (logScale16 : ℝ) ≤ ∑ m ∈ Finset.range 14, f m ∧
      ∑ m ∈ Finset.range 14, f m ≤ ((lp.2 : ℝ) - 0) / (logScale16 : ℝ) := by
    simpa [f, Nat.zero_add, Nat.cast_zero, sub_zero] using
      logLoop16_sound hb_pos 14 0 ((logScale16 * a) / b)
        (SciNat.ceilDiv (logScale16 * a) b) 0 0 htLo0 htHi0
  simp only [sub_zero] at hloop
  have hlog2_lo : (ln2Lo16 : ℝ) / (logScale16 : ℝ) ≤ Real.log 2 := by
    unfold ln2Lo16 logScale16; linarith [consts.ln2_bounds.1]
  have hlog2_hi : Real.log 2 ≤ (ln2Hi16 : ℝ) / (logScale16 : ℝ) := by
    unfold ln2Hi16 logScale16; linarith [consts.ln2_bounds.2]
  dsimp only [SciNat.toReal]
  have hsc : (10 : ℝ) ^ 16 = (logScale16 : ℝ) := by unfold logScale16; norm_num
  rw [hsc]
  push_cast; rw [add_div, add_div, add_div, mul_div_assoc, mul_div_assoc]
  constructor
  · have := mul_le_mul_of_nonneg_left hlog2_lo (Nat.cast_nonneg k); linarith [hlog_x, hloop.1, hsum_le]
  · have := mul_le_mul_of_nonneg_left hlog2_hi (Nat.cast_nonneg k); linarith [hlog_x, hloop.2, hsum_ge]

lemma ratLogBounds_sound (consts : External.CertifiedConstants) {num den : ℕ}
    (h : (ratLogBounds num den).1 = true) :
    (ratLogBounds num den).2.1.toReal ≤ Real.log ((num : ℝ) / (den : ℝ)) ∧
      Real.log ((num : ℝ) / (den : ℝ)) ≤ (ratLogBounds num den).2.2.toReal :=
  ratLogBoundsWithK_sound consts h

def checkRatLogBounds (num den : ℕ) (lo hi : SciNat) : Bool :=
  let (ok, bLo, bHi) := ratLogBounds num den
  ok && lo.ble bLo && bHi.ble hi

lemma checkRatLogBounds_sound (consts : External.CertifiedConstants) {num den : ℕ} {lo hi : SciNat}
    (h : checkRatLogBounds num den lo hi = true) :
    lo.toReal ≤ Real.log ((num : ℝ) / (den : ℝ)) ∧ Real.log ((num : ℝ) / (den : ℝ)) ≤ hi.toReal := by
  unfold checkRatLogBounds at h; simp only [Bool.and_eq_true] at h
  have hbs := ratLogBounds_sound consts h.1.1
  exact ⟨(SciProofs.ble_sound h.1.2).trans hbs.1, hbs.2.trans (SciProofs.ble_sound h.2)⟩

def checkLogNat (x : ℕ) (lo hi : SciNat) : Bool := checkRatLogBounds x 1 lo hi

lemma checkLogNat_sound (consts : External.CertifiedConstants) {x : ℕ} {lo hi : SciNat}
    (h : checkLogNat x lo hi = true) :
    lo.toReal ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ hi.toReal := by
  simpa using checkRatLogBounds_sound consts h

def sciLogBounds (a : SciNat) : Bool × SciNat × SciNat := ratLogBounds a.m (10 ^ a.e)

lemma sciLogBounds_sound (consts : External.CertifiedConstants) {a : SciNat}
    (h : (sciLogBounds a).1 = true) :
    (sciLogBounds a).2.1.toReal ≤ Real.log a.toReal ∧ Real.log a.toReal ≤ (sciLogBounds a).2.2.toReal := by
  simpa [sciLogBounds, SciNat.toReal] using ratLogBounds_sound consts h

def log27000Lo : SciNat := ⟨102035921449864610, 16⟩
def log27000Hi : SciNat := ⟨102035921449864778, 16⟩
private lemma checkLog27000_ok : checkLogNat 27000 log27000Lo log27000Hi = true := by decide

lemma log27000_bounds (consts : External.CertifiedConstants) :
    log27000Lo.toReal ≤ Real.log (27000 : ℝ) ∧ Real.log (27000 : ℝ) ≤ log27000Hi.toReal :=
  checkLogNat_sound consts checkLog27000_ok

/-! ## 3. Certified `exp` Checkers (`checkExpPos`, `checkExpNeg`) -/

private def expScale16 : ℕ := 10 ^ 16

private lemma expScale16_pos : (0 : ℝ) < (expScale16 : ℝ) := by unfold expScale16; positivity

private def expShiftAux (t : SciNat) : ℕ → ℕ → ℕ
  | 0, s => s
  | fuel + 1, s => if 4 * t.m ≤ 10 ^ t.e * 2 ^ s then s else expShiftAux t fuel (s + 1)

private def expTaylorLoopUb (num den : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, t, s => (t, s)
  | k + 1, j, t, s =>
    let t' := SciNat.ceilDiv (t * num) (den * (j + 1))
    expTaylorLoopUb num den k (j + 1) t' (s + t)

private lemma expTaylorLoopUb_sound (num den : ℕ) (hden : 0 < den) :
    ∀ k j t s : ℕ,
      ((num : ℝ) / (den : ℝ)) ^ j / (j.factorial : ℝ) ≤ (t : ℝ) / (expScale16 : ℝ) →
      ∑ m ∈ Finset.range j, ((num : ℝ) / (den : ℝ)) ^ m / (m.factorial : ℝ) ≤
        (s : ℝ) / (expScale16 : ℝ) →
      let res := expTaylorLoopUb num den k j t s
      ((num : ℝ) / (den : ℝ)) ^ (j + k) / ((j + k).factorial : ℝ) ≤
          (res.1 : ℝ) / (expScale16 : ℝ) ∧
        ∑ m ∈ Finset.range (j + k), ((num : ℝ) / (den : ℝ)) ^ m / (m.factorial : ℝ) ≤
          (res.2 : ℝ) / (expScale16 : ℝ) := by
  intro k
  induction k with
  | zero => intro j t s ht hs; simpa [expTaylorLoopUb] using ⟨ht, hs⟩
  | succ k ih =>
    intro j t s ht hs
    set t' := SciNat.ceilDiv (t * num) (den * (j + 1))
    have hS : (0 : ℝ) < (expScale16 : ℝ) := expScale16_pos
    have hd_pos : 0 < den * (j + 1) := Nat.mul_pos hden (Nat.succ_pos j)
    have ht' : ((num : ℝ) / (den : ℝ)) ^ (j + 1) / ((j + 1).factorial : ℝ) ≤
        (t' : ℝ) / (expScale16 : ℝ) := by
      have hceil := SciProofs.ceilDiv_ge (n := t * num) hd_pos
      have h2 : (((t : ℝ) * (num : ℝ)) / ((den : ℝ) * ((j : ℝ) + 1))) / (expScale16 : ℝ) =
          ((t : ℝ) / (expScale16 : ℝ)) * ((num : ℝ) / (den : ℝ)) / ((j : ℝ) + 1) := by
        field_simp [hS.ne']
      have h3 : (((num : ℝ) / (den : ℝ)) ^ j / (j.factorial : ℝ)) * ((num : ℝ) / (den : ℝ)) /
            ((j : ℝ) + 1) ≤
          ((t : ℝ) / (expScale16 : ℝ)) * ((num : ℝ) / (den : ℝ)) / ((j : ℝ) + 1) := by gcongr
      have h4 : (((num : ℝ) / (den : ℝ)) ^ j / (j.factorial : ℝ)) * ((num : ℝ) / (den : ℝ)) /
            ((j : ℝ) + 1) =
          ((num : ℝ) / (den : ℝ)) ^ (j + 1) / ((j + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ, pow_succ]; push_cast
        field_simp [(by positivity : (den : ℝ) ≠ 0), (by positivity : (j.factorial : ℝ) ≠ 0),
          (by positivity : (j : ℝ) + 1 ≠ 0)]
      refine (h4 ▸ h3).trans (h2 ▸ div_le_div_of_nonneg_right ?_ hS.le)
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hceil
    have hs' : ∑ m ∈ Finset.range (j + 1), ((num : ℝ) / (den : ℝ)) ^ m / (m.factorial : ℝ) ≤
        ((s + t : ℕ) : ℝ) / (expScale16 : ℝ) := by
      rw [Finset.sum_range_succ]; push_cast; rw [add_div]; exact add_le_add hs ht
    have hrec := ih (j + 1) t' (s + t) ht' hs'
    rw [show j + 1 + k = j + (k + 1) by omega] at hrec
    simpa [expTaylorLoopUb] using hrec

private lemma expTaylorLoopUb_ge (num den : ℕ) :
    ∀ k j t s : ℕ, expScale16 ≤ s + t → 0 < k →
      expScale16 ≤ (expTaylorLoopUb num den k j t s).2 := by
  intro k
  induction k with
  | zero => intro _ _ _ _ hk; omega
  | succ k ih =>
    intro j t s hst _
    cases k with
    | zero => simpa [expTaylorLoopUb] using hst
    | succ k' =>
      dsimp only [expTaylorLoopUb]
      exact ih (j + 1) (SciNat.ceilDiv (t * num) (den * (j + 1))) (s + t) (by omega) (Nat.succ_pos k')

private def sciSquareUb : ℕ → SciNat → SciNat
  | 0, r => r
  | s + 1, r => sciSquareUb s ((r.mul r).trimUb 24)

private lemma sciSquareUb_sound : ∀ (s : ℕ) (r : SciNat) (y : ℝ),
    0 ≤ y → y ≤ r.toReal → y ^ (2 ^ s) ≤ (sciSquareUb s r).toReal := by
  intro s
  induction s with
  | zero => intro r y _ hy; simpa [sciSquareUb] using hy
  | succ s ih =>
    intro r y hy0 hy
    have hsq : y ^ 2 ≤ ((r.mul r).trimUb 24).toReal := by
      calc y ^ 2 ≤ r.toReal ^ 2 := pow_le_pow_left₀ hy0 hy 2
        _ = (r.mul r).toReal := by rw [SciProofs.mul_toReal, sq]
        _ ≤ ((r.mul r).trimUb 24).toReal := SciNat.trimUb_le _ 24
    have hpow : y ^ (2 ^ (s + 1)) = (y ^ 2) ^ (2 ^ s) := by
      rw [← pow_mul, pow_succ', mul_comm]
    rw [hpow]
    exact ih ((r.mul r).trimUb 24) (y ^ 2) (sq_nonneg y) hsq

private lemma sciSquareUb_ge_one : ∀ (s : ℕ) (r : SciNat),
    1 ≤ r.toReal → 1 ≤ (sciSquareUb s r).toReal := by
  intro s r hr
  simpa using sciSquareUb_sound s r 1 zero_le_one hr

def expUbBounds (t : SciNat) : Bool × SciNat :=
  let s := expShiftAux t 20 0
  let den := 10 ^ t.e * 2 ^ s
  let ok := decide (4 * t.m ≤ den)
  let (t12, s12) := expTaylorLoopUb t.m den 12 0 expScale16 0
  let r0 : SciNat := ⟨s12 + SciNat.ceilDiv (13 * t12) 12, 16⟩
  (ok, sciSquareUb s r0)

lemma expUbBounds_sound {t : SciNat} (h : (expUbBounds t).1 = true) :
    Real.exp t.toReal ≤ (expUbBounds t).2.toReal ∧ 1 ≤ (expUbBounds t).2.toReal := by
  unfold expUbBounds at h ⊢
  set s := expShiftAux t 20 0
  set den := 10 ^ t.e * 2 ^ s
  have hok : 4 * t.m ≤ den := by simpa using h
  have hden_pos : 0 < den := Nat.mul_pos (pow_pos (by norm_num) t.e) (pow_pos (by norm_num) s)
  set y : ℝ := (t.m : ℝ) / (den : ℝ)
  have hy_nn : 0 ≤ y := by positivity
  have hy_le1 : y ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hden_pos)]; exact_mod_cast (by omega : t.m ≤ den)
  have htaylor := expTaylorLoopUb_sound t.m den hden_pos 12 0 expScale16 0
    (by simp [div_self expScale16_pos.ne']) (by simp)
  have hge := expTaylorLoopUb_ge t.m den 12 0 expScale16 0 le_rfl (by norm_num)
  set res := expTaylorLoopUb t.m den 12 0 expScale16 0
  have hbd := Real.exp_bound' hy_nn hy_le1 (n := 12) (by norm_num)
  have htail_le : y ^ 12 * ((12 + 1 : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) ≤
      ((SciNat.ceilDiv (13 * res.1) 12 : ℕ) : ℝ) / (expScale16 : ℝ) := by
    have h1 : y ^ 12 * ((12 + 1 : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) =
        (y ^ 12 / ((12 : ℕ).factorial : ℝ)) * (13 / 12 : ℝ) := by ring
    have h2 : (y ^ 12 / ((12 : ℕ).factorial : ℝ)) * (13 / 12 : ℝ) ≤
        ((res.1 : ℝ) / (expScale16 : ℝ)) * (13 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right htaylor.1 (by norm_num)
    have h3 : ((res.1 : ℝ) / (expScale16 : ℝ)) * (13 / 12 : ℝ) =
        ((13 * (res.1 : ℝ)) / 12) / (expScale16 : ℝ) := by ring
    have hceil := SciProofs.ceilDiv_ge (n := 13 * res.1) (d := 12) (by norm_num)
    push_cast at hceil
    exact h1 ▸ h2.trans (h3 ▸ div_le_div_of_nonneg_right hceil expScale16_pos.le)
  set r0 : SciNat := ⟨res.2 + SciNat.ceilDiv (13 * res.1) 12, 16⟩
  have hsc : (10 : ℝ) ^ 16 = (expScale16 : ℝ) := by unfold expScale16; norm_num
  have hr0_ge : Real.exp y ≤ r0.toReal := by
    dsimp only [r0, SciNat.toReal]; rw [hsc, Nat.cast_add, add_div]; linarith [htaylor.2]
  have hr0_ge1 : 1 ≤ r0.toReal := by
    dsimp only [r0, SciNat.toReal]; rw [hsc, le_div_iff₀ expScale16_pos, one_mul]
    exact_mod_cast hge.trans (Nat.le_add_right _ _)
  have hexp_eq : Real.exp t.toReal = (Real.exp y) ^ (2 ^ s) := by
    rw [← Real.exp_natCast_mul]
    congr 1; dsimp only [y, den, SciNat.toReal]; push_cast
    field_simp [(by positivity : (10 : ℝ) ^ t.e ≠ 0), (by positivity : (2 : ℝ) ^ s ≠ 0)]
  refine ⟨?_, sciSquareUb_ge_one s r0 hr0_ge1⟩
  rw [hexp_eq]; exact sciSquareUb_sound s r0 (Real.exp y) (Real.exp_pos y).le hr0_ge

def checkExpPos (t ub : SciNat) : Bool := let (ok, eUb) := expUbBounds t; ok && eUb.ble ub

lemma checkExpPos_sound {t ub : SciNat} (h : checkExpPos t ub = true) : Real.exp t.toReal ≤ ub.toReal := by
  unfold checkExpPos at h; simp only [Bool.and_eq_true] at h
  exact (expUbBounds_sound h.1).1.trans (SciProofs.ble_sound h.2)

def checkExpNeg (t lb : SciNat) : Bool :=
  let (ok, eUb) := expUbBounds t; ok && lb.ble (divLbSig ⟨1, 0⟩ eUb 24)

lemma checkExpNeg_sound {t lb : SciNat} (h : checkExpNeg t lb = true) :
    lb.toReal ≤ Real.exp (-t.toReal) := by
  unfold checkExpNeg at h; simp only [Bool.and_eq_true] at h
  have he := expUbBounds_sound h.1
  have hinv : 1 / (expUbBounds t).2.toReal ≤ Real.exp (-t.toReal) := by
    rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos _) he.1
  have hdiv := divLbSig_le ⟨1, 0⟩ (expUbBounds t).2 24
  have h1 : (⟨1, 0⟩ : SciNat).toReal = 1 := by simp [SciNat.toReal]
  rw [h1] at hdiv; exact (SciProofs.ble_sound h.2).trans (hdiv.trans hinv)

/-! ## 4. Outward-Rounded Interval DP for `elemSym` -/

def elemSymIntervalStep (p : ℕ) (dp : List (SciNat × SciNat)) : List (SciNat × SciNat) :=
  let wLo := SciNat.divLb (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24
  let wUb := SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24
  (⟨1, 0⟩, ⟨1, 0⟩) :: List.zipWith (fun cur prev =>
    ((cur.1.add (wLo.mul prev.1)).trimLb 24,
     (cur.2.add (wUb.mul prev.2)).trimUb 24)) dp.tail dp

def elemSymInterval (ps : List ℕ) (m : ℕ) : List (SciNat × SciNat) :=
  ps.foldl (fun dp p => elemSymIntervalStep p dp)
    ((⟨1, 0⟩, ⟨1, 0⟩) :: List.replicate m (⟨0, 0⟩, ⟨0, 0⟩))

private lemma elemSymIntervalStep_length (p : ℕ) {dp : List (SciNat × SciNat)} {m : ℕ}
    (hdp : dp.length = m + 1) : (elemSymIntervalStep p dp).length = m + 1 := by
  simp [elemSymIntervalStep, hdp]

private lemma foldl_elemSymStep_length (ps : List ℕ) (m : ℕ) :
    ∀ dp : List (SciNat × SciNat), dp.length = m + 1 →
      (ps.foldl (fun acc p => elemSymIntervalStep p acc) dp).length = m + 1 := by
  induction ps with
  | nil => intro dp hdp; exact hdp
  | cons p tl ih => intro dp hdp; rw [List.foldl_cons]; exact ih _ (elemSymIntervalStep_length p hdp)

lemma elemSymInterval_length (ps : List ℕ) (m : ℕ) : (elemSymInterval ps m).length = m + 1 :=
  foldl_elemSymStep_length ps m _ (by simp)

private lemma elemSymIntervalStep_sound {p : ℕ} (hp : p.Prime) {T : Finset ℕ} (hpT : p ∉ T)
    {dp : List (SciNat × SciNat)} {m : ℕ} (hdp : dp.length = m + 1)
    (hinv : ∀ j (hj : j ≤ m),
      (dp[j]'(by omega)).1.toReal ≤ BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ≤ (dp[j]'(by omega)).2.toReal) :
    ∀ j (hj : j ≤ m),
      ((elemSymIntervalStep p dp)[j]'(by rw [elemSymIntervalStep_length p hdp]; omega)).1.toReal ≤
        BuchstabSwitching.elemSym BuchstabSwitching.gTot (insert p T) j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot (insert p T) j ≤
        ((elemSymIntervalStep p dp)[j]'(by rw [elemSymIntervalStep_length p hdp]; omega)).2.toReal := by
  intro j hj
  cases j with
  | zero => simp [elemSymIntervalStep, SciNat.toReal, BuchstabSwitching.elemSym_zero]
  | succ k =>
    have hk_lt : k < m := by omega
    have hk_dp : k < dp.length := by omega
    have hk1_dp : k + 1 < dp.length := by omega
    have hget : (elemSymIntervalStep p dp)[k + 1]'(by rw [elemSymIntervalStep_length p hdp]; omega) =
        let wLo := SciNat.divLb (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24
        let wUb := SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24
        (((dp[k + 1]'hk1_dp).1.add (wLo.mul (dp[k]'hk_dp).1)).trimLb 24,
         ((dp[k + 1]'hk1_dp).2.add (wUb.mul (dp[k]'hk_dp).2)).trimUb 24) := by
      simp [elemSymIntervalStep, List.getElem_zipWith, List.getElem_tail]
    rw [hget, BuchstabSwitching.elemSym_insert BuchstabSwitching.gTot hpT k]
    have hw_eq := BuchstabSwitching.gTot_prime hp
    have hw_lo : (SciNat.divLb (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24).toReal ≤
        BuchstabSwitching.gTot p := by
      have hdiv := SciNat.divLb_le (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24
      rwa [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, Nat.cast_sub hp.one_lt.le,
        Nat.cast_one, ← hw_eq] at hdiv
    have hw_ub : BuchstabSwitching.gTot p ≤
        (SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24).toReal := by
      have hdiv := SciNat.divUb_le (SciNat.ofNat 1) (SciNat.ofNat (p - 1)) 24
      rwa [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, Nat.cast_sub hp.one_lt.le,
        Nat.cast_one, ← hw_eq] at hdiv
    have hcur := hinv (k + 1) hj
    have hprev := hinv k (by omega)
    have hprev_nn : 0 ≤ BuchstabSwitching.elemSym BuchstabSwitching.gTot T k :=
      BuchstabSwitching.elemSym_nonneg (fun q _ => BuchstabSwitching.gTot_nonneg q) k
    constructor
    · refine (SciNat.trimLb_le _ 24).trans ?_
      rw [SciProofs.add_toReal, SciProofs.mul_toReal]
      exact add_le_add hcur.1 (mul_le_mul hw_lo hprev.1 (SciNat.toReal_nonneg _)
        (BuchstabSwitching.gTot_nonneg p))
    · refine le_trans ?_ (SciNat.trimUb_le _ 24)
      rw [SciProofs.add_toReal, SciProofs.mul_toReal]
      exact add_le_add hcur.2 (mul_le_mul hw_ub hprev.2 hprev_nn (SciNat.toReal_nonneg _))

private lemma elemSymIntervalAux_sound (ps : List ℕ) (m : ℕ) :
    ∀ (T : Finset ℕ) (dp : List (SciNat × SciNat)) (hdp : dp.length = m + 1),
      ps.Nodup → (∀ p ∈ ps, p.Prime ∧ p ∉ T) →
      (∀ j (hj : j ≤ m),
        (dp[j]'(by omega)).1.toReal ≤ BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ∧
        BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ≤ (dp[j]'(by omega)).2.toReal) →
      ∀ j (hj : j ≤ m),
        ((ps.foldl (fun acc p => elemSymIntervalStep p acc) dp)[j]'(by
          rw [foldl_elemSymStep_length ps m dp hdp]; omega)).1.toReal ≤
          BuchstabSwitching.elemSym BuchstabSwitching.gTot (T ∪ ps.toFinset) j ∧
        BuchstabSwitching.elemSym BuchstabSwitching.gTot (T ∪ ps.toFinset) j ≤
          ((ps.foldl (fun acc p => elemSymIntervalStep p acc) dp)[j]'(by
            rw [foldl_elemSymStep_length ps m dp hdp]; omega)).2.toReal := by
  induction ps with
  | nil => intro T dp hdp _ _ hinv j hj; simpa using hinv j hj
  | cons p tl ih =>
    intro T dp hdp hnd hps hinv j hj
    rcases List.nodup_cons.mp hnd with ⟨hptl, htl_nd⟩
    have hp := hps p List.mem_cons_self
    have hstep := elemSymIntervalStep_sound hp.1 hp.2 hdp hinv
    have hrec := ih (insert p T) (elemSymIntervalStep p dp) (elemSymIntervalStep_length p hdp) htl_nd
      (fun q hq => ⟨(hps q (List.mem_cons_of_mem p hq)).1, fun hmem => by
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact hptl hq
        · exact (hps q (List.mem_cons_of_mem p hq)).2 hmem⟩) hstep j hj
    have hun : insert p T ∪ tl.toFinset = T ∪ (p :: tl).toFinset := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto
    simpa [List.foldl_cons, hun] using hrec

theorem elemSymInterval_sound {ps : List ℕ} (hnodup : ps.Nodup) (hpr : ∀ p ∈ ps, p.Prime)
    (m : ℕ) :
    ∀ j (hj : j ≤ m),
      ((elemSymInterval ps m)[j]'(by rw [elemSymInterval_length]; omega)).1.toReal ≤
        BuchstabSwitching.elemSym BuchstabSwitching.gTot ps.toFinset j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot ps.toFinset j ≤
        ((elemSymInterval ps m)[j]'(by rw [elemSymInterval_length]; omega)).2.toReal := by
  have hinit : ∀ j (hj : j ≤ m),
      ((((⟨1, 0⟩, ⟨1, 0⟩) :: List.replicate m (⟨0, 0⟩, ⟨0, 0⟩) : List (SciNat × SciNat))[j]'(by
        simp; omega)).1.toReal ≤ BuchstabSwitching.elemSym BuchstabSwitching.gTot ∅ j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot ∅ j ≤
        (((⟨1, 0⟩, ⟨1, 0⟩) :: List.replicate m (⟨0, 0⟩, ⟨0, 0⟩) : List (SciNat × SciNat))[j]'(by
          simp; omega)).2.toReal) := by
    intro j hj; cases j with
    | zero => simp [SciNat.toReal, BuchstabSwitching.elemSym_zero]
    | succ k =>
      simp only [List.getElem_cons_succ, List.getElem_replicate, SciNat.toReal,
        BuchstabSwitching.elemSym_eq_zero_of_lt (show (∅ : Finset ℕ).card < k + 1 by simp)]; norm_num
  have hres := elemSymIntervalAux_sound ps m ∅
    ((⟨1, 0⟩, ⟨1, 0⟩) :: List.replicate m (⟨0, 0⟩, ⟨0, 0⟩)) (by simp)
    hnodup (fun p hp => ⟨hpr p hp, by simp⟩) hinit
  simpa [elemSymInterval] using hres

end

end BuchstabSwitching.SieveInst
