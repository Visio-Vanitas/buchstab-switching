import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSciProofs
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option maxRecDepth 200000

/-!
# Division-Free Q64 `log`, `exp`, and Factorial Constants

Provides witness-verified `checkLogDyadic` / `checkLogNat`, `log27000_bounds`,
Q64-Horner `expUbDyadic` / `expGeQ64`, `invFactUb`, and `sumPowDivFactUb`.
-/

namespace BuchstabSwitching.SieveInst

section

def ln2Lo64 : ℕ := 12786308645202649952
def ln2Hi64 : ℕ := 12786308645202668399
private def logTail64 : ℕ := 256

def inv2OddPairs64 : List (ℕ × ℕ) := [
  (36893488147419103232, 36893488147419103232),
  (12297829382473034410, 12297829382473034411),
  (7378697629483820646, 7378697629483820647),
  (5270498306774157604, 5270498306774157605),
  (4099276460824344803, 4099276460824344804),
  (3353953467947191202, 3353953467947191203),
  (2837960626724546402, 2837960626724546403),
  (2459565876494606882, 2459565876494606883),
  (2170205185142300190, 2170205185142300191),
  (1941762534074689643, 1941762534074689644),
  (1756832768924719201, 1756832768924719202),
  (1604064702061700140, 1604064702061700141),
  (1475739525896764129, 1475739525896764130),
  (1366425486941448267, 1366425486941448268),
  (1272189246462727697, 1272189246462727698),
  (1190112520884487201, 1190112520884487202)
]

def checkInv2OddPairs : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | j, (cLo, cHi) :: rest =>
    decide (cLo * (2 * j + 1) ≤ 2 * q64Scale) &&
    decide (2 * q64Scale ≤ cHi * (2 * j + 1)) &&
    checkInv2OddPairs (j + 1) rest

lemma inv2OddPairs64_ok : checkInv2OddPairs 0 inv2OddPairs64 = true := by native_decide

def logLoopList64 (u2Lo u2Hi : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | [], _, _, sLo, sHi => (sLo, sHi)
  | (cLo, cHi) :: rest, tLo, tHi, sLo, sHi =>
    logLoopList64 u2Lo u2Hi rest
      ((tLo * u2Lo) >>> 64) (Dyadic.ceilShr (tHi * u2Hi) 64)
      (sLo + ((tLo * cLo) >>> 64)) (sHi + Dyadic.ceilShr (tHi * cHi) 64)

lemma logLoopList64_sound {u : ℝ} (hu_nn : 0 ≤ u)
    {u2Lo u2Hi : ℕ} (hu2Lo : (u2Lo : ℝ) / (q64Scale : ℝ) ≤ u ^ 2)
    (hu2Hi : u ^ 2 ≤ (u2Hi : ℝ) / (q64Scale : ℝ)) :
    ∀ (ps : List (ℕ × ℕ)) (j tLo tHi sLo sHi : ℕ),
      checkInv2OddPairs j ps = true →
      (tLo : ℝ) / (q64Scale : ℝ) ≤ u ^ (2 * j + 1) →
      u ^ (2 * j + 1) ≤ (tHi : ℝ) / (q64Scale : ℝ) →
      let res := logLoopList64 u2Lo u2Hi ps tLo tHi sLo sHi
      ((res.1 : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) ≤
        ∑ m ∈ Finset.range ps.length, (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) *
          u ^ (2 * (j + m) + 1) ∧
      ∑ m ∈ Finset.range ps.length, (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) *
          u ^ (2 * (j + m) + 1) ≤
        ((res.2 : ℝ) - (sHi : ℝ)) / (q64Scale : ℝ)
  | [], _, _, _, sLo, sHi, _, _, _ => by simp [logLoopList64]
  | (cLo, cHi) :: rest, j, tLo, tHi, sLo, sHi, hchk, htLo, htHi => by
    simp only [checkInv2OddPairs, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have hd_pos : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
    have hq_pos := q64Scale_pos
    have hcLo : (cLo : ℝ) / (q64Scale : ℝ) ≤ 2 / (2 * (j : ℝ) + 1) := by
      rw [div_le_div_iff₀ hq_pos hd_pos]; exact_mod_cast hchk.1.1
    have hcHi : 2 / (2 * (j : ℝ) + 1) ≤ (cHi : ℝ) / (q64Scale : ℝ) := by
      rw [div_le_div_iff₀ hd_pos hq_pos]; exact_mod_cast hchk.1.2
    have hterm_lo : (((tLo * cLo) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤
        (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) := by
      have h1 := (q64MulLb_le tLo cLo).trans (mul_le_mul htLo hcLo (by positivity) (pow_nonneg hu_nn _))
      linarith [show (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) = u ^ (2 * j + 1) * (2 / (2 * (j : ℝ) + 1)) by ring]
    have hterm_hi : (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) ≤
        (Dyadic.ceilShr (tHi * cHi) 64 : ℝ) / (q64Scale : ℝ) := by
      have h1 := (mul_le_mul htHi hcHi (by positivity) (by positivity)).trans (le_q64MulUb tHi cHi)
      linarith [show (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) = u ^ (2 * j + 1) * (2 / (2 * (j : ℝ) + 1)) by ring]
    have htLo1 : (((tLo * u2Lo) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤ u ^ (2 * (j + 1) + 1) := by
      have h1 := (q64MulLb_le tLo u2Lo).trans (mul_le_mul htLo hu2Lo (by positivity) (pow_nonneg hu_nn _))
      rw [← pow_add, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega] at h1
      exact h1
    have htHi1 : u ^ (2 * (j + 1) + 1) ≤ (Dyadic.ceilShr (tHi * u2Hi) 64 : ℝ) / (q64Scale : ℝ) := by
      have h1 := (mul_le_mul htHi hu2Hi (sq_nonneg u) (by positivity)).trans (le_q64MulUb tHi u2Hi)
      rw [← pow_add, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega] at h1
      exact h1
    have hrec := logLoopList64_sound hu_nn hu2Lo hu2Hi rest (j + 1)
      ((tLo * u2Lo) >>> 64) (Dyadic.ceilShr (tHi * u2Hi) 64)
      (sLo + ((tLo * cLo) >>> 64)) (sHi + Dyadic.ceilShr (tHi * cHi) 64) hchk.2 htLo1 htHi1
    dsimp only [logLoopList64] at hrec ⊢
    rw [List.length_cons, Finset.sum_range_succ']
    have hshift : ∑ x ∈ Finset.range rest.length, (2 : ℝ) * (1 / (2 * ((j + (x + 1) : ℕ) : ℝ) + 1)) *
        u ^ (2 * (j + (x + 1)) + 1) =
        ∑ m ∈ Finset.range rest.length, (2 : ℝ) * (1 / (2 * (((j + 1 + m : ℕ) : ℝ)) + 1)) *
          u ^ (2 * (j + 1 + m) + 1) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show j + (m + 1) = j + 1 + m by omega]
    rw [hshift]; simp only [Nat.add_zero]
    push_cast at hrec ⊢
    set res := logLoopList64 u2Lo u2Hi rest ((tLo * u2Lo) >>> 64) (Dyadic.ceilShr (tHi * u2Hi) 64)
      (sLo + ((tLo * cLo) >>> 64)) (sHi + Dyadic.ceilShr (tHi * cHi) 64)
    have hs1 : ((res.1 : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) =
        ((res.1 : ℝ) - ((sLo : ℝ) + (((tLo * cLo) >>> 64 : ℕ) : ℝ))) / (q64Scale : ℝ) +
          (((tLo * cLo) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) := by ring
    have hs2 : ((res.2 : ℝ) - (sHi : ℝ)) / (q64Scale : ℝ) =
        ((res.2 : ℝ) - ((sHi : ℝ) + (Dyadic.ceilShr (tHi * cHi) 64 : ℝ))) / (q64Scale : ℝ) +
          (Dyadic.ceilShr (tHi * cHi) 64 : ℝ) / (q64Scale : ℝ) := by ring
    rw [hs1, hs2]; exact ⟨add_le_add hrec.1 hterm_lo, add_le_add hrec.2 hterm_hi⟩

/-- Division-free witness verifier for `lo.toReal ≤ Real.log x.toReal ≤ hi.toReal`. -/
def checkLogDyadic (x : Dyadic) (w : LogWitness) (lo hi : Dyadic) : Bool :=
  let p2 := 1 <<< w.b
  let a := x.m - p2
  let b := x.m + p2
  let okB := decide (0 < x.m) && decide (dyadicBias ≤ w.b + x.e) &&
    decide (p2 ≤ x.m) && decide (x.m < 2 * p2) &&
    decide (w.mU * b ≤ (a <<< 64)) && decide ((a <<< 64) ≤ (w.mU + 1) * b)
  if !okB then false
  else
    let k := w.b + x.e - dyadicBias
    let u2Lo := (w.mU * w.mU) >>> 64
    let u2Hi := Dyadic.ceilShr ((w.mU + 1) * (w.mU + 1)) 64
    let (sLo, sHi) := logLoopList64 u2Lo u2Hi inv2OddPairs64 w.mU (w.mU + 1) 0 0
    let resLo := Dyadic.ofQ64 (k * ln2Lo64 + sLo)
    let resHi := Dyadic.ofQ64 (k * ln2Hi64 + sHi + logTail64)
    lo.ble resLo && resHi.ble hi

lemma checkLogDyadic_sound (consts : External.CertifiedConstants) {x : Dyadic} {w : LogWitness}
    {lo hi : Dyadic} (h : checkLogDyadic x w lo hi = true) :
    lo.toReal ≤ Real.log x.toReal ∧ Real.log x.toReal ≤ hi.toReal := by
  unfold checkLogDyadic at h; dsimp only at h
  cases hok : decide (0 < x.m) && decide (dyadicBias ≤ w.b + x.e) &&
      decide (1 <<< w.b ≤ x.m) && decide (x.m < 2 * (1 <<< w.b)) &&
      decide (w.mU * (x.m + 1 <<< w.b) ≤ (x.m - 1 <<< w.b) <<< 64) &&
      decide ((x.m - 1 <<< w.b) <<< 64 ≤ (w.mU + 1) * (x.m + 1 <<< w.b)) with
  | false => rw [hok] at h; simp at h
  | true =>
  rw [hok] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.shiftLeft_eq, one_mul] at hok
  rcases hok with ⟨⟨⟨⟨⟨hx_pos, hbias⟩, hp2_lo⟩, hp2_hi⟩, hu_lo⟩, hu_hi⟩
  set p2 : ℕ := 2 ^ w.b
  set a : ℕ := x.m - p2
  set b : ℕ := x.m + p2
  set k : ℕ := w.b + x.e - dyadicBias
  set u : ℝ := (a : ℝ) / (b : ℝ)
  have hp2_pos : 0 < p2 := by positivity
  have hb_pos : 0 < b := by omega
  have hu_nn : 0 ≤ u := by positivity
  have hu_lt_third : u < (1 / 3 : ℝ) := by
    rw [div_lt_div_iff₀ (by exact_mod_cast hb_pos) (by norm_num)]
    exact_mod_cast (by omega : a * 3 < 1 * b)
  have hu_abs : |u| < 1 := by rw [abs_of_nonneg hu_nn]; linarith
  have hlog_x : Real.log x.toReal = (k : ℝ) * Real.log 2 + Real.log ((x.m : ℝ) / (p2 : ℝ)) := by
    unfold Dyadic.toReal
    have hm_pos : (0 : ℝ) < (x.m : ℝ) := by exact_mod_cast hx_pos
    have hp2_r : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2_pos
    have hpow : (2 : ℝ) ^ x.e * (2 : ℝ) ^ w.b = (2 : ℝ) ^ dyadicBias * (2 : ℝ) ^ k := by
      rw [← pow_add, ← pow_add, add_comm x.e w.b, Nat.add_sub_of_le hbias]
    have hx_split : (x.m : ℝ) * (2 : ℝ) ^ x.e / Dyadic.twoPowBias =
        (2 : ℝ) ^ k * ((x.m : ℝ) / (p2 : ℝ)) := by
      rw [div_eq_iff Dyadic.twoPowBias_pos.ne', Dyadic.twoPowBias_eq]
      calc (x.m : ℝ) * (2 : ℝ) ^ x.e
          = ((x.m : ℝ) / (p2 : ℝ)) * ((2 : ℝ) ^ x.e * (2 : ℝ) ^ w.b) := by
            dsimp only [p2]; rw [Nat.cast_pow, Nat.cast_ofNat]; field_simp [hp2_r.ne']
        _ = ((x.m : ℝ) / (p2 : ℝ)) * ((2 : ℝ) ^ dyadicBias * (2 : ℝ) ^ k) := by rw [hpow]
        _ = (2 : ℝ) ^ k * ((x.m : ℝ) / (p2 : ℝ)) * (2 : ℝ) ^ dyadicBias := by ring
    rw [hx_split, Real.log_mul (by positivity) (div_pos hm_pos hp2_r).ne', Real.log_pow]
  have hlog_y : Real.log ((x.m : ℝ) / (p2 : ℝ)) = Real.log (1 + u) - Real.log (1 - u) := by
    have hb_real : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    have ha_real : (a : ℝ) = (x.m : ℝ) - (p2 : ℝ) := Nat.cast_sub hp2_lo
    have hb_eq : (b : ℝ) = (x.m : ℝ) + (p2 : ℝ) := by push_cast [b]; rfl
    have h1pu : 1 + u = (2 * (x.m : ℝ)) / (b : ℝ) := by
      simp only [u]; rw [one_add_div hb_real.ne', ha_real, hb_eq]; ring
    have h1mu : 1 - u = (2 * (p2 : ℝ)) / (b : ℝ) := by
      simp only [u]; rw [one_sub_div hb_real.ne', ha_real, hb_eq]; ring
    have hp2_real : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2_pos
    have hnum_pos : (0 : ℝ) < (x.m : ℝ) := by exact_mod_cast hx_pos
    rw [← Real.log_div (by rw [h1pu]; positivity) (by rw [h1mu]; positivity), h1pu, h1mu]
    congr 1; field_simp [hb_real.ne', hp2_real.ne']
  have hhasSum := hlog_y ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  set f : ℕ → ℝ := fun j => (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1)
  have hsum_le : ∑ j ∈ Finset.range 16, f j ≤ Real.log ((x.m : ℝ) / (p2 : ℝ)) :=
    sum_le_hasSum (Finset.range 16) (fun j _ => by positivity) hhasSum
  have hsum_ge : Real.log ((x.m : ℝ) / (p2 : ℝ)) ≤
      (∑ j ∈ Finset.range 16, f j) + (logTail64 : ℝ) / (q64Scale : ℝ) := by
    have hsplit := hhasSum.summable.sum_add_tsum_nat_add 16
    have hu2_lt1 : u ^ 2 < 1 / 9 := by
      have : u ^ 2 < (1 / 3 : ℝ) ^ 2 := sq_lt_sq' (by linarith) hu_lt_third
      linarith
    have hgeom : HasSum (fun m : ℕ => (u ^ 2) ^ m) (1 - u ^ 2)⁻¹ :=
      hasSum_geometric_of_lt_one (sq_nonneg u) (by linarith)
    have htail_le : ∀ m : ℕ, f (m + 16) ≤ ((2 / 33 : ℝ) * u ^ 33) * (u ^ 2) ^ m := by
      intro m
      have hden_le : (1 : ℝ) / (2 * ((m + 16 : ℕ) : ℝ) + 1) ≤ 1 / 33 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
      dsimp only [f]; rw [show u ^ (2 * (m + 16) + 1) = u ^ 33 * (u ^ 2) ^ m by ring]
      linarith [show (2 : ℝ) * (1 / (2 * ((m + 16 : ℕ) : ℝ) + 1)) * (u ^ 33 * (u ^ 2) ^ m) ≤
        (2 : ℝ) * (1 / 33) * (u ^ 33 * (u ^ 2) ^ m) by gcongr]
    have htsum_bound : ∑' m : ℕ, f (m + 16) ≤ ((2 / 33 : ℝ) * u ^ 33) * (1 - u ^ 2)⁻¹ := by
      have hsum_m := hhasSum.summable.comp_injective (add_left_injective 16)
      have h1 := Summable.tsum_le_tsum htail_le hsum_m (hgeom.summable.mul_left _)
      rwa [tsum_mul_left, hgeom.tsum_eq] at h1
    have hnum_tail : ((2 / 33 : ℝ) * u ^ 33) * (1 - u ^ 2)⁻¹ ≤ (logTail64 : ℝ) / (q64Scale : ℝ) := by
      have hu33 : u ^ 33 ≤ (1 / 3 : ℝ) ^ 33 := pow_le_pow_left₀ hu_nn hu_lt_third.le 33
      have hinv : (1 - u ^ 2)⁻¹ ≤ (9 / 8 : ℝ) := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have hu33_nn : 0 ≤ (2 / 33 : ℝ) * u ^ 33 := mul_nonneg (by norm_num) (pow_nonneg hu_nn 33)
      have hmul : ((2 / 33 : ℝ) * u ^ 33) * (1 - u ^ 2)⁻¹ ≤
          ((2 / 33 : ℝ) * (1 / 3 : ℝ) ^ 33) * (9 / 8 : ℝ) :=
        mul_le_mul (by gcongr) hinv (inv_nonneg.mpr (by linarith)) (by positivity)
      refine hmul.trans ?_
      rw [Dyadic.q64Scale_real_eq]; unfold logTail64; norm_num
    linarith [hsplit, hhasSum.tsum_eq]
  have huLo : (w.mU : ℝ) / (q64Scale : ℝ) ≤ u := by
    rw [div_le_div_iff₀ q64Scale_pos (by exact_mod_cast hb_pos)]
    have hq : q64Scale = 2 ^ 64 := by unfold q64Scale; rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [← hq] at hu_lo; exact_mod_cast hu_lo
  have huHi : u ≤ ((w.mU + 1 : ℕ) : ℝ) / (q64Scale : ℝ) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hb_pos) q64Scale_pos]
    have hq : q64Scale = 2 ^ 64 := by unfold q64Scale; rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [← hq] at hu_hi; exact_mod_cast hu_hi
  have hu2Lo : (((w.mU * w.mU) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤ u ^ 2 :=
    (q64MulLb_le w.mU w.mU).trans (sq u ▸ mul_le_mul huLo huLo (by positivity) (by positivity))
  have hu2Hi : u ^ 2 ≤ (Dyadic.ceilShr ((w.mU + 1) * (w.mU + 1)) 64 : ℝ) / (q64Scale : ℝ) :=
    (sq u ▸ mul_le_mul huHi huHi hu_nn (by positivity)).trans (le_q64MulUb (w.mU + 1) (w.mU + 1))
  have hloop := logLoopList64_sound hu_nn hu2Lo hu2Hi inv2OddPairs64 0 w.mU (w.mU + 1) 0 0
    inv2OddPairs64_ok (by simpa using huLo) (by simpa using huHi)
  have hlen : inv2OddPairs64.length = 16 := rfl
  simp only [hlen, Nat.cast_zero, sub_zero, Nat.zero_add] at hloop
  have hlog2_lo : (ln2Lo64 : ℝ) / (q64Scale : ℝ) ≤ Real.log 2 := by
    have h1 : (ln2Lo64 : ℝ) / (q64Scale : ℝ) ≤ (0.693147180559945 : ℝ) := by
      rw [Dyadic.q64Scale_real_eq]; unfold ln2Lo64; norm_num
    exact h1.trans consts.ln2_bounds.1
  have hlog2_hi : Real.log 2 ≤ (ln2Hi64 : ℝ) / (q64Scale : ℝ) := by
    have h1 : (0.693147180559946 : ℝ) ≤ (ln2Hi64 : ℝ) / (q64Scale : ℝ) := by
      rw [Dyadic.q64Scale_real_eq]; unfold ln2Hi64; norm_num
    exact consts.ln2_bounds.2.trans h1
  set lp := logLoopList64 ((w.mU * w.mU) >>> 64) (Dyadic.ceilShr ((w.mU + 1) * (w.mU + 1)) 64)
    inv2OddPairs64 w.mU (w.mU + 1) 0 0
  have hlo_b := Dyadic.ble_sound h.1
  have hhi_b := Dyadic.ble_sound h.2
  rw [Dyadic.ofQ64_toReal] at hlo_b hhi_b
  push_cast at hlo_b hhi_b
  rw [add_div, mul_div_assoc] at hlo_b
  rw [add_div, add_div, mul_div_assoc] at hhi_b
  constructor
  · have := mul_le_mul_of_nonneg_left hlog2_lo (Nat.cast_nonneg k)
    linarith [hlog_x, hloop.1, hsum_le, hlo_b]
  · have := mul_le_mul_of_nonneg_left hlog2_hi (Nat.cast_nonneg k)
    linarith [hlog_x, hloop.2, hsum_ge, hhi_b]

def checkLogNat (n : ℕ) (w : LogWitness) (lo hi : Dyadic) : Bool :=
  checkLogDyadic (Dyadic.ofNat n) w lo hi

lemma checkLogNat_sound (consts : External.CertifiedConstants) {n : ℕ} {w : LogWitness}
    {lo hi : Dyadic} (h : checkLogNat n w lo hi = true) :
    lo.toReal ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ hi.toReal := by
  simpa [checkLogNat, Dyadic.ofNat_toReal] using checkLogDyadic_sound consts h

def log27000Lo : Dyadic := Dyadic.ofQ64 188223052931078346056
def log27000Hi : Dyadic := Dyadic.ofQ64 188223052931078604594
private def log27000W : LogWitness := ⟨14, 4513890722074972339⟩

private lemma checkLog27000_ok : checkLogNat 27000 log27000W log27000Lo log27000Hi = true := by native_decide

lemma log27000_bounds (consts : External.CertifiedConstants) :
    log27000Lo.toReal ≤ Real.log (27000 : ℝ) ∧ Real.log (27000 : ℝ) ≤ log27000Hi.toReal :=
  checkLogNat_sound consts checkLog27000_ok

private def invSucc64Ub : List ℕ := [
  18446744073709551616, 9223372036854775808, 6148914691236517206, 4611686018427387904,
  3689348814741910324, 3074457345618258603, 2635249153387078803, 2305843009213693952,
  2049638230412172402, 1844674407370955162, 1676976733973595602, 1537228672809129302
]

private def checkInvSucc : ℕ → List ℕ → Bool
  | _, [] => true
  | j, c :: rest => decide (q64Scale ≤ c * (j + 1)) && checkInvSucc (j + 1) rest

private lemma invSucc64Ub_ok : checkInvSucc 0 invSucc64Ub = true := by native_decide
private lemma invSucc64Ub_len : invSucc64Ub.length = 12 := rfl

private def expTaylorLoopQ64 (y64 : ℕ) : List ℕ → ℕ → ℕ → ℕ × ℕ
  | [], t, s => (t, s)
  | c :: rest, t, s =>
    let ty := Dyadic.ceilShr (t * y64) 64
    let t' := Dyadic.ceilShr (ty * c) 64
    expTaylorLoopQ64 y64 rest t' (s + t)

private lemma expTaylorLoopQ64_sound {y : ℝ} (hy_nn : 0 ≤ y) {y64 : ℕ}
    (hy64 : y ≤ (y64 : ℝ) / (q64Scale : ℝ)) :
    ∀ (cs : List ℕ) (j t s : ℕ), checkInvSucc j cs = true →
      y ^ j / (j.factorial : ℝ) ≤ (t : ℝ) / (q64Scale : ℝ) →
      ∑ m ∈ Finset.range j, y ^ m / (m.factorial : ℝ) ≤ (s : ℝ) / (q64Scale : ℝ) →
      let res := expTaylorLoopQ64 y64 cs t s
      y ^ (j + cs.length) / ((j + cs.length).factorial : ℝ) ≤ (res.1 : ℝ) / (q64Scale : ℝ) ∧
        ∑ m ∈ Finset.range (j + cs.length), y ^ m / (m.factorial : ℝ) ≤ (res.2 : ℝ) / (q64Scale : ℝ)
  | [], j, t, s, _, ht, hs => by simpa [expTaylorLoopQ64] using ⟨ht, hs⟩
  | c :: rest, j, t, s, hchk, ht, hs => by
    simp only [checkInvSucc, Bool.and_eq_true, decide_eq_true_eq] at hchk
    set ty := Dyadic.ceilShr (t * y64) 64
    set t' := Dyadic.ceilShr (ty * c) 64
    have hc : 1 / ((j : ℝ) + 1) ≤ (c : ℝ) / (q64Scale : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) q64Scale_pos]
      simpa [Nat.cast_add, Nat.cast_one, one_mul] using
        (by exact_mod_cast hchk.1 : (q64Scale : ℝ) ≤ (c : ℝ) * ((j : ℝ) + 1))
    have ht' : y ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ (t' : ℝ) / (q64Scale : ℝ) := by
      have h1 : y ^ (j + 1) / ((j + 1).factorial : ℝ) =
          (y ^ j / (j.factorial : ℝ) * y) * (1 / ((j : ℝ) + 1)) := by
        rw [Nat.factorial_succ, pow_succ]; push_cast
        field_simp [(by positivity : (j.factorial : ℝ) ≠ 0), (by positivity : (j : ℝ) + 1 ≠ 0)]
      have hty' : y ^ j / (j.factorial : ℝ) * y ≤ (ty : ℝ) / (q64Scale : ℝ) :=
        (mul_le_mul ht hy64 hy_nn (by positivity)).trans (le_q64MulUb t y64)
      have h2 := (mul_le_mul hty' hc (by positivity) (by positivity)).trans (le_q64MulUb ty c)
      rw [h1]; exact h2
    have hs' : ∑ m ∈ Finset.range (j + 1), y ^ m / (m.factorial : ℝ) ≤ ((s + t : ℕ) : ℝ) / (q64Scale : ℝ) := by
      rw [Finset.sum_range_succ]; push_cast; rw [add_div]; exact add_le_add hs ht
    have hrec := expTaylorLoopQ64_sound hy_nn hy64 rest (j + 1) t' (s + t) hchk.2 ht' hs'
    rw [List.length_cons, show j + (rest.length + 1) = j + 1 + rest.length by omega]
    exact hrec

private lemma expTaylorLoopQ64_ge :
    ∀ (y64 : ℕ) (cs : List ℕ) (t s : ℕ), cs ≠ [] → q64Scale ≤ s + t →
      q64Scale ≤ (expTaylorLoopQ64 y64 cs t s).2
  | _, [], _, _, hne, _ => absurd rfl hne
  | y64, [_], t, s, _, hst => by simpa [expTaylorLoopQ64] using hst
  | y64, _ :: c2 :: rest, t, s, _, hst => by
    dsimp only [expTaylorLoopQ64]
    exact expTaylorLoopQ64_ge y64 (c2 :: rest) _ (s + t) (List.cons_ne_nil _ _) (by omega)

private def dyadicSquareUb : ℕ → Dyadic → Dyadic
  | 0, r => r
  | s + 1, r => dyadicSquareUb s (r.mulUb r)

private lemma dyadicSquareUb_sound : ∀ (s : ℕ) (r : Dyadic) (y : ℝ),
    0 ≤ y → y ≤ r.toReal → y ^ (2 ^ s) ≤ (dyadicSquareUb s r).toReal := by
  intro s
  induction s with
  | zero => intro r y _ hy; simpa [dyadicSquareUb] using hy
  | succ s ih =>
    intro r y hy0 hy
    have hsq : y ^ 2 ≤ (r.mulUb r).toReal := by
      calc y ^ 2 = y * y := sq y
        _ ≤ r.toReal * r.toReal := mul_le_mul hy hy hy0 r.toReal_nonneg
        _ ≤ (r.mulUb r).toReal := Dyadic.le_mulUb r r
    rw [show y ^ (2 ^ (s + 1)) = (y ^ 2) ^ (2 ^ s) by rw [← pow_mul, pow_succ', mul_comm]]
    exact ih (r.mulUb r) (y ^ 2) (sq_nonneg y) hsq

private lemma dyadicSquareUb_ge_one : ∀ (s : ℕ) (r : Dyadic),
    1 ≤ r.toReal → 1 ≤ (dyadicSquareUb s r).toReal := fun s r hr => by
  simpa using dyadicSquareUb_sound s r 1 zero_le_one hr

private def ratio13_12_ub : ℕ := 19983972746518680918

/-- Division-free binary-halving + Q64 Horner upper bound for `Real.exp t.toReal`. -/
def expUbDyadic (t : Dyadic) : Bool × Dyadic :=
  if t.m == 0 then (true, Dyadic.one)
  else
    let b := Dyadic.msbPos (4 * t.m)
    let s := if dyadicBias ≤ b + 1 + t.e then (b + 1 + t.e) - dyadicBias else 0
    let y := t.divPow2Ub s
    let y64 := y.toQ64Ub
    let ok := decide (4 * y64 ≤ q64Scale)
    let (t12, s12) := expTaylorLoopQ64 y64 invSucc64Ub q64Scale 0
    let rem := Dyadic.ceilShr (t12 * ratio13_12_ub) 64
    let r0 := Dyadic.ofQ64 (s12 + rem)
    (ok, dyadicSquareUb s r0)

lemma expUbDyadic_sound {t : Dyadic} (h : (expUbDyadic t).1 = true) :
    Real.exp t.toReal ≤ (expUbDyadic t).2.toReal ∧ 1 ≤ (expUbDyadic t).2.toReal := by
  unfold expUbDyadic at h ⊢
  split_ifs at h ⊢ with hm0
  · have hm : t.m = 0 := beq_iff_eq.mp hm0
    rw [Dyadic.one_toReal]; simp [Dyadic.toReal, hm]
  · simp only [decide_eq_true_eq] at h
    set b := Dyadic.msbPos (4 * t.m)
    set s := if dyadicBias ≤ b + 1 + t.e then (b + 1 + t.e) - dyadicBias else 0
    set yD := t.divPow2Ub s
    set y64 := yD.toQ64Ub
    set y : ℝ := t.toReal / (2 : ℝ) ^ s
    have hy_nn : 0 ≤ y := div_nonneg t.toReal_nonneg (by positivity)
    have hy_le_y64 : y ≤ (y64 : ℝ) / (q64Scale : ℝ) :=
      (Dyadic.le_divPow2Ub t s).trans (Dyadic.le_toQ64Ub yD)
    have hy_le1 : y ≤ 1 := by
      have hy64_le1 : (y64 : ℝ) / (q64Scale : ℝ) ≤ 1 := by
        rw [div_le_one q64Scale_pos]; exact_mod_cast (by omega : y64 ≤ q64Scale)
      exact hy_le_y64.trans hy64_le1
    have htaylor := expTaylorLoopQ64_sound hy_nn hy_le_y64 invSucc64Ub 0 q64Scale 0
      invSucc64Ub_ok (by simp [div_self q64Scale_pos.ne']) (by simp)
    rw [invSucc64Ub_len, zero_add] at htaylor
    have hge := expTaylorLoopQ64_ge y64 invSucc64Ub q64Scale 0 (List.cons_ne_nil _ _) le_rfl
    set res := expTaylorLoopQ64 y64 invSucc64Ub q64Scale 0
    have hbd := Real.exp_bound' hy_nn hy_le1 (n := 12) (by norm_num)
    have hr13 : (13 : ℝ) / 12 ≤ (ratio13_12_ub : ℝ) / (q64Scale : ℝ) := by
      rw [Dyadic.q64Scale_real_eq]; unfold ratio13_12_ub; norm_num
    have htail_le : y ^ 12 * ((12 + 1 : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) ≤
        (Dyadic.ceilShr (res.1 * ratio13_12_ub) 64 : ℝ) / (q64Scale : ℝ) := by
      have h1 : y ^ 12 * ((12 + 1 : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) =
          (y ^ 12 / ((12 : ℕ).factorial : ℝ)) * ((13 : ℝ) / 12) := by ring
      rw [h1]
      exact (mul_le_mul htaylor.1 hr13 (by positivity) (by positivity)).trans
        (le_q64MulUb res.1 ratio13_12_ub)
    set r0 := Dyadic.ofQ64 (res.2 + Dyadic.ceilShr (res.1 * ratio13_12_ub) 64)
    have hr0_ge : Real.exp y ≤ r0.toReal := by
      dsimp only [r0]; rw [Dyadic.ofQ64_toReal, Nat.cast_add, add_div]; linarith [htaylor.2]
    have hr0_ge1 : 1 ≤ r0.toReal := by
      dsimp only [r0]; rw [Dyadic.ofQ64_toReal, le_div_iff₀ q64Scale_pos, one_mul]
      exact_mod_cast hge.trans (Nat.le_add_right _ _)
    have hexp_eq : Real.exp t.toReal = (Real.exp y) ^ (2 ^ s) := by
      rw [← Real.exp_nat_mul]; congr 1
      dsimp only [y]; rw [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel₀ _ (by positivity)]
    refine ⟨?_, dyadicSquareUb_ge_one s r0 hr0_ge1⟩
    rw [hexp_eq]; exact dyadicSquareUb_sound s r0 (Real.exp y) (Real.exp_pos y).le hr0_ge

private def inv32Succ64Lb : List ℕ := [
  576460752303423488, 288230376151711744, 192153584101141162, 144115188075855872,
  115292150460684697, 96076792050570581, 82351536043346212, 72057594037927936
]

private def checkInv32Succ : ℕ → List ℕ → Bool
  | _, [] => true
  | j, c :: rest => decide (c * (32 * (j + 1)) ≤ q64Scale) && checkInv32Succ (j + 1) rest

private lemma inv32Succ64Lb_ok : checkInv32Succ 0 inv32Succ64Lb = true := by native_decide

private def expGeLoopQ64 (x64 : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, r => r
  | c :: rest, t, r =>
    let tx := (t * x64) >>> 64
    let t' := (tx * c) >>> 64
    expGeLoopQ64 x64 rest t' (r + t')

private lemma expGeLoopQ64_sound {x : ℝ} (hx_nn : 0 ≤ x) {x64 : ℕ}
    (hx64 : (x64 : ℝ) / (q64Scale : ℝ) ≤ x) :
    ∀ (cs : List ℕ) (j t r : ℕ), checkInv32Succ j cs = true →
      (t : ℝ) / (q64Scale : ℝ) ≤ (x / 32) ^ j / (j.factorial : ℝ) →
      (r : ℝ) / (q64Scale : ℝ) ≤ ∑ m ∈ Finset.range (j + 1), (x / 32) ^ m / (m.factorial : ℝ) →
      (expGeLoopQ64 x64 cs t r : ℝ) / (q64Scale : ℝ) ≤
        ∑ m ∈ Finset.range (j + 1 + cs.length), (x / 32) ^ m / (m.factorial : ℝ)
  | [], _, _, r, _, _, hr => by simpa [expGeLoopQ64] using hr
  | c :: rest, j, t, r, hchk, ht, hr => by
    simp only [checkInv32Succ, Bool.and_eq_true, decide_eq_true_eq] at hchk
    set t' := (((t * x64) >>> 64) * c) >>> 64
    have hc : (c : ℝ) / (q64Scale : ℝ) ≤ 1 / (32 * ((j : ℝ) + 1)) := by
      rw [div_le_div_iff₀ q64Scale_pos (by positivity)]
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        (by exact_mod_cast hchk.1 : (c : ℝ) * (32 * ((j : ℝ) + 1)) ≤ (q64Scale : ℝ))
    have ht' : (t' : ℝ) / (q64Scale : ℝ) ≤ (x / 32) ^ (j + 1) / ((j + 1).factorial : ℝ) := by
      have htx := (q64MulLb_le t x64).trans (mul_le_mul ht hx64 (by positivity) (by positivity))
      have h1 := (q64MulLb_le ((t * x64) >>> 64) c).trans (mul_le_mul htx hc (by positivity) (by positivity))
      refine h1.trans_eq ?_
      rw [Nat.factorial_succ, pow_succ]; push_cast
      field_simp [(by positivity : (j.factorial : ℝ) ≠ 0), (by positivity : (j : ℝ) + 1 ≠ 0)]
    have hr' : ((r + t' : ℕ) : ℝ) / (q64Scale : ℝ) ≤
        ∑ m ∈ Finset.range (j + 2), (x / 32) ^ m / (m.factorial : ℝ) := by
      rw [Finset.sum_range_succ]; push_cast; rw [add_div]; exact add_le_add hr ht'
    have hrec := expGeLoopQ64_sound hx_nn hx64 rest (j + 1) t' (r + t') hchk.2 ht' hr'
    rw [List.length_cons, show j + 1 + (rest.length + 1) = (j + 1) + 1 + rest.length by omega]
    exact hrec

private def square5Q64 : ℕ → ℕ → ℕ
  | 0, r => r
  | s + 1, r => square5Q64 s ((r * r) >>> 64)

private lemma square5Q64_sound : ∀ (s : ℕ) (r : ℕ) (y : ℝ),
    (r : ℝ) / (q64Scale : ℝ) ≤ y →
    (square5Q64 s r : ℝ) / (q64Scale : ℝ) ≤ y ^ (2 ^ s)
  | 0, r, y, hy => by simpa [square5Q64] using hy
  | s + 1, r, y, hy => by
    have hr_nn : 0 ≤ (r : ℝ) / (q64Scale : ℝ) := by positivity
    have hsq : (((r * r) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤ y ^ 2 :=
      (q64MulLb_le r r).trans (sq y ▸ mul_le_mul hy hy hr_nn (hr_nn.trans hy))
    rw [show y ^ (2 ^ (s + 1)) = (y ^ 2) ^ (2 ^ s) by rw [← pow_mul, pow_succ', mul_comm]]
    exact square5Q64_sound s ((r * r) >>> 64) (y ^ 2) hsq

/-- Division-free Q64 lower bound for `Real.exp x` via 8-term Taylor at `x/32` + 5 squarings. -/
def expGeQ64 (x64 : ℕ) : ℕ :=
  max q64Scale (square5Q64 5 (expGeLoopQ64 x64 inv32Succ64Lb q64Scale q64Scale))

lemma expGeQ64_sound {x64 : ℕ} {x : ℝ} (hx_nn : 0 ≤ x)
    (hx : (x64 : ℝ) / (q64Scale : ℝ) ≤ x) :
    (q64Scale : ℝ) ≤ (expGeQ64 x64 : ℝ) ∧
      ((expGeQ64 x64 : ℝ) / (q64Scale : ℝ)) ≤ Real.exp x := by
  refine ⟨by unfold expGeQ64; exact_mod_cast le_max_left _ _, ?_⟩
  have hloop := expGeLoopQ64_sound hx_nn hx inv32Succ64Lb 0 q64Scale q64Scale inv32Succ64Lb_ok
    (by simp [div_self q64Scale_pos.ne'])
    (by simp [div_self q64Scale_pos.ne'])
  have hsum : ∑ m ∈ Finset.range (0 + 1 + inv32Succ64Lb.length), (x / 32) ^ m / (m.factorial : ℝ) ≤
      Real.exp (x / 32) :=
    Real.sum_le_exp_of_nonneg (by positivity) _
  have hsq5 := square5Q64_sound 5 (expGeLoopQ64 x64 inv32Succ64Lb q64Scale q64Scale)
    (Real.exp (x / 32)) (hloop.trans hsum)
  have hexp32 : (Real.exp (x / 32)) ^ (2 ^ 5) = Real.exp x := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hexp32] at hsq5
  unfold expGeQ64
  by_cases hle : q64Scale ≤ square5Q64 5 (expGeLoopQ64 x64 inv32Succ64Lb q64Scale q64Scale)
  · rw [max_eq_right hle]; exact hsq5
  · rw [max_eq_left (le_of_not_ge hle), div_self q64Scale_pos.ne']; exact Real.one_le_exp hx_nn

def invFact64Ub : List ℕ := [
  18446744073709551616, 18446744073709551616, 9223372036854775808, 3074457345618258603,
  768614336404564651, 153722867280912931, 25620477880152156, 3660068268593166,
  457508533574146, 50834281508239, 5083428150824, 462129831894,
  38510819325, 2962370718, 211597909, 14106528
]

private def checkInvFact : ℕ → List ℕ → Bool
  | _, [] => true
  | j, c :: rest => decide (q64Scale ≤ c * j.factorial) && checkInvFact (j + 1) rest

private lemma invFact64Ub_ok : checkInvFact 0 invFact64Ub = true := by native_decide

/-- Certified Q64 upper bound on `1 / j!` for `0 ≤ j < 16` (exact `decide` guarantee). -/
def invFactUb (j : ℕ) : Dyadic := Dyadic.ofQ64 (invFact64Ub.getD j q64Scale)

lemma invFactUb_le {j : ℕ} (hj : j < 16) :
    (1 : ℝ) / (j.factorial : ℝ) ≤ (invFactUb j).toReal := by
  have hchk : ∀ (cs : List ℕ) (m : ℕ), checkInvFact m cs = true →
      ∀ i (hi : i < cs.length), q64Scale ≤ cs[i] * (m + i).factorial := by
    intro cs; induction cs with
    | nil => intro _ _ i hi; simp at hi
    | cons c rest ih =>
      intro m h i hi
      simp only [checkInvFact, Bool.and_eq_true, decide_eq_true_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ k =>
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using
          ih (m + 1) h.2 k (by simpa using Nat.lt_of_succ_lt_succ hi)
  have hlen : invFact64Ub.length = 16 := rfl
  have hi := hchk invFact64Ub 0 invFact64Ub_ok j (hlen ▸ hj)
  rw [zero_add] at hi
  unfold invFactUb
  rw [Dyadic.ofQ64_toReal, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hj), Option.getD_some]
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos j)) q64Scale_pos, one_mul]
  exact_mod_cast hi

/-- Division-free outward upper bound on `∑ j ≤ k, x^j / j!` (`k < 16`). -/
def sumPowDivFactUb (x : Dyadic) : ℕ → Dyadic
  | 0 => Dyadic.one
  | k + 1 => (sumPowDivFactUb x k).add ((Dyadic.powUb x (k + 1)).mulUb (invFactUb (k + 1)))

lemma sumPowDivFactUb_sound (x : Dyadic) {k : ℕ} (hk : k < 16) :
    ∑ j ∈ Finset.range (k + 1), x.toReal ^ j / (j.factorial : ℝ) ≤
      (sumPowDivFactUb x k).toReal := by
  induction k with
  | zero => simp [sumPowDivFactUb, Dyadic.one_toReal]
  | succ k ih =>
    rw [Finset.sum_range_succ, sumPowDivFactUb, Dyadic.add_toReal]
    have hinv := invFactUb_le hk
    have hpow := Dyadic.powUb_sound x (k + 1)
    have hterm : x.toReal ^ (k + 1) / ((k + 1).factorial : ℝ) ≤
        ((Dyadic.powUb x (k + 1)).mulUb (invFactUb (k + 1))).toReal := by
      rw [div_eq_mul_one_div]
      exact (mul_le_mul hpow hinv (by positivity) (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)
    exact add_le_add (ih (by omega)) hterm

end

end BuchstabSwitching.SieveInst
