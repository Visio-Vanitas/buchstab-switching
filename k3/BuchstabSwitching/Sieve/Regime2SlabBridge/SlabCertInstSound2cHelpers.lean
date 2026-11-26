import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cLower
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstJOddSmall
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.DiscreteJFull
import BuchstabSwitching.Sieve.OddSquarefreeBounds.ConstantBounds
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstCJ
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstLogExp
import Mathlib.Tactic

/-!
# Shared Regime `2c` `SciNat` Helpers, `α₀` Bound, `J_odd`, & Mertens Helpers

Provides:
1. `ExtraSciHelpers`: `sub_le_subLb_toReal`, `subLb_le_max_zero`, `ble_false_le`, `blt_false_le`,
   `sumSciFin`, `sum_fin_le_sumSciFin`;
2. `JOddAndMertHelpers`: `alpha0_ge_63518`, `expGe12`, `expNegUb12`, `jOddLbSci`, `jOddUbSci`,
   `jOddHybridUbSci`, `jsMertLoUbSci`, `jsMertHiUbSci` and their soundness theorems.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

private abbrev sn (m e : ℕ) : SciNat := ⟨m, e⟩

section ExtraSciHelpers

lemma sub_le_subLb_toReal (a b : SciNat) : a.toReal - b.toReal ≤ (a.subLb b).toReal := by
  unfold SciNat.subLb SciNat.toReal; split_ifs with he
  · have h10 : (10 : ℝ) ^ b.e = (10 : ℝ) ^ a.e * (10 : ℝ) ^ (b.e - a.e) := by rw [← pow_add, Nat.add_sub_of_le he]
    dsimp only; rw [le_div_iff₀ (by positivity : (0 : ℝ) < (10 : ℝ) ^ b.e)]
    rcases le_or_gt b.m (a.m * 10 ^ (b.e - a.e)) with hle | hlt
    · rw [Nat.cast_sub hle]; push_cast; rw [h10]; field_simp [(by positivity : (10 : ℝ) ^ a.e ≠ 0)]; ring_nf; rfl
    · have h0 : ((a.m * 10 ^ (b.e - a.e) - b.m : ℕ) : ℝ) = 0 := by simp [Nat.sub_eq_zero_of_le hlt.le]
      rw [h0]
      have : (a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e) < (b.m : ℝ) := by exact_mod_cast hlt
      rw [h10]; field_simp [(by positivity : (10 : ℝ) ^ a.e ≠ 0)]; nlinarith [(by positivity : (0 : ℝ) < (10 : ℝ) ^ a.e)]
  · have he' : b.e ≤ a.e := le_of_not_ge he
    have h10 : (10 : ℝ) ^ a.e = (10 : ℝ) ^ b.e * (10 : ℝ) ^ (a.e - b.e) := by rw [← pow_add, Nat.add_sub_of_le he']
    dsimp only; rw [le_div_iff₀ (by positivity : (0 : ℝ) < (10 : ℝ) ^ a.e)]
    rcases le_or_gt (b.m * 10 ^ (a.e - b.e)) a.m with hle | hlt
    · rw [Nat.cast_sub hle]; push_cast; rw [h10]; field_simp [(by positivity : (10 : ℝ) ^ b.e ≠ 0)]; ring_nf; rfl
    · have h0 : ((a.m - b.m * 10 ^ (a.e - b.e) : ℕ) : ℝ) = 0 := by simp [Nat.sub_eq_zero_of_le hlt.le]
      rw [h0]
      have : (a.m : ℝ) < (b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e) := by exact_mod_cast hlt
      rw [h10]; field_simp [(by positivity : (10 : ℝ) ^ b.e ≠ 0)]; nlinarith [(by positivity : (0 : ℝ) < (10 : ℝ) ^ b.e)]

lemma subLb_le_max_zero {a b : SciNat} {A B : ℝ} (ha : a.toReal ≤ A) (hb : B ≤ b.toReal) :
    (a.subLb b).toReal ≤ max 0 (A - B) := by
  by_cases hba : b.toReal ≤ a.toReal
  · exact (SciProofs.subLb_le hba).trans (le_trans (by linarith) (le_max_right _ _))
  · have hba' : a.toReal < b.toReal := lt_of_not_ge hba
    have hzero : (a.subLb b).toReal = 0 := by
      unfold SciNat.subLb SciNat.toReal at hba' ⊢; split_ifs with he
      · have h10 : (10 : ℝ) ^ b.e = (10 : ℝ) ^ a.e * (10 : ℝ) ^ (b.e - a.e) := by rw [← pow_add, Nat.add_sub_of_le he]
        rw [div_lt_div_iff₀ (by positivity) (by positivity), h10] at hba'
        have hm : a.m * 10 ^ (b.e - a.e) < b.m := by
          exact_mod_cast lt_of_mul_lt_mul_right (by linarith : ((a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e)) * (10 : ℝ) ^ a.e < (b.m : ℝ) * (10 : ℝ) ^ a.e) (by positivity)
        simp [Nat.sub_eq_zero_of_le hm.le]
      · have he' : b.e ≤ a.e := le_of_not_ge he
        have h10 : (10 : ℝ) ^ a.e = (10 : ℝ) ^ b.e * (10 : ℝ) ^ (a.e - b.e) := by rw [← pow_add, Nat.add_sub_of_le he']
        rw [div_lt_div_iff₀ (by positivity) (by positivity), h10] at hba'
        have hm : a.m < b.m * 10 ^ (a.e - b.e) := by
          exact_mod_cast lt_of_mul_lt_mul_right (by linarith : (a.m : ℝ) * (10 : ℝ) ^ b.e < ((b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e)) * (10 : ℝ) ^ b.e) (by positivity)
        simp [Nat.sub_eq_zero_of_le hm.le]
    rw [hzero]; exact le_max_left _ _

lemma ble_false_le {a b : SciNat} (h : a.ble b = false) : b.toReal ≤ a.toReal := by
  unfold SciNat.ble at h; unfold SciNat.toReal; split_ifs at h with he
  · rw [decide_eq_false_iff_not, not_le] at h
    have h10 : (10 : ℝ) ^ b.e = (10 : ℝ) ^ a.e * (10 : ℝ) ^ (b.e - a.e) := by rw [← pow_add, Nat.add_sub_of_le he]
    rw [div_le_div_iff₀ (by positivity) (by positivity), h10]
    have hm : (b.m : ℝ) ≤ (a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e) := by exact_mod_cast h.le
    nlinarith [(by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ a.e)]
  · have he' : b.e ≤ a.e := le_of_not_ge he
    rw [decide_eq_false_iff_not, not_le] at h
    have h10 : (10 : ℝ) ^ a.e = (10 : ℝ) ^ b.e * (10 : ℝ) ^ (a.e - b.e) := by rw [← pow_add, Nat.add_sub_of_le he']
    rw [div_le_div_iff₀ (by positivity) (by positivity), h10]
    have hm : (b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e) ≤ (a.m : ℝ) := by exact_mod_cast h.le
    nlinarith [(by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ b.e)]

lemma blt_false_le {a b : SciNat} (h : a.blt b = false) : b.toReal ≤ a.toReal := by
  unfold SciNat.blt at h; unfold SciNat.toReal; split_ifs at h with he
  · rw [decide_eq_false_iff_not, not_lt] at h
    have h10 : (10 : ℝ) ^ b.e = (10 : ℝ) ^ a.e * (10 : ℝ) ^ (b.e - a.e) := by rw [← pow_add, Nat.add_sub_of_le he]
    rw [div_le_div_iff₀ (by positivity) (by positivity), h10]
    have hm : (b.m : ℝ) ≤ (a.m : ℝ) * (10 : ℝ) ^ (b.e - a.e) := by exact_mod_cast h
    nlinarith [(by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ a.e)]
  · have he' : b.e ≤ a.e := le_of_not_ge he
    rw [decide_eq_false_iff_not, not_lt] at h
    have h10 : (10 : ℝ) ^ a.e = (10 : ℝ) ^ b.e * (10 : ℝ) ^ (a.e - b.e) := by rw [← pow_add, Nat.add_sub_of_le he']
    rw [div_le_div_iff₀ (by positivity) (by positivity), h10]
    have hm : (b.m : ℝ) * (10 : ℝ) ^ (a.e - b.e) ≤ (a.m : ℝ) := by exact_mod_cast h
    nlinarith [(by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ b.e)]

def sumSciFin {n : ℕ} (f : Fin n → SciNat) : SciNat :=
  (List.finRange n).foldl (fun a i => a.add (f i)) (sn 0 0)

lemma sumSciFin_toReal {n : ℕ} (f : Fin n → SciNat) :
    (sumSciFin f).toReal = ∑ i : Fin n, (f i).toReal := by
  have hgen : ∀ (L : List (Fin n)) (acc : SciNat),
      (L.foldl (fun a i => a.add (f i)) acc).toReal =
        acc.toReal + (L.map (fun i => (f i).toReal)).sum := by
    intro L; induction L with
    | nil => intro acc; simp
    | cons i tl ih =>
      intro acc; rw [List.foldl_cons, ih, SciProofs.add_toReal, List.map_cons, List.sum_cons]; ring
  have h1 := hgen (List.finRange n) (sn 0 0)
  have hsum : (List.map (fun i => (f i).toReal) (List.finRange n)).sum = ∑ i : Fin n, (f i).toReal := by
    rw [← List.sum_toFinset _ (List.nodup_finRange n)]; simp
  rw [sumSciFin, h1, hsum, show (sn 0 0).toReal = 0 by simp [SciNat.toReal], zero_add]

lemma sum_fin_le_sumSciFin {n : ℕ} (f : Fin n → SciNat) (g : Fin n → ℝ)
    (hg : ∀ i : Fin n, g i ≤ (f i).toReal) :
    ∑ i : Fin n, g i ≤ (sumSciFin f).toReal := by
  rw [sumSciFin_toReal]; exact Finset.sum_le_sum fun i _ => hg i

lemma sumSciFin_le_sum_fin {n : ℕ} (f : Fin n → SciNat) (g : Fin n → ℝ)
    (hg : ∀ i : Fin n, (f i).toReal ≤ g i) :
    (sumSciFin f).toReal ≤ ∑ i : Fin n, g i := by
  rw [sumSciFin_toReal]; exact Finset.sum_le_sum fun i _ => hg i

end ExtraSciHelpers

section JOddAndMertHelpers

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
      have h1 := floorDiv_le_real (a := BuchstabSwitching.scaleS) (b := lo + m + 1) (by omega)
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

private lemma hc2c_0 : harmChunk2c 0 32 = 4058495195428 := by decide
private lemma hc2c_1 : harmChunk2c 32 32 = 685395708257 := by decide
private lemma hc2c_2 : harmChunk2c 64 32 = 402872243836 := by decide
private lemma hc2c_3 : harmChunk2c 96 32 = 286383945022 := by decide
private lemma hc2c_4 : harmChunk2c 128 32 = 222364132337 := by decide
private lemma hc2c_5 : harmChunk2c 160 32 = 181801718088 := by decide
private lemma hc2c_6 : harmChunk2c 192 32 = 153779255741 := by decide
private lemma hc2c_7 : harmChunk2c 224 32 = 133252764007 := by decide

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

private def h0LoSci : SciNat := (sn 1514236169719 12)
private def h0HiSci : SciNat := (sn 1516136089708 12)
private def cjUbSci : SciNat := (sn 8030531202875 12)
private def a0LbSci : SciNat := (sn 63518 5)
private def a0UbSci : SciNat := (sn 636 3)

private lemma scaleS_cast_12 : (BuchstabSwitching.scaleS : ℝ) = (10 : ℝ) ^ 12 := by
  unfold BuchstabSwitching.scaleS; norm_num

def expGe12 (t : SciNat) : SciNat :=
  let r := t.trimLb 8; ⟨max BuchstabSwitching.scaleS (BuchstabSwitching.expGe r.m (10 ^ r.e)), 12⟩

lemma expGe12_sound (t : SciNat) :
    0 < (expGe12 t).toReal ∧ (expGe12 t).toReal ≤ Real.exp t.toReal := by
  let r := t.trimLb 8
  have hS : 0 < BuchstabSwitching.scaleS := by unfold BuchstabSwitching.scaleS; positivity
  refine ⟨by unfold expGe12 SciNat.toReal; exact div_pos (by exact_mod_cast lt_of_lt_of_le hS (le_max_left _ _)) (by positivity), ?_⟩
  have he := BuchstabSwitching.expGe_sound (num := r.m) (den := 10 ^ r.e) (pow_pos (by norm_num) r.e)
  rw [scaleS_cast_12] at he; push_cast at he
  have he' := he.trans (Real.exp_le_exp.mpr (SciProofs.trimLb_le t 8))
  have h1 : ((BuchstabSwitching.scaleS : ℕ) : ℝ) / (10 : ℝ) ^ 12 ≤ Real.exp t.toReal := by
    rw [scaleS_cast_12, div_self (by positivity)]; exact Real.one_le_exp (SciNat.toReal_nonneg _)
  unfold expGe12 SciNat.toReal; dsimp only
  by_cases hle : BuchstabSwitching.scaleS ≤ BuchstabSwitching.expGe r.m (10 ^ r.e)
  · rw [max_eq_right hle]; exact he'
  · rw [max_eq_left (le_of_not_ge hle)]; exact h1

def expNegUb12 (t : SciNat) : SciNat :=
  let r := t.trimLb 8; ⟨BuchstabSwitching.expNegUb r.m (10 ^ r.e), 12⟩

lemma expNegUb12_sound {t : SciNat} {x : ℝ} (ht : t.toReal ≤ x) :
    Real.exp (-x) ≤ (expNegUb12 t).toReal := by
  let r := t.trimLb 8
  have he := BuchstabSwitching.expNegUb_sound (num := r.m) (den := 10 ^ r.e) (pow_pos (by norm_num) r.e)
  rw [scaleS_cast_12] at he; push_cast at he
  exact (Real.exp_le_exp.mpr (neg_le_neg ((SciProofs.trimLb_le t 8).trans ht))).trans he

def jOddLbSci (logLo : SciNat) : SciNat :=
  let mainLb := h0LoSci.mul ((logLo.mul (sn 5 1)).add a0LbSci)
  let errUb := cjUbSci.mul (expNegUb12 (divLbSig logLo (sn 4 0) 8))
  if errUb.ble mainLb then (mainLb.subLb errUb).trimLb 12 else (sn 0 0)

lemma jOddLbSci_sound {logLo : SciNat} {X : ℝ} (hX1 : 1 ≤ X) (hlog : logLo.toReal ≤ Real.log X) :
    (jOddLbSci logLo).toReal ≤ BuchstabSwitching.J_odd_lb_asym X := by
  unfold jOddLbSci; dsimp only; split_ifs with hcmp
  · have hXpos : 0 < X := by linarith
    have hneg : X ^ (-(1 / 4 : ℝ)) ≤ (expNegUb12 (divLbSig logLo (sn 4 0) 8)).toReal := by
      rw [Real.rpow_def_of_pos hXpos, mul_neg, mul_one_div]
      exact expNegUb12_sound ((divLbSig_le _ _ 8).trans (by
        simpa [SciNat.toReal] using div_le_div_of_nonneg_right hlog (by norm_num)))
    have hH0 : h0LoSci.toReal ≤ BuchstabSwitching.H_0 := by
      simpa [h0LoSci, SciNat.toReal, scaleS_cast_12] using BuchstabSwitching.H_0_bounds_cert.1
    have hCJ : BuchstabSwitching.C_J ≤ cjUbSci.toReal := by
      simpa [cjUbSci, SciNat.toReal, scaleS_cast_12] using BuchstabSwitching.C_J_le_cert
    have hm_le : (h0LoSci.mul ((logLo.mul (sn 5 1)).add a0LbSci)).toReal ≤
        BuchstabSwitching.H_0 * ((1 / 2 : ℝ) * Real.log X + BuchstabSwitching.alpha0) := by
      rw [SciProofs.mul_toReal, SciProofs.add_toReal, SciProofs.mul_toReal,
        show (sn 5 1).toReal = 1 / 2 by simp [SciNat.toReal]; norm_num,
        show a0LbSci.toReal = 63518 / 100000 by simp [a0LbSci, SciNat.toReal]; norm_num]
      have h1 : logLo.toReal * (1 / 2 : ℝ) + 63518 / 100000 ≤ (1 / 2 : ℝ) * Real.log X + BuchstabSwitching.alpha0 := by
        linarith [alpha0_ge_63518]
      exact mul_le_mul hH0 h1 (by have := SciNat.toReal_nonneg logLo; linarith)
        (hH0.trans' (SciNat.toReal_nonneg _))
    have herr_le : BuchstabSwitching.C_J * X ^ (-(1 / 4 : ℝ)) ≤
        (cjUbSci.mul (expNegUb12 (divLbSig logLo (sn 4 0) 8))).toReal := by
      rw [SciProofs.mul_toReal]; exact mul_le_mul hCJ hneg (Real.rpow_nonneg hXpos.le _) (SciNat.toReal_nonneg _)
    exact (SciProofs.trimLb_le _ 12).trans ((SciProofs.subLb_le (SciProofs.ble_sound hcmp)).trans
      (le_trans (by linarith) (le_max_right _ _)))
  · simpa [SciNat.toReal] using BuchstabSwitching.J_odd_lb_asym_nonneg X

def jOddUbSci (logLo logHi : SciNat) : SciNat :=
  ((h0HiSci.mul ((logHi.mul (sn 5 1)).add a0UbSci)).add
    (cjUbSci.mul (expNegUb12 (divLbSig logLo (sn 4 0) 8)))).trimUb 12

lemma jOddUbSci_sound {logLo logHi : SciNat} {X : ℝ} (hX1 : 1 ≤ X)
    (hlo : logLo.toReal ≤ Real.log X) (hhi : Real.log X ≤ logHi.toReal) :
    BuchstabSwitching.J_odd_ub_asym X ≤ (jOddUbSci logLo logHi).toReal := by
  have hXpos : 0 < X := by linarith
  have hneg : X ^ (-(1 / 4 : ℝ)) ≤ (expNegUb12 (divLbSig logLo (sn 4 0) 8)).toReal := by
    rw [Real.rpow_def_of_pos hXpos, mul_neg, mul_one_div]
    exact expNegUb12_sound ((divLbSig_le _ _ 8).trans (by
      simpa [SciNat.toReal] using div_le_div_of_nonneg_right hlo (by norm_num)))
  have hH0 : BuchstabSwitching.H_0 ≤ h0HiSci.toReal := by
    simpa [h0HiSci, SciNat.toReal, scaleS_cast_12] using BuchstabSwitching.H_0_bounds_cert.2
  have hCJ : BuchstabSwitching.C_J ≤ cjUbSci.toReal := by
    simpa [cjUbSci, SciNat.toReal, scaleS_cast_12] using BuchstabSwitching.C_J_le_cert
  have hmain : BuchstabSwitching.H_0 * ((1 / 2 : ℝ) * Real.log X + BuchstabSwitching.alpha0) ≤
      (h0HiSci.mul ((logHi.mul (sn 5 1)).add a0UbSci)).toReal := by
    rw [SciProofs.mul_toReal, SciProofs.add_toReal, SciProofs.mul_toReal,
      show (sn 5 1).toReal = 1 / 2 by simp [SciNat.toReal]; norm_num,
      show a0UbSci.toReal = 636 / 1000 by simp [a0UbSci, SciNat.toReal]; norm_num]
    have h1 : (1 / 2 : ℝ) * Real.log X + BuchstabSwitching.alpha0 ≤ logHi.toReal * (1 / 2 : ℝ) + 636 / 1000 := by
      linarith [BuchstabSwitching.alpha0_le_636_div_1000]
    exact mul_le_mul hH0 h1 (by have := Real.log_nonneg hX1; linarith [alpha0_ge_63518]) (SciNat.toReal_nonneg _)
  have herr : BuchstabSwitching.C_J * X ^ (-(1 / 4 : ℝ)) ≤
      (cjUbSci.mul (expNegUb12 (divLbSig logLo (sn 4 0) 8))).toReal := by
    rw [SciProofs.mul_toReal]; exact mul_le_mul hCJ hneg (Real.rpow_nonneg hXpos.le _) (SciNat.toReal_nonneg _)
  refine le_trans ?_ (SciProofs.trimUb_le _ 12); rw [SciProofs.add_toReal]; unfold BuchstabSwitching.J_odd_ub_asym; linarith

/-- Hybrid `J_odd` upper bound combining the 11-step small-`X` staircase with `jOddUbSci`. -/
def jOddHybridUbSci (logLo logHi : SciNat) : SciNat :=
  jOddStepMin logHi (jOddUbSci logLo logHi)

lemma jOddHybridUbSci_sound (consts : External.CertifiedConstants) {logLo logHi : SciNat} {X : ℝ}
    (hX1 : 1 ≤ X) (hlo : logLo.toReal ≤ Real.log X) (hhi : Real.log X ≤ logHi.toReal) :
    BuchstabSwitching.J_odd X ≤ (jOddHybridUbSci logLo logHi).toReal :=
  jOddStepMin_sound consts hX1 hhi
    ((BuchstabSwitching.le_J_odd_ub_asym hX1).trans (jOddUbSci_sound hX1 hlo hhi))

def jsMertLoUbSci (logLo : SciNat) : SciNat := divUbSig (sn 2964 9) logLo 12

lemma jsMertLoUbSci_sound {logLo : SciNat} {x : ℝ} (hpos : 0 < logLo.toReal)
    (hx : logLo.toReal ≤ Real.log x) : External.jsMertensLoErr x ≤ (jsMertLoUbSci logLo).toReal := by
  unfold External.jsMertensLoErr jsMertLoUbSci
  have h2 := divUbSig_le (sn 2964 9) logLo 12
  rw [show (sn 2964 9).toReal = (2.964e-6 : ℝ) by unfold SciNat.toReal; norm_num] at h2
  exact (div_le_div_of_nonneg_left (by norm_num) hpos hx).trans h2

def jsMertHiUbSci (logLo : SciNat) : SciNat :=
  let t1 := divUbSig (sn 6836 9) logLo 12
  if (sn 27631022 6).ble logLo then t1
  else
    let sqLb := expGe12 ((logLo.mul (sn 5 1)).trimLb 8)
    let t2 := divUbSig (sn 2 0) (sqLb.mul logLo) 12
    if t1.ble t2 then t2 else t1

private lemma exp_27631022_gt_10_12 (consts : External.CertifiedConstants) :
    (10 : ℝ) ^ 12 < Real.exp ((sn 27631022 6).toReal) := by
  have hok : (ratLogBounds 10 1).1 = true ∧ ((ratLogBounds 10 1).2.2.mul (sn 12 0)).blt (sn 27631022 6) = true := by decide
  have hr := (ratLogBounds_sound consts hok.1).2
  rw [Nat.cast_one, div_one, Nat.cast_ofNat] at hr
  have hlt := SciProofs.blt_sound hok.2
  rw [SciProofs.mul_toReal, show (sn 12 0).toReal = 12 by simp [SciNat.toReal]] at hlt
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (10 : ℝ) ^ 12), Real.exp_lt_exp, Real.log_pow]
  push_cast
  linarith

lemma jsMertHiUbSci_sound (consts : External.CertifiedConstants) {logLo : SciNat} {x : ℝ}
    (hx_pos : 0 < x) (h10 : (sn 10 0).blt logLo = true)
    (hx : logLo.toReal ≤ Real.log x) : External.jsMertensHiErr x ≤ (jsMertHiUbSci logLo).toReal := by
  have h10r : (10 : ℝ) < logLo.toReal := by simpa [SciNat.toReal] using SciProofs.blt_sound h10
  have hx_log10 : 10 < Real.log x := h10r.trans_le hx
  have h6836 : (6.836e-6 : ℝ) / Real.log x ≤ (divUbSig (sn 6836 9) logLo 12).toReal := by
    have h2 := divUbSig_le (sn 6836 9) logLo 12
    rw [show (sn 6836 9).toReal = (6.836e-6 : ℝ) by unfold SciNat.toReal; norm_num] at h2
    exact (div_le_div_of_nonneg_left (by norm_num) (by linarith) hx).trans h2
  set sqLb := expGe12 ((logLo.mul (sn 5 1)).trimLb 8)
  have hbjv : ¬ x > (10 : ℝ) ^ 12 → External.jsMertensHiErr x ≤ (divUbSig (sn 2 0) (sqLb.mul logLo) 12).toReal := by
    intro hx12; rw [External.jsMertensHiErr_eq_bjv (not_lt.mp hx12) hx_log10]
    have hsq : 0 < sqLb.toReal ∧ sqLb.toReal ≤ Real.sqrt x := by
      refine ⟨(expGe12_sound _).1, (expGe12_sound _).2.trans ?_⟩
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]
      refine Real.exp_le_exp.mpr ((SciProofs.trimLb_le _ 8).trans ?_)
      rw [SciProofs.mul_toReal, show (sn 5 1).toReal = 1 / 2 by simp [SciNat.toReal]; norm_num]; linarith
    have h2 := divUbSig_le (sn 2 0) (sqLb.mul logLo) 12
    rw [SciProofs.mul_toReal, show (sn 2 0).toReal = (2 : ℝ) by simp [SciNat.toReal]] at h2
    exact (div_le_div₀ (by norm_num) (le_refl (2 : ℝ)) (mul_pos hsq.1 (by linarith))
      (mul_le_mul hsq.2 hx (by linarith) (Real.sqrt_nonneg _))).trans h2
  unfold jsMertHiUbSci; dsimp only; split_ifs with hbig hcmp
  · have hx12 : (10 : ℝ) ^ 12 < x := by
      simpa [Real.exp_log hx_pos] using
        (exp_27631022_gt_10_12 consts).trans_le (Real.exp_le_exp.mpr ((SciProofs.ble_sound hbig).trans hx))
    rw [External.jsMertensHiErr_eq_tail hx12]; exact h6836
  · by_cases hx12 : x > (10 : ℝ) ^ 12
    · rw [External.jsMertensHiErr_eq_tail hx12]; exact h6836.trans (SciProofs.ble_sound hcmp)
    · exact hbjv hx12
  · by_cases hx12 : x > (10 : ℝ) ^ 12
    · rw [External.jsMertensHiErr_eq_tail hx12]; exact h6836
    · exact (hbjv hx12).trans (ble_false_le (Bool.eq_false_iff.mpr hcmp))

end JOddAndMertHelpers

section JFullTerm1Helpers

private def linCombLog (a b d : ℕ) (sLo sHi tLo tHi : SciNat) : SciNat × SciNat :=
  (divLbSig (((SciNat.ofNat a).mul sLo).add ((SciNat.ofNat b).mul tLo)) (SciNat.ofNat d) 12,
   divUbSig (((SciNat.ofNat a).mul sHi).add ((SciNat.ofNat b).mul tHi)) (SciNat.ofNat d) 12)

private lemma linCombLog_sound {a b d : ℕ} (hd : 0 < d) {sLo sHi tLo tHi : SciNat} {s t : ℝ}
    (hs : sLo.toReal ≤ s ∧ s ≤ sHi.toReal) (ht : tLo.toReal ≤ t ∧ t ≤ tHi.toReal) :
    (linCombLog a b d sLo sHi tLo tHi).1.toReal ≤ ((a : ℝ) * s + (b : ℝ) * t) / (d : ℝ) ∧
      ((a : ℝ) * s + (b : ℝ) * t) / (d : ℝ) ≤ (linCombLog a b d sLo sHi tLo tHi).2.toReal := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  constructor
  · have h1 := divLbSig_le (((SciNat.ofNat a).mul sLo).add ((SciNat.ofNat b).mul tLo)) (SciNat.ofNat d) 12
    rw [SciProofs.ofNat_toReal, SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal,
      SciProofs.ofNat_toReal, SciProofs.ofNat_toReal] at h1
    refine h1.trans (div_le_div_of_nonneg_right ?_ hd_pos.le)
    exact add_le_add (mul_le_mul_of_nonneg_left hs.1 (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg _))
  · have h2 := divUbSig_le (((SciNat.ofNat a).mul sHi).add ((SciNat.ofNat b).mul tHi)) (SciNat.ofNat d) 12
    rw [SciProofs.ofNat_toReal, SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal,
      SciProofs.ofNat_toReal, SciProofs.ofNat_toReal] at h2
    refine le_trans (div_le_div_of_nonneg_right ?_ hd_pos.le) h2
    exact add_le_add (mul_le_mul_of_nonneg_left hs.2 (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg _))

def jFullTerm1 (zLogLo zLogHi xiLogLo xiLogHi xiLb : SciNat) (k : Fin 12) : Bool × SciNat :=
  let w0 := linCombLog (12 - k.1) k.1 12 zLogLo zLogHi xiLogLo xiLogHi
  let w1 := linCombLog (11 - k.1) (k.1 + 1) 12 zLogLo zLogHi xiLogLo xiLogHi
  let w1pHi := if k.1 + 1 == 12 then w1.2.add (divUbSig (sn 1 0) xiLb 12) else w1.2
  let rUb := divUbSig w1pHi w0.1 12
  let rLog := ratLogBounds rUb.m (10 ^ rUb.e)
  let w0Lb := expGe12 w0.1
  let den2 := w0Lb.subLb (sn 2 0)
  let mertUb := ((rLog.2.2.add (jsMertHiUbSci w1.1)).add (jsMertLoUbSci w0.1)).add (divUbSig (sn 2 0) den2 12)
  let ok := (sn 10 0).blt w0.1 && (sn 10 0).blt w1.1 && (sn 2 0).ble w0Lb && (sn 1 0).ble den2 && rLog.1
  (ok, (jOddHybridUbSci (xiLogLo.subLb w0.2) (xiLogHi.subLb w0.1)).mul mertUb)

private lemma jFullTerm1_sound_aux (consts : External.CertifiedConstants) {z_nat : ℕ} {xi : ℝ}
    (hz_pos : (0 : ℝ) < (z_nat : ℝ)) (hzxi : (z_nat : ℝ) < xi)
    {xiLogLo xiLogHi xiLb : SciNat}
    (hxiL : xiLogLo.toReal ≤ Real.log xi ∧ Real.log xi ≤ xiLogHi.toReal)
    (hxiLbPos : 0 < xiLb.toReal) (hxiLb : xiLb.toReal ≤ xi) (k : Fin 12)
    {w0Lo w0Hi w1Lo w1Hi w1pHi rUb rLogUb w0Lb den2 : SciNat}
    (hw0_b : w0Lo.toReal ≤ ((12 - k.1 : ℕ) * Real.log (z_nat : ℝ) + (k.1 : ℕ) * Real.log xi) / 12 ∧
      ((12 - k.1 : ℕ) * Real.log (z_nat : ℝ) + (k.1 : ℕ) * Real.log xi) / 12 ≤ w0Hi.toReal)
    (hw1_b : w1Lo.toReal ≤ ((11 - k.1 : ℕ) * Real.log (z_nat : ℝ) + ((k.1 + 1 : ℕ) : ℝ) * Real.log xi) / 12 ∧
      ((11 - k.1 : ℕ) * Real.log (z_nat : ℝ) + ((k.1 + 1 : ℕ) : ℝ) * Real.log xi) / 12 ≤ w1Hi.toReal)
    (hw010 : (sn 10 0).blt w0Lo = true) (hw110 : (sn 10 0).blt w1Lo = true)
    (hw0Lb_eq : w0Lb = expGe12 w0Lo) (hden2_eq : den2 = w0Lb.subLb (sn 2 0))
    (hw02 : (sn 2 0).ble w0Lb = true) (hden1 : (sn 1 0).ble den2 = true)
    (hw1pHi_eq : w1pHi = if k.1 + 1 == 12 then w1Hi.add (divUbSig (sn 1 0) xiLb 12) else w1Hi)
    (hrUb_eq : rUb = divUbSig w1pHi w0Lo 12)
    (hokL : (ratLogBounds rUb.m (10 ^ rUb.e)).1 = true)
    (hrLog_eq : rLogUb = (ratLogBounds rUb.m (10 ^ rUb.e)).2.2) :
    let w : Fin 13 → ℝ := fun j =>
      Real.exp (((12 - j.1 : ℕ) * Real.log (z_nat : ℝ) + (j.1 : ℕ) * Real.log xi) / 12)
    let w0 := w k.castSucc
    let w1p := if k.val + 1 = 12 then w k.succ + 1 else w k.succ
    BuchstabSwitching.J_odd (xi / w0) *
        (max 0 (Real.log (Real.log w1p / Real.log w0) +
          External.jsMertensHiErr w1p + External.jsMertensLoErr w0) + 2 / (w0 - 2)) ≤
      ((jOddHybridUbSci (xiLogLo.subLb w0Hi) (xiLogHi.subLb w0Lo)).mul
        (((rLogUb.add (jsMertHiUbSci w1Lo)).add (jsMertLoUbSci w0Lo)).add
          (divUbSig (sn 2 0) den2 12))).toReal := by
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
      rw [hw1_xi, SciProofs.add_toReal, show xi + 1 = xi * (1 + 1 / xi) by field_simp [hxi_pos.ne'],
        Real.log_mul hxi_pos.ne' (by positivity)]
      have hlog_1 : Real.log (1 + 1 / xi) ≤ 1 / xi := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / xi)]
      have hinv : 1 / xi ≤ (divUbSig (sn 1 0) xiLb 12).toReal := by
        refine (one_div_le_one_div_of_le hxiLbPos hxiLb).trans ?_
        have h := divUbSig_le (sn 1 0) xiLb 12
        rwa [show (sn 1 0).toReal = 1 by simp [SciNat.toReal]] at h
      have hlogxi : Real.log xi ≤ w1Hi.toReal := by rw [← hw1_xi]; exact hw1_b.2
      linarith
    · have hk12v : k.val + 1 ≠ 12 := hk12
      have hk12b : (k.1 + 1 == 12) = false := beq_false_of_ne hk12
      simp only [hk12v, ↓reduceIte, hk12b, Bool.false_eq_true]
      exact hw1_b.2
  have hw0_10r : (10 : ℝ) < w0Lo.toReal := by
    have h := SciProofs.blt_sound hw010; rwa [show (sn 10 0).toReal = 10 by simp [SciNat.toReal]] at h
  have hr_le : Real.log (Real.log w1p / Real.log w0) ≤ rLogUb.toReal := by
    have hlogw0_pos : 0 < Real.log w0 := by linarith [hw0_b.1]
    have hlogw1p_pos : 0 < Real.log w1p := lt_of_lt_of_le hlogw0_pos
      ((Real.log_le_log hw0_pos hw0_le_w1).trans (Real.log_le_log hw1_pos hw1_le_w1p))
    have hratio : Real.log w1p / Real.log w0 ≤ rUb.toReal := by
      rw [hrUb_eq]
      exact (div_le_div₀ (SciNat.toReal_nonneg _) hw1p_b.2 (by linarith : 0 < w0Lo.toReal) hw0_b.1).trans
        (divUbSig_le w1pHi w0Lo 12)
    have hrat := (ratLogBounds_sound consts hokL).2
    have hr_eq : (rUb.m : ℝ) / ((10 ^ rUb.e : ℕ) : ℝ) = rUb.toReal := by simp [SciNat.toReal]
    rw [hr_eq] at hrat; rw [hrLog_eq]
    exact (Real.log_le_log (div_pos hlogw1p_pos hlogw0_pos) hratio).trans hrat
  have h2_ge_sn : (sn 2 0).toReal ≤ w0Lb.toReal := SciProofs.ble_sound hw02
  have h2_ge : (2 : ℝ) ≤ w0Lb.toReal := by
    rwa [show (sn 2 0).toReal = 2 by simp [SciNat.toReal]] at h2_ge_sn
  have hw0_ge_w0Lb : w0Lb.toReal ≤ w0 := by
    rw [hw0Lb_eq]
    have h := (expGe12_sound w0Lo).2.trans (Real.exp_le_exp.mpr hw0_b.1); rwa [Real.exp_log hw0_pos] at h
  have hw0_2_le : 2 / (w0 - 2) ≤ (divUbSig (sn 2 0) den2 12).toReal := by
    have h1_sn : (sn 1 0).toReal ≤ den2.toReal := SciProofs.ble_sound hden1
    have h1 : (1 : ℝ) ≤ den2.toReal := by
      rwa [show (sn 1 0).toReal = 1 by simp [SciNat.toReal]] at h1_sn
    have hsub : den2.toReal ≤ w0Lb.toReal - 2 := by
      rw [hden2_eq]
      have h := SciProofs.subLb_le h2_ge_sn
      rwa [show (sn 2 0).toReal = 2 by simp [SciNat.toReal]] at h
    have h2' := divUbSig_le (sn 2 0) den2 12
    rw [show (sn 2 0).toReal = 2 by simp [SciNat.toReal]] at h2'
    exact (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)).trans h2'
  have hJub : BuchstabSwitching.J_odd (xi / w0) ≤ (jOddHybridUbSci (xiLogLo.subLb w0Hi) (xiLogHi.subLb w0Lo)).toReal := by
    refine jOddHybridUbSci_sound consts ((one_le_div hw0_pos).mpr hw0_le_xi) ?_ ?_
    · rw [Real.log_div hxi_pos.ne' hw0_pos.ne']
      exact (subLb_le_max_zero hxiL.1 hw0_b.2).trans (by rw [max_eq_right (sub_nonneg.mpr (Real.log_le_log hw0_pos hw0_le_xi))])
    · rw [Real.log_div hxi_pos.ne' hw0_pos.ne']
      exact (by linarith [hxiL.2, hw0_b.1] : Real.log xi - Real.log w0 ≤ xiLogHi.toReal - w0Lo.toReal).trans (sub_le_subLb_toReal _ _)
  have hmert_le : max 0 (Real.log (Real.log w1p / Real.log w0) + External.jsMertensHiErr w1p + External.jsMertensLoErr w0) +
      2 / (w0 - 2) ≤ (((rLogUb.add (jsMertHiUbSci w1Lo)).add (jsMertLoUbSci w0Lo)).add (divUbSig (sn 2 0) den2 12)).toReal := by
    have hhi := jsMertHiUbSci_sound consts hw1p_pos hw110 hw1p_b.1
    have hlo := jsMertLoUbSci_sound (by linarith) hw0_b.1
    rw [SciProofs.add_toReal, SciProofs.add_toReal, SciProofs.add_toReal]
    have hnn : 0 ≤ rLogUb.toReal + (jsMertHiUbSci w1Lo).toReal + (jsMertLoUbSci w0Lo).toReal :=
      add_nonneg (add_nonneg (SciNat.toReal_nonneg _) (SciNat.toReal_nonneg _)) (SciNat.toReal_nonneg _)
    have hmax : max 0 (Real.log (Real.log w1p / Real.log w0) + External.jsMertensHiErr w1p + External.jsMertensLoErr w0) ≤
        rLogUb.toReal + (jsMertHiUbSci w1Lo).toReal + (jsMertLoUbSci w0Lo).toReal :=
      max_le hnn (by linarith)
    linarith
  rw [SciProofs.mul_toReal]
  exact mul_le_mul hJub hmert_le (add_nonneg (le_max_left _ _) (div_nonneg (by norm_num) (by linarith)))
    (SciNat.toReal_nonneg _)

lemma jFullTerm1_sound (consts : External.CertifiedConstants) {z_nat : ℕ} {xi : ℝ}
    (_hz3 : 3 ≤ z_nat) (hzxi : (z_nat : ℝ) < xi) {zLogLo zLogHi xiLogLo xiLogHi xiLb : SciNat}
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
  simp only [Bool.and_eq_true] at hk
  rcases hk with ⟨⟨⟨⟨hw010, hw110⟩, hw02⟩, hden1⟩, hokL⟩
  have hz_pos : (0 : ℝ) < (z_nat : ℝ) := by exact_mod_cast (by omega : 0 < z_nat)
  have hw0_b := linCombLog_sound (a := 12 - k.1) (b := k.1) (d := 12) (by norm_num) hzL hxiL
  have hw1_b := linCombLog_sound (a := 11 - k.1) (b := k.1 + 1) (d := 12) (by norm_num) hzL hxiL
  rw [Nat.cast_ofNat] at hw0_b hw1_b
  exact jFullTerm1_sound_aux consts hz_pos hzxi hxiL hxiLbPos hxiLb k hw0_b hw1_b hw010 hw110
    rfl rfl hw02 hden1 rfl rfl hokL rfl

end JFullTerm1Helpers

end

end BuchstabSwitching.SieveInst
