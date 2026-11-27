import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cFastPrimes
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstElemBounds
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEngineWiring
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Soundness of Regime `2c` Odd-Bonferroni Lower-Sieve Witness Verification (`Dyadic`)

Verifies `Lower2cWitness` with `isBrun = false` (`OddBonf`) for Regime `2c` slabs
(`10^84 ≤ c.X_lo < 10^600`) using cleared denominators and `MertensTailWitness`.
-/

namespace BuchstabSwitching.SieveInst

section

section ClearedDenomHelpers2c

/-- Division-free verification of `x * y / vFullLb ≤ ub` via `(nx.mulUb epdUb).ble (ub.mulLb vFullLb)`. -/
lemma remNorm_le_of_ble {x y : ℝ} {nx epdUb vFullLb ub : Dyadic}
    (hx0 : 0 ≤ x) (hx : x ≤ nx.toReal) (hy : y ≤ epdUb.toReal) (hv : 0 < vFullLb.toReal)
    (hble : (nx.mulUb epdUb).ble (ub.mulLb vFullLb) = true) :
    x * y / vFullLb.toReal ≤ ub.toReal := by
  have hnum : x * y ≤ (nx.mulUb epdUb).toReal :=
    ((mul_le_mul_of_nonneg_left hy hx0).trans
      (mul_le_mul_of_nonneg_right hx epdUb.toReal_nonneg)).trans (Dyadic.le_mulUb _ _)
  have hmul : (ub.mulLb vFullLb).toReal ≤ ub.toReal * vFullLb.toReal := Dyadic.mulLb_le _ _
  exact (div_le_iff₀ hv).mpr (hnum.trans ((Dyadic.ble_sound hble).trans hmul))

/-- Division-free verification of `lb ≤ 1 - errReal` via `(lb.add err).ble dyOne`. -/
lemma ratLb_of_add_ble {err lb : Dyadic} {errReal : ℝ}
    (hble : (lb.add err).ble dyOne = true) (herr : errReal ≤ err.toReal) :
    lb.toReal ≤ 1 - errReal := by
  have h := (Dyadic.ble_sound hble).trans_eq dyOne_toReal
  rw [Dyadic.add_toReal] at h
  linarith

end ClearedDenomHelpers2c

section OddBonfLower2c

/-- Computable binary witness checker for `Lower2cWitness` with `isBrun = false`. -/
def checkOddBonfLower2c (c : BuchstabSwitching.SlabCert)
    (zLogLb zLogUb epdUb vFullLb : Dyadic) (lo : Lower2cWitness) : Bool :=
  if h : lo.a < smallOddPrimes40.length then
    let pMin := smallOddPrimes40[lo.a]
    let k := 2 * lo.mOdd + 1
    let ndUb := (sumPowDivFactUb lo.piZUb k).mulPow2 lo.a
    let errDen := (Dyadic.ofNat (Nat.factorial (k + 1))).mulLb lo.gLb
    decide (k < 16) &&
    decide (pMin < c.z) &&
    decide ((smallOddPrimes40.take lo.a).prod * c.z ^ k ≤ lo.dMax) &&
    decide (lo.dMax ^ 2 ≤ c.X_lo) &&
    checkMertensTailWithLogs pMin c.z dyZero dyZero zLogLb zLogUb lo.tail &&
    lo.tail.s1Ub.ble lo.s1Ub &&
    (Dyadic.ofNat lo.tail.piUb).ble lo.piZUb &&
    ndUb.ble (Dyadic.ofNat lo.nD) &&
    decide (0 < lo.gLb.m) &&
    lo.gLb.ble lo.tail.gLb &&
    (lo.s1Ub.powUb (k + 1)).ble (lo.errUb.mulLb errDen) &&
    (lo.ratLb.add lo.errUb).ble dyOne &&
    ((Dyadic.ofNat lo.nD).mulUb epdUb).ble (lo.remANormUb.mulLb vFullLb)
  else false

lemma oddBonfLower2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLb zLogUb epdUb vFullLb : Dyadic} {lo : Lower2cWitness}
    (hzLog : 27000 < c.z → zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ zLogUb.toReal)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal)
    (h : checkOddBonfLower2c c zLogLb zLogUb epdUb vFullLb lo = true) :
    ∃ s : External.OddBonfLowerSpec c (c.X_lo : ℝ),
      lo.ratLb.toReal ≤ s.rat_lb ∧
      s.n_d * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) / vFullLb.toReal ≤
        lo.remANormUb.toReal := by
  by_cases ha_sm : lo.a < smallOddPrimes40.length
  · have ha : lo.a < oddPrimesLt27000.length := lt_of_lt_of_le ha_sm smallOddPrimes40_len_le
    unfold checkOddBonfLower2c at h
    simp only [ha_sm, ↓reduceDIte] at h
    rw [smallOddPrimes40_getElem ha_sm, smallOddPrimes40_take ha_sm.le] at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨h1_12, hrem⟩
    rcases (Bool.and_eq_true _ _).mp h1_12 with ⟨h1_11, hrat⟩
    rcases (Bool.and_eq_true _ _).mp h1_11 with ⟨h1_10, herr_ble⟩
    rcases (Bool.and_eq_true _ _).mp h1_10 with ⟨h1_9, hg_le⟩
    rcases (Bool.and_eq_true _ _).mp h1_9 with ⟨h1_8, hg_pos_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_8 with ⟨h1_7, hnd⟩
    rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, hpi⟩
    rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hs1⟩
    rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, htail⟩
    rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hd_sq_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hd_le_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hk16_b, hpz_b⟩
    have hk16 : 2 * lo.mOdd + 1 < 16 := decide_eq_true_eq.mp hk16_b
    have hpz : oddPrimesLt27000[lo.a] < c.z := decide_eq_true_eq.mp hpz_b
    have hd_le : (oddPrimesLt27000.take lo.a).prod * c.z ^ (2 * lo.mOdd + 1) ≤ lo.dMax :=
      decide_eq_true_eq.mp hd_le_b
    have hd_sq : lo.dMax ^ 2 ≤ c.X_lo := decide_eq_true_eq.mp hd_sq_b
    have hg_pos : 0 < lo.gLb.m := decide_eq_true_eq.mp hg_pos_b
    set pMin := oddPrimesLt27000[lo.a]
    have hpMin_mem := mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)
    have hpa_lt : (if lo.a = 0 then 2 else oddPrimesLt27000[lo.a - 1]'(by omega)) < pMin := by
      split_ifs with ha0
      · exact lt_of_lt_of_le (by norm_num) hpMin_mem.2.2
      · exact (List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt)
          (lo.a - 1) lo.a (by omega) ha (by omega)
    have hsplit := oddPrimesLt27000_split_props ha hpz.le hpa_lt le_rfl
    set Q₁ : Finset ℕ := (oddPrimesLt27000.take lo.a).toFinset
    set P₂ : Finset ℕ := (Finset.Ico pMin c.z).filter Nat.Prime
    have hm := checkMertensTailWithLogs_sound consts hGRH hCls hMert
      (fun h27 => absurd h27 (by linarith [hpMin_mem.1])) hzLog htail
    have hnd_real : ((BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * lo.mOdd + 1)).card : ℝ) ≤ (lo.nD : ℝ) := by
      have hcard := BuchstabSwitching.card_bonfDivisors_le_factorial_sum hsplit.1
        (fun p hp => (hsplit.2.2.2.1 p hp).1) (fun p hp => (hsplit.2.2.2.2 p hp).1) (2 * lo.mOdd + 1)
        (hm.2.2.1.trans (by simpa [Dyadic.ofNat_toReal] using Dyadic.ble_sound hpi))
      rw [hsplit.2.2.1] at hcard
      have hble := Dyadic.ble_sound hnd
      rw [Dyadic.mulPow2_toReal, Dyadic.ofNat_toReal] at hble
      have h1 := mul_le_mul_of_nonneg_right
        (sumPowDivFactUb_sound lo.piZUb hk16) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ lo.a)
      linarith
    have hd_max_le : ∀ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * lo.mOdd + 1), (d : ℝ) ≤ (lo.dMax : ℝ) := by
      intro d hd
      have hbd := BuchstabSwitching.bonfDivisors_le_prod_mul_pow_of_pos (by omega : 1 ≤ c.z)
        (fun p hp => (hsplit.2.2.2.1 p hp).1.pos)
        (fun p hp => (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le) hd
      have hqprod : ∏ p ∈ Q₁, p = (oddPrimesLt27000.take lo.a).prod := by
        simpa using List.prod_toFinset (fun x : ℕ => x) oddPrimesLt27000_nodup.take
      exact_mod_cast (hqprod ▸ hbd).trans hd_le
    have hg_pos_r : 0 < lo.gLb.toReal := Dyadic.toReal_pos_of_m hg_pos
    have hv_tail := hm.2.2.2 hpMin_mem.2.2
    have hrat_bonf := BuchstabSwitching.analytic_bonf_RTrunc_odd_lb
      (fun p hp => ⟨(hsplit.2.2.2.2 p hp).1, by have := hpMin_mem.2.2; have := (hsplit.2.2.2.2 p hp).2.2; omega⟩)
      lo.mOdd hg_pos_r ((Dyadic.ble_sound hg_le).trans hv_tail)
      (hm.1.trans (Dyadic.ble_sound hs1))
    have hk_eq : (2 * lo.mOdd + 1) + 1 = 2 * lo.mOdd + 2 := by omega
    have hden_le : ((Dyadic.ofNat (Nat.factorial (2 * lo.mOdd + 2))).mulLb lo.gLb).toReal ≤
        (Nat.factorial (2 * lo.mOdd + 2) : ℝ) * lo.gLb.toReal :=
      (Dyadic.mulLb_le _ _).trans (by rw [Dyadic.ofNat_toReal])
    have herr_le : lo.s1Ub.toReal ^ (2 * lo.mOdd + 2) /
        ((Nat.factorial (2 * lo.mOdd + 2) : ℝ) * lo.gLb.toReal) ≤ lo.errUb.toReal := by
      rw [hk_eq] at herr_ble
      exact Dyadic.div_le_of_ble_mulLb (Dyadic.powUb_sound lo.s1Ub (2 * lo.mOdd + 2))
        (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hg_pos_r) hden_le herr_ble
    exact ⟨⟨Q₁, P₂, hsplit.1, hsplit.2.1, lo.mOdd, lo.dMax, hd_max_le,
      Real.le_sqrt_of_sq_le (by exact_mod_cast hd_sq), lo.nD, lo.ratLb.toReal, hnd_real,
      (ratLb_of_add_ble hrat herr_le).trans hrat_bonf⟩, le_rfl,
      remNorm_le_of_ble (Nat.cast_nonneg _) (by rw [Dyadic.ofNat_toReal]) hepd hv_pos hrem⟩
  · unfold checkOddBonfLower2c at h; simp only [ha_sm, ↓reduceDIte] at h; simp at h

end OddBonfLower2c

section SliceChainAndCommonHelpers2c

def bptsOfSlices2c (z : ℕ) (slices : List Slice2cWitness) (i : Fin (slices.length + 1)) : ℕ :=
  if h0 : i.1 = 0 then z else (slices[i.1 - 1]'(by omega)).q1

def checkSliceChain2c (cur y : ℕ) : List Slice2cWitness → Bool
  | [] => decide (cur = y)
  | sl :: rest => decide (sl.q0 = cur) && decide (sl.q0 ≤ sl.q1) && checkSliceChain2c sl.q1 y rest

lemma bptsOfSlices2c_zero (z : ℕ) (slices : List Slice2cWitness) :
    bptsOfSlices2c z slices 0 = z := by simp [bptsOfSlices2c]

private lemma bptsOfSlices2c_cons_succ (z : ℕ) (sl : Slice2cWitness)
    (rest : List Slice2cWitness) (i : Fin (rest.length + 1)) :
    bptsOfSlices2c z (sl :: rest) i.succ = bptsOfSlices2c sl.q1 rest i := by
  rcases i with ⟨n, _⟩; cases n <;> simp [bptsOfSlices2c]

lemma checkSliceChain2c_last : ∀ (slices : List Slice2cWitness) (cur y : ℕ),
    checkSliceChain2c cur y slices = true →
    bptsOfSlices2c cur slices ⟨slices.length, Nat.lt_succ_self _⟩ = y
  | [], cur, y, h => by simp only [checkSliceChain2c, decide_eq_true_eq] at h; simpa [bptsOfSlices2c] using h
  | sl :: rest, cur, y, h => by
    simp only [checkSliceChain2c, Bool.and_eq_true, decide_eq_true_eq] at h
    have hsucc : (⟨(sl :: rest).length, Nat.lt_succ_self _⟩ : Fin ((sl :: rest).length + 1)) =
        (⟨rest.length, Nat.lt_succ_self _⟩ : Fin (rest.length + 1)).succ := by ext; simp
    rw [hsucc, bptsOfSlices2c_cons_succ]; exact checkSliceChain2c_last rest sl.q1 y h.2

lemma checkSliceChain2c_castSucc : ∀ (slices : List Slice2cWitness) (cur y : ℕ),
    checkSliceChain2c cur y slices = true →
    ∀ i : Fin slices.length, bptsOfSlices2c cur slices i.castSucc = slices[i].q0
  | [], _, _, _, i => i.elim0
  | sl :: _, cur, _, h, ⟨0, _⟩ => by
    simp only [checkSliceChain2c, Bool.and_eq_true, decide_eq_true_eq] at h; simp [bptsOfSlices2c, h.1.1]
  | sl :: rest, _, y, h, ⟨j + 1, hj⟩ => by
    simp only [checkSliceChain2c, Bool.and_eq_true, decide_eq_true_eq] at h
    have heq : (⟨j + 1, hj⟩ : Fin (sl :: rest).length).castSucc =
        (⟨j, Nat.succ_lt_succ_iff.mp hj⟩ : Fin rest.length).castSucc.succ := by ext; simp
    rw [heq, bptsOfSlices2c_cons_succ]
    exact checkSliceChain2c_castSucc rest sl.q1 y h.2 ⟨j, Nat.succ_lt_succ_iff.mp hj⟩

lemma bptsOfSlices2c_succ (z : ℕ) (slices : List Slice2cWitness) (i : Fin slices.length) :
    bptsOfSlices2c z slices i.succ = slices[i].q1 := by simp [bptsOfSlices2c]

private lemma checkSliceChain2c_le : ∀ (slices : List Slice2cWitness) (cur y : ℕ),
    checkSliceChain2c cur y slices = true → cur ≤ y
  | [], cur, y, h => by simp only [checkSliceChain2c, decide_eq_true_eq] at h; omega
  | sl :: rest, cur, y, h => by
    simp only [checkSliceChain2c, Bool.and_eq_true, decide_eq_true_eq] at h
    have := checkSliceChain2c_le rest sl.q1 y h.2; omega

lemma checkSliceChain2c_bounds : ∀ (slices : List Slice2cWitness) (cur y : ℕ),
    checkSliceChain2c cur y slices = true →
    ∀ i : Fin slices.length, cur ≤ slices[i].q0 ∧ slices[i].q0 ≤ slices[i].q1 ∧ slices[i].q1 ≤ y
  | [], _, _, _, i => i.elim0
  | sl :: rest, cur, y, h, ⟨0, _⟩ => by
    simp only [checkSliceChain2c, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.ge, h.1.2, checkSliceChain2c_le rest sl.q1 y h.2⟩
  | sl :: rest, _, y, h, ⟨j + 1, hj⟩ => by
    simp only [checkSliceChain2c, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := checkSliceChain2c_bounds rest sl.q1 y h.2 ⟨j, Nat.succ_lt_succ_iff.mp hj⟩
    simp only [Fin.getElem_fin, List.getElem_cons_succ] at hrec ⊢
    exact ⟨by omega, hrec.2.1, hrec.2.2⟩

def sumDyadicList2c (f : Slice2cWitness → Dyadic) (slices : List Slice2cWitness) : Dyadic :=
  slices.foldl (fun s sl => s.add (f sl)) dyZero

private lemma sum_fin_le_sumDyadicList2cAux (f : Slice2cWitness → Dyadic) :
    ∀ (slices : List Slice2cWitness) (acc : Dyadic) (g : Fin slices.length → ℝ),
      (∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) →
      acc.toReal + ∑ i : Fin slices.length, g i ≤ (slices.foldl (fun s sl => s.add (f sl)) acc).toReal
  | [], _, _, _ => by simp
  | sl :: rest, acc, g, hg => by
    have hrec := sum_fin_le_sumDyadicList2cAux f rest (acc.add (f sl)) (fun i => g i.succ) (fun i => hg i.succ)
    have hsum : ∑ i : Fin (sl :: rest).length, g i = g 0 + ∑ i : Fin rest.length, g i.succ := Fin.sum_univ_succ g
    rw [hsum]
    have h0 : g 0 ≤ (f sl).toReal := hg 0
    have hacc := Dyadic.add_toReal acc (f sl)
    simp only [List.foldl_cons] at hrec ⊢; linarith

lemma sum_fin_le_sumDyadicList2c (f : Slice2cWitness → Dyadic) (slices : List Slice2cWitness)
    (g : Fin slices.length → ℝ) (hg : ∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) :
    ∑ i : Fin slices.length, g i ≤ (sumDyadicList2c f slices).toReal := by
  simpa [sumDyadicList2c, dyZero_toReal] using sum_fin_le_sumDyadicList2cAux f slices dyZero g hg

lemma sum_bonfDivisors_gTot_eq {Q₁ P₂ : Finset ℕ}
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime ∧ 2 < p) (hP₂ : ∀ p ∈ P₂, p.Prime ∧ 2 < p)
    (k : ℕ) :
    ∑ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ k, BuchstabSwitching.gTot d =
      (∏ p ∈ Q₁, (p : ℝ) / ((p : ℝ) - 1)) *
        ∑ j ∈ Finset.range (k + 1), BuchstabSwitching.elemSym BuchstabSwitching.gTot P₂ j := by
  rw [BuchstabSwitching.sum_bonfDivisors_density Q₁ P₂ BuchstabSwitching.gTot k hdisj
    (fun p hp => (hQ₁ p hp).1) (fun p hp => (hP₂ p hp).1)
    (fun S₁ hS₁ Q₂ hQ₂ => BuchstabSwitching.gTot_prod_disjoint_primes (hdisj.mono hS₁ hQ₂)
      (fun p hp => (hQ₁ p (hS₁ hp)).1) (fun p hp => (hP₂ p (hQ₂ hp)).1))]
  congr 1; refine Finset.prod_congr rfl fun p hp => ?_
  rw [BuchstabSwitching.gTot_prime (hQ₁ p hp).1]
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hQ₁ p hp).2
  field_simp [(by linarith : (p : ℝ) - 1 ≠ 0)]; ring

lemma q_mul_dMax_sqrt {c : BuchstabSwitching.SlabCert} {q0 q1 dMax : ℕ}
    (h : ((q1 - 1) * dMax) ^ 2 ≤ c.X_lo) :
    ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
      (q : ℝ) * (dMax : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
  intro q hq
  have hq_lt : q < q1 := lt_of_lt_of_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2 (min_le_right _ _)
  rw [← Nat.cast_mul, Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.pow_le_pow_left (Nat.mul_le_mul_right dMax (by omega)) 2).trans h

end SliceChainAndCommonHelpers2c

end

end BuchstabSwitching.SieveInst
