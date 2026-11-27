import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2abLower
import BuchstabSwitching.Certificates.Soundness
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Soundness of `checkSlab2abWitness` for Regimes `2a` & `2b` (`61` Slabs, Binary `Dyadic`)

Implements:
- `checkSlice2abWitness` & `checkSlice2abWitness_sound` (`kind = 0` trivial, `kind = 1`
  exact `elemSymInterval64` even-Bonferroni, `kind = 2` analytic even-Bonferroni);
- `checkSliceChain` & breakpoint extraction `bptsOfSlices`;
- `checkSquare2abWitness` & `checkSquare2abWitness_sound` (`SquareEngine2ab`);
- `checkSlab2abWitness` & `checkSlab2abWitness_sound` producing `Regime2abSlabBridge c`.
-/

namespace BuchstabSwitching.SieveInst

section

section SliceChainAndSums

def bptsOfSlices (z : ℕ) (slices : List Slice2abWitness) (i : Fin (slices.length + 1)) : ℕ :=
  if h0 : i.1 = 0 then z else (slices[i.1 - 1]'(by omega)).q1

def checkSliceChain (cur y : ℕ) : List Slice2abWitness → Bool
  | [] => decide (cur = y)
  | sl :: rest =>
      decide (sl.q0 = cur) && decide (sl.q0 ≤ sl.q1) && checkSliceChain sl.q1 y rest

lemma bptsOfSlices_zero (z : ℕ) (slices : List Slice2abWitness) :
    bptsOfSlices z slices 0 = z := by simp [bptsOfSlices]

private lemma bptsOfSlices_cons_succ (z : ℕ) (sl : Slice2abWitness)
    (rest : List Slice2abWitness) (i : Fin (rest.length + 1)) :
    bptsOfSlices z (sl :: rest) i.succ = bptsOfSlices sl.q1 rest i := by
  rcases i with ⟨n, _⟩; cases n <;> simp [bptsOfSlices]

lemma checkSliceChain_last : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true →
    bptsOfSlices cur slices ⟨slices.length, Nat.lt_succ_self _⟩ = y
  | [], cur, y, h => by simp only [checkSliceChain, decide_eq_true_eq] at h; simpa [bptsOfSlices] using h
  | sl :: rest, cur, y, h => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have hsucc : (⟨(sl :: rest).length, Nat.lt_succ_self _⟩ : Fin ((sl :: rest).length + 1)) =
        (⟨rest.length, Nat.lt_succ_self _⟩ : Fin (rest.length + 1)).succ := by ext; simp
    rw [hsucc, bptsOfSlices_cons_succ]; exact checkSliceChain_last rest sl.q1 y h.2

lemma checkSliceChain_castSucc : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true →
    ∀ i : Fin slices.length, bptsOfSlices cur slices i.castSucc = slices[i].q0
  | [], _, _, _, i => i.elim0
  | sl :: _, cur, _, h, ⟨0, _⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h; simp [bptsOfSlices, h.1.1]
  | sl :: rest, _, y, h, ⟨j + 1, hj⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have heq : (⟨j + 1, hj⟩ : Fin (sl :: rest).length).castSucc =
        (⟨j, Nat.succ_lt_succ_iff.mp hj⟩ : Fin rest.length).castSucc.succ := by ext; simp
    rw [heq, bptsOfSlices_cons_succ]
    exact checkSliceChain_castSucc rest sl.q1 y h.2 ⟨j, Nat.succ_lt_succ_iff.mp hj⟩

lemma bptsOfSlices_succ (z : ℕ) (slices : List Slice2abWitness) (i : Fin slices.length) :
    bptsOfSlices z slices i.succ = slices[i].q1 := by simp [bptsOfSlices]

private lemma checkSliceChain_le_y : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true → cur ≤ y
  | [], cur, y, h => by simp only [checkSliceChain, decide_eq_true_eq] at h; omega
  | sl :: rest, cur, y, h => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have := checkSliceChain_le_y rest sl.q1 y h.2; omega

lemma checkSliceChain_bounds : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true →
    ∀ i : Fin slices.length, cur ≤ slices[i].q0 ∧ slices[i].q0 ≤ slices[i].q1 ∧ slices[i].q1 ≤ y
  | [], _, _, _, i => i.elim0
  | sl :: rest, cur, y, h, ⟨0, _⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.ge, h.1.2, checkSliceChain_le_y rest sl.q1 y h.2⟩
  | sl :: rest, cur, y, h, ⟨j + 1, hj⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := checkSliceChain_bounds rest sl.q1 y h.2 ⟨j, Nat.succ_lt_succ_iff.mp hj⟩
    simp only [Fin.getElem_fin, List.getElem_cons_succ] at hrec ⊢
    exact ⟨le_trans (by omega) hrec.1, hrec.2.1, hrec.2.2⟩

def sumDyadicListAux (acc : Dyadic) (f : Slice2abWitness → Dyadic)
    (slices : List Slice2abWitness) : Dyadic :=
  slices.foldl (fun s sl => s.add (f sl)) acc

def sumDyadicList (f : Slice2abWitness → Dyadic) (slices : List Slice2abWitness) : Dyadic :=
  sumDyadicListAux dyZero f slices

lemma sum_fin_le_sumDyadicListAux (f : Slice2abWitness → Dyadic) :
    ∀ (slices : List Slice2abWitness) (acc : Dyadic) (g : Fin slices.length → ℝ),
      (∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) →
      acc.toReal + ∑ i : Fin slices.length, g i ≤ (sumDyadicListAux acc f slices).toReal
  | [], acc, _, _ => by simp [sumDyadicListAux]
  | sl :: rest, acc, g, hg => by
    have hrec := sum_fin_le_sumDyadicListAux f rest (acc.add (f sl)) (fun i => g i.succ) (fun i => hg i.succ)
    have hsum : ∑ i : Fin (sl :: rest).length, g i = g 0 + ∑ i : Fin rest.length, g i.succ :=
      Fin.sum_univ_succ g
    rw [hsum]
    have h0 : g 0 ≤ (f sl).toReal := hg 0
    have hacc := Dyadic.add_toReal acc (f sl)
    simp only [sumDyadicListAux, List.foldl_cons] at hrec ⊢
    linarith

lemma sum_fin_le_sumDyadicList (f : Slice2abWitness → Dyadic) (slices : List Slice2abWitness)
    (g : Fin slices.length → ℝ) (hg : ∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) :
    ∑ i : Fin slices.length, g i ≤ (sumDyadicList f slices).toReal := by
  simpa [sumDyadicList, dyZero_toReal] using sum_fin_le_sumDyadicListAux f slices dyZero g hg

end SliceChainAndSums

section SliceChecker

def checkEvenBonfCommon (c : BuchstabSwitching.SlabCert) (sl : Slice2abWitness) : Bool :=
  let ps := oddPrimesList sl.zSub
  let q1 := ps.take sl.aQ
  let p2 := ps.drop sl.aQ
  let k := 2 * sl.mEv
  decide (sl.zSub ≤ c.z) && decide (sl.zSub ≤ pExact) && decide (sl.aQ ≤ ps.length) &&
  decide (q1.prod * (p2.reverse.take k).prod ≤ sl.dMax) &&
  decide (((sl.q1 - 1) * sl.dMax) ^ 2 ≤ c.X_lo) &&
  decide (bonfCardNat sl.aQ p2.length k ≤ sl.nD) &&
  (exactProdOneSubInvPredUb 3 sl.zSub).ble sl.vSubUb

def checkSliceRatExact (p2e : List PrimeLeafEntry) (mEv : ℕ) (ratUb : Dyadic) : Bool :=
  match p2e with
  | [] => dyOne.ble ratUb
  | _ :: _ =>
    let sums := elemSymSums (elemSymInterval64 p2e (2 * mEv))
    let gP2Lb := v2EntriesLb p2e
    decide (0 < gP2Lb.m) && sums.2.1.ble (sums.2.2.1.add (ratUb.mulLb gP2Lb))

lemma checkSliceRatExact_sound {p2e : List PrimeLeafEntry}
    (hP2_lt : (p2e.map PrimeLeafEntry.p).Pairwise (· < ·))
    (hP2_ok : ∀ e ∈ p2e, checkPrimeLeafEntry e = true ∧ e.p.Prime)
    {mEv : ℕ} {ratUb : Dyadic}
    (h : checkSliceRatExact p2e mEv ratUb = true) :
    BuchstabSwitching.RTrunc BuchstabSwitching.gTot (p2e.map PrimeLeafEntry.p).toFinset (2 * mEv) ≤ ratUb.toReal := by
  unfold checkSliceRatExact at h; dsimp only at h
  have hP2_nd := pairwise_lt_nodup hP2_lt
  cases p2e with
  | nil =>
    rw [List.map_nil, List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
    exact dyOne_toReal ▸ Dyadic.ble_sound h
  | cons e0 tl =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hble := Dyadic.ble_sound h.2
    rw [Dyadic.add_toReal] at hble
    have hsum := elemSymSums_interval64_sound hP2_nd hP2_ok (2 * mEv)
    have hgLb := v2EntriesLb_sound hP2_nd hP2_ok
    have hgLb_pos : 0 < (v2EntriesLb (e0 :: tl)).toReal := Dyadic.toReal_pos_of_m h.1
    have hV2_pos : 0 < BuchstabSwitching.V2 BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset :=
      lt_of_lt_of_le hgLb_pos hgLb
    have hmul_le : BuchstabSwitching.gTrunc BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset (2 * mEv) ≤
        ratUb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset := by
      have h1 : (ratUb.mulLb (v2EntriesLb (e0 :: tl))).toReal ≤
          ratUb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset :=
        (Dyadic.mulLb_le _ _).trans (mul_le_mul_of_nonneg_left hgLb ratUb.toReal_nonneg)
      linarith [hsum.2.1]
    rw [BuchstabSwitching.RTrunc]
    exact (div_le_iff₀ hV2_pos).mpr hmul_le

def checkSliceRatAnalytic (p2e : List PrimeLeafEntry) (mEv : ℕ)
    (c2Ub gSubLb errUb ratUb : Dyadic) : Bool :=
  let k := 2 * mEv
  let s1Ub := sumG1EntriesUb p2e
  let errDen := (Dyadic.ofNat (Nat.factorial (k + 1))).mulLb gSubLb
  checkAnalyticV2Lb p2e c2Ub gSubLb &&
    match p2e with
    | [] => dyOne.ble ratUb
    | _ :: _ =>
      (s1Ub.powUb (k + 1)).ble (errUb.mulLb errDen) &&
      (dyOne.add errUb).ble ratUb

lemma checkSliceRatAnalytic_sound {p2e : List PrimeLeafEntry}
    (hP2_lt : (p2e.map PrimeLeafEntry.p).Pairwise (· < ·))
    (hP2_ok : ∀ e ∈ p2e, checkPrimeLeafEntry e = true ∧ e.p.Prime)
    {mEv : ℕ} {c2Ub gSubLb errUb ratUb : Dyadic}
    (h : checkSliceRatAnalytic p2e mEv c2Ub gSubLb errUb ratUb = true) :
    BuchstabSwitching.RTrunc BuchstabSwitching.gTot (p2e.map PrimeLeafEntry.p).toFinset (2 * mEv) ≤ ratUb.toReal := by
  unfold checkSliceRatAnalytic at h; dsimp only at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨hv2_chk, hm_chk⟩
  have hg := checkAnalyticV2Lb_sound hP2_lt hP2_ok hv2_chk
  have hP2_nd := pairwise_lt_nodup hP2_lt
  have hP2_fin_pr : ∀ p ∈ (p2e.map PrimeLeafEntry.p).toFinset, p.Prime ∧ 2 < p := fun p hp => by
    rcases List.mem_map.mp (List.mem_toFinset.mp hp) with ⟨e, he, rfl⟩
    have hp3 := (checkPrimeLeafEntry_props (hP2_ok e he).1).1
    exact ⟨(hP2_ok e he).2, by omega⟩
  cases p2e with
  | nil =>
    rw [List.map_nil, List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
    exact dyOne_toReal ▸ Dyadic.ble_sound hm_chk
  | cons e0 tl =>
    rcases (Bool.and_eq_true _ _).mp hm_chk with ⟨herr_ble, hadd_ble⟩
    have hS1 := sumG1EntriesUb_sound hP2_nd hP2_ok
    have hR := BuchstabSwitching.analytic_bonf_RTrunc_even_ub hP2_fin_pr mEv hg.1 hg.2 hS1
    set s1Ub := sumG1EntriesUb (e0 :: tl)
    have hden_le : ((Dyadic.ofNat (Nat.factorial (2 * mEv + 1))).mulLb gSubLb).toReal ≤
        (Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal :=
      (Dyadic.mulLb_le _ _).trans (by rw [Dyadic.ofNat_toReal])
    have herr_le : s1Ub.toReal ^ (2 * mEv + 1) /
        ((Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal) ≤ errUb.toReal :=
      Dyadic.div_le_of_ble_mulLb (Dyadic.powUb_sound s1Ub (2 * mEv + 1))
        (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hg.1) hden_le herr_ble
    have hble := Dyadic.ble_sound hadd_ble
    rw [Dyadic.add_toReal, dyOne_toReal] at hble
    linarith

def checkSlice2abWitness (c : BuchstabSwitching.SlabCert) (epdUb : Dyadic)
    (sl : Slice2abWitness) : Bool :=
  let hLogs :=
    (if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.wQ0Log sl.logQ0Lb sl.logQ0Ub else true) &&
    (if pExact < sl.q1 then checkLogNat sl.q1 sl.wQ1Log sl.logQ1Lb sl.logQ1Ub else true)
  let hSliceBase :=
    hLogs &&
    checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb sl.anW
  if !hSliceBase then false
  else if sl.kind == 0 then
    decide ((sl.q1 - 1) ^ 2 ≤ c.X_lo) &&
    sl.sqUb.ble sl.mSl &&
    (sl.cntUb.mulUb epdUb).ble sl.eSl
  else if sl.kind == 1 then
    let es := oddPrimeEntriesList sl.zSub
    let q1e := es.take sl.aQ
    let p2e := es.drop sl.aQ
    let k := 2 * sl.mEv
    let sums := elemSymSums (elemSymInterval64 p2e k)
    let ip2Ub := (invPhiEntriesUb q1e).mulUb (sums.2.1.add sums.2.2.2)
    checkEvenBonfCommon c sl &&
    ip2Ub.ble sl.ip2 &&
    checkSliceRatExact p2e sl.mEv sl.ratUb &&
    ((sl.sqUb.mulUb sl.vSubUb).mulUb sl.ratUb).ble sl.mSl &&
    ((sl.cntUb.mulUb ((Dyadic.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mulUb epdUb).ble sl.eSl
  else if sl.kind == 2 then
    let es := oddPrimeEntriesList sl.zSub
    let q1e := es.take sl.aQ
    let p2e := es.drop sl.aQ
    let s1Ub := sumG1EntriesUb p2e
    let expRes := expUbDyadic s1Ub
    checkEvenBonfCommon c sl &&
    checkSliceRatAnalytic p2e sl.mEv sl.c2Ub sl.gSubLb sl.errUb sl.ratUb &&
    expRes.1 &&
    ((invPhiEntriesUb q1e).mulUb expRes.2).ble sl.ip2 &&
    ((sl.sqUb.mulUb sl.vSubUb).mulUb sl.ratUb).ble sl.mSl &&
    ((sl.cntUb.mulUb ((Dyadic.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mulUb epdUb).ble sl.eSl
  else false

private lemma evenBonfCommon_sound (c : BuchstabSwitching.SlabCert) (sl : Slice2abWitness)
    (_hq1_y : sl.q1 ≤ c.y) (hcom : checkEvenBonfCommon c sl = true) :
    let ps := oddPrimesList sl.zSub
    let q1 := ps.take sl.aQ
    let p2 := ps.drop sl.aQ
    let k := 2 * sl.mEv
    sl.zSub ≤ c.z ∧
    Disjoint q1.toFinset p2.toFinset ∧
    q1.toFinset ∪ p2.toFinset = BuchstabSwitching.fullOddPrimesBelow sl.zSub ∧
    (∀ d ∈ BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k, (d : ℝ) ≤ (sl.dMax : ℝ)) ∧
    (∀ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (q : ℝ) * (sl.dMax : ℝ) ≤ Real.sqrt (c.X_lo : ℝ)) ∧
    ((BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k).card : ℝ) ≤ (sl.nD : ℝ) ∧
    BuchstabSwitching.External.VN 2 sl.zSub ≤ sl.vSubUb.toReal := by
  unfold checkEvenBonfCommon at hcom
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hcom
  rcases hcom with ⟨hz_c, hz_ex, ha_le, hd_prod, hqd_sq, hnd_nat, hv_ub⟩
  set ps := oddPrimesList sl.zSub
  set k := 2 * sl.mEv
  have hps_lt := oddPrimesList_pairwise_lt sl.zSub
  have hps_pr := oddPrimesList_props sl.zSub
  refine ⟨hz_c, take_drop_disjoint hps_lt sl.aQ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [take_drop_union, oddPrimesList_toFinset hz_ex]
  · intro d hd
    exact_mod_cast (bonfDivisors_le_take_mul_rev_drop hps_lt
      (fun p hp => (hps_pr p hp).1.one_lt.le) sl.aQ k d hd).trans hd_prod
  · intro q hq
    have hq_lt : q < sl.q1 := lt_of_lt_of_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2 (min_le_right _ _)
    have hmul : (q * sl.dMax) ^ 2 ≤ c.X_lo :=
      (Nat.pow_le_pow_left (Nat.mul_le_mul_right sl.dMax (by omega)) 2).trans hqd_sq
    rw [← Nat.cast_mul, Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast hmul
  · rw [bonfCardNat_eq] at hnd_nat
    exact_mod_cast (card_bonfDivisors_take_drop hps_lt
      (fun p hp => (hps_pr p hp).1) ha_le k).trans_le hnd_nat
  · exact (VN_two_le_exactProdOneSubInvPredUb hz_ex).trans (Dyadic.ble_sound hv_ub)

private lemma evenBonfSliceEngine {c : BuchstabSwitching.SlabCert} {epdUb : Dyadic}
    {sl : Slice2abWitness} {li2 : ℝ} {Q₁ P₂ : Finset ℕ}
    (hz_c : sl.zSub ≤ c.z) (hdisj : Disjoint Q₁ P₂)
    (hunion : Q₁ ∪ P₂ = BuchstabSwitching.fullOddPrimesBelow sl.zSub)
    (hd_le : ∀ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * sl.mEv), (d : ℝ) ≤ (sl.dMax : ℝ))
    (hqd_sqrt : ∀ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (q : ℝ) * (sl.dMax : ℝ) ≤ Real.sqrt (c.X_lo : ℝ))
    (hnd : ((BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * sl.mEv)).card : ℝ) ≤ (sl.nD : ℝ))
    (hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * sl.mEv), BuchstabSwitching.gTot d ≤ sl.ip2.toReal)
    (hrat : BuchstabSwitching.RTrunc BuchstabSwitching.gTot P₂ (2 * sl.mEv) ≤ sl.ratUb.toReal)
    (hsq : ∑ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤ sl.sqUb.toReal)
    (hcnt : (((Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime).card : ℝ) ≤ sl.cntUb.toReal)
    (hv_sub : BuchstabSwitching.External.VN 2 sl.zSub ≤ sl.vSubUb.toReal)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hm_chk : ((sl.sqUb.mulUb sl.vSubUb).mulUb sl.ratUb).ble sl.mSl = true)
    (he_chk : ((sl.cntUb.mulUb ((Dyadic.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mulUb epdUb).ble sl.eSl = true) :
    ∃ s_eng : BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ) sl.q0 sl.q1,
      s_eng.mSl ≤ sl.mSl.toReal ∧ s_eng.eSl li2 ≤ sl.eSl.toReal := by
  refine ⟨.evenBonf
    { z_sub := sl.zSub, m_ev := sl.mEv, hz_sub := hz_c, Q₁ := Q₁, P₂ := P₂, hdisj := hdisj,
      hunion := hunion, d_max := (sl.dMax : ℝ), hd_le := hd_le, hqd_sqrt := hqd_sqrt,
      n_d := (sl.nD : ℝ), ip2 := sl.ip2.toReal, rat_ub := sl.ratUb.toReal,
      sq_ub := sl.sqUb.toReal, cnt_ub := sl.cntUb.toReal,
      hnd := hnd, hip2 := hip2, hrat := hrat, hsq := hsq, hcnt := hcnt }, ?_, ?_⟩
  · dsimp only [BuchstabSwitching.External.SliceEngine2ab.mSl]
    have h1 : sl.sqUb.toReal * BuchstabSwitching.External.VN 2 sl.zSub ≤ (sl.sqUb.mulUb sl.vSubUb).toReal :=
      (mul_le_mul_of_nonneg_left hv_sub sl.sqUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
    have h2 : (sl.sqUb.toReal * BuchstabSwitching.External.VN 2 sl.zSub) * sl.ratUb.toReal ≤
        ((sl.sqUb.mulUb sl.vSubUb).mulUb sl.ratUb).toReal :=
      (mul_le_mul_of_nonneg_right h1 sl.ratUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
    rw [← mul_assoc]
    exact h2.trans (Dyadic.ble_sound hm_chk)
  · dsimp only [BuchstabSwitching.External.SliceEngine2ab.eSl]
    set sumTerm := (Dyadic.ofNat sl.nD).add (sl.ip2.add sl.ratUb)
    have hsum_eq : sumTerm.toReal = (sl.nD : ℝ) + sl.ip2.toReal + sl.ratUb.toReal := by
      dsimp [sumTerm]; rw [Dyadic.add_toReal, Dyadic.add_toReal, Dyadic.ofNat_toReal, add_assoc]
    have h1 : sl.cntUb.toReal * ((sl.nD : ℝ) + sl.ip2.toReal + sl.ratUb.toReal) ≤
        (sl.cntUb.mulUb sumTerm).toReal := by
      rw [← hsum_eq]; exact Dyadic.le_mulUb _ _
    have hcoeff_nn : 0 ≤ sl.cntUb.toReal * ((sl.nD : ℝ) + sl.ip2.toReal + sl.ratUb.toReal) :=
      mul_nonneg sl.cntUb.toReal_nonneg
        (add_nonneg (add_nonneg (Nat.cast_nonneg _) sl.ip2.toReal_nonneg) sl.ratUb.toReal_nonneg)
    exact (mul_le_mul_of_nonneg_left hepd hcoeff_nn).trans
      ((mul_le_mul_of_nonneg_right h1 epdUb.toReal_nonneg).trans
        ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound he_chk)))

theorem checkSlice2abWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {epdUb : Dyadic} {sl : Slice2abWitness}
    (hz_q0 : c.z ≤ sl.q0) (hq1_y : sl.q1 ≤ c.y)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (h : checkSlice2abWitness c epdUb sl = true) :
    ∃ s_eng : BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ) sl.q0 sl.q1,
      s_eng.mSl ≤ sl.mSl.toReal ∧ s_eng.eSl consts.li2 ≤ sl.eSl.toReal := by
  unfold checkSlice2abWitness at h; dsimp only at h
  cases hbase : ((if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.wQ0Log sl.logQ0Lb sl.logQ0Ub else true) &&
      (if pExact < sl.q1 then checkLogNat sl.q1 sl.wQ1Log sl.logQ1Lb sl.logQ1Ub else true)) &&
      checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb sl.anW with
  | false => rw [hbase] at h; simp at h
  | true =>
  rw [hbase] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  rcases (Bool.and_eq_true _ _).mp hbase with ⟨hlogs, hsc_chk⟩
  rcases (Bool.and_eq_true _ _).mp hlogs with ⟨hl0, hl1⟩
  have hLog0 : 27000 ≤ sl.q0 →
      sl.logQ0Lb.toReal ≤ Real.log (sl.q0 : ℝ) ∧ Real.log (sl.q0 : ℝ) ≤ sl.logQ0Ub.toReal := fun hq0 =>
    checkLogNat_sound consts (by have hq0' : pExact ≤ sl.q0 := hq0; simpa [hq0'] using hl0)
  have hLog1 : 27000 < sl.q1 →
      sl.logQ1Lb.toReal ≤ Real.log (sl.q1 : ℝ) ∧ Real.log (sl.q1 : ℝ) ≤ sl.logQ1Ub.toReal := fun hq1 =>
    checkLogNat_sound consts (by have hq1' : pExact < sl.q1 := hq1; simpa [hq1'] using hl1)
  have hsc := checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hLog0 hLog1 hsc_chk
  have hico_eq : Finset.Ico (max c.z sl.q0) (min c.y sl.q1) = Finset.Ico sl.q0 sl.q1 := by
    rw [max_eq_right hz_q0, min_eq_right hq1_y]
  have hsq : ∑ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sl.sqUb.toReal := by rw [hico_eq]; exact hsc.1
  have hcnt : (((Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime).card : ℝ) ≤
      sl.cntUb.toReal := by rw [hico_eq]; exact hsc.2
  cases hk0 : (sl.kind == 0) with
  | true =>
    rw [hk0] at h; simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
    rcases h with ⟨hq_sq_c, hm_chk, he_chk⟩
    have hq_sqrt : ∀ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
        (q : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := fun q hq => by
      have hq_lt : q < sl.q1 := lt_of_lt_of_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2 (min_le_right _ _)
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast (Nat.pow_le_pow_left (by omega : q ≤ sl.q1 - 1) 2).trans hq_sq_c
    refine ⟨.trivial ⟨hq_sqrt, sl.sqUb.toReal, sl.cntUb.toReal, hsq, hcnt⟩, Dyadic.ble_sound hm_chk, ?_⟩
    exact (mul_le_mul_of_nonneg_left hepd sl.cntUb.toReal_nonneg).trans
      ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound he_chk))
  | false =>
  rw [hk0] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
  set es := oddPrimeEntriesList sl.zSub; set q1e := es.take sl.aQ; set p2e := es.drop sl.aQ
  set ps := oddPrimesList sl.zSub; set q1 := ps.take sl.aQ; set p2 := ps.drop sl.aQ; set k := 2 * sl.mEv
  have hq1_map : q1e.map PrimeLeafEntry.p = q1 := List.map_take
  have hp2_map : p2e.map PrimeLeafEntry.p = p2 := List.map_drop
  have hps_lt := oddPrimesList_pairwise_lt sl.zSub; have hps_pr := oddPrimesList_props sl.zSub
  have htd : (q1 ++ p2).Pairwise (· < ·) := by dsimp only [q1, p2]; rw [List.take_append_drop]; exact hps_lt
  have hpair := List.pairwise_append.mp htd
  have hQ_nd : (q1e.map PrimeLeafEntry.p).Nodup := hq1_map ▸ pairwise_lt_nodup hpair.1
  have hP_lt : (p2e.map PrimeLeafEntry.p).Pairwise (· < ·) := hp2_map ▸ hpair.2.1
  have hP_nd : (p2e.map PrimeLeafEntry.p).Nodup := pairwise_lt_nodup hP_lt
  have hQ_ok : ∀ e ∈ q1e, checkPrimeLeafEntry e = true := fun e he =>
    (oddPrimeEntriesList_ok sl.zSub e (List.mem_of_mem_take he)).1
  have hP_ok : ∀ e ∈ p2e, checkPrimeLeafEntry e = true ∧ e.p.Prime := fun e he =>
    let ho := oddPrimeEntriesList_ok sl.zSub e (List.mem_of_mem_drop he); ⟨ho.1, ho.2.1⟩
  have hQ_fin_pr : ∀ p ∈ q1.toFinset, p.Prime ∧ 2 < p := fun p hp =>
    let hp' := hps_pr p (List.mem_of_mem_take (List.mem_toFinset.mp hp)); ⟨hp'.1, hp'.2.1⟩
  have hP_fin_pr : ∀ p ∈ p2.toFinset, p.Prime ∧ 2 < p := fun p hp =>
    let hp' := hps_pr p (List.mem_of_mem_drop (List.mem_toFinset.mp hp)); ⟨hp'.1, hp'.2.1⟩
  split_ifs at h with hk1 hk2
  · simp only [Bool.and_eq_true, and_assoc] at h
    rcases h with ⟨hcom, hip2_chk, hrat_chk, hm_chk, he_chk⟩
    obtain ⟨hz_c, hdisj, hunion, hd_le, hqd_sqrt, hnd, hv_sub⟩ := evenBonfCommon_sound c sl hq1_y hcom
    have hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k,
        BuchstabSwitching.gTot d ≤ sl.ip2.toReal := by
      rw [BuchstabSwitching.sum_bonfDivisors_density q1.toFinset p2.toFinset BuchstabSwitching.gTot
        k hdisj (fun p hp => (hQ_fin_pr p hp).1) (fun p hp => (hP_fin_pr p hp).1)
        (fun S₁ hS₁ S₂ hS₂ => BuchstabSwitching.gTot_prod_disjoint_primes (hdisj.mono hS₁ hS₂)
          (fun p hp => (hQ_fin_pr p (hS₁ hp)).1) (fun p hp => (hP_fin_pr p (hS₂ hp)).1))]
      have hQ_eq : ∏ p ∈ q1.toFinset, (1 + BuchstabSwitching.gTot p) =
          ∏ p ∈ q1.toFinset, (p : ℝ) / ((p : ℝ) - 1) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpp := hQ_fin_pr p hp; rw [BuchstabSwitching.gTot_prime hpp.1]
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.2
        field_simp [(by linarith : (p : ℝ) - 1 ≠ 0)]; ring
      have hQ_ub := hq1_map ▸ invPhiEntriesUb_sound hQ_nd hQ_ok
      have hsum := hp2_map ▸ elemSymSums_interval64_sound hP_nd hP_ok k
      have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (k + 1),
          BuchstabSwitching.elemSym BuchstabSwitching.gTot p2.toFinset j :=
        Finset.sum_nonneg fun j _ =>
          BuchstabSwitching.elemSym_nonneg (fun _ _ => BuchstabSwitching.gTot_nonneg _) j
      rw [hQ_eq]
      exact (mul_le_mul hQ_ub hsum.2.2 hsum_nn (invPhiEntriesUb q1e).toReal_nonneg).trans
        ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hip2_chk))
    have hrat : BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset k ≤ sl.ratUb.toReal := by
      rw [← hp2_map]; exact checkSliceRatExact_sound hP_lt hP_ok hrat_chk
    exact evenBonfSliceEngine hz_c hdisj hunion hd_le hqd_sqrt hnd hip2 hrat hsq hcnt hv_sub
      hepd hm_chk he_chk
  · simp only [Bool.and_eq_true, and_assoc] at h
    rcases h with ⟨hcom, hrat_chk, hexp_ok, hip2_chk, hm_chk, he_chk⟩
    obtain ⟨hz_c, hdisj, hunion, hd_le, hqd_sqrt, hnd, hv_sub⟩ := evenBonfCommon_sound c sl hq1_y hcom
    have hS1 := hp2_map ▸ sumG1EntriesUb_sound hP_nd hP_ok
    have hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k,
        BuchstabSwitching.gTot d ≤ sl.ip2.toReal := by
      have hle := BuchstabSwitching.sum_bonfDivisors_gTot_le_exp hdisj hQ_fin_pr hP_fin_pr k hS1
      have hQ_ub := hq1_map ▸ invPhiEntriesUb_sound hQ_nd hQ_ok
      have hexp_ub := (expUbDyadic_sound hexp_ok).1
      exact hle.trans ((mul_le_mul hQ_ub hexp_ub (Real.exp_pos _).le
        (invPhiEntriesUb q1e).toReal_nonneg).trans
        ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hip2_chk)))
    have hrat : BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset k ≤ sl.ratUb.toReal := by
      rw [← hp2_map]; exact checkSliceRatAnalytic_sound hP_lt hP_ok hrat_chk
    exact evenBonfSliceEngine hz_c hdisj hunion hd_le hqd_sqrt hnd hip2 hrat hsq hcnt hv_sub
      hepd hm_chk he_chk

end SliceChecker

section SquareChecker

def checkSquare2abWitness (c : BuchstabSwitching.SlabCert) (w : Slab2abWitness) : Bool :=
  let sq := w.square
  let qEnd := min c.y (sq.qSq + 1)
  let sExact := exactInvMulPredSumUb c.z (min qEnd pExact)
  let sTailOk :=
    if pExact < qEnd then
      dyOne.ble (sq.invTailUb.mulLb (Dyadic.ofNat (pExact - 1))) &&
      (sExact.add sq.invTailUb).ble sq.sQ2Ub
    else sExact.ble sq.sQ2Ub
  let hEndLog := if pExact < qEnd then checkLogNat qEnd sq.wLogEnd sq.logEndLb sq.logEndUb else true
  let tailQ2Ok :=
    if c.y ≤ sq.qSq + 1 then true
    else w.xHiLogUb.ble (sq.tailQ2Ub.mulLb (Dyadic.ofNat sq.qSq))
  let tailQ2 := if c.y ≤ sq.qSq + 1 then dyZero else sq.tailQ2Ub
  let innerUb := sq.sQ2Ub.add ((sq.cntLoUb.mulUb w.epdUb).add tailQ2)
  decide (1 ≤ sq.qSq) && decide (sq.qSq ^ 4 ≤ c.X_lo) && sTailOk && hEndLog && tailQ2Ok &&
  checkSlice2abOr2cBounds c.z qEnd w.xLoLogLb w.xLoLogUb sq.logEndLb sq.logEndUb
    (Dyadic.ofNat 1000) sq.cntLoUb sq.anEndW &&
  innerUb.ble (sq.errQ2Ub.add sq.errQ2Ub)

theorem checkSquare2abWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {w : Slab2abWitness}
    (hz2 : 2 ≤ c.z) (hz_lt : c.z < pExact)
    (hlogHi : Real.log (c.X_hi : ℝ) ≤ w.xHiLogUb.toReal)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ w.epdUb.toReal)
    (h : checkSquare2abWitness c w = true) :
    ∃ q2_eng : BuchstabSwitching.External.SquareEngine2ab c (c.X_lo : ℝ),
      q2_eng.errQ2 consts.li2 (c.X_hi : ℝ) ≤ w.square.errQ2Ub.toReal := by
  unfold checkSquare2abWitness at h; dsimp only at h
  set sq := w.square; set qEnd := min c.y (sq.qSq + 1)
  rcases (Bool.and_eq_true _ _).mp h with ⟨h123456, herr_chk⟩
  rcases (Bool.and_eq_true _ _).mp h123456 with ⟨h12345, hcnt_chk⟩
  rcases (Bool.and_eq_true _ _).mp h12345 with ⟨h1234, htail_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1234 with ⟨h123, hlogEnd_chk⟩
  rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hs_chk⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨hq1_b, hq4_b⟩
  have hq1 : 1 ≤ sq.qSq := decide_eq_true_eq.mp hq1_b
  have hq4 : sq.qSq ^ 4 ≤ c.X_lo := decide_eq_true_eq.mp hq4_b
  have hq_rt : ((sq.qSq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast ((show (sq.qSq ^ 2) ^ 2 = sq.qSq ^ 4 by ring).symm ▸ hq4 : (sq.qSq ^ 2) ^ 2 ≤ c.X_lo)
  have hs_q2 : ∑ q ∈ (Finset.Ico c.z qEnd).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ sq.sQ2Ub.toReal := by
    have hsplit := BuchstabSwitching.sum_inv_mul_pred_split_le c.z qEnd pExact hz2 (by native_decide)
    have hex := sum_inv_mul_pred_le_exact (q0 := c.z) (q1 := min qEnd pExact) (min_le_right _ _)
    split_ifs at hs_chk with hlt
    · rcases (Bool.and_eq_true _ _).mp hs_chk with ⟨hinv_chk, hadd_chk⟩
      have hinv_le : 1 / ((pExact : ℝ) - 1) ≤ sq.invTailUb.toReal := by
        have hpos : (0 : ℝ) < (pExact : ℝ) - 1 := by unfold pExact; norm_num
        exact Dyadic.div_le_of_ble_mulLb (by rw [dyOne_toReal]) hpos
          (by rw [Dyadic.ofNat_toReal]; unfold pExact; norm_num) hinv_chk
      have hble := Dyadic.ble_sound hadd_chk; rw [Dyadic.add_toReal] at hble
      simp only [hlt, ↓reduceIte] at hsplit
      linarith
    · simp only [hlt, ↓reduceIte, add_zero] at hsplit
      exact hsplit.trans (hex.trans (Dyadic.ble_sound hs_chk))
  have hLog0 : 27000 ≤ c.z →
      w.xLoLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ w.xLoLogUb.toReal := by
    intro hc; exfalso; unfold pExact at hz_lt; omega
  have hLog1 : 27000 < qEnd →
      sq.logEndLb.toReal ≤ Real.log (qEnd : ℝ) ∧ Real.log (qEnd : ℝ) ≤ sq.logEndUb.toReal := by
    intro hlt; have hlt' : pExact < qEnd := hlt
    simp only [hlt', ↓reduceIte] at hlogEnd_chk
    exact checkLogNat_sound consts hlogEnd_chk
  have hcnt := (checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hLog0 hLog1 hcnt_chk).2
  let q2_eng : BuchstabSwitching.External.SquareEngine2ab c (c.X_lo : ℝ) :=
    { q_sq := sq.qSq, hq_sq1 := hq1, hq_sq_rt := hq_rt,
      s_q2 := sq.sQ2Ub.toReal, hs_q2 := hs_q2, cnt_lo := sq.cntLoUb.toReal, hcnt_lo := hcnt }
  refine ⟨q2_eng, ?_⟩
  have htail_le : (if c.y ≤ sq.qSq + 1 then (0 : ℝ) else Real.log (c.X_hi : ℝ) / (sq.qSq : ℝ)) ≤
      (if c.y ≤ sq.qSq + 1 then dyZero else sq.tailQ2Ub).toReal := by
    split_ifs with hy
    · rw [dyZero_toReal]
    · simp only [hy, ↓reduceIte] at htail_chk
      have hq_pos : (0 : ℝ) < (sq.qSq : ℝ) := by exact_mod_cast hq1
      exact Dyadic.div_le_of_ble_mulLb hlogHi hq_pos (by rw [Dyadic.ofNat_toReal]) htail_chk
  have herr_le := Dyadic.ble_sound herr_chk
  rw [Dyadic.add_toReal, Dyadic.add_toReal, Dyadic.add_toReal] at herr_le
  have hcnt_epd : sq.cntLoUb.toReal * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤
      (sq.cntLoUb.mulUb w.epdUb).toReal :=
    (mul_le_mul_of_nonneg_left hepd sq.cntLoUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
  dsimp only [BuchstabSwitching.External.SquareEngine2ab.errQ2, q2_eng]
  linarith

end SquareChecker

section Master2abChecker

private lemma sliceEngineCast {c : BuchstabSwitching.SlabCert} {X_lo : ℝ}
    {q0 q1 q0' q1' : ℕ} (h0 : q0 = q0') (h1 : q1 = q1')
    (s : BuchstabSwitching.External.SliceEngine2ab c X_lo q0 q1) :
    ∃ s' : BuchstabSwitching.External.SliceEngine2ab c X_lo q0' q1',
      s'.mSl = s.mSl ∧ ∀ li2, s'.eSl li2 = s.eSl li2 := by
  subst h0; subst h1; exact ⟨s, rfl, fun _ => rfl⟩

private def bonfKeyEq2ab (a b : Slice2abWitness) : Bool :=
  a.kind == b.kind && a.zSub == b.zSub && a.aQ == b.aQ && a.mEv == b.mEv &&
  a.nD == b.nD && a.dMax == b.dMax && a.ip2 == b.ip2 && a.vSubUb == b.vSubUb &&
  a.gSubLb == b.gSubLb && a.ratUb == b.ratUb && a.c2Ub == b.c2Ub && a.errUb == b.errUb

private def checkSlice2abFastStep (c : BuchstabSwitching.SlabCert) (epdUb : Dyadic)
    (cache : List Slice2abWitness) (sl : Slice2abWitness) : Bool :=
  if cache.any (fun ref => bonfKeyEq2ab ref sl) && (sl.kind == 1 || sl.kind == 2) then
    (if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.wQ0Log sl.logQ0Lb sl.logQ0Ub else true) &&
    (if pExact < sl.q1 then checkLogNat sl.q1 sl.wQ1Log sl.logQ1Lb sl.logQ1Ub else true) &&
    checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb sl.anW &&
    decide (((sl.q1 - 1) * sl.dMax) ^ 2 ≤ c.X_lo) &&
    ((sl.sqUb.mulUb sl.vSubUb).mulUb sl.ratUb).ble sl.mSl &&
    ((sl.cntUb.mulUb ((Dyadic.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mulUb epdUb).ble sl.eSl
  else checkSlice2abWitness c epdUb sl

private def checkSlices2abMemo (c : BuchstabSwitching.SlabCert) (epdUb : Dyadic) :
    List Slice2abWitness → List Slice2abWitness → Bool
  | _, [] => true
  | cache, sl :: rest =>
    checkSlice2abFastStep c epdUb cache sl &&
    checkSlices2abMemo c epdUb (if cache.any (fun r => bonfKeyEq2ab r sl) then cache else sl :: cache) rest

private lemma checkSlice2abFastStep_sound {c : BuchstabSwitching.SlabCert} {epdUb : Dyadic}
    {cache : List Slice2abWitness} {sl : Slice2abWitness}
    (hcache : ∀ r ∈ cache, checkSlice2abWitness c epdUb r = true)
    (h : checkSlice2abFastStep c epdUb cache sl = true) :
    checkSlice2abWitness c epdUb sl = true := by
  unfold checkSlice2abFastStep at h
  cases hhit : ((cache.any fun ref => bonfKeyEq2ab ref sl) && (sl.kind == 1 || sl.kind == 2)) with
  | false => rw [hhit] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; exact h
  | true =>
    rw [hhit] at h; simp only [↓reduceIte] at h
    rcases (Bool.and_eq_true _ _).mp hhit with ⟨hany, hkind⟩
    rcases List.any_eq_true.mp hany with ⟨r, hr_mem, hkey⟩
    have hr_ok := hcache r hr_mem
    simp only [bonfKeyEq2ab, Bool.and_eq_true, beq_iff_eq, and_assoc] at hkey
    rcases hkey with ⟨hk, hz, ha, hm, hnd, hdm, hip, hvs, hgs, hrt, hc2, her⟩
    rcases (Bool.and_eq_true _ _).mp h with ⟨h1_5, he_sl⟩; rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hm_sl⟩
    rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hqd_sl⟩; rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hbd_sl⟩
    rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hl0_sl, hl1_sl⟩
    have hbase_sl : (((if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.wQ0Log sl.logQ0Lb sl.logQ0Ub else true) &&
        (if pExact < sl.q1 then checkLogNat sl.q1 sl.wQ1Log sl.logQ1Lb sl.logQ1Ub else true)) &&
        checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb sl.anW) = true := by
      simp [hl0_sl, hl1_sl, hbd_sl]
    unfold checkSlice2abWitness checkEvenBonfCommon at hr_ok ⊢
    dsimp only at hr_ok ⊢; rw [hbase_sl]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hb_r : (((if pExact ≤ r.q0 then checkLogNat r.q0 r.wQ0Log r.logQ0Lb r.logQ0Ub else true) &&
        (if pExact < r.q1 then checkLogNat r.q1 r.wQ1Log r.logQ1Lb r.logQ1Ub else true)) &&
        checkSlice2abOr2cBounds r.q0 r.q1 r.logQ0Lb r.logQ0Ub r.logQ1Lb r.logQ1Ub r.sqUb r.cntUb r.anW) with
    | false => rw [hb_r] at hr_ok; simp at hr_ok
    | true =>
      rw [hb_r] at hr_ok; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr_ok
      simp only [← hk, ← hz, ← ha, ← hm, ← hnd, ← hdm, ← hip, ← hvs, ← hgs, ← hrt, ← hc2, ← her] at hkind hqd_sl hm_sl he_sl ⊢
      rcases (Bool.or_eq_true _ _).mp hkind with hk1 | hk2
      · have hk0 : (r.kind == 0) = false := by rw [beq_iff_eq.mp hk1]; rfl
        simp only [hk0, hk1, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hr_ok ⊢
        tauto
      · have hk0 : (r.kind == 0) = false := by rw [beq_iff_eq.mp hk2]; rfl
        have hk1f : (r.kind == 1) = false := by rw [beq_iff_eq.mp hk2]; rfl
        simp only [hk0, hk1f, hk2, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hr_ok ⊢
        tauto

private lemma checkSlices2abMemo_sound {c : BuchstabSwitching.SlabCert} {epdUb : Dyadic} :
    ∀ (slices cache : List Slice2abWitness),
      (∀ r ∈ cache, checkSlice2abWitness c epdUb r = true) →
      checkSlices2abMemo c epdUb cache slices = true →
      slices.all (checkSlice2abWitness c epdUb) = true
  | [], _, _, _ => rfl
  | sl :: rest, cache, hcache, h => by
    unfold checkSlices2abMemo at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨hstep, hrec⟩
    have hsl := checkSlice2abFastStep_sound hcache hstep
    rw [List.all_cons, hsl, Bool.true_and]
    refine checkSlices2abMemo_sound rest _ (fun x hx => ?_) hrec
    split_ifs at hx
    · exact hcache x hx
    · rcases List.mem_cons.mp hx with rfl | hx'; exacts [hsl, hcache x hx']

/-- Complete computable witness verifier for Regime `2a`/`2b` slabs (`61` slabs). -/
def checkSlab2abWitness (c : BuchstabSwitching.SlabCert) (w : Slab2abWitness) : Bool :=
  let sumMSl := sumDyadicList (·.mSl) w.slices
  let sumESl := sumDyadicList (·.eSl) w.slices
  let remAUb := (Dyadic.ofNat w.lower.nD).mulUb w.epdUb
  let twoErrBase := (remAUb.add w.square.errQ2Ub).add (remAUb.add w.square.errQ2Ub)
  c.valid && decide (4 * 10 ^ 18 ≤ c.X_lo) && decide (c.z < pExact) &&
  checkLogNat c.X_lo w.wXLoLog w.xLoLogLb w.xLoLogUb &&
  checkLogNat c.X_hi w.wXHiLog dyZero w.xHiLogUb &&
  checkEpdWitness c.X_lo w.xLoLogLb w.xLoLogUb w.epdUb w.epdW &&
  checkLower2abWitness c w.lower && checkSliceChain c.z c.y w.slices &&
  checkSlices2abMemo c w.epdUb [] w.slices && checkSquare2abWitness c w &&
  ((Dyadic.ofNat (2 * c.main_num)).add ((Dyadic.ofNat c.den).mulUb sumMSl)).ble
    ((Dyadic.ofNat (2 * c.den)).mulLb (w.lower.vFullLb.mulLb w.lower.ratLb)) &&
  ((twoErrBase.add sumESl).mulUb (Dyadic.ofNat c.den)).ble (Dyadic.ofNat (2 * c.err_num))

theorem checkSlab2abWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {w : Slab2abWitness}
    (h : checkSlab2abWitness c w = true) :
    BuchstabSwitching.External.Regime2abSlabBridge c := by
  unfold checkSlab2abWitness at h; dsimp only at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨h1_11, herr_chk⟩; rcases (Bool.and_eq_true _ _).mp h1_11 with ⟨h1_10, hmain_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1_10 with ⟨h1_9, hsq_chk⟩; rcases (Bool.and_eq_true _ _).mp h1_9 with ⟨h1_8, hslices_all⟩
  rcases (Bool.and_eq_true _ _).mp h1_8 with ⟨h1_7, hchain⟩; rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, hlo_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hepd_chk⟩; rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hlogHi⟩
  rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hlogLo⟩; rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hz_lt_b⟩
  rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hval, hX4_b⟩
  have hX4 : 4 * 10 ^ 18 ≤ c.X_lo := decide_eq_true_eq.mp hX4_b; have hz_lt : c.z < pExact := decide_eq_true_eq.mp hz_lt_b
  have hval_s := BuchstabSwitching.SlabCert.valid_sound hval; have hz2 : 2 ≤ c.z := hval_s.2.1; have hzy : c.z ≤ c.y := hval_s.2.2.1
  have hden_pos : 0 < c.den := by
    have hnet : (0 : ℚ) < (c.net_num : ℚ) / (c.den : ℚ) := hval_s.2.2.2.2.2.1
    by_contra h0; simp [show c.den = 0 by omega] at hnet
  have hlogXlo := checkLogNat_sound consts hlogLo
  have hlogXhi := (checkLogNat_sound consts hlogHi).2
  have hepd := checkEpdWitness_sound consts hlogXlo hepd_chk
  have hepd_nn : 0 ≤ w.epdUb.toReal := w.epdUb.toReal_nonneg
  obtain ⟨lo_eng, hlo_r, hlo_rem, hv_lb, _⟩ := checkLower2abWitness_sound c w.lower hlo_chk
  obtain ⟨q2_eng, hq2_err⟩ :=
    checkSquare2abWitness_sound consts hGRH hCls hMert hz2 hz_lt hlogXhi hepd hsq_chk
  have hslices_mem : ∀ sl ∈ w.slices, checkSlice2abWitness c w.epdUb sl = true :=
    List.all_eq_true.mp (checkSlices2abMemo_sound w.slices [] (by simp) hslices_all)
  have hcb := checkSliceChain_bounds w.slices c.z c.y hchain
  have hcast_eq := checkSliceChain_castSucc w.slices c.z c.y hchain
  have hslice_ex : ∀ i : Fin w.slices.length,
      ∃ s' : BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ)
        (bptsOfSlices c.z w.slices i.castSucc) (bptsOfSlices c.z w.slices i.succ),
        s'.mSl ≤ w.slices[i].mSl.toReal ∧ s'.eSl consts.li2 ≤ w.slices[i].eSl.toReal := by
    intro i; have hbi := hcb i
    obtain ⟨s0, hm0, he0⟩ := checkSlice2abWitness_sound consts hGRH hCls hMert hbi.1 hbi.2.2 hepd
      (hslices_mem w.slices[i] (List.getElem_mem i.2))
    obtain ⟨s', hm', he'⟩ := sliceEngineCast (hcast_eq i).symm (bptsOfSlices_succ c.z w.slices i).symm s0
    exact ⟨s', hm'.trans_le hm0, (he' consts.li2).trans_le he0⟩
  let sl_eng : ∀ i : Fin w.slices.length,
      BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ)
        (bptsOfSlices c.z w.slices i.castSucc) (bptsOfSlices c.z w.slices i.succ) :=
    fun i => Classical.choose (hslice_ex i)
  have hslice_spec : ∀ i : Fin w.slices.length,
      (sl_eng i).mSl ≤ w.slices[i].mSl.toReal ∧ (sl_eng i).eSl consts.li2 ≤ w.slices[i].eSl.toReal :=
    fun i => Classical.choose_spec (hslice_ex i)
  have hm_sum := sum_fin_le_sumDyadicList (·.mSl) w.slices _ fun i => (hslice_spec i).1
  have he_sum := sum_fin_le_sumDyadicList (·.eSl) w.slices _ fun i => (hslice_spec i).2
  have hden_real : (0 : ℝ) < (c.den : ℝ) := by exact_mod_cast hden_pos
  set sumMSl := sumDyadicList (·.mSl) w.slices
  set sumESl := sumDyadicList (·.eSl) w.slices
  have hmain_dy := Dyadic.ble_sound hmain_chk
  rw [Dyadic.add_toReal, Dyadic.ofNat_toReal] at hmain_dy
  have hmain_lhs : (2 * c.main_num : ℝ) + (c.den : ℝ) * sumMSl.toReal ≤
      (2 * c.main_num : ℕ) + ((Dyadic.ofNat c.den).mulUb sumMSl).toReal := by
    push_cast
    have hmul : (c.den : ℝ) * sumMSl.toReal ≤ ((Dyadic.ofNat c.den).mulUb sumMSl).toReal := by
      rw [← Dyadic.ofNat_toReal]; exact Dyadic.le_mulUb _ _
    linarith
  have hmain_rhs : ((Dyadic.ofNat (2 * c.den)).mulLb (w.lower.vFullLb.mulLb w.lower.ratLb)).toReal ≤
      2 * (c.den : ℝ) * (w.lower.vFullLb.toReal * w.lower.ratLb.toReal) := by
    refine (Dyadic.mulLb_le _ _).trans ?_
    rw [Dyadic.ofNat_toReal]; push_cast
    exact mul_le_mul_of_nonneg_left (Dyadic.mulLb_le _ _) (by positivity)
  have hmain_div : 2 * (c.main_lb : ℝ) + sumMSl.toReal ≤
      2 * (w.lower.vFullLb.toReal * w.lower.ratLb.toReal) := by
    have hc_main : (c.main_num : ℝ) = (c.main_lb : ℝ) * (c.den : ℝ) := by
      simp only [BuchstabSwitching.SlabCert.main_lb]; push_cast; field_simp [hden_real.ne']
    have hcomb := hmain_lhs.trans (hmain_dy.trans hmain_rhs)
    rw [hc_main] at hcomb
    exact le_of_mul_le_mul_left (by nlinarith) hden_real
  have hV_prod_le : w.lower.vFullLb.toReal * w.lower.ratLb.toReal ≤
      BuchstabSwitching.External.VN 2 c.z * lo_eng.rOdd := by
    rw [hlo_r]; exact mul_le_mul_of_nonneg_right hv_lb w.lower.ratLb.toReal_nonneg
  have hmain_le : (c.main_lb : ℝ) ≤
      BuchstabSwitching.External.VN 2 c.z * lo_eng.rOdd -
        (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).mSl := by
    linarith [hmain_div, hV_prod_le, hm_sum]
  have hb_pos : 0 ≤ BuchstabSwitching.External.VN 2 c.z * lo_eng.rOdd -
      (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).mSl := by
    have hc_nn : 0 ≤ (c.main_lb : ℝ) := by simp only [BuchstabSwitching.SlabCert.main_lb]; push_cast; positivity
    exact hc_nn.trans hmain_le
  set remAUb := (Dyadic.ofNat w.lower.nD).mulUb w.epdUb
  have hremAUb : (w.lower.nD : ℝ) * w.epdUb.toReal ≤ remAUb.toReal := by
    dsimp [remAUb]; rw [← Dyadic.ofNat_toReal]; exact Dyadic.le_mulUb _ _
  have herr_dy := (Dyadic.le_mulUb _ _).trans
    ((Dyadic.ble_sound herr_chk).trans_eq (Dyadic.ofNat_toReal (2 * c.err_num)))
  rw [Dyadic.ofNat_toReal, Dyadic.add_toReal, Dyadic.add_toReal, Dyadic.add_toReal] at herr_dy
  have herr_div : 2 * ((w.lower.nD : ℝ) * w.epdUb.toReal + w.square.errQ2Ub.toReal) +
      sumESl.toReal ≤ 2 * (c.err_ub : ℝ) := by
    have hc_err : (c.err_num : ℝ) = (c.err_ub : ℝ) * (c.den : ℝ) := by
      simp only [BuchstabSwitching.SlabCert.err_ub]; push_cast; field_simp [hden_real.ne']
    push_cast at herr_dy; rw [hc_err] at herr_dy
    exact le_of_mul_le_mul_right (by nlinarith) hden_real
  have hremA_le : lo_eng.remA consts.li2 ≤ (w.lower.nD : ℝ) * w.epdUb.toReal :=
    hlo_rem consts.li2 w.epdUb.toReal hepd hepd_nn
  have herr_le : lo_eng.remA consts.li2 +
      (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).eSl consts.li2 +
      q2_eng.errQ2 consts.li2 (c.X_hi : ℝ) ≤ (c.err_ub : ℝ) := by
    linarith [herr_div, hremA_le, he_sum, hq2_err]
  exact BuchstabSwitching.External.Regime2abSlabBridge.of_sieveEngines hGRH hCls
    (by exact_mod_cast hX4) le_rfl le_rfl hz2 hzy w.slices.length
    (bptsOfSlices c.z w.slices) (bptsOfSlices_zero c.z w.slices)
    (checkSliceChain_last w.slices c.z c.y hchain)
    (fun i => by rw [hcast_eq i, bptsOfSlices_succ]; exact (hcb i).2.1)
    lo_eng sl_eng q2_eng hb_pos hmain_le herr_le

end Master2abChecker

end

end BuchstabSwitching.SieveInst
