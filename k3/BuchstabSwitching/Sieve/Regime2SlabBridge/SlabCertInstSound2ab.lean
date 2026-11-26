import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2abLower
import BuchstabSwitching.Certificates.Soundness
import Mathlib.Tactic

/-!
# Soundness of `checkSlab2abWitness` for Regimes `2a` & `2b` (`61` Slabs)

Implements:
- `checkSlice2abWitness` & `checkSlice2abWitness_sound` (`kind = 0` trivial, `kind = 1`
  exact `elemSymInterval` even-Bonferroni, `kind = 2` analytic even-Bonferroni);
- `checkSliceChain` & breakpoint extraction `bptsOfSlices`;
- `checkSquare2abWitness` & `checkSquare2abWitness_sound` (`SquareEngine2ab` with exact+tail `s_q2`);
- `checkSlab2abWitness` & `checkSlab2abWitness_sound` producing `Regime2abSlabBridge c`
  via `Regime2abSlabBridge.of_sieveEngines`.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

section SliceChainAndSums

/-- Breakpoint function `Fin (slices.length + 1) → ℕ` induced by a slice list starting at `z`. -/
def bptsOfSlices (z : ℕ) (slices : List Slice2abWitness) (i : Fin (slices.length + 1)) : ℕ :=
  if h0 : i.1 = 0 then z else (slices[i.1 - 1]'(by omega)).q1

/-- Decidable check that `slices` forms a contiguous non-decreasing partition `[cur, y)`. -/
def checkSliceChain (cur y : ℕ) : List Slice2abWitness → Bool
  | [] => decide (cur = y)
  | sl :: rest =>
      decide (sl.q0 = cur) && decide (sl.q0 ≤ sl.q1) && checkSliceChain sl.q1 y rest

lemma bptsOfSlices_zero (z : ℕ) (slices : List Slice2abWitness) :
    bptsOfSlices z slices 0 = z := by
  simp [bptsOfSlices]

private lemma bptsOfSlices_cons_succ (z : ℕ) (sl : Slice2abWitness)
    (rest : List Slice2abWitness) (i : Fin (rest.length + 1)) :
    bptsOfSlices z (sl :: rest) i.succ = bptsOfSlices sl.q1 rest i := by
  rcases i with ⟨n, hn⟩
  cases n with
  | zero => simp [bptsOfSlices]
  | succ m => simp [bptsOfSlices]

lemma checkSliceChain_last : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true →
    bptsOfSlices cur slices ⟨slices.length, Nat.lt_succ_self _⟩ = y
  | [], cur, y, h => by
    simp only [checkSliceChain, decide_eq_true_eq] at h
    simpa [bptsOfSlices] using h
  | sl :: rest, cur, y, h => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have hsucc :
        (⟨(sl :: rest).length, Nat.lt_succ_self _⟩ : Fin ((sl :: rest).length + 1)) =
          (⟨rest.length, Nat.lt_succ_self _⟩ : Fin (rest.length + 1)).succ := by
      ext; simp
    rw [hsucc, bptsOfSlices_cons_succ]
    exact checkSliceChain_last rest sl.q1 y h.2

lemma checkSliceChain_castSucc : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true →
    ∀ i : Fin slices.length, bptsOfSlices cur slices i.castSucc = slices[i].q0
  | [], cur, y, _, i => i.elim0
  | sl :: rest, cur, y, h, ⟨0, _⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [bptsOfSlices, h.1.1]
  | sl :: rest, cur, y, h, ⟨j + 1, hj⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := checkSliceChain_castSucc rest sl.q1 y h.2 ⟨j, Nat.succ_lt_succ_iff.mp hj⟩
    have heq : (⟨j + 1, hj⟩ : Fin (sl :: rest).length).castSucc =
        (⟨j, Nat.succ_lt_succ_iff.mp hj⟩ : Fin rest.length).castSucc.succ := by
      ext; simp
    rw [heq, bptsOfSlices_cons_succ]
    exact hrec

lemma bptsOfSlices_succ (z : ℕ) (slices : List Slice2abWitness) (i : Fin slices.length) :
    bptsOfSlices z slices i.succ = slices[i].q1 := by
  simp [bptsOfSlices]

private lemma checkSliceChain_le_y : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true → cur ≤ y
  | [], cur, y, h => by
    simp only [checkSliceChain, decide_eq_true_eq] at h; omega
  | sl :: rest, cur, y, h => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := checkSliceChain_le_y rest sl.q1 y h.2
    omega

lemma checkSliceChain_bounds : ∀ (slices : List Slice2abWitness) (cur y : ℕ),
    checkSliceChain cur y slices = true →
    ∀ i : Fin slices.length, cur ≤ slices[i].q0 ∧ slices[i].q0 ≤ slices[i].q1 ∧ slices[i].q1 ≤ y
  | [], _, _, _, i => i.elim0
  | sl :: rest, cur, y, h, ⟨0, _⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have hlast : sl.q1 ≤ y := checkSliceChain_le_y rest sl.q1 y h.2
    exact ⟨h.1.1.ge, h.1.2, hlast⟩
  | sl :: rest, cur, y, h, ⟨j + 1, hj⟩ => by
    simp only [checkSliceChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := checkSliceChain_bounds rest sl.q1 y h.2 ⟨j, Nat.succ_lt_succ_iff.mp hj⟩
    exact ⟨le_trans (by omega) hrec.1, hrec.2.1, hrec.2.2⟩

/-- Tail-recursive `SciNat` sum over `slices` via projection `f`. -/
def sumSciListAux (acc : SciNat) (f : Slice2abWitness → SciNat)
    (slices : List Slice2abWitness) : SciNat :=
  slices.foldl (fun s sl => s.add (f sl)) acc

def sumSciList (f : Slice2abWitness → SciNat) (slices : List Slice2abWitness) : SciNat :=
  sumSciListAux (SciNat.ofNat 0) f slices

lemma sum_fin_le_sumSciListAux (f : Slice2abWitness → SciNat) :
    ∀ (slices : List Slice2abWitness) (acc : SciNat) (g : Fin slices.length → ℝ),
      (∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) →
      acc.toReal + ∑ i : Fin slices.length, g i ≤ (sumSciListAux acc f slices).toReal
  | [], acc, _, _ => by simp [sumSciListAux]
  | sl :: rest, acc, g, hg => by
    have hrec := sum_fin_le_sumSciListAux f rest (acc.add (f sl)) (fun i => g i.succ)
      (fun i => hg i.succ)
    have hsum : ∑ i : Fin (sl :: rest).length, g i = g 0 + ∑ i : Fin rest.length, g i.succ := by
      convert Fin.sum_univ_succ (fun i : Fin (rest.length + 1) => g i)
    rw [hsum]
    have h0 : g 0 ≤ (f sl).toReal := hg 0
    have hacc : (acc.add (f sl)).toReal = acc.toReal + (f sl).toReal := SciProofs.add_toReal _ _
    simp only [sumSciListAux, List.foldl_cons] at hrec ⊢
    linarith

lemma sum_fin_le_sumSciList (f : Slice2abWitness → SciNat) (slices : List Slice2abWitness)
    (g : Fin slices.length → ℝ) (hg : ∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) :
    ∑ i : Fin slices.length, g i ≤ (sumSciList f slices).toReal := by
  have h := sum_fin_le_sumSciListAux f slices (SciNat.ofNat 0) g hg
  simpa [sumSciList, SciProofs.ofNat_toReal] using h

end SliceChainAndSums

section SliceChecker

/-- Shared combinatorial even-Bonferroni parameter check (`kind = 1` and `kind = 2`). -/
def checkEvenBonfCommon (c : BuchstabSwitching.SlabCert) (sl : Slice2abWitness) : Bool :=
  let ps := oddPrimesList sl.zSub
  let q1 := ps.take sl.aQ
  let p2 := ps.drop sl.aQ
  let k := 2 * sl.mEv
  decide (sl.zSub ≤ c.z) &&
  decide (sl.zSub ≤ pExact) &&
  decide (sl.aQ ≤ ps.length) &&
  decide (q1.prod * (p2.reverse.take k).prod ≤ sl.dMax) &&
  decide (((sl.q1 - 1) * sl.dMax) ^ 2 ≤ c.X_lo) &&
  decide (2 ^ sl.aQ * (∑ j ∈ Finset.range (k + 1), p2.length.choose j) ≤ sl.nD) &&
  (exactProdOneSubInvPredUb 3 sl.zSub 24).ble sl.vSubUb

/-- Exact DP `RTrunc` even upper-bound checker on `p2`. -/
def checkSliceRatExact (p2 : List ℕ) (mEv : ℕ) (ratUb : SciNat) : Bool :=
  match p2 with
  | [] => (SciNat.ofNat 1).ble ratUb
  | _ :: _ =>
    let sums := elemSymSums (elemSymInterval p2 (2 * mEv))
    let gP2Lb := v2ListLb p2
    decide (0 < gP2Lb.m) && sums.2.1.ble (sums.2.2.1.add (ratUb.mul gP2Lb))

private lemma checkSliceRatExact_sound {p2 : List ℕ} (hP2_lt : p2.Pairwise (· < ·))
    (hP2_pr : ∀ p ∈ p2, p.Prime ∧ 2 < p) {mEv : ℕ} {ratUb : SciNat}
    (h : checkSliceRatExact p2 mEv ratUb = true) :
    BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset (2 * mEv) ≤ ratUb.toReal := by
  unfold checkSliceRatExact at h
  dsimp only at h
  have hP2_nd := pairwise_lt_nodup hP2_lt
  have hP2_fin_pr : ∀ p ∈ p2.toFinset, p.Prime ∧ 2 < p := fun p hp =>
    hP2_pr p (List.mem_toFinset.mp hp)
  cases p2 with
  | nil =>
    rw [List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
    simpa [SciProofs.ofNat_toReal] using SciProofs.ble_sound h
  | cons p0 tl =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hble := SciProofs.ble_sound h.2
    rw [SciProofs.add_toReal, SciProofs.mul_toReal] at hble
    have hsum := elemSymSums_interval_sound hP2_nd (fun p hp => (hP2_pr p hp).1) (2 * mEv)
    have hgLb := v2ListLb_sound hP2_nd hP2_pr
    have hgLb_pos : 0 < (v2ListLb (p0 :: tl)).toReal := by
      unfold v2ListLb; rw [sciNat_scale_toReal]; exact div_pos (by exact_mod_cast h.1) sciScale_pos
    have hV2_pos : 0 < BuchstabSwitching.V2 BuchstabSwitching.gTot (p0 :: tl).toFinset :=
      lt_of_lt_of_le hgLb_pos hgLb
    have hmul_le : BuchstabSwitching.gTrunc BuchstabSwitching.gTot (p0 :: tl).toFinset (2 * mEv) ≤
        ratUb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot (p0 :: tl).toFinset := by
      have h1 : ratUb.toReal * (v2ListLb (p0 :: tl)).toReal ≤
          ratUb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot (p0 :: tl).toFinset :=
        mul_le_mul_of_nonneg_left hgLb ratUb.toReal_nonneg
      linarith [hsum.2.1]
    rw [BuchstabSwitching.RTrunc]
    exact (div_le_iff₀ hV2_pos).mpr hmul_le

/-- Analytic `RTrunc` even upper-bound checker on `p2`. -/
def checkSliceRatAnalytic (p2 : List ℕ) (mEv : ℕ) (gSubLb ratUb : SciNat) : Bool :=
  let k := 2 * mEv
  let s1Ub := sumG1ListUb p2
  let errNum := sciPowUb s1Ub (k + 1)
  let errDen := (SciNat.ofNat (Nat.factorial (k + 1))).mul gSubLb
  let errUb := errNum.divUb errDen 24
  checkAnalyticV2Lb p2 gSubLb &&
    match p2 with
    | [] => (SciNat.ofNat 1).ble ratUb
    | _ :: _ => ((SciNat.ofNat 1).add errUb).ble ratUb

private lemma checkSliceRatAnalytic_sound {p2 : List ℕ} (hP2_lt : p2.Pairwise (· < ·))
    (hP2_pr : ∀ p ∈ p2, p.Prime ∧ 2 < p) {mEv : ℕ} {gSubLb ratUb : SciNat}
    (h : checkSliceRatAnalytic p2 mEv gSubLb ratUb = true) :
    BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset (2 * mEv) ≤ ratUb.toReal := by
  unfold checkSliceRatAnalytic at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  have hg := checkAnalyticV2Lb_sound hP2_lt hP2_pr h.1
  have hP2_nd := pairwise_lt_nodup hP2_lt
  have hP2_fin_pr : ∀ p ∈ p2.toFinset, p.Prime ∧ 2 < p := fun p hp =>
    hP2_pr p (List.mem_toFinset.mp hp)
  cases p2 with
  | nil =>
    rw [List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
    simpa [SciProofs.ofNat_toReal] using SciProofs.ble_sound h.2
  | cons p0 tl =>
    have hble := SciProofs.ble_sound h.2
    rw [SciProofs.add_toReal, SciProofs.ofNat_toReal, Nat.cast_one] at hble
    have hS1 := sumG1ListUb_sound hP2_nd hP2_pr
    have hR := BuchstabSwitching.analytic_bonf_RTrunc_even_ub hP2_fin_pr mEv hg.1 hg.2 hS1
    set s1Ub := sumG1ListUb (p0 :: tl)
    set errNum := sciPowUb s1Ub (2 * mEv + 1)
    set errDen := (SciNat.ofNat (Nat.factorial (2 * mEv + 1))).mul gSubLb
    set errUb := errNum.divUb errDen 24
    have herr_le : s1Ub.toReal ^ (2 * mEv + 1) /
        ((Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal) ≤ errUb.toReal := by
      have hpow := sciPowUb_sound s1Ub (2 * mEv + 1)
      have hden_eq : errDen.toReal = (Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal := by
        dsimp [errDen]; rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal]
      have h1 : s1Ub.toReal ^ (2 * mEv + 1) /
          ((Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal) ≤
          errNum.toReal / errDen.toReal := by
        rw [hden_eq]
        exact div_le_div_of_nonneg_right hpow (mul_nonneg (by positivity) hg.1.le)
      exact h1.trans (SciProofs.divUb_le errNum errDen 24)
    dsimp only [errUb, s1Ub] at herr_le
    linarith

/-- Per-slice witness checker for Regimes `2a`/`2b` (`kind = 0, 1, 2`). -/
def checkSlice2abWitness (c : BuchstabSwitching.SlabCert) (epdUb : SciNat)
    (sl : Slice2abWitness) : Bool :=
  let hLogs :=
    (if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.logQ0Lb sl.logQ0Ub else true) &&
    (if pExact < sl.q1 then checkLogNat sl.q1 sl.logQ1Lb sl.logQ1Ub else true)
  let hSliceBase :=
    hLogs &&
    checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb
  if !hSliceBase then false
  else if sl.kind == 0 then
    decide ((sl.q1 - 1) ^ 2 ≤ c.X_lo) &&
    sl.sqUb.ble sl.mSl &&
    (sl.cntUb.mul epdUb).ble sl.eSl
  else if sl.kind == 1 then
    let ps := oddPrimesList sl.zSub
    let q1 := ps.take sl.aQ
    let p2 := ps.drop sl.aQ
    let k := 2 * sl.mEv
    let sums := elemSymSums (elemSymInterval p2 k)
    let ip2Ub := (invPhiListUb q1).mul (sums.2.1.add sums.2.2.2)
    checkEvenBonfCommon c sl &&
    ip2Ub.ble sl.ip2 &&
    checkSliceRatExact p2 sl.mEv sl.ratUb &&
    ((sl.sqUb.mul sl.vSubUb).mul sl.ratUb).ble sl.mSl &&
    ((sl.cntUb.mul ((SciNat.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mul epdUb).ble sl.eSl
  else if sl.kind == 2 then
    let ps := oddPrimesList sl.zSub
    let q1 := ps.take sl.aQ
    let p2 := ps.drop sl.aQ
    let s1Ub := sumG1ListUb p2
    let expRes := expUbBounds s1Ub
    checkEvenBonfCommon c sl &&
    checkSliceRatAnalytic p2 sl.mEv sl.gSubLb sl.ratUb &&
    expRes.1 &&
    ((invPhiListUb q1).mul expRes.2).ble sl.ip2 &&
    ((sl.sqUb.mul sl.vSubUb).mul sl.ratUb).ble sl.mSl &&
    ((sl.cntUb.mul ((SciNat.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mul epdUb).ble sl.eSl
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
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcom
  rcases hcom with ⟨⟨⟨⟨⟨⟨hz_c, hz_ex⟩, ha_le⟩, hd_prod⟩, hqd_sq⟩, hnd_nat⟩, hv_ub⟩
  set ps := oddPrimesList sl.zSub
  set q1 := ps.take sl.aQ
  set p2 := ps.drop sl.aQ
  set k := 2 * sl.mEv
  have hps_lt := oddPrimesList_pairwise_lt sl.zSub
  have hps_pr := oddPrimesList_props sl.zSub
  refine ⟨hz_c, take_drop_disjoint hps_lt sl.aQ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [take_drop_union, oddPrimesList_toFinset hz_ex]
  · intro d hd
    exact_mod_cast (bonfDivisors_le_take_mul_rev_drop hps_lt
      (fun p hp => (hps_pr p hp).1.one_lt.le) sl.aQ k d hd).trans hd_prod
  · intro q hq
    have hq_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
    have hq_lt : q < sl.q1 := lt_of_lt_of_le hq_ico.2 (min_le_right _ _)
    have hq_le : q ≤ sl.q1 - 1 := by omega
    have hmul : (q * sl.dMax) ^ 2 ≤ c.X_lo := by
      have h1 : q * sl.dMax ≤ (sl.q1 - 1) * sl.dMax := Nat.mul_le_mul_right sl.dMax hq_le
      exact (Nat.pow_le_pow_left h1 2).trans hqd_sq
    rw [← Nat.cast_mul, Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast hmul
  · exact_mod_cast (card_bonfDivisors_take_drop hps_lt
      (fun p hp => (hps_pr p hp).1) ha_le k).trans_le hnd_nat
  · exact (VN_two_le_exactProdOneSubInvPredUb hz_ex 24).trans (SciProofs.ble_sound hv_ub)

private lemma evenBonfSliceEngine {c : BuchstabSwitching.SlabCert} {epdUb : SciNat}
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
    (hm_chk : ((sl.sqUb.mul sl.vSubUb).mul sl.ratUb).ble sl.mSl = true)
    (he_chk : ((sl.cntUb.mul ((SciNat.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mul epdUb).ble sl.eSl = true) :
    ∃ s_eng : BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ) sl.q0 sl.q1,
      s_eng.mSl ≤ sl.mSl.toReal ∧ s_eng.eSl li2 ≤ sl.eSl.toReal := by
  refine ⟨.evenBonf
    { z_sub := sl.zSub, m_ev := sl.mEv, hz_sub := hz_c, Q₁ := Q₁, P₂ := P₂, hdisj := hdisj,
      hunion := hunion, d_max := (sl.dMax : ℝ), hd_le := hd_le, hqd_sqrt := hqd_sqrt,
      n_d := (sl.nD : ℝ), ip2 := sl.ip2.toReal, rat_ub := sl.ratUb.toReal,
      sq_ub := sl.sqUb.toReal, cnt_ub := sl.cntUb.toReal,
      hnd := hnd, hip2 := hip2, hrat := hrat, hsq := hsq, hcnt := hcnt }, ?_, ?_⟩
  · have hm := SciProofs.ble_sound hm_chk
    rw [SciProofs.mul_toReal, SciProofs.mul_toReal, mul_assoc] at hm
    have h1 : BuchstabSwitching.External.VN 2 sl.zSub * sl.ratUb.toReal ≤ sl.vSubUb.toReal * sl.ratUb.toReal :=
      mul_le_mul_of_nonneg_right hv_sub sl.ratUb.toReal_nonneg
    exact (mul_le_mul_of_nonneg_left h1 sl.sqUb.toReal_nonneg).trans hm
  · have he := SciProofs.ble_sound he_chk
    rw [SciProofs.mul_toReal, SciProofs.mul_toReal, SciProofs.add_toReal, SciProofs.add_toReal, SciProofs.ofNat_toReal, ← add_assoc] at he
    have hcoeff_nn : 0 ≤ sl.cntUb.toReal * ((sl.nD : ℝ) + sl.ip2.toReal + sl.ratUb.toReal) :=
      mul_nonneg sl.cntUb.toReal_nonneg
        (add_nonneg (add_nonneg (Nat.cast_nonneg _) sl.ip2.toReal_nonneg) sl.ratUb.toReal_nonneg)
    exact (mul_le_mul_of_nonneg_left hepd hcoeff_nn).trans he

/-- Soundness of `checkSlice2abWitness`: constructs `SliceEngine2ab c c.X_lo sl.q0 sl.q1`
and bounds `.mSl ≤ sl.mSl.toReal` and `.eSl consts.li2 ≤ sl.eSl.toReal`. -/
theorem checkSlice2abWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {epdUb : SciNat} {sl : Slice2abWitness}
    (hz_q0 : c.z ≤ sl.q0) (hq1_y : sl.q1 ≤ c.y)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (h : checkSlice2abWitness c epdUb sl = true) :
    ∃ s_eng : BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ) sl.q0 sl.q1,
      s_eng.mSl ≤ sl.mSl.toReal ∧ s_eng.eSl consts.li2 ≤ sl.eSl.toReal := by
  unfold checkSlice2abWitness at h
  dsimp only at h
  cases hbase : ((if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.logQ0Lb sl.logQ0Ub else true) &&
      (if pExact < sl.q1 then checkLogNat sl.q1 sl.logQ1Lb sl.logQ1Ub else true)) &&
      checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb with
  | false => rw [hbase] at h; simp at h
  | true =>
  rw [hbase] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  simp only [Bool.and_eq_true] at hbase
  have hLog0 : 27000 ≤ sl.q0 →
      sl.logQ0Lb.toReal ≤ Real.log (sl.q0 : ℝ) ∧ Real.log (sl.q0 : ℝ) ≤ sl.logQ0Ub.toReal := fun hq0 =>
    checkLogNat_sound consts (by have hq0' : pExact ≤ sl.q0 := hq0; simpa [hq0'] using hbase.1.1)
  have hLog1 : 27000 < sl.q1 →
      sl.logQ1Lb.toReal ≤ Real.log (sl.q1 : ℝ) ∧ Real.log (sl.q1 : ℝ) ≤ sl.logQ1Ub.toReal := fun hq1 =>
    checkLogNat_sound consts (by have hq1' : pExact < sl.q1 := hq1; simpa [hq1'] using hbase.1.2)
  have hsc := checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hLog0 hLog1 hbase.2
  have hico_eq : Finset.Ico (max c.z sl.q0) (min c.y sl.q1) = Finset.Ico sl.q0 sl.q1 := by
    rw [max_eq_right hz_q0, min_eq_right hq1_y]
  have hsq : ∑ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sl.sqUb.toReal := by
    rw [hico_eq]; exact hsc.1
  have hcnt : (((Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime).card : ℝ) ≤
      sl.cntUb.toReal := by
    rw [hico_eq]; exact hsc.2
  split_ifs at h with hk0 hk1 hk2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hq_sqrt : ∀ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
        (q : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
      intro q hq
      have hq_lt : q < sl.q1 := lt_of_lt_of_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2
        (min_le_right _ _)
      have hq_le : q ≤ sl.q1 - 1 := by omega
      have hq_sq : q ^ 2 ≤ c.X_lo := (Nat.pow_le_pow_left hq_le 2).trans h.1.1
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast hq_sq
    refine ⟨.trivial ⟨hq_sqrt, sl.sqUb.toReal, sl.cntUb.toReal, hsq, hcnt⟩, ?_, ?_⟩
    · exact SciProofs.ble_sound h.1.2
    · have he := SciProofs.ble_sound h.2
      rw [SciProofs.mul_toReal] at he
      exact (mul_le_mul_of_nonneg_left hepd sl.cntUb.toReal_nonneg).trans he
  · set ps := oddPrimesList sl.zSub; set q1 := ps.take sl.aQ; set p2 := ps.drop sl.aQ; set k := 2 * sl.mEv
    have hps_lt := oddPrimesList_pairwise_lt sl.zSub; have hps_pr := oddPrimesList_props sl.zSub
    have htd : (q1 ++ p2).Pairwise (· < ·) := by dsimp only [q1, p2]; rw [List.take_append_drop]; exact hps_lt
    have hpair := List.pairwise_append.mp htd; have hQ_nd : q1.Nodup := pairwise_lt_nodup hpair.1
    have hP_lt : p2.Pairwise (· < ·) := hpair.2.1; have hP_nd : p2.Nodup := pairwise_lt_nodup hP_lt
    have hQ_pr : ∀ p ∈ q1, p.Prime ∧ 2 < p := fun p hp => let hp' := hps_pr p (List.mem_of_mem_take hp); ⟨hp'.1, hp'.2.1⟩
    have hP_pr : ∀ p ∈ p2, p.Prime ∧ 2 < p := fun p hp => let hp' := hps_pr p (List.mem_of_mem_drop hp); ⟨hp'.1, hp'.2.1⟩
    have hQ_fin_pr : ∀ p ∈ q1.toFinset, p.Prime ∧ 2 < p := fun p hp => hQ_pr p (List.mem_toFinset.mp hp)
    have hP_fin_pr : ∀ p ∈ p2.toFinset, p.Prime ∧ 2 < p := fun p hp => hP_pr p (List.mem_toFinset.mp hp)
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨hcom, hip2_chk⟩, hrat_chk⟩, hm_chk⟩, he_chk⟩
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
        have hpp := hQ_fin_pr p hp
        rw [BuchstabSwitching.gTot_prime hpp.1]
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.2
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp; ring
      have hQ_ub := invPhiListUb_sound hQ_nd (fun p hp => (hQ_pr p hp).1.two_le)
      have hsum := elemSymSums_interval_sound hP_nd (fun p hp => (hP_pr p hp).1) k
      have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (k + 1),
          BuchstabSwitching.elemSym BuchstabSwitching.gTot p2.toFinset j :=
        Finset.sum_nonneg fun j _ =>
          BuchstabSwitching.elemSym_nonneg (fun _ _ => BuchstabSwitching.gTot_nonneg _) j
      rw [hQ_eq]
      have hmul := mul_le_mul hQ_ub hsum.2.2 hsum_nn (invPhiListUb q1).toReal_nonneg
      rw [← SciProofs.mul_toReal] at hmul
      exact hmul.trans (SciProofs.ble_sound hip2_chk)
    have hrat : BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset k ≤ sl.ratUb.toReal :=
      checkSliceRatExact_sound hP_lt hP_pr hrat_chk
    exact evenBonfSliceEngine hz_c hdisj hunion hd_le hqd_sqrt hnd hip2 hrat hsq hcnt hv_sub
      hepd hm_chk he_chk
  · set ps := oddPrimesList sl.zSub; set q1 := ps.take sl.aQ; set p2 := ps.drop sl.aQ; set k := 2 * sl.mEv
    have hps_lt := oddPrimesList_pairwise_lt sl.zSub; have hps_pr := oddPrimesList_props sl.zSub
    have htd : (q1 ++ p2).Pairwise (· < ·) := by dsimp only [q1, p2]; rw [List.take_append_drop]; exact hps_lt
    have hpair := List.pairwise_append.mp htd; have hQ_nd : q1.Nodup := pairwise_lt_nodup hpair.1
    have hP_lt : p2.Pairwise (· < ·) := hpair.2.1; have hP_nd : p2.Nodup := pairwise_lt_nodup hP_lt
    have hQ_pr : ∀ p ∈ q1, p.Prime ∧ 2 < p := fun p hp => let hp' := hps_pr p (List.mem_of_mem_take hp); ⟨hp'.1, hp'.2.1⟩
    have hP_pr : ∀ p ∈ p2, p.Prime ∧ 2 < p := fun p hp => let hp' := hps_pr p (List.mem_of_mem_drop hp); ⟨hp'.1, hp'.2.1⟩
    have hQ_fin_pr : ∀ p ∈ q1.toFinset, p.Prime ∧ 2 < p := fun p hp => hQ_pr p (List.mem_toFinset.mp hp)
    have hP_fin_pr : ∀ p ∈ p2.toFinset, p.Prime ∧ 2 < p := fun p hp => hP_pr p (List.mem_toFinset.mp hp)
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨hcom, hrat_chk⟩, hexp_ok⟩, hip2_chk⟩, hm_chk⟩, he_chk⟩
    obtain ⟨hz_c, hdisj, hunion, hd_le, hqd_sqrt, hnd, hv_sub⟩ := evenBonfCommon_sound c sl hq1_y hcom
    have hS1 := sumG1ListUb_sound hP_nd hP_pr
    have hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k,
        BuchstabSwitching.gTot d ≤ sl.ip2.toReal := by
      have hle := BuchstabSwitching.sum_bonfDivisors_gTot_le_exp hdisj hQ_fin_pr hP_fin_pr k hS1
      have hQ_ub := invPhiListUb_sound hQ_nd (fun p hp => (hQ_pr p hp).1.two_le)
      have hexp_ub := (expUbBounds_sound hexp_ok).1
      have hmul := mul_le_mul hQ_ub hexp_ub (Real.exp_pos _).le (invPhiListUb q1).toReal_nonneg
      rw [← SciProofs.mul_toReal] at hmul
      exact hle.trans (hmul.trans (SciProofs.ble_sound hip2_chk))
    have hrat : BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset k ≤ sl.ratUb.toReal :=
      checkSliceRatAnalytic_sound hP_lt hP_pr hrat_chk
    exact evenBonfSliceEngine hz_c hdisj hunion hd_le hqd_sqrt hnd hip2 hrat hsq hcnt hv_sub
      hepd hm_chk he_chk

end SliceChecker

section SquareChecker

/-- Computable prime-square witness checker for Regimes `2a`/`2b`. -/
def checkSquare2abWitness (c : BuchstabSwitching.SlabCert) (w : Slab2abWitness) : Bool :=
  let sq := w.square
  let qEnd := min c.y (sq.qSq + 1)
  let sExact := exactInvMulPredSumUb c.z (min qEnd pExact) 24
  let sTail :=
    if pExact < qEnd then SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat (pExact - 1)) 24
    else SciNat.ofNat 0
  let hEndLog := if pExact < qEnd then checkLogNat qEnd sq.logEndLb sq.logEndUb else true
  let tailQ2 :=
    if c.y ≤ sq.qSq + 1 then SciNat.ofNat 0
    else w.xHiLogUb.divUb (SciNat.ofNat sq.qSq) 24
  let innerUb := sq.sQ2Ub.add ((sq.cntLoUb.mul w.epdUb).add tailQ2)
  decide (1 ≤ sq.qSq) &&
  decide (sq.qSq ^ 4 ≤ c.X_lo) &&
  (sExact.add sTail).ble sq.sQ2Ub &&
  hEndLog &&
  checkSlice2abOr2cBounds c.z qEnd w.xLoLogLb w.xLoLogUb sq.logEndLb sq.logEndUb ⟨1000, 0⟩ sq.cntLoUb &&
  innerUb.ble (sq.errQ2Ub.mul (SciNat.ofNat 2))

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
  unfold checkSquare2abWitness at h
  dsimp only at h
  set sq := w.square
  set qEnd := min c.y (sq.qSq + 1)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hq1, hq4⟩, hs_chk⟩, hlogEnd_chk⟩, hcnt_chk⟩, herr_chk⟩
  have hq_rt : ((sq.qSq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    have hpow : (sq.qSq ^ 2) ^ 2 = sq.qSq ^ 4 := by ring
    exact_mod_cast (hpow.symm ▸ hq4 : (sq.qSq ^ 2) ^ 2 ≤ c.X_lo)
  have hs_q2 : ∑ q ∈ (Finset.Ico c.z qEnd).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ sq.sQ2Ub.toReal := by
    have hsplit := BuchstabSwitching.sum_inv_mul_pred_split_le c.z qEnd pExact hz2 (by decide)
    have hex := sum_inv_mul_pred_le_exact (q0 := c.z) (q1 := min qEnd pExact) (min_le_right _ _) 24
    have htail : (if pExact < qEnd then 1 / ((pExact : ℝ) - 1) else 0) ≤
        (if pExact < qEnd then SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat (pExact - 1)) 24
         else SciNat.ofNat 0).toReal := by
      split_ifs with hlt
      · have hdiv := SciProofs.divUb_le (SciNat.ofNat 1) (SciNat.ofNat (pExact - 1)) 24
        rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, Nat.cast_sub (by decide : 1 ≤ pExact),
          Nat.cast_one] at hdiv
        simpa using hdiv
      · simp [SciProofs.ofNat_toReal]
    have hble := SciProofs.ble_sound hs_chk
    rw [SciProofs.add_toReal] at hble
    unfold pExact at hsplit hex htail hble
    linarith
  have hLog0 : 27000 ≤ c.z →
      w.xLoLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ w.xLoLogUb.toReal := by
    intro hc; exfalso; unfold pExact at hz_lt; omega
  have hLog1 : 27000 < qEnd →
      sq.logEndLb.toReal ≤ Real.log (qEnd : ℝ) ∧ Real.log (qEnd : ℝ) ≤ sq.logEndUb.toReal := by
    intro hlt
    have hlt' : pExact < qEnd := hlt
    simp only [hlt', ↓reduceIte] at hlogEnd_chk
    exact checkLogNat_sound consts hlogEnd_chk
  have hcnt := (checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hLog0 hLog1 hcnt_chk).2
  let q2_eng : BuchstabSwitching.External.SquareEngine2ab c (c.X_lo : ℝ) :=
    { q_sq := sq.qSq
      hq_sq1 := hq1
      hq_sq_rt := hq_rt
      s_q2 := sq.sQ2Ub.toReal
      hs_q2 := hs_q2
      cnt_lo := sq.cntLoUb.toReal
      hcnt_lo := hcnt }
  refine ⟨q2_eng, ?_⟩
  have htail_le : (if c.y ≤ sq.qSq + 1 then (0 : ℝ) else Real.log (c.X_hi : ℝ) / (sq.qSq : ℝ)) ≤
      (if c.y ≤ sq.qSq + 1 then SciNat.ofNat 0
       else w.xHiLogUb.divUb (SciNat.ofNat sq.qSq) 24).toReal := by
    split_ifs with hy
    · simp [SciProofs.ofNat_toReal]
    · have h1 : Real.log (c.X_hi : ℝ) / (sq.qSq : ℝ) ≤ w.xHiLogUb.toReal / (sq.qSq : ℝ) :=
        div_le_div_of_nonneg_right hlogHi (Nat.cast_nonneg _)
      have h2 := SciProofs.divUb_le w.xHiLogUb (SciNat.ofNat sq.qSq) 24
      rw [SciProofs.ofNat_toReal] at h2
      exact h1.trans h2
  have herr_le := SciProofs.ble_sound herr_chk
  rw [SciProofs.add_toReal, SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal,
    SciProofs.ofNat_toReal] at herr_le
  have hcnt_epd : sq.cntLoUb.toReal * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤
      sq.cntLoUb.toReal * w.epdUb.toReal :=
    mul_le_mul_of_nonneg_left hepd sq.cntLoUb.toReal_nonneg
  dsimp only [BuchstabSwitching.External.SquareEngine2ab.errQ2, q2_eng]
  norm_num at herr_le
  linarith

end SquareChecker

section Master2abChecker

private lemma sliceEngineCast {c : BuchstabSwitching.SlabCert} {X_lo : ℝ}
    {q0 q1 q0' q1' : ℕ} (h0 : q0 = q0') (h1 : q1 = q1')
    (s : BuchstabSwitching.External.SliceEngine2ab c X_lo q0 q1) :
    ∃ s' : BuchstabSwitching.External.SliceEngine2ab c X_lo q0' q1',
      s'.mSl = s.mSl ∧ ∀ li2, s'.eSl li2 = s.eSl li2 := by
  subst h0; subst h1; exact ⟨s, rfl, fun _ => rfl⟩

/-- Complete computable witness verifier for Regime `2a`/`2b` slabs. -/
def checkSlab2abWitness (c : BuchstabSwitching.SlabCert) (w : Slab2abWitness) : Bool :=
  let sumMSl := sumSciList (·.mSl) w.slices
  let sumESl := sumSciList (·.eSl) w.slices
  let remAUb := (SciNat.ofNat w.lower.nD).mul w.epdUb
  c.valid &&
  decide (4 * 10 ^ 18 ≤ c.X_lo) &&
  decide (c.z < pExact) &&
  checkLogNat c.X_lo w.xLoLogLb w.xLoLogUb &&
  (ratLogBounds c.X_hi 1).1 &&
  (ratLogBounds c.X_hi 1).2.2.ble w.xHiLogUb &&
  checkEpdUb c.X_lo w.xLoLogLb w.xLoLogUb w.epdUb &&
  checkLower2abWitness c w.lower &&
  checkSliceChain c.z c.y w.slices &&
  w.slices.all (checkSlice2abWitness c w.epdUb) &&
  checkSquare2abWitness c w &&
  ((SciNat.ofNat (2 * c.main_num)).add ((SciNat.ofNat c.den).mul sumMSl)).ble
    ((SciNat.ofNat (2 * c.den)).mul (w.lower.vFullLb.mul w.lower.ratLb)) &&
  (((SciNat.ofNat 2).mul (remAUb.add w.square.errQ2Ub)).add sumESl |>.mul
    (SciNat.ofNat c.den)).ble (SciNat.ofNat (2 * c.err_num))

/-- Master soundness theorem for `checkSlab2abWitness`: produces `Regime2abSlabBridge c`
via `Regime2abSlabBridge.of_sieveEngines`. -/
theorem checkSlab2abWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {w : Slab2abWitness}
    (h : checkSlab2abWitness c w = true) :
    BuchstabSwitching.External.Regime2abSlabBridge c := by
  unfold checkSlab2abWitness at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hval, hX4⟩, hz_lt⟩, hlogLo⟩, hlogHi_ok⟩, hlogHi_ble⟩, hepd_chk⟩,
    hlo_chk⟩, hchain⟩, hslices_all⟩, hsq_chk⟩, hmain_chk⟩, herr_chk⟩
  have hval_s := BuchstabSwitching.SlabCert.valid_sound hval
  have hz2 : 2 ≤ c.z := hval_s.2.1
  have hzy : c.z ≤ c.y := hval_s.2.2.1
  have hden_pos : 0 < c.den := by
    have hnet : (0 : ℚ) < (c.net_num : ℚ) / (c.den : ℚ) := hval_s.2.2.2.2.2.1
    by_contra h0
    have hde : c.den = 0 := by omega
    simp [hde] at hnet
  have hlogXlo := checkLogNat_sound consts hlogLo
  have hlogXhi : Real.log (c.X_hi : ℝ) ≤ w.xHiLogUb.toReal := by
    have hr := (ratLogBounds_sound consts hlogHi_ok).2
    rw [Nat.cast_one, div_one] at hr
    exact hr.trans (SciProofs.ble_sound hlogHi_ble)
  have hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ w.epdUb.toReal :=
    checkEpdUb_sound consts hlogXlo hepd_chk
  have hepd_nn : 0 ≤ w.epdUb.toReal := w.epdUb.toReal_nonneg
  obtain ⟨lo_eng, hlo_r, hlo_rem, hv_lb, _⟩ := checkLower2abWitness_sound c w.lower hlo_chk
  obtain ⟨q2_eng, hq2_err⟩ :=
    checkSquare2abWitness_sound consts hGRH hCls hMert hz2 hz_lt hlogXhi hepd hsq_chk
  have hslices_mem : ∀ sl ∈ w.slices, checkSlice2abWitness c w.epdUb sl = true :=
    List.all_eq_true.mp hslices_all
  have hcb := checkSliceChain_bounds w.slices c.z c.y hchain
  have hcast_eq := checkSliceChain_castSucc w.slices c.z c.y hchain
  have hslice_ex : ∀ i : Fin w.slices.length,
      ∃ s' : BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ)
        (bptsOfSlices c.z w.slices i.castSucc) (bptsOfSlices c.z w.slices i.succ),
        s'.mSl ≤ w.slices[i].mSl.toReal ∧ s'.eSl consts.li2 ≤ w.slices[i].eSl.toReal := by
    intro i
    have hbi := hcb i
    have hsl_ok := hslices_mem w.slices[i] (List.getElem_mem i.2)
    obtain ⟨s0, hm0, he0⟩ :=
      checkSlice2abWitness_sound consts hGRH hCls hMert hbi.1 hbi.2.2 hepd hsl_ok
    obtain ⟨s', hm', he'⟩ :=
      sliceEngineCast (hcast_eq i).symm (bptsOfSlices_succ c.z w.slices i).symm s0
    exact ⟨s', hm'.trans_le hm0, (he' consts.li2).trans_le he0⟩
  let sl_eng : ∀ i : Fin w.slices.length,
      BuchstabSwitching.External.SliceEngine2ab c (c.X_lo : ℝ)
        (bptsOfSlices c.z w.slices i.castSucc) (bptsOfSlices c.z w.slices i.succ) :=
    fun i => Classical.choose (hslice_ex i)
  have hslice_spec : ∀ i : Fin w.slices.length,
      (sl_eng i).mSl ≤ w.slices[i].mSl.toReal ∧
        (sl_eng i).eSl consts.li2 ≤ w.slices[i].eSl.toReal :=
    fun i => Classical.choose_spec (hslice_ex i)
  have hm_sum : ∑ i : Fin w.slices.length, (sl_eng i).mSl ≤
      (sumSciList (·.mSl) w.slices).toReal :=
    sum_fin_le_sumSciList (·.mSl) w.slices (fun i => (sl_eng i).mSl) fun i => (hslice_spec i).1
  have he_sum : ∑ i : Fin w.slices.length, (sl_eng i).eSl consts.li2 ≤
      (sumSciList (·.eSl) w.slices).toReal :=
    sum_fin_le_sumSciList (·.eSl) w.slices (fun i => (sl_eng i).eSl consts.li2)
      fun i => (hslice_spec i).2
  have hden_real : (0 : ℝ) < (c.den : ℝ) := by exact_mod_cast hden_pos
  have hmain_sci := SciProofs.ble_sound hmain_chk
  rw [SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal,
    SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, SciProofs.ofNat_toReal] at hmain_sci
  have hmain_div : 2 * (c.main_lb : ℝ) + (sumSciList (·.mSl) w.slices).toReal ≤
      2 * (w.lower.vFullLb.toReal * w.lower.ratLb.toReal) := by
    have hc_main : (c.main_num : ℝ) = (c.main_lb : ℝ) * (c.den : ℝ) := by
      simp only [BuchstabSwitching.SlabCert.main_lb]
      push_cast; field_simp [hden_real.ne']
    push_cast at hmain_sci
    rw [hc_main] at hmain_sci
    refine le_of_mul_le_mul_left ?_ hden_real
    calc (c.den : ℝ) * (2 * (c.main_lb : ℝ) + (sumSciList (·.mSl) w.slices).toReal)
        = 2 * ((c.main_lb : ℝ) * (c.den : ℝ)) +
            (c.den : ℝ) * (sumSciList (·.mSl) w.slices).toReal := by ring
      _ ≤ 2 * (c.den : ℝ) * (w.lower.vFullLb.toReal * w.lower.ratLb.toReal) := hmain_sci
      _ = (c.den : ℝ) * (2 * (w.lower.vFullLb.toReal * w.lower.ratLb.toReal)) := by ring
  have hV_prod_le : w.lower.vFullLb.toReal * w.lower.ratLb.toReal ≤
      BuchstabSwitching.External.VN 2 c.z * lo_eng.rOdd := by
    rw [hlo_r]
    exact mul_le_mul_of_nonneg_right hv_lb w.lower.ratLb.toReal_nonneg
  have hmain_le : (c.main_lb : ℝ) ≤
      BuchstabSwitching.External.VN 2 c.z * lo_eng.rOdd -
        (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).mSl := by
    linarith [hmain_div, hV_prod_le, hm_sum]
  have hb_pos : 0 ≤ BuchstabSwitching.External.VN 2 c.z * lo_eng.rOdd -
      (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).mSl := by
    have hc_nn : 0 ≤ (c.main_lb : ℝ) := by
      simp only [BuchstabSwitching.SlabCert.main_lb]
      push_cast; positivity
    exact hc_nn.trans hmain_le
  have herr_sci := SciProofs.ble_sound herr_chk
  simp only [SciProofs.mul_toReal, SciProofs.add_toReal, SciProofs.ofNat_toReal] at herr_sci
  have herr_div : 2 * ((w.lower.nD : ℝ) * w.epdUb.toReal + w.square.errQ2Ub.toReal) +
      (sumSciList (·.eSl) w.slices).toReal ≤ 2 * (c.err_ub : ℝ) := by
    have hc_err : (c.err_num : ℝ) = (c.err_ub : ℝ) * (c.den : ℝ) := by
      simp only [BuchstabSwitching.SlabCert.err_ub]
      push_cast; field_simp [hden_real.ne']
    push_cast at herr_sci
    rw [hc_err] at herr_sci
    refine le_of_mul_le_mul_right ?_ hden_real
    calc (2 * ((w.lower.nD : ℝ) * w.epdUb.toReal + w.square.errQ2Ub.toReal) +
            (sumSciList (·.eSl) w.slices).toReal) * (c.den : ℝ)
        = (2 * ((w.lower.nD : ℝ) * w.epdUb.toReal + w.square.errQ2Ub.toReal) +
            (sumSciList (·.eSl) w.slices).toReal) * (c.den : ℝ) := rfl
      _ ≤ 2 * ((c.err_ub : ℝ) * (c.den : ℝ)) := herr_sci
      _ = (2 * (c.err_ub : ℝ)) * (c.den : ℝ) := by ring
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
    (fun i => by
      rw [hcast_eq i, bptsOfSlices_succ]
      exact (hcb i).2.1)
    lo_eng sl_eng q2_eng hb_pos hmain_le herr_le

end Master2abChecker

end

end BuchstabSwitching.SieveInst
