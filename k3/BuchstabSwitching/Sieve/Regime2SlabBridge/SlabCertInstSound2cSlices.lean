import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cJFull
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cBrun
import BuchstabSwitching.Certificates.Soundness
import Mathlib.Tactic

/-!
# Soundness of `checkSlab2cWitness` for Regime `2c` (`66` Slabs)

Verifies `Slice2cWitness` (`EvenBonf` for `z_sub ≤ 27000` and `z_sub = c.z`, and `Selberg`
with `J_full` via `checkJFullLb2c_sound`), `SquareEngine2c`, and `checkSlab2cWitness_sound`,
producing `External.Regime2cSlabBridge c` via `Regime2cSlabBridge.of_sieveEngines`.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

private abbrev sn (m e : ℕ) : SciNat := ⟨m, e⟩

section SliceChainAndSums2c

/-- Breakpoint function `Fin (slices.length + 1) → ℕ` induced by a Regime `2c` slice list. -/
def bptsOfSlices2c (z : ℕ) (slices : List Slice2cWitness) (i : Fin (slices.length + 1)) : ℕ :=
  if h0 : i.1 = 0 then z else (slices[i.1 - 1]'(by omega)).q1

/-- Decidable check that `slices` forms a contiguous non-decreasing partition `[cur, y)`. -/
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
    have hlast : sl.q1 ≤ y := checkSliceChain2c_le rest sl.q1 y h.2
    exact ⟨h.1.1.ge, h.1.2, hlast⟩
  | sl :: rest, _, y, h, ⟨j + 1, hj⟩ => by
    simp only [checkSliceChain2c, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := checkSliceChain2c_bounds rest sl.q1 y h.2 ⟨j, Nat.succ_lt_succ_iff.mp hj⟩
    simp only [Fin.getElem_fin, List.getElem_cons_succ] at hrec ⊢
    exact ⟨by omega, hrec.2.1, hrec.2.2⟩

def sumSciList2c (f : Slice2cWitness → SciNat) (slices : List Slice2cWitness) : SciNat :=
  slices.foldl (fun s sl => s.add (f sl)) (SciNat.ofNat 0)

private lemma sum_fin_le_sumSciList2cAux (f : Slice2cWitness → SciNat) :
    ∀ (slices : List Slice2cWitness) (acc : SciNat) (g : Fin slices.length → ℝ),
      (∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) →
      acc.toReal + ∑ i : Fin slices.length, g i ≤ (slices.foldl (fun s sl => s.add (f sl)) acc).toReal
  | [], _, _, _ => by simp
  | sl :: rest, acc, g, hg => by
    have hrec := sum_fin_le_sumSciList2cAux f rest (acc.add (f sl)) (fun i => g i.succ) (fun i => hg i.succ)
    have hsum : ∑ i : Fin (sl :: rest).length, g i = g 0 + ∑ i : Fin rest.length, g i.succ := Fin.sum_univ_succ g
    rw [hsum]
    have h0 : g 0 ≤ (f sl).toReal := hg 0
    have := SciProofs.add_toReal acc (f sl)
    simp only [List.foldl_cons] at hrec ⊢; linarith

lemma sum_fin_le_sumSciList2c (f : Slice2cWitness → SciNat) (slices : List Slice2cWitness)
    (g : Fin slices.length → ℝ) (hg : ∀ i : Fin slices.length, g i ≤ (f slices[i]).toReal) :
    ∑ i : Fin slices.length, g i ≤ (sumSciList2c f slices).toReal := by
  simpa [sumSciList2c, SciProofs.ofNat_toReal] using sum_fin_le_sumSciList2cAux f slices (SciNat.ofNat 0) g hg

end SliceChainAndSums2c

section EvenBonfSlice2c

private lemma sum_bonfDivisors_gTot_eq {Q₁ P₂ : Finset ℕ}
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
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp; ring

private def checkSliceRatSmall (p2 : List ℕ) (mEv : ℕ) (gSubLb ratUb : SciNat) : Bool :=
  match p2 with
  | [] => (SciNat.ofNat 1).ble ratUb
  | _ :: _ =>
    let k := 2 * mEv
    let errUb := divUbSig (sciPowUb (sumG1ListUb p2) (k + 1))
      ((SciNat.ofNat (Nat.factorial (k + 1))).mul gSubLb) 24
    let okAn := checkAnalyticV2Lb p2 gSubLb && ((SciNat.ofNat 1).add errUb).ble ratUb
    okAn || (let sums := elemSymSums (elemSymInterval p2 k); let gLb := v2ListLb p2
      decide (0 < gLb.m) && sums.2.1.ble (sums.2.2.1.add (ratUb.mul gLb)))

private lemma checkSliceRatSmall_sound {p2 : List ℕ} (hP2_lt : p2.Pairwise (· < ·))
    (hP2_pr : ∀ p ∈ p2, p.Prime ∧ 2 < p) {mEv : ℕ} {gSubLb ratUb : SciNat}
    (h : checkSliceRatSmall p2 mEv gSubLb ratUb = true) :
    BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset (2 * mEv) ≤ ratUb.toReal := by
  have hP2_nd := pairwise_lt_nodup hP2_lt
  cases p2 with
  | nil => rw [List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
           simpa [checkSliceRatSmall, SciProofs.ofNat_toReal] using SciProofs.ble_sound h
  | cons p0 tl =>
    simp only [checkSliceRatSmall, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hV, hble⟩ | ⟨hgPos, hble⟩
    · have hg := checkAnalyticV2Lb_sound hP2_lt hP2_pr hV
      have hR := BuchstabSwitching.analytic_bonf_RTrunc_even_ub
        (fun p hp => hP2_pr p (List.mem_toFinset.mp hp)) mEv hg.1 hg.2 (sumG1ListUb_sound hP2_nd hP2_pr)
      have herr := divUbSig_le (sciPowUb (sumG1ListUb (p0 :: tl)) (2 * mEv + 1))
        ((SciNat.ofNat (Nat.factorial (2 * mEv + 1))).mul gSubLb) 24
      rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal] at herr
      have h1 : (sumG1ListUb (p0 :: tl)).toReal ^ (2 * mEv + 1) /
            ((Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal) ≤
          (sciPowUb (sumG1ListUb (p0 :: tl)) (2 * mEv + 1)).toReal /
            ((Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal) :=
        div_le_div_of_nonneg_right (sciPowUb_sound _ _) (mul_nonneg (by positivity) hg.1.le)
      have h2 := SciProofs.ble_sound hble; rw [SciProofs.add_toReal, SciProofs.ofNat_toReal, Nat.cast_one] at h2
      linarith [hR, h1.trans herr]
    · have hble' := SciProofs.ble_sound hble; rw [SciProofs.add_toReal, SciProofs.mul_toReal] at hble'
      have hsum := elemSymSums_interval_sound hP2_nd (fun p hp => (hP2_pr p hp).1) (2 * mEv)
      have hgLb := v2ListLb_sound hP2_nd hP2_pr
      have hgPos' : 0 < (v2ListLb (p0 :: tl)).toReal := by
        unfold v2ListLb; rw [sciNat_scale_toReal]; exact div_pos (by exact_mod_cast hgPos) sciScale_pos
      rw [BuchstabSwitching.RTrunc, div_le_iff₀ (lt_of_lt_of_le hgPos' hgLb)]
      have := mul_le_mul_of_nonneg_left hgLb ratUb.toReal_nonneg; linarith [hsum.2.1]

/-- Checker for `EvenBonf` slices (`isSelberg = false`) in Regime `2c` (`zSub ≤ 27000` or `zSub = c.z`). -/
def checkEvenBonf2c (c : BuchstabSwitching.SlabCert) (zLogLb zLogUb epdUb vFullLb : SciNat)
    (sl : Slice2cWitness) : Bool :=
  let baseOk :=
    (divUbSig ((sl.cntUb.mul ((SciNat.ofNat sl.nD).add (sl.ip2.add sl.ratUb))).mul epdUb) vFullLb 24).ble sl.eSl &&
    (sl.sqUb.mul sl.mRatUb).ble sl.mSl
  if sl.zSub ≤ 27000 then
    let ps := fastOddPrimesList2c sl.zSub; let q1 := ps.take sl.aQ; let p2 := ps.drop sl.aQ; let k := 2 * sl.mEv
    let expS1 := expUbBounds (sumG1ListUb p2)
    let ipOk := (expS1.1 && ((invPhiListUb q1).mul expS1.2).ble sl.ip2) ||
      ((invPhiListUb q1).mul (let s := elemSymSums (elemSymInterval p2 k); s.2.1.add s.2.2.2)).ble sl.ip2
    baseOk && decide (sl.zSub ≤ c.z) && decide (sl.aQ ≤ ps.length) &&
    decide (q1.prod * (p2.reverse.take k).prod ≤ sl.dMax) &&
    decide (((sl.q1 - 1) * sl.dMax) ^ 2 ≤ c.X_lo) &&
    decide (2 ^ sl.aQ * ((List.range (k + 1)).foldl (fun acc j => acc + fastChoose p2.length j) 0) ≤ sl.nD) &&
    ipOk && checkSliceRatSmall p2 sl.mEv sl.gSubLb sl.ratUb &&
    (fastV2UbExact2c 3 sl.zSub).ble sl.vSubUb &&
    (divUbSig (sl.vSubUb.mul sl.ratUb) vFullLb 24).ble sl.mRatUb
  else if h : sl.aQ < smallOddPrimes2c.length then
    let pMin := smallOddPrimes2c[sl.aQ]; let k := 2 * sl.mEv
    let (okM, s1, _, piN) := computeMertensTail2c pMin c.z (sn 0 0) (sn 0 0) zLogLb zLogUb
    let (okV, gLb) := v2TailLb2c pMin c.z (sn 0 0) (sn 0 0) zLogLb zLogUb
    let (okE, eS1) := expUbBounds s1
    let errR := divUbSig (sciPowUb s1 (k + 1)) ((SciNat.ofNat (Nat.factorial (k + 1))).mul sl.gSubLb) 24
    baseOk && decide (sl.zSub = c.z) && decide (pMin < c.z) &&
    (if 27000 < c.z then checkLogNat c.z zLogLb zLogUb else true) &&
    decide ((smallOddPrimes2c.take sl.aQ).prod * c.z ^ k ≤ sl.dMax) &&
    decide (((sl.q1 - 1) * sl.dMax) ^ 2 ≤ c.X_lo) &&
    okM && okV && okE && decide (0 < sl.gSubLb.m) && sl.gSubLb.ble gLb &&
    ((SciNat.ofNat (2 ^ sl.aQ)).mul (sumPowDivFactUb (SciNat.ofNat piN) k)).ble (SciNat.ofNat sl.nD) &&
    ((invPhiListUb (smallOddPrimes2c.take sl.aQ)).mul eS1).ble sl.ip2 &&
    ((SciNat.ofNat 1).add errR).ble sl.ratUb && sl.ratUb.ble sl.mRatUb
  else false

private lemma q_mul_dMax_sqrt {c : BuchstabSwitching.SlabCert} {q0 q1 dMax : ℕ}
    (h : ((q1 - 1) * dMax) ^ 2 ≤ c.X_lo) :
    ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
      (q : ℝ) * (dMax : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
  intro q hq
  have hq_lt : q < q1 := lt_of_lt_of_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2 (min_le_right _ _)
  rw [← Nat.cast_mul, Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.pow_le_pow_left (Nat.mul_le_mul_right dMax (by omega)) 2).trans h

lemma evenBonf2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLb zLogUb epdUb vFullLb : SciNat} {sl : Slice2cWitness}
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (hv_le : vFullLb.toReal ≤ External.VN 2 c.z)
    (hsq : ∑ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sl.sqUb.toReal)
    (hcnt : (((Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime).card : ℝ) ≤ sl.cntUb.toReal)
    (h : checkEvenBonf2c c zLogLb zLogUb epdUb vFullLb sl = true) :
    ∃ s : External.SliceEngine2c c (c.X_lo : ℝ) sl.q0 sl.q1,
      s.mSl ≤ sl.mSl.toReal ∧ s.eSl consts.li2 ≤ sl.eSl.toReal := by
  unfold checkEvenBonf2c at h
  by_cases hz_sm : sl.zSub ≤ 27000
  · simp only [hz_sm, ↓reduceIte] at h
    rw [fastOddPrimesList2c_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbase, hz_c⟩, ha_le⟩, hd_prod⟩, hqd⟩, hnd_n⟩, hip⟩, hrat⟩, hvsub⟩, hmrat⟩
    rw [foldl_range_sum_eq] at hnd_n
    have hnd_n' : 2 ^ sl.aQ * (∑ j ∈ Finset.range (2 * sl.mEv + 1), ((oddPrimesList sl.zSub).drop sl.aQ).length.choose j) ≤ sl.nD := by
      simpa [fastChoose_eq_choose] using hnd_n
    rcases hbase with ⟨hesl, hmsl⟩
    set ps := oddPrimesList sl.zSub; set q1 := ps.take sl.aQ; set p2 := ps.drop sl.aQ
    have hps_lt := oddPrimesList_pairwise_lt sl.zSub; have hps_pr := oddPrimesList_props sl.zSub
    have hq1_nd : q1.Nodup := (pairwise_lt_nodup hps_lt).take
    have hp2_lt : p2.Pairwise (· < ·) := (List.pairwise_append.mp (by rw [List.take_append_drop]; exact hps_lt)).2.1
    have hp2_nd : p2.Nodup := pairwise_lt_nodup hp2_lt
    have hq1_pr : ∀ p ∈ q1.toFinset, p.Prime ∧ 2 < p := fun p hp =>
      let h := hps_pr p (List.mem_of_mem_take (List.mem_toFinset.mp hp)); ⟨h.1, h.2.1⟩
    have hp2_pr : ∀ p ∈ p2.toFinset, p.Prime ∧ 2 < p := fun p hp =>
      let h := hps_pr p (List.mem_of_mem_drop (List.mem_toFinset.mp hp)); ⟨h.1, h.2.1⟩
    have hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset (2 * sl.mEv),
        BuchstabSwitching.gTot d ≤ sl.ip2.toReal := by
      have hphi := invPhiListUb_sound hq1_nd fun p hp => (hps_pr p (List.mem_of_mem_take hp)).1.two_le
      have hQ_nn : 0 ≤ ∏ p ∈ q1.toFinset, (p : ℝ) / ((p : ℝ) - 1) :=
        Finset.prod_nonneg fun p hp => div_nonneg (Nat.cast_nonneg _)
          (by have hp3 : (3 : ℝ) ≤ (p : ℝ) := (by exact_mod_cast (hq1_pr p hp).2); linarith)
      rcases Bool.or_eq_true _ _ |>.mp hip with hE | hDP
      · rcases Bool.and_eq_true _ _ |>.mp hE with ⟨hE1, hEble⟩
        have hbonf := BuchstabSwitching.sum_bonfDivisors_gTot_le_exp (take_drop_disjoint hps_lt sl.aQ)
          hq1_pr hp2_pr (2 * sl.mEv) (sumG1ListUb_sound hp2_nd fun p hp =>
            let h := hps_pr p (List.mem_of_mem_drop hp); ⟨h.1, h.2.1⟩)
        have hble := SciProofs.ble_sound hEble; rw [SciProofs.mul_toReal] at hble
        exact hbonf.trans ((mul_le_mul hphi (expUbBounds_sound hE1).1 (Real.exp_pos _).le (hQ_nn.trans hphi)).trans hble)
      · rw [sum_bonfDivisors_gTot_eq (take_drop_disjoint hps_lt sl.aQ) hq1_pr hp2_pr]
        have hsum := elemSymSums_interval_sound hp2_nd (fun p hp => (hps_pr p (List.mem_of_mem_drop hp)).1) (2 * sl.mEv)
        have hble := SciProofs.ble_sound hDP; rw [SciProofs.mul_toReal] at hble
        exact (mul_le_mul hphi hsum.2.2 (Finset.sum_nonneg fun _ _ => BuchstabSwitching.elemSym_nonneg
          (fun _ _ => BuchstabSwitching.gTot_nonneg _) _) (hQ_nn.trans hphi)).trans hble
    have hrat_s := checkSliceRatSmall_sound hp2_lt
      (fun p hp => let h := hps_pr p (List.mem_of_mem_drop hp); ⟨h.1, h.2.1⟩) hrat
    let spec : External.EvenBonfSliceSpec c (c.X_lo : ℝ) sl.q0 sl.q1 :=
      ⟨sl.zSub, sl.mEv, hz_c, q1.toFinset, p2.toFinset, take_drop_disjoint hps_lt sl.aQ,
        by rw [take_drop_union, oddPrimesList_toFinset hz_sm], sl.dMax,
        fun d hd => by exact_mod_cast (bonfDivisors_le_take_mul_rev_drop hps_lt
          (fun p hp => (hps_pr p hp).1.one_lt.le) sl.aQ (2 * sl.mEv) d hd).trans hd_prod,
        q_mul_dMax_sqrt hqd, sl.nD, sl.ip2.toReal, sl.ratUb.toReal, sl.sqUb.toReal, sl.cntUb.toReal,
        by exact_mod_cast (card_bonfDivisors_take_drop hps_lt (fun p hp => (hps_pr p hp).1) ha_le
          (2 * sl.mEv)).trans_le hnd_n', hip2, hrat_s, hsq, hcnt⟩
    have hm_rat : (External.VN 2 spec.z_sub / External.VN 2 c.z) * spec.rat_ub ≤ sl.mRatUb.toReal := by
      have hv_s : External.VN 2 sl.zSub ≤ sl.vSubUb.toReal :=
        ((VN_two_eq_prod_Ico sl.zSub).symm ▸ fastV2UbExact2c_sound hz_sm).trans (SciProofs.ble_sound hvsub)
      have h1 := mul_le_mul_of_nonneg_right (div_le_div₀ (SciNat.toReal_nonneg sl.vSubUb)
        hv_s hv_pos hv_le) (SciNat.toReal_nonneg sl.ratUb)
      have h2 := (divUbSig_le (sl.vSubUb.mul sl.ratUb) vFullLb 24).trans (SciProofs.ble_sound hmrat)
      rw [SciProofs.mul_toReal, ← div_mul_eq_mul_div] at h2
      exact h1.trans h2
    refine ⟨External.SliceEngine2c.evenBonf spec vFullLb.toReal sl.mRatUb.toReal hv_pos hv_le hm_rat, ?_, ?_⟩
    · dsimp [External.SliceEngine2c.mSl, spec]; rw [← SciProofs.mul_toReal]; exact SciProofs.ble_sound hmsl
    · dsimp [External.SliceEngine2c.eSl, spec]
      refine remNorm_le_of_ble (mul_nonneg (SciNat.toReal_nonneg _)
        (add_nonneg (add_nonneg (Nat.cast_nonneg _) (SciNat.toReal_nonneg _)) (SciNat.toReal_nonneg _)))
        ?_ hepd hv_pos hesl
      rw [SciProofs.mul_toReal, SciProofs.add_toReal, SciProofs.add_toReal, SciProofs.ofNat_toReal]; linarith
  · simp only [hz_sm, ↓reduceIte] at h
    by_cases ha_sm : sl.aQ < smallOddPrimes2c.length
    · have ha : sl.aQ < oddPrimesLt27000.length := lt_of_lt_of_le ha_sm smallOddPrimes2c_len_le
      simp only [ha_sm, ↓reduceDIte] at h
      rw [smallOddPrimes2c_getElem ha_sm, smallOddPrimes2c_take ha_sm.le] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbase, hz_eq⟩, hpz⟩, hlogZ⟩, hd_prod⟩, hqd⟩, hokM⟩, hokV⟩, hokE⟩,
        hgPos⟩, hgLe⟩, hnd_n⟩, hip⟩, hrat⟩, hmrat⟩
      rcases hbase with ⟨hesl, hmsl⟩
      set pMin := oddPrimesLt27000[sl.aQ]
      have hpa_lt : (if sl.aQ = 0 then 2 else oddPrimesLt27000[sl.aQ - 1]'(by omega)) < pMin := by
        split_ifs with ha0
        · exact lt_of_lt_of_le (by norm_num) (mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)).1
        · exact (List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt) (sl.aQ - 1) sl.aQ (by omega) ha (by omega)
      have hsplit := oddPrimesLt27000_split_props ha hpz.le hpa_lt le_rfl
      set Q₁ : Finset ℕ := (oddPrimesLt27000.take sl.aQ).toFinset
      set P₂ : Finset ℕ := (Finset.Ico pMin c.z).filter Nat.Prime
      have hLogZ : 27000 < c.z → zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ zLogUb.toReal :=
        fun hz27 => checkLogNat_sound consts (by simpa [hz27] using hlogZ)
      have hpMin_lt : pMin < 27000 := (mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)).2.1
      have hm := computeMertensTail2c_sound consts hGRH hCls hMert (fun _ => by omega) hLogZ hokM
      have hv := v2TailLb2c_sound consts hGRH hCls hMert (fun _ => by omega) hLogZ hokV
      have hQ₁_pr : ∀ p ∈ Q₁, p.Prime ∧ 2 < p := fun p hp => ⟨(hsplit.2.2.2.1 p hp).1, (hsplit.2.2.2.1 p hp).2.1⟩
      have hP₂_pr : ∀ p ∈ P₂, p.Prime ∧ 2 < p := fun p hp =>
        ⟨(hsplit.2.2.2.2 p hp).1, (mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)).1.trans (hsplit.2.2.2.2 p hp).2.2⟩
      have hnd_real : ((BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * sl.mEv)).card : ℝ) ≤ (sl.nD : ℝ) := by
        have hcard := BuchstabSwitching.card_bonfDivisors_le_factorial_sum hsplit.1
          (fun p hp => (hQ₁_pr p hp).1) (fun p hp => (hP₂_pr p hp).1) (2 * sl.mEv) hm.2.2
        rw [hsplit.2.2.1] at hcard
        have hble := SciProofs.ble_sound hnd_n
        rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal, SciProofs.ofNat_toReal] at hble
        push_cast at hble
        have h1 := mul_le_mul_of_nonneg_left
          (sumPowDivFactUb_sound
            (SciNat.ofNat (computeMertensTail2c pMin c.z (sn 0 0) (sn 0 0) zLogLb zLogUb).2.2.2) (2 * sl.mEv))
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ sl.aQ)
        rw [SciProofs.ofNat_toReal] at h1; linarith
      have hq_nd : (oddPrimesLt27000.take sl.aQ).Nodup := oddPrimesLt27000_nodup.take
      have hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * sl.mEv), BuchstabSwitching.gTot d ≤ sl.ip2.toReal := by
        have hbonf := BuchstabSwitching.sum_bonfDivisors_gTot_le_exp hsplit.1 hQ₁_pr hP₂_pr (2 * sl.mEv) hm.1
        have hphi := invPhiListUb_sound hq_nd fun p hp =>
          (mem_oddPrimesLt27000_iff.mp (List.mem_of_mem_take hp)).2.2.two_le
        have hQ_nn : 0 ≤ ∏ p ∈ Q₁, (p : ℝ) / ((p : ℝ) - 1) :=
          Finset.prod_nonneg fun p hp => div_nonneg (Nat.cast_nonneg _)
            (by have hp3 : (3 : ℝ) ≤ (p : ℝ) := (by exact_mod_cast (hQ₁_pr p hp).2); linarith)
        have hble := SciProofs.ble_sound hip; rw [SciProofs.mul_toReal] at hble
        exact hbonf.trans ((mul_le_mul hphi (expUbBounds_sound hokE).1 (Real.exp_pos _).le (hQ_nn.trans hphi)).trans hble)
      have hrat_s : BuchstabSwitching.RTrunc BuchstabSwitching.gTot P₂ (2 * sl.mEv) ≤ sl.ratUb.toReal := by
        have hgPos' : 0 < sl.gSubLb.toReal := by unfold SciNat.toReal; exact div_pos (by exact_mod_cast hgPos) (by positivity)
        have hR := BuchstabSwitching.analytic_bonf_RTrunc_even_ub hP₂_pr sl.mEv hgPos'
          ((SciProofs.ble_sound hgLe).trans hv.2) hm.1
        have hdiv := divUbSig_le (sciPowUb (computeMertensTail2c pMin c.z (sn 0 0) (sn 0 0) zLogLb zLogUb).2.1 (2 * sl.mEv + 1))
          ((SciNat.ofNat (Nat.factorial (2 * sl.mEv + 1))).mul sl.gSubLb) 24
        rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal] at hdiv
        have h1 : (computeMertensTail2c pMin c.z (sn 0 0) (sn 0 0) zLogLb zLogUb).2.1.toReal ^ (2 * sl.mEv + 1) /
              ((Nat.factorial (2 * sl.mEv + 1) : ℝ) * sl.gSubLb.toReal) ≤
            (sciPowUb (computeMertensTail2c pMin c.z (sn 0 0) (sn 0 0) zLogLb zLogUb).2.1 (2 * sl.mEv + 1)).toReal /
              ((Nat.factorial (2 * sl.mEv + 1) : ℝ) * sl.gSubLb.toReal) :=
          div_le_div_of_nonneg_right (sciPowUb_sound _ _) (mul_nonneg (by positivity) hgPos'.le)
        have hble := SciProofs.ble_sound hrat; rw [SciProofs.add_toReal, SciProofs.ofNat_toReal, Nat.cast_one] at hble
        linarith [hR, h1.trans hdiv]
      let spec : External.EvenBonfSliceSpec c (c.X_lo : ℝ) sl.q0 sl.q1 :=
        ⟨sl.zSub, sl.mEv, hz_eq.le, Q₁, P₂, hsplit.1, hz_eq ▸ hsplit.2.1, sl.dMax, fun d hd => by
          have hbd := BuchstabSwitching.bonfDivisors_le_prod_mul_pow_of_pos (by omega : 1 ≤ c.z)
            (fun p hp => (hQ₁_pr p hp).1.pos) (fun p hp => (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le) hd
          have hqprod : ∏ p ∈ Q₁, p = (oddPrimesLt27000.take sl.aQ).prod := by
            simpa [Q₁] using List.prod_toFinset (fun x : ℕ => x) hq_nd
          exact_mod_cast (hqprod ▸ hbd).trans hd_prod,
          q_mul_dMax_sqrt hqd, sl.nD, sl.ip2.toReal, sl.ratUb.toReal, sl.sqUb.toReal, sl.cntUb.toReal,
          hnd_real, hip2, hrat_s, hsq, hcnt⟩
      have hm_rat : (External.VN 2 spec.z_sub / External.VN 2 c.z) * spec.rat_ub ≤ sl.mRatUb.toReal := by
        have hv_z : 0 < External.VN 2 c.z := lt_of_lt_of_le hv_pos hv_le
        dsimp [spec]; rw [hz_eq, div_self hv_z.ne', one_mul]; exact SciProofs.ble_sound hmrat
      refine ⟨External.SliceEngine2c.evenBonf spec vFullLb.toReal sl.mRatUb.toReal hv_pos hv_le hm_rat, ?_, ?_⟩
      · dsimp [External.SliceEngine2c.mSl, spec]; rw [← SciProofs.mul_toReal]; exact SciProofs.ble_sound hmsl
      · dsimp [External.SliceEngine2c.eSl, spec]
        refine remNorm_le_of_ble (mul_nonneg (SciNat.toReal_nonneg _)
          (add_nonneg (add_nonneg (Nat.cast_nonneg _) (SciNat.toReal_nonneg _)) (SciNat.toReal_nonneg _)))
          ?_ hepd hv_pos hesl
        rw [SciProofs.mul_toReal, SciProofs.add_toReal, SciProofs.add_toReal, SciProofs.ofNat_toReal]; linarith
    · simp only [ha_sm, ↓reduceDIte] at h; simp at h

end EvenBonfSlice2c

section SelbergSlice2c

/-- Checker for `Selberg` slices (`isSelberg = true`) in Regime `2c`. -/
def checkSelberg2c (c : BuchstabSwitching.SlabCert) (zLogLo zLogUb epdUb vFullLb : SciNat)
    (sl : Slice2cWitness) : Bool :=
  let s3cOk := (sl.cntUb.mul (sl.xiQLb.mul sl.xiQLb)).ble sl.s3cUb || (sl.sqUb.mul sl.hQ).ble sl.s3cUb
  let es1Lhs := ((sn 625 4).mul sl.s3cUb).mul ((sciPowUb (((sn 2 0).mul sl.xiQLogUb).add (sn 6 0)) 2).mul epdUb)
  let f0Lhs := sl.xiQLogUb.add ((sn 636 3).add (divUbSig (sn 78 2) (sl.xiQLb.mul sl.xiQLb) 24))
  let eNum := sl.es1Ub.add ((sl.cntUb.mul ((sn 1 0).add (sciPowUb ((sn 13 1).mul sl.f0Ub) 3))).mul epdUb)
  sl.xiQLb.ble sl.xiQUb &&
  ((SciNat.ofNat (sl.q1 - 1)).mul (sl.xiQUb.mul sl.xiQUb)).ble sl.hQ &&
  (sl.hQ.mul sl.hQ).ble (SciNat.ofNat c.X_lo) &&
  checkJFullLb2c c.z zLogLo zLogUb sl.xiQLb sl.xiQLogLb sl.xiQLogUb sl.jfLb &&
  (divUbSig sl.sqUb (vFullLb.mul sl.jfLb) 24).ble sl.mSl &&
  s3cOk && es1Lhs.ble sl.es1Ub && f0Lhs.ble sl.f0Ub &&
  (divUbSig eNum vFullLb 24).ble sl.eSl

lemma selberg2c_sound (consts : External.CertifiedConstants)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLo zLogUb epdUb vFullLb : SciNat} {sl : Slice2cWitness}
    (hepd0 : 0 ≤ BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ))
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (hv_le : vFullLb.toReal ≤ External.VN 2 c.z)
    (hsq : ∑ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sl.sqUb.toReal)
    (hcnt : (((Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime).card : ℝ) ≤ sl.cntUb.toReal)
    (h : checkSelberg2c c zLogLo zLogUb epdUb vFullLb sl = true) :
    ∃ s : External.SliceEngine2c c (c.X_lo : ℝ) sl.q0 sl.q1,
      s.mSl ≤ sl.mSl.toReal ∧ s.eSl consts.li2 ≤ sl.eSl.toReal := by
  unfold checkSelberg2c at h; dsimp only at h; simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hxiU, hqxi⟩, hhsq⟩, hjf⟩, hmsl⟩, hs3c⟩, hes1⟩, hf0⟩, hesl⟩
  rcases checkJFullLb2c_sound consts hMert hjf with ⟨_, hxi1, hjPos, hjLe⟩
  have hqxi_s : ∀ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (q : ℝ) * sl.xiQLb.toReal ^ 2 ≤ sl.hQ.toReal := by
    intro q hq
    have hq_lt : q < sl.q1 := lt_of_lt_of_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2 (min_le_right _ _)
    have hble := SciProofs.ble_sound hqxi
    rw [SciProofs.mul_toReal, SciProofs.mul_toReal, SciProofs.ofNat_toReal] at hble
    have hsq_le : sl.xiQLb.toReal ^ 2 ≤ sl.xiQUb.toReal * sl.xiQUb.toReal := by
      rw [sq]
      exact mul_le_mul (SciProofs.ble_sound hxiU) (SciProofs.ble_sound hxiU)
        (SciNat.toReal_nonneg _) (SciNat.toReal_nonneg _)
    have h1 : (q : ℝ) * sl.xiQLb.toReal ^ 2 ≤ ((sl.q1 - 1 : ℕ) : ℝ) * (sl.xiQUb.toReal * sl.xiQUb.toReal) :=
      mul_le_mul (by exact_mod_cast (by omega : q ≤ sl.q1 - 1)) hsq_le (by positivity) (Nat.cast_nonneg _)
    exact h1.trans hble
  have hh_sqrt : sl.hQ.toReal ≤ Real.sqrt (c.X_lo : ℝ) := by
    have hble := SciProofs.ble_sound hhsq; rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal] at hble
    exact Real.le_sqrt_of_sq_le (by rw [sq]; exact hble)
  let spec : External.SelbergSliceSpec c (c.X_lo : ℝ) sl.q0 sl.q1 :=
    ⟨sl.xiQLb.toReal, sl.hQ.toReal, hxi1, SciNat.toReal_nonneg _, hqxi_s, hh_sqrt,
      sl.sqUb.toReal, sl.cntUb.toReal, sl.jfLb.toReal, vFullLb.toReal, hsq, hcnt, hjPos, hjLe, hv_pos, hv_le⟩
  refine ⟨External.SliceEngine2c.selberg spec, ?_, ?_⟩
  · dsimp [External.SliceEngine2c.mSl, spec]
    have hdiv := divUbSig_le sl.sqUb (vFullLb.mul sl.jfLb) 24; rw [SciProofs.mul_toReal] at hdiv
    exact hdiv.trans (SciProofs.ble_sound hmsl)
  · dsimp [External.SliceEngine2c.eSl, spec]
    have hxiLog : Real.log sl.xiQLb.toReal ≤ sl.xiQLogUb.toReal := by
      unfold checkJFullLb2c at hjf; dsimp only at hjf
      set b := decide (3 ≤ c.z) && decide (0 < sl.jfLb.m) && (sn 1 0).ble sl.xiQLb &&
        checkLogNat c.z zLogLo zLogUb && (sciLogBounds sl.xiQLb).1 &&
        sl.xiQLogLb.ble (sciLogBounds sl.xiQLb).2.1 && (sciLogBounds sl.xiQLb).2.2.ble sl.xiQLogUb
      have hb : b = true := by by_contra hf; simp [b, hf] at hjf
      simp only [b, Bool.and_eq_true] at hb
      exact (sciLogBounds_sound consts hb.1.1.2).2.trans (SciProofs.ble_sound hb.2)
    have hs3c_le : min (sl.cntUb.toReal * sl.xiQLb.toReal ^ 2) (sl.sqUb.toReal * sl.hQ.toReal) ≤ sl.s3cUb.toReal := by
      rcases Bool.or_eq_true _ _ |>.mp hs3c with h1 | h2
      · have hb := SciProofs.ble_sound h1; rw [SciProofs.mul_toReal, SciProofs.mul_toReal, ← sq] at hb
        exact (min_le_left _ _).trans hb
      · have hb := SciProofs.ble_sound h2; rw [SciProofs.mul_toReal] at hb; exact (min_le_right _ _).trans hb
    have hes1_le : (1 / 16 : ℝ) * min (sl.cntUb.toReal * sl.xiQLb.toReal ^ 2) (sl.sqUb.toReal * sl.hQ.toReal) *
        (2 * Real.log sl.xiQLb.toReal + 6) ^ 2 * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤
        sl.es1Ub.toReal := by
      have hlog0 : 0 ≤ 2 * Real.log sl.xiQLb.toReal + 6 := by linarith [Real.log_nonneg hxi1]
      have hlog_ub : (2 * Real.log sl.xiQLb.toReal + 6) ^ 2 ≤
          (sciPowUb (((sn 2 0).mul sl.xiQLogUb).add (sn 6 0)) 2).toReal := by
        have h1 : 2 * Real.log sl.xiQLb.toReal + 6 ≤ (((sn 2 0).mul sl.xiQLogUb).add (sn 6 0)).toReal := by
          rw [SciProofs.add_toReal, SciProofs.mul_toReal,
            show (sn 2 0).toReal = 2 by simp [SciNat.toReal],
            show (sn 6 0).toReal = 6 by simp [SciNat.toReal]]
          linarith
        exact (pow_le_pow_left₀ hlog0 h1 2).trans (sciPowUb_sound _ 2)
      have hm1 : (1 / 16 : ℝ) * min (sl.cntUb.toReal * sl.xiQLb.toReal ^ 2) (sl.sqUb.toReal * sl.hQ.toReal) ≤
          ((sn 625 4).mul sl.s3cUb).toReal := by
        rw [SciProofs.mul_toReal, show (sn 625 4).toReal = 1 / 16 by unfold SciNat.toReal; norm_num]
        exact mul_le_mul_of_nonneg_left hs3c_le (by norm_num)
      have hble := SciProofs.ble_sound hes1
      rw [SciProofs.mul_toReal ((sn 625 4).mul sl.s3cUb), SciProofs.mul_toReal (sciPowUb _ 2), ← mul_assoc] at hble
      exact (mul_le_mul (mul_le_mul hm1 hlog_ub (sq_nonneg _) (SciNat.toReal_nonneg _)) hepd hepd0
        (mul_nonneg (SciNat.toReal_nonneg _) (SciNat.toReal_nonneg _))).trans hble
    have hf0_nn : 0 ≤ (1 / 2 : ℝ) * Real.log (sl.xiQLb.toReal ^ 2) + BuchstabSwitching.alpha0 +
        BuchstabSwitching.C_F0 / sl.xiQLb.toReal ^ 2 := by
      have hlog2 : Real.log (sl.xiQLb.toReal ^ 2) = 2 * Real.log sl.xiQLb.toReal := by
        rw [Real.log_pow]; ring
      have ha0 : 0 ≤ BuchstabSwitching.alpha0 := by linarith [alpha0_ge_63518]
      have hcf : BuchstabSwitching.C_F0 = (78 / 100 : ℝ) := rfl
      rw [hlog2, hcf]; positivity [Real.log_nonneg hxi1]
    have hf0_le : (1 / 2 : ℝ) * Real.log (sl.xiQLb.toReal ^ 2) + BuchstabSwitching.alpha0 +
        BuchstabSwitching.C_F0 / sl.xiQLb.toReal ^ 2 ≤ sl.f0Ub.toReal := by
      have hlog2 : Real.log (sl.xiQLb.toReal ^ 2) = 2 * Real.log sl.xiQLb.toReal := by
        rw [Real.log_pow]; ring
      have hcf : BuchstabSwitching.C_F0 = (78 / 100 : ℝ) := rfl
      have hdiv := divUbSig_le (sn 78 2) (sl.xiQLb.mul sl.xiQLb) 24
      rw [SciProofs.mul_toReal, ← sq, show (sn 78 2).toReal = (78 / 100 : ℝ) by unfold SciNat.toReal; norm_num] at hdiv
      have hble := SciProofs.ble_sound hf0; rw [SciProofs.add_toReal, SciProofs.add_toReal,
        show (sn 636 3).toReal = (636 / 1000 : ℝ) by unfold SciNat.toReal; norm_num] at hble
      rw [hlog2, hcf]; linarith [BuchstabSwitching.alpha0_le_636_div_1000]
    have hH_nn : 0 ≤ BuchstabSwitching.H_tilde := BuchstabSwitching.H_tilde_nonneg
    have hH_le : (BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (sl.xiQLb.toReal ^ 2) +
        BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / sl.xiQLb.toReal ^ 2)) ^ 3 ≤
        (sciPowUb ((sn 13 1).mul sl.f0Ub) 3).toReal := by
      have hm : BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (sl.xiQLb.toReal ^ 2) +
          BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / sl.xiQLb.toReal ^ 2) ≤
          ((sn 13 1).mul sl.f0Ub).toReal := by
        rw [SciProofs.mul_toReal, show (sn 13 1).toReal = (13 / 10 : ℝ) by unfold SciNat.toReal; norm_num]
        exact mul_le_mul BuchstabSwitching.H_tilde_le_cert hf0_le hf0_nn (by norm_num)
      exact (pow_le_pow_left₀ (mul_nonneg hH_nn hf0_nn) hm 3).trans (sciPowUb_sound _ 3)
    have hnum_le : (1 / 16 : ℝ) * min (sl.cntUb.toReal * sl.xiQLb.toReal ^ 2) (sl.sqUb.toReal * sl.hQ.toReal) *
          (2 * Real.log sl.xiQLb.toReal + 6) ^ 2 * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) +
        sl.cntUb.toReal * (1 + (BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (sl.xiQLb.toReal ^ 2) +
          BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / sl.xiQLb.toReal ^ 2)) ^ 3) *
          BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤
        (sl.es1Ub.add ((sl.cntUb.mul ((sn 1 0).add (sciPowUb ((sn 13 1).mul sl.f0Ub) 3))).mul epdUb)).toReal := by
      rw [SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal, SciProofs.add_toReal,
        show (sn 1 0).toReal = 1 by simp [SciNat.toReal]]
      have h2 := mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add le_rfl hH_le) (SciNat.toReal_nonneg sl.cntUb))
        hepd hepd0 (mul_nonneg (SciNat.toReal_nonneg sl.cntUb) (add_nonneg zero_le_one (SciNat.toReal_nonneg _)))
      linarith
    exact ((div_le_div_of_nonneg_right hnum_le hv_pos.le).trans (divUbSig_le _ _ 24)).trans (SciProofs.ble_sound hesl)

end SelbergSlice2c

section SquareAndMaster2c

/-- Unified Regime `2c` slice witness checker (`EvenBonf` or `Selberg`). -/
def checkSlice2cWitness (c : BuchstabSwitching.SlabCert) (zLogLo zLogUb epdUb vFullLb : SciNat)
    (sl : Slice2cWitness) : Bool :=
  (if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.logQ0Lb sl.logQ0Ub else true) &&
  (if pExact < sl.q1 then checkLogNat sl.q1 sl.logQ1Lb sl.logQ1Ub else true) &&
  checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb &&
  (if sl.isSelberg then checkSelberg2c c zLogLo zLogUb epdUb vFullLb sl
   else checkEvenBonf2c c zLogLo zLogUb epdUb vFullLb sl)

lemma checkSlice2cWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLo zLogUb epdUb vFullLb : SciNat} {sl : Slice2cWitness}
    (hcz : c.z ≤ sl.q0) (hqy : sl.q1 ≤ c.y)
    (hepd0 : 0 ≤ BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ))
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (hv_le : vFullLb.toReal ≤ External.VN 2 c.z)
    (h : checkSlice2cWitness c zLogLo zLogUb epdUb vFullLb sl = true) :
    ∃ s : External.SliceEngine2c c (c.X_lo : ℝ) sl.q0 sl.q1,
      s.mSl ≤ sl.mSl.toReal ∧ s.eSl consts.li2 ≤ sl.eSl.toReal := by
  unfold checkSlice2cWitness at h; simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hl0, hl1⟩, hbd⟩, hsub⟩
  have hLog0 : 27000 ≤ sl.q0 → sl.logQ0Lb.toReal ≤ Real.log (sl.q0 : ℝ) ∧ Real.log (sl.q0 : ℝ) ≤ sl.logQ0Ub.toReal :=
    fun h27 => checkLogNat_sound consts (by simpa [pExact, h27] using hl0)
  have hLog1 : 27000 < sl.q1 → sl.logQ1Lb.toReal ≤ Real.log (sl.q1 : ℝ) ∧ Real.log (sl.q1 : ℝ) ≤ sl.logQ1Ub.toReal :=
    fun h27 => checkLogNat_sound consts (by simpa [pExact, h27] using hl1)
  have hsc := checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hLog0 hLog1 hbd
  have hsq : ∑ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sl.sqUb.toReal := by
    rw [max_eq_right hcz, min_eq_right hqy]; exact hsc.1
  have hcnt : (((Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime).card : ℝ) ≤ sl.cntUb.toReal := by
    rw [max_eq_right hcz, min_eq_right hqy]; exact hsc.2
  split_ifs at hsub
  · exact selberg2c_sound consts hMert hepd0 hepd hv_pos hv_le hsq hcnt hsub
  · exact evenBonf2c_sound consts hGRH hCls hMert hepd hv_pos hv_le hsq hcnt hsub

/-- Regime `2c` prime-square witness checker (`SquareEngine2c`). -/
def checkSquare2cWitness (c : BuchstabSwitching.SlabCert) (w : Slab2cWitness) : Bool :=
  let sq := w.square; let qEnd := min c.y (sq.qSq + 1)
  let sOk :=
    if c.z ≤ pExact then
      ((exactInvMulPredSumUb c.z (min qEnd pExact) 24).add
        (if pExact < qEnd then divUbSig (sn 1 0) (SciNat.ofNat (pExact - 1)) 24 else (sn 0 0))).ble sq.sQ2Ub
    else (divUbSig (sn 1 0) (SciNat.ofNat (c.z - 1)) 24).ble sq.sQ2Ub
  let tailQ2 := if c.y ≤ sq.qSq + 1 then (sn 0 0) else divUbSig w.xHiLogUb (SciNat.ofNat sq.qSq) 24
  let innerUb := sq.sQ2Ub.add ((sq.cntLoUb.mul w.epdUb).add tailQ2)
  decide (1 ≤ sq.qSq) && decide (sq.qSq ^ 4 ≤ c.X_lo) && sOk &&
  (if pExact < qEnd then checkLogNat qEnd sq.logEndLb sq.logEndUb else true) &&
  checkSlice2abOr2cBounds c.z qEnd w.zLogLb w.zLogUb sq.logEndLb sq.logEndUb (sn 1000 0) sq.cntLoUb &&
  innerUb.ble (sq.errQ2Ub.mul (sn 2 0)) &&
  (divUbSig sq.errQ2Ub w.vFullLb 24).ble w.errQ2NormUb

lemma checkSquare2cWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {w : Slab2cWitness}
    (hz2 : 2 ≤ c.z)
    (hzLog : 27000 ≤ c.z → w.zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ w.zLogUb.toReal)
    (hlogHi : Real.log (c.X_hi : ℝ) ≤ w.xHiLogUb.toReal)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ w.epdUb.toReal)
    (hv_pos : 0 < w.vFullLb.toReal) (hv_le : w.vFullLb.toReal ≤ External.VN 2 c.z)
    (h : checkSquare2cWitness c w = true) :
    ∃ q2 : External.SquareEngine2c c (c.X_lo : ℝ),
      q2.errQ2 consts.li2 (c.X_hi : ℝ) ≤ w.errQ2NormUb.toReal := by
  unfold checkSquare2cWitness at h; dsimp only at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hq1, hq4⟩, hsOk⟩, hlEnd⟩, hcnt⟩, herr⟩, hnorm⟩
  set sq := w.square; set qEnd := min c.y (sq.qSq + 1)
  have hq_rt : ((sq.qSq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast ((show (sq.qSq ^ 2) ^ 2 = sq.qSq ^ 4 by ring).symm ▸ hq4 : (sq.qSq ^ 2) ^ 2 ≤ c.X_lo)
  have hs_q2 : ∑ q ∈ (Finset.Ico c.z qEnd).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤ sq.sQ2Ub.toReal := by
    by_cases hzp : c.z ≤ pExact
    · simp only [hzp, ↓reduceIte] at hsOk
      have hsplit := BuchstabSwitching.sum_inv_mul_pred_split_le c.z qEnd pExact hz2 (by decide)
      have hex := sum_inv_mul_pred_le_exact (q0 := c.z) (q1 := min qEnd pExact) (min_le_right _ _) 24
      have htail : (if pExact < qEnd then 1 / ((pExact : ℝ) - 1) else 0) ≤
          (if pExact < qEnd then divUbSig (sn 1 0) (SciNat.ofNat (pExact - 1)) 24 else (sn 0 0)).toReal := by
        split_ifs with hlt
        · have hd := divUbSig_le (sn 1 0) (SciNat.ofNat (pExact - 1)) 24
          rw [SciProofs.ofNat_toReal, Nat.cast_sub (by decide : 1 ≤ pExact)] at hd
          simpa [SciNat.toReal] using hd
        · simp [SciNat.toReal]
      have hble := SciProofs.ble_sound hsOk; rw [SciProofs.add_toReal] at hble; unfold pExact at hsplit hex htail hble; linarith
    · simp only [hzp, ↓reduceIte] at hsOk
      have hd := divUbSig_le (sn 1 0) (SciNat.ofNat (c.z - 1)) 24
      rw [SciProofs.ofNat_toReal, Nat.cast_sub (by omega : 1 ≤ c.z)] at hd
      have hle := BuchstabSwitching.sum_Ico_primes_inv_mul_pred_le c.z qEnd hz2
      have h1 : (sn 1 0).toReal = 1 := by simp [SciNat.toReal]
      rw [h1] at hd; exact hle.trans (hd.trans (SciProofs.ble_sound hsOk))
  have hLog1 : 27000 < qEnd → sq.logEndLb.toReal ≤ Real.log (qEnd : ℝ) ∧ Real.log (qEnd : ℝ) ≤ sq.logEndUb.toReal :=
    fun h27 => checkLogNat_sound consts (by simpa [pExact, h27] using hlEnd)
  let base : External.SquareEngine2ab c (c.X_lo : ℝ) :=
    ⟨sq.qSq, hq1, hq_rt, sq.sQ2Ub.toReal, hs_q2, sq.cntLoUb.toReal,
      (checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hzLog hLog1 hcnt).2⟩
  let q2 : External.SquareEngine2c c (c.X_lo : ℝ) := ⟨base, w.vFullLb.toReal, hv_pos, hv_le⟩
  refine ⟨q2, ?_⟩
  have htail_le : (if c.y ≤ sq.qSq + 1 then (0 : ℝ) else Real.log (c.X_hi : ℝ) / (sq.qSq : ℝ)) ≤
      (if c.y ≤ sq.qSq + 1 then (sn 0 0) else divUbSig w.xHiLogUb (SciNat.ofNat sq.qSq) 24).toReal := by
    split_ifs with hy
    · simp [SciNat.toReal]
    · exact (div_le_div_of_nonneg_right hlogHi (Nat.cast_nonneg _)).trans
        (by simpa [SciProofs.ofNat_toReal] using divUbSig_le w.xHiLogUb (SciNat.ofNat sq.qSq) 24)
  have herr_le := SciProofs.ble_sound herr
  rw [SciProofs.add_toReal, SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal,
    show (sn 2 0).toReal = 2 by simp [SciNat.toReal]] at herr_le
  have hbase_err : base.errQ2 consts.li2 (c.X_hi : ℝ) ≤ sq.errQ2Ub.toReal := by
    dsimp [External.SquareEngine2ab.errQ2, base]
    have := mul_le_mul_of_nonneg_left hepd sq.cntLoUb.toReal_nonneg; linarith
  exact (div_le_div_of_nonneg_right hbase_err hv_pos.le).trans ((divUbSig_le _ _ 24).trans (SciProofs.ble_sound hnorm))

private lemma sliceEngine2cCast {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} {q0 q1 q0' q1' : ℕ}
    (h0 : q0 = q0') (h1 : q1 = q1') (s : External.SliceEngine2c c X_lo q0 q1) :
    ∃ s' : External.SliceEngine2c c X_lo q0' q1', s'.mSl = s.mSl ∧ ∀ li2, s'.eSl li2 = s.eSl li2 := by
  subst h0; subst h1; exact ⟨s, rfl, fun _ => rfl⟩

/-- Complete computable witness verifier for Regime `2c` slabs (`66` slabs). -/
def checkSlab2cWitness (c : BuchstabSwitching.SlabCert) (w : Slab2cWitness) : Bool :=
  let sumMSl := sumSciList2c (·.mSl) w.slices
  let sumESl := sumSciList2c (·.eSl) w.slices
  c.valid && decide (4 * 10 ^ 18 ≤ c.X_lo) &&
  checkLogNat c.X_lo w.xLoLogLb w.xLoLogUb &&
  (ratLogBounds c.X_hi 1).1 && (ratLogBounds c.X_hi 1).2.2.ble w.xHiLogUb &&
  (if pExact ≤ c.z then checkLogNat c.z w.zLogLb w.zLogUb else true) &&
  checkEpdUb c.X_lo w.xLoLogLb w.xLoLogUb w.epdUb &&
  decide (0 < w.vFullLb.m) && checkVFullLb2c c.z w.zLogLb w.zLogUb w.vFullLb &&
  checkLower2cWitness c w.epdUb w.vFullLb w.lower &&
  checkSliceChain2c c.z c.y w.slices &&
  w.slices.all (checkSlice2cWitness c w.zLogLb w.zLogUb w.epdUb w.vFullLb) &&
  checkSquare2cWitness c w &&
  ((SciNat.ofNat (2 * c.main_num)).add ((SciNat.ofNat c.den).mul sumMSl)).ble
    ((SciNat.ofNat (2 * c.den)).mul w.lower.ratLb) &&
  ((((SciNat.ofNat 2).mul (w.lower.remANormUb.add w.errQ2NormUb)).add sumESl).mul
    (SciNat.ofNat c.den)).ble (SciNat.ofNat (2 * c.err_num))

/-- Master soundness theorem for `checkSlab2cWitness`: produces `Regime2cSlabBridge c`
via `Regime2cSlabBridge.of_sieveEngines`. -/
theorem checkSlab2cWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {w : Slab2cWitness}
    (h : checkSlab2cWitness c w = true) :
    External.Regime2cSlabBridge c := by
  unfold checkSlab2cWitness at h; dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hval, hX4⟩, hlogLo⟩, hlogHi_ok⟩, hlogHi_ble⟩, hzLog⟩,
    hepd_chk⟩, hvPos⟩, hvChk⟩, hlo_chk⟩, hchain⟩, hslices⟩, hsq⟩, hmain⟩, herr⟩
  have hval_s := BuchstabSwitching.SlabCert.valid_sound hval
  have hden_pos : 0 < c.den := by
    have hnet : (0 : ℚ) < (c.net_num : ℚ) / (c.den : ℚ) := hval_s.2.2.2.2.2.1
    by_contra h0; simp [show c.den = 0 by omega] at hnet
  have hden_real : (0 : ℝ) < (c.den : ℝ) := by exact_mod_cast hden_pos
  have hlogXlo := checkLogNat_sound consts hlogLo
  have hlogXhi : Real.log (c.X_hi : ℝ) ≤ w.xHiLogUb.toReal := by
    simpa using (ratLogBounds_sound consts hlogHi_ok).2.trans (SciProofs.ble_sound hlogHi_ble)
  have hzLog_27 : 27000 ≤ c.z → w.zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ w.zLogUb.toReal :=
    fun h27 => checkLogNat_sound consts (by simpa [pExact, h27] using hzLog)
  have hepd0 : 0 ≤ BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) :=
    BuchstabSwitching.epdNormFn_nonneg_of_premises hGRH hCls (by exact_mod_cast hX4) le_rfl
  have hepd := checkEpdUb_sound consts hlogXlo hepd_chk
  have hv_pos : 0 < w.vFullLb.toReal := by unfold SciNat.toReal; exact div_pos (by exact_mod_cast hvPos) (by positivity)
  have hv_le := checkVFullLb2c_sound consts hMert (fun h27 => hzLog_27 h27.le) hvChk
  obtain ⟨lo_eng, hlo_sa, hlo_rem⟩ := lower2c_sound consts hGRH hCls hMert hepd hv_pos hv_le hlo_chk
  obtain ⟨q2_eng, hq2_err⟩ := checkSquare2cWitness_sound consts hGRH hCls hMert hval_s.2.1 hzLog_27
    hlogXhi hepd hv_pos hv_le hsq
  have hsl_mem := List.all_eq_true.mp hslices
  have hcb := checkSliceChain2c_bounds w.slices c.z c.y hchain
  have hcast := checkSliceChain2c_castSucc w.slices c.z c.y hchain
  have hslice_ex : ∀ i : Fin w.slices.length,
      ∃ s' : External.SliceEngine2c c (c.X_lo : ℝ) (bptsOfSlices2c c.z w.slices i.castSucc)
        (bptsOfSlices2c c.z w.slices i.succ),
        s'.mSl ≤ w.slices[i].mSl.toReal ∧ s'.eSl consts.li2 ≤ w.slices[i].eSl.toReal := by
    intro i; have hbi := hcb i
    obtain ⟨s0, hm0, he0⟩ := checkSlice2cWitness_sound consts hGRH hCls hMert hbi.1 hbi.2.2 hepd0 hepd
      hv_pos hv_le (hsl_mem w.slices[i] (List.getElem_mem i.2))
    obtain ⟨s', hm', he'⟩ := sliceEngine2cCast (hcast i).symm (bptsOfSlices2c_succ c.z w.slices i).symm s0
    exact ⟨s', hm'.trans_le hm0, (he' consts.li2).trans_le he0⟩
  let sl_eng := fun i : Fin w.slices.length => (hslice_ex i).choose
  have hm_sum := sum_fin_le_sumSciList2c (·.mSl) w.slices (fun i => (sl_eng i).mSl) fun i => (hslice_ex i).choose_spec.1
  have he_sum := sum_fin_le_sumSciList2c (·.eSl) w.slices (fun i => (sl_eng i).eSl consts.li2)
    fun i => (hslice_ex i).choose_spec.2
  have hmain_sci := SciProofs.ble_sound hmain
  rw [SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.mul_toReal, SciProofs.ofNat_toReal,
    SciProofs.ofNat_toReal, SciProofs.ofNat_toReal] at hmain_sci
  have hc_main : (c.main_num : ℝ) = (c.main_lb : ℝ) * (c.den : ℝ) := by
    simp only [BuchstabSwitching.SlabCert.main_lb]; push_cast; field_simp [hden_real.ne']
  have hmain_div : 2 * (c.main_lb : ℝ) + (sumSciList2c (·.mSl) w.slices).toReal ≤ 2 * w.lower.ratLb.toReal := by
    push_cast at hmain_sci; rw [hc_main] at hmain_sci
    refine le_of_mul_le_mul_left ?_ hden_real; nlinarith
  have hmain_le : (c.main_lb : ℝ) ≤ lo_eng.saNorm - (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).mSl := by
    linarith
  have herr_sci := SciProofs.ble_sound herr
  rw [SciProofs.mul_toReal, SciProofs.add_toReal, SciProofs.mul_toReal, SciProofs.add_toReal,
    SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, SciProofs.ofNat_toReal] at herr_sci
  have hc_err : (c.err_num : ℝ) = (c.err_ub : ℝ) * (c.den : ℝ) := by
    simp only [BuchstabSwitching.SlabCert.err_ub]; push_cast; field_simp [hden_real.ne']
  have herr_div : 2 * (w.lower.remANormUb.toReal + w.errQ2NormUb.toReal) +
      (sumSciList2c (·.eSl) w.slices).toReal ≤ 2 * (c.err_ub : ℝ) := by
    push_cast at herr_sci; rw [hc_err] at herr_sci
    refine le_of_mul_le_mul_right ?_ hden_real; nlinarith
  have herr_le : lo_eng.remANorm consts.li2 + (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).eSl consts.li2 +
      q2_eng.errQ2 consts.li2 (c.X_hi : ℝ) ≤ (c.err_ub : ℝ) := by
    linarith
  exact External.Regime2cSlabBridge.of_sieveEngines hGRH hCls (by exact_mod_cast hX4) le_rfl le_rfl
    hval_s.2.1 hval_s.2.2.1 w.slices.length (bptsOfSlices2c c.z w.slices) (bptsOfSlices2c_zero c.z w.slices)
    (checkSliceChain2c_last w.slices c.z c.y hchain) (fun i => by rw [hcast i, bptsOfSlices2c_succ]; exact (hcb i).2.1)
    lo_eng sl_eng q2_eng hmain_le herr_le

end SquareAndMaster2c

end

end BuchstabSwitching.SieveInst
