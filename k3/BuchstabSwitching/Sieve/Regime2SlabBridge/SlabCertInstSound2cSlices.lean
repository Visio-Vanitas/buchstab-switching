import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cJFull
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cBrun
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2ab
import BuchstabSwitching.Certificates.Soundness
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Soundness of `checkSlab2cWitness` for Regime `2c` (`66` Slabs, Binary `Dyadic`)

Verifies `Slice2cWitness` (`Slice2cMode.evenBonf` for `zSub ≤ 27000` and `zSub = c.z`, and
`Slice2cMode.selberg` with `J_full` via `checkJFullLb2c_sound`), `SquareEngine2c`, and
`checkSlab2cWitness_sound`, producing `External.Regime2cSlabBridge c`.
-/

namespace BuchstabSwitching.SieveInst

section

section EvenBonfSlice2c

/-- Checker for `Slice2cMode.evenBonf` (`zSub ≤ 27000` or `zSub = c.z`). -/
def checkEvenBonf2c (c : BuchstabSwitching.SlabCert) (zLogLb zLogUb epdUb vFullLb : Dyadic)
    (q1 : ℕ) (sqUb cntUb mSl eSl : Dyadic)
    (zSub aQ mEv nD dMax : ℕ) (ip2 vSubUb gSubLb ratUb mRatUb c2Ub errUb : Dyadic)
    (tailW : Option MertensTailWitness) : Bool :=
  let baseOk :=
    (((cntUb.mulUb ((Dyadic.ofNat nD).add (ip2.add ratUb))).mulUb epdUb).ble (eSl.mulLb vFullLb)) &&
    (sqUb.mulUb mRatUb).ble mSl
  if zSub ≤ 27000 then
    let es := oddPrimeEntriesList zSub
    let ps := oddPrimesList zSub
    let q1e := es.take aQ
    let p2e := es.drop aQ
    let q1L := ps.take aQ
    let p2L := ps.drop aQ
    let k := 2 * mEv
    let expS1 := expUbDyadic (sumG1EntriesUb p2e)
    let ipOk := (expS1.1 && ((invPhiEntriesUb q1e).mulUb expS1.2).ble ip2) ||
      ((invPhiEntriesUb q1e).mulUb (let s := elemSymSums (elemSymInterval64 p2e k); s.2.1.add s.2.2.2)).ble ip2
    let ratOk := checkSliceRatAnalytic p2e mEv c2Ub gSubLb errUb ratUb || checkSliceRatExact p2e mEv ratUb
    baseOk && decide (zSub ≤ c.z) && decide (aQ ≤ ps.length) &&
    decide (q1L.prod * (p2L.reverse.take k).prod ≤ dMax) &&
    decide (((q1 - 1) * dMax) ^ 2 ≤ c.X_lo) &&
    decide (bonfCardNat aQ p2L.length k ≤ nD) &&
    ipOk && ratOk &&
    (exactProdOneSubInvPredUb 3 zSub).ble vSubUb &&
    (vSubUb.mulUb ratUb).ble (mRatUb.mulLb vFullLb)
  else if h : aQ < smallOddPrimes40.length then
    match tailW with
    | none => false
    | some tw =>
      let pMin := smallOddPrimes40[aQ]
      let k := 2 * mEv
      let expRes := expUbDyadic tw.s1Ub
      let errDen := (Dyadic.ofNat (Nat.factorial (k + 1))).mulLb gSubLb
      baseOk && decide (k < 16) && decide (zSub = c.z) && decide (pMin < c.z) &&
      decide ((smallOddPrimes40.take aQ).prod * c.z ^ k ≤ dMax) &&
      decide (((q1 - 1) * dMax) ^ 2 ≤ c.X_lo) &&
      checkMertensTailWithLogs pMin c.z dyZero dyZero zLogLb zLogUb tw &&
      expRes.1 && decide (0 < gSubLb.m) && gSubLb.ble tw.gLb &&
      ((sumPowDivFactUb (Dyadic.ofNat tw.piUb) k).mulPow2 aQ).ble (Dyadic.ofNat nD) &&
      ((invPhiEntriesUb (smallOddEntries40.take aQ)).mulUb expRes.2).ble ip2 &&
      (tw.s1Ub.powUb (k + 1)).ble (errUb.mulLb errDen) &&
      (dyOne.add errUb).ble ratUb && ratUb.ble mRatUb
  else false

lemma evenBonf2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLb zLogUb epdUb vFullLb : Dyadic}
    {q0 q1 : ℕ} {sqUb cntUb mSl eSl : Dyadic}
    {zSub aQ mEv nD dMax : ℕ} {ip2 vSubUb gSubLb ratUb mRatUb c2Ub errUb : Dyadic}
    {tailW : Option MertensTailWitness}
    (hzLog : 27000 < c.z → zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ zLogUb.toReal)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (hv_le : vFullLb.toReal ≤ External.VN 2 c.z)
    (hsq : ∑ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sqUb.toReal)
    (hcnt : (((Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime).card : ℝ) ≤ cntUb.toReal)
    (h : checkEvenBonf2c c zLogLb zLogUb epdUb vFullLb q1 sqUb cntUb mSl eSl
      zSub aQ mEv nD dMax ip2 vSubUb gSubLb ratUb mRatUb c2Ub errUb tailW = true) :
    ∃ s : External.SliceEngine2c c (c.X_lo : ℝ) q0 q1,
      s.mSl ≤ mSl.toReal ∧ s.eSl consts.li2 ≤ eSl.toReal := by
  unfold checkEvenBonf2c at h
  by_cases hz_sm : zSub ≤ 27000
  · simp only [hz_sm, ↓reduceIte] at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨h1_9, hmrat⟩
    rcases (Bool.and_eq_true _ _).mp h1_9 with ⟨h1_8, hvsub⟩
    rcases (Bool.and_eq_true _ _).mp h1_8 with ⟨h1_7, hrat_or⟩
    rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, hip_or⟩
    rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hnd_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hqd_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hd_prod_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, ha_le_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hbase, hz_c_b⟩
    rcases (Bool.and_eq_true _ _).mp hbase with ⟨hesl, hmsl⟩
    have hz_c := decide_eq_true_eq.mp hz_c_b
    have ha_le := decide_eq_true_eq.mp ha_le_b
    have hd_prod := decide_eq_true_eq.mp hd_prod_b
    have hqd := decide_eq_true_eq.mp hqd_b
    have hnd_n := decide_eq_true_eq.mp hnd_b
    rw [bonfCardNat_eq] at hnd_n
    set es := oddPrimeEntriesList zSub; set ps := oddPrimesList zSub
    set q1e := es.take aQ; set p2e := es.drop aQ
    set q1L := ps.take aQ; set p2L := ps.drop aQ; set k := 2 * mEv
    have hq1_map : q1e.map PrimeLeafEntry.p = q1L := List.map_take
    have hp2_map : p2e.map PrimeLeafEntry.p = p2L := List.map_drop
    have hps_lt := oddPrimesList_pairwise_lt zSub; have hps_pr := oddPrimesList_props zSub
    have htd : (q1L ++ p2L).Pairwise (· < ·) := by dsimp only [q1L, p2L]; rw [List.take_append_drop]; exact hps_lt
    have hpair := List.pairwise_append.mp htd
    have hQ_nd : (q1e.map PrimeLeafEntry.p).Nodup := hq1_map ▸ pairwise_lt_nodup hpair.1
    have hP_lt : (p2e.map PrimeLeafEntry.p).Pairwise (· < ·) := hp2_map ▸ hpair.2.1
    have hP_nd : (p2e.map PrimeLeafEntry.p).Nodup := pairwise_lt_nodup hP_lt
    have hQ_ok : ∀ e ∈ q1e, checkPrimeLeafEntry e = true := fun e he =>
      (oddPrimeEntriesList_ok zSub e (List.mem_of_mem_take he)).1
    have hP_ok : ∀ e ∈ p2e, checkPrimeLeafEntry e = true ∧ e.p.Prime := fun e he =>
      let ho := oddPrimeEntriesList_ok zSub e (List.mem_of_mem_drop he); ⟨ho.1, ho.2.1⟩
    have hq1_pr : ∀ p ∈ q1L.toFinset, p.Prime ∧ 2 < p := fun p hp =>
      let hp' := hps_pr p (List.mem_of_mem_take (List.mem_toFinset.mp hp)); ⟨hp'.1, hp'.2.1⟩
    have hp2_pr : ∀ p ∈ p2L.toFinset, p.Prime ∧ 2 < p := fun p hp =>
      let hp' := hps_pr p (List.mem_of_mem_drop (List.mem_toFinset.mp hp)); ⟨hp'.1, hp'.2.1⟩
    have hip2 : ∑ d ∈ BuchstabSwitching.bonfDivisors q1L.toFinset p2L.toFinset k,
        BuchstabSwitching.gTot d ≤ ip2.toReal := by
      have hphi := hq1_map ▸ invPhiEntriesUb_sound hQ_nd hQ_ok
      rcases (Bool.or_eq_true _ _).mp hip_or with hE | hDP
      · rcases (Bool.and_eq_true _ _).mp hE with ⟨hE1, hEble⟩
        have hS1 := hp2_map ▸ sumG1EntriesUb_sound hP_nd hP_ok
        have hbonf := BuchstabSwitching.sum_bonfDivisors_gTot_le_exp (take_drop_disjoint hps_lt aQ)
          hq1_pr hp2_pr k hS1
        exact hbonf.trans ((mul_le_mul hphi (expUbDyadic_sound hE1).1 (Real.exp_pos _).le
          (invPhiEntriesUb q1e).toReal_nonneg).trans ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hEble)))
      · rw [sum_bonfDivisors_gTot_eq (take_drop_disjoint hps_lt aQ) hq1_pr hp2_pr]
        have hsum := hp2_map ▸ elemSymSums_interval64_sound hP_nd hP_ok k
        exact (mul_le_mul hphi hsum.2.2 (Finset.sum_nonneg fun _ _ =>
          BuchstabSwitching.elemSym_nonneg (fun _ _ => BuchstabSwitching.gTot_nonneg _) _)
          (invPhiEntriesUb q1e).toReal_nonneg).trans ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hDP))
    have hrat_s : BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2L.toFinset k ≤ ratUb.toReal := by
      rw [← hp2_map]
      rcases (Bool.or_eq_true _ _).mp hrat_or with hAn | hEx
      · exact checkSliceRatAnalytic_sound hP_lt hP_ok hAn
      · exact checkSliceRatExact_sound hP_lt hP_ok hEx
    let spec : External.EvenBonfSliceSpec c (c.X_lo : ℝ) q0 q1 :=
      ⟨zSub, mEv, hz_c, q1L.toFinset, p2L.toFinset, take_drop_disjoint hps_lt aQ,
        by rw [take_drop_union, oddPrimesList_toFinset hz_sm], dMax,
        fun d hd => by exact_mod_cast (bonfDivisors_le_take_mul_rev_drop hps_lt
          (fun p hp => (hps_pr p hp).1.one_lt.le) aQ k d hd).trans hd_prod,
        q_mul_dMax_sqrt hqd, nD, ip2.toReal, ratUb.toReal, sqUb.toReal, cntUb.toReal,
        by exact_mod_cast (card_bonfDivisors_take_drop hps_lt (fun p hp => (hps_pr p hp).1) ha_le k).trans_le hnd_n,
        hip2, hrat_s, hsq, hcnt⟩
    have hm_rat : (External.VN 2 spec.z_sub / External.VN 2 c.z) * spec.rat_ub ≤ mRatUb.toReal := by
      have hv_s : External.VN 2 zSub ≤ vSubUb.toReal :=
        (VN_two_le_exactProdOneSubInvPredUb hz_sm).trans (Dyadic.ble_sound hvsub)
      have hnum : External.VN 2 zSub * ratUb.toReal ≤ (vSubUb.mulUb ratUb).toReal :=
        (mul_le_mul_of_nonneg_right hv_s ratUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
      rw [div_mul_eq_mul_div]
      exact Dyadic.div_le_of_ble_mulLb hnum (lt_of_lt_of_le hv_pos hv_le) hv_le hmrat
    refine ⟨External.SliceEngine2c.evenBonf spec vFullLb.toReal mRatUb.toReal hv_pos hv_le hm_rat, ?_, ?_⟩
    · dsimp [External.SliceEngine2c.mSl, spec]
      exact (Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hmsl)
    · dsimp [External.SliceEngine2c.eSl, spec]
      refine remNorm_le_of_ble (mul_nonneg cntUb.toReal_nonneg
        (add_nonneg (add_nonneg (Nat.cast_nonneg _) ip2.toReal_nonneg) ratUb.toReal_nonneg))
        ?_ hepd hv_pos hesl
      have hsum_eq : ((Dyadic.ofNat nD).add (ip2.add ratUb)).toReal = (nD : ℝ) + ip2.toReal + ratUb.toReal := by
        rw [Dyadic.add_toReal, Dyadic.add_toReal, Dyadic.ofNat_toReal, add_assoc]
      rw [← hsum_eq]; exact Dyadic.le_mulUb _ _
  · simp only [hz_sm, ↓reduceIte] at h
    by_cases ha_sm : aQ < smallOddPrimes40.length
    · simp only [ha_sm, ↓reduceDIte] at h
      cases tailW with
      | none => simp at h
      | some tw =>
        have ha : aQ < oddPrimesLt27000.length := lt_of_lt_of_le ha_sm smallOddPrimes40_len_le
        rw [smallOddPrimes40_getElem ha_sm, smallOddPrimes40_take ha_sm.le] at h
        rcases (Bool.and_eq_true _ _).mp h with ⟨h1_14, hmrat⟩
        rcases (Bool.and_eq_true _ _).mp h1_14 with ⟨h1_13, hrat_add⟩
        rcases (Bool.and_eq_true _ _).mp h1_13 with ⟨h1_12, herr_ble⟩
        rcases (Bool.and_eq_true _ _).mp h1_12 with ⟨h1_11, hip⟩
        rcases (Bool.and_eq_true _ _).mp h1_11 with ⟨h1_10, hnd_n⟩
        rcases (Bool.and_eq_true _ _).mp h1_10 with ⟨h1_9, hgLe⟩
        rcases (Bool.and_eq_true _ _).mp h1_9 with ⟨h1_8, hgPos_b⟩
        rcases (Bool.and_eq_true _ _).mp h1_8 with ⟨h1_7, hokE⟩
        rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, htw⟩
        rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hqd_b⟩
        rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hd_prod_b⟩
        rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hpz_b⟩
        rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hz_eq_b⟩
        rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hbase, hk16_b⟩
        rcases (Bool.and_eq_true _ _).mp hbase with ⟨hesl, hmsl⟩
        have hk16 : 2 * mEv < 16 := decide_eq_true_eq.mp hk16_b
        have hz_eq : zSub = c.z := decide_eq_true_eq.mp hz_eq_b
        have hpz : oddPrimesLt27000[aQ] < c.z := decide_eq_true_eq.mp hpz_b
        have hd_prod := decide_eq_true_eq.mp hd_prod_b
        have hqd := decide_eq_true_eq.mp hqd_b
        have hgPos : 0 < gSubLb.m := decide_eq_true_eq.mp hgPos_b
        set pMin := oddPrimesLt27000[aQ]
        have hpMin_mem := mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)
        have hpa_lt : (if aQ = 0 then 2 else oddPrimesLt27000[aQ - 1]'(by omega)) < pMin := by
          split_ifs with ha0
          · exact lt_of_lt_of_le (by norm_num) hpMin_mem.2.2
          · exact (List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt)
              (aQ - 1) aQ (by omega) ha (by omega)
        have hsplit := oddPrimesLt27000_split_props ha hpz.le hpa_lt le_rfl
        set Q₁ : Finset ℕ := (oddPrimesLt27000.take aQ).toFinset
        set P₂ : Finset ℕ := (Finset.Ico pMin c.z).filter Nat.Prime
        have hm := checkMertensTailWithLogs_sound consts hGRH hCls hMert
          (fun h27 => absurd h27 (by linarith [hpMin_mem.1])) hzLog htw
        have hQ₁_pr : ∀ p ∈ Q₁, p.Prime ∧ 2 < p := fun p hp =>
          ⟨(hsplit.2.2.2.1 p hp).1, (hsplit.2.2.2.1 p hp).2.1⟩
        have hP₂_pr : ∀ p ∈ P₂, p.Prime ∧ 2 < p := fun p hp =>
          ⟨(hsplit.2.2.2.2 p hp).1, by have := hpMin_mem.2.2; have := (hsplit.2.2.2.2 p hp).2.2; omega⟩
        have hnd_real : ((BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * mEv)).card : ℝ) ≤ (nD : ℝ) := by
          have hcard := BuchstabSwitching.card_bonfDivisors_le_factorial_sum hsplit.1
            (fun p hp => (hQ₁_pr p hp).1) (fun p hp => (hP₂_pr p hp).1) (2 * mEv) hm.2.2.1
          rw [hsplit.2.2.1] at hcard
          have hble := Dyadic.ble_sound hnd_n
          rw [Dyadic.mulPow2_toReal, Dyadic.ofNat_toReal] at hble
          have h1 := mul_le_mul_of_nonneg_right
            (sumPowDivFactUb_sound (Dyadic.ofNat tw.piUb) hk16) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ aQ)
          rw [Dyadic.ofNat_toReal] at h1; linarith
        have hq_nd : (oddPrimesLt27000.take aQ).Nodup := oddPrimesLt27000_nodup.take
        have hip2_le : ∑ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * mEv),
            BuchstabSwitching.gTot d ≤ ip2.toReal := by
          have hbonf := BuchstabSwitching.sum_bonfDivisors_gTot_le_exp hsplit.1 hQ₁_pr hP₂_pr (2 * mEv) hm.1
          have hq_map := smallOddEntries40_take_primes ha_sm.le
          have hqe_nd : ((smallOddEntries40.take aQ).map PrimeLeafEntry.p).Nodup := hq_map.symm ▸ hq_nd
          have hqe_ok : ∀ e ∈ smallOddEntries40.take aQ, checkPrimeLeafEntry e = true :=
            fun e he => smallOddEntries40_ok e (List.mem_of_mem_take he)
          have hphi : ∏ p ∈ Q₁, (p : ℝ) / ((p : ℝ) - 1) ≤
              (invPhiEntriesUb (smallOddEntries40.take aQ)).toReal := by
            dsimp only [Q₁]; rw [← hq_map]; exact invPhiEntriesUb_sound hqe_nd hqe_ok
          exact hbonf.trans ((mul_le_mul hphi (expUbDyadic_sound hokE).1 (Real.exp_pos _).le
            (invPhiEntriesUb _).toReal_nonneg).trans ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hip)))
        have hrat_s : BuchstabSwitching.RTrunc BuchstabSwitching.gTot P₂ (2 * mEv) ≤ ratUb.toReal := by
          have hgPos' : 0 < gSubLb.toReal := Dyadic.toReal_pos_of_m hgPos
          have hR := BuchstabSwitching.analytic_bonf_RTrunc_even_ub hP₂_pr mEv hgPos'
            ((Dyadic.ble_sound hgLe).trans (hm.2.2.2 hpMin_mem.2.2)) hm.1
          have hden_le : ((Dyadic.ofNat (Nat.factorial (2 * mEv + 1))).mulLb gSubLb).toReal ≤
              (Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal :=
            (Dyadic.mulLb_le _ _).trans (by rw [Dyadic.ofNat_toReal])
          have herr_le : tw.s1Ub.toReal ^ (2 * mEv + 1) /
              ((Nat.factorial (2 * mEv + 1) : ℝ) * gSubLb.toReal) ≤ errUb.toReal :=
            Dyadic.div_le_of_ble_mulLb (Dyadic.powUb_sound tw.s1Ub (2 * mEv + 1))
              (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hgPos') hden_le herr_ble
          have hble := Dyadic.ble_sound hrat_add
          rw [Dyadic.add_toReal, dyOne_toReal] at hble
          linarith
        let spec : External.EvenBonfSliceSpec c (c.X_lo : ℝ) q0 q1 :=
          ⟨zSub, mEv, hz_eq.le, Q₁, P₂, hsplit.1, hz_eq ▸ hsplit.2.1, dMax, fun d hd => by
            have hbd := BuchstabSwitching.bonfDivisors_le_prod_mul_pow_of_pos (by omega : 1 ≤ c.z)
              (fun p hp => (hQ₁_pr p hp).1.pos)
              (fun p hp => (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le) hd
            have hqprod : ∏ p ∈ Q₁, p = (oddPrimesLt27000.take aQ).prod := by
              simpa [Q₁] using List.prod_toFinset (fun x : ℕ => x) hq_nd
            exact_mod_cast (hqprod ▸ hbd).trans hd_prod,
            q_mul_dMax_sqrt hqd, nD, ip2.toReal, ratUb.toReal, sqUb.toReal, cntUb.toReal,
            hnd_real, hip2_le, hrat_s, hsq, hcnt⟩
        have hm_rat : (External.VN 2 spec.z_sub / External.VN 2 c.z) * spec.rat_ub ≤ mRatUb.toReal := by
          have hv_z : 0 < External.VN 2 c.z := lt_of_lt_of_le hv_pos hv_le
          dsimp [spec]; rw [hz_eq, div_self hv_z.ne', one_mul]; exact Dyadic.ble_sound hmrat
        refine ⟨External.SliceEngine2c.evenBonf spec vFullLb.toReal mRatUb.toReal hv_pos hv_le hm_rat, ?_, ?_⟩
        · dsimp [External.SliceEngine2c.mSl, spec]
          exact (Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hmsl)
        · dsimp [External.SliceEngine2c.eSl, spec]
          refine remNorm_le_of_ble (mul_nonneg cntUb.toReal_nonneg
            (add_nonneg (add_nonneg (Nat.cast_nonneg _) ip2.toReal_nonneg) ratUb.toReal_nonneg))
            ?_ hepd hv_pos hesl
          have hsum_eq : ((Dyadic.ofNat nD).add (ip2.add ratUb)).toReal = (nD : ℝ) + ip2.toReal + ratUb.toReal := by
            rw [Dyadic.add_toReal, Dyadic.add_toReal, Dyadic.ofNat_toReal, add_assoc]
          rw [← hsum_eq]; exact Dyadic.le_mulUb _ _
    · simp only [ha_sm, ↓reduceDIte] at h; simp at h

end EvenBonfSlice2c

section SelbergSlice2c

def dy78e2Ub : Dyadic := Dyadic.ofQ64 14388460377493450261
def dy13e1Ub : Dyadic := Dyadic.ofQ64 23980767295822417101

private lemma dy78e2_ok : 78 * q64Scale ≤ 14388460377493450261 * 100 := by native_decide
private lemma dy13e1_ok : 13 * q64Scale ≤ 23980767295822417101 * 10 := by native_decide

private lemma le_dy78e2Ub : (78 / 100 : ℝ) ≤ dy78e2Ub.toReal := by
  rw [dy78e2Ub, Dyadic.ofQ64_toReal, div_le_div_iff₀ (by norm_num) q64Scale_pos]
  exact_mod_cast dy78e2_ok

private lemma H_tilde_le_dy13e1Ub : BuchstabSwitching.H_tilde ≤ dy13e1Ub.toReal := by
  refine BuchstabSwitching.H_tilde_le_cert.trans ?_
  rw [dy13e1Ub, Dyadic.ofQ64_toReal, div_le_div_iff₀ (by norm_num) q64Scale_pos]
  exact_mod_cast dy13e1_ok

/-- Division-free binary witness checker for `Slice2cMode.selberg`. -/
def checkSelberg2c (c : BuchstabSwitching.SlabCert) (zLogLo zLogUb epdUb vFullLb : Dyadic)
    (q1 : ℕ) (sqUb cntUb mSl eSl : Dyadic)
    (hQ xiQLb xiQUb xiQLogLb xiQLogUb jfLb s3cUb es1Ub f0Ub invXiSq78Ub : Dyadic)
    (wXiLog : LogWitness) : Bool :=
  let s3cOk := (cntUb.mulUb (xiQLb.mulUb xiQLb)).ble s3cUb || (sqUb.mulUb hQ).ble s3cUb
  let es1Lhs := (s3cUb.divPow2Ub 4).mulUb
    ((((xiQLogUb.mulPow2 1).add (Dyadic.ofNat 6)).powUb 2).mulUb epdUb)
  let f0Lhs := xiQLogUb.add (a0UbDy.add invXiSq78Ub)
  let eNum := es1Ub.add ((cntUb.mulUb (dyOne.add ((dy13e1Ub.mulUb f0Ub).powUb 3))).mulUb epdUb)
  xiQLb.ble xiQUb &&
  ((Dyadic.ofNat (q1 - 1)).mulUb (xiQUb.mulUb xiQUb)).ble hQ &&
  (hQ.mulUb hQ).ble (Dyadic.ofNat c.X_lo) &&
  checkJFullLb2c c.z zLogLo zLogUb xiQLb xiQLogLb xiQLogUb jfLb wXiLog &&
  sqUb.ble (mSl.mulLb (vFullLb.mulLb jfLb)) &&
  s3cOk && es1Lhs.ble es1Ub &&
  dy78e2Ub.ble (invXiSq78Ub.mulLb (xiQLb.mulLb xiQLb)) &&
  f0Lhs.ble f0Ub &&
  eNum.ble (eSl.mulLb vFullLb)

lemma selberg2c_sound (consts : External.CertifiedConstants)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLo zLogUb epdUb vFullLb : Dyadic}
    {q0 q1 : ℕ} {sqUb cntUb mSl eSl : Dyadic}
    {hQ xiQLb xiQUb xiQLogLb xiQLogUb jfLb s3cUb es1Ub f0Ub invXiSq78Ub : Dyadic}
    {wXiLog : LogWitness}
    (hzL : zLogLo.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ zLogUb.toReal)
    (hepd0 : 0 ≤ BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ))
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (hv_le : vFullLb.toReal ≤ External.VN 2 c.z)
    (hsq : ∑ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sqUb.toReal)
    (hcnt : (((Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime).card : ℝ) ≤ cntUb.toReal)
    (h : checkSelberg2c c zLogLo zLogUb epdUb vFullLb q1 sqUb cntUb mSl eSl
      hQ xiQLb xiQUb xiQLogLb xiQLogUb jfLb s3cUb es1Ub f0Ub invXiSq78Ub wXiLog = true) :
    ∃ s : External.SliceEngine2c c (c.X_lo : ℝ) q0 q1,
      s.mSl ≤ mSl.toReal ∧ s.eSl consts.li2 ≤ eSl.toReal := by
  unfold checkSelberg2c at h; dsimp only at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨h1_9, hesl⟩
  rcases (Bool.and_eq_true _ _).mp h1_9 with ⟨h1_8, hf0⟩
  rcases (Bool.and_eq_true _ _).mp h1_8 with ⟨h1_7, hinv78⟩
  rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, hes1⟩
  rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hs3c⟩
  rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hmsl⟩
  rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hjf⟩
  rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hhsq⟩
  rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hxiU, hqxi⟩
  rcases checkJFullLb2c_sound consts hMert hzL hjf with ⟨_, hxi1, hjPos, hxiL, hjLe⟩
  have hqxi_s : ∀ q ∈ (Finset.Ico (max c.z q0) (min c.y q1)).filter Nat.Prime,
      (q : ℝ) * xiQLb.toReal ^ 2 ≤ hQ.toReal := by
    intro q hq
    have hq_lt : q < q1 := lt_of_lt_of_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2 (min_le_right _ _)
    have hsq_le : xiQLb.toReal ^ 2 ≤ (xiQUb.mulUb xiQUb).toReal := by
      rw [sq]
      exact (mul_le_mul (Dyadic.ble_sound hxiU) (Dyadic.ble_sound hxiU)
        xiQLb.toReal_nonneg xiQUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
    have h1 : (q : ℝ) * xiQLb.toReal ^ 2 ≤ ((q1 - 1 : ℕ) : ℝ) * (xiQUb.mulUb xiQUb).toReal :=
      mul_le_mul (by exact_mod_cast (by omega : q ≤ q1 - 1)) hsq_le (by positivity) (Nat.cast_nonneg _)
    have h2 : ((q1 - 1 : ℕ) : ℝ) * (xiQUb.mulUb xiQUb).toReal ≤
        ((Dyadic.ofNat (q1 - 1)).mulUb (xiQUb.mulUb xiQUb)).toReal := by
      rw [← Dyadic.ofNat_toReal]; exact Dyadic.le_mulUb _ _
    exact h1.trans (h2.trans (Dyadic.ble_sound hqxi))
  have hh_sqrt : hQ.toReal ≤ Real.sqrt (c.X_lo : ℝ) := by
    have hble := (Dyadic.le_mulUb hQ hQ).trans ((Dyadic.ble_sound hhsq).trans_eq (Dyadic.ofNat_toReal _))
    exact Real.le_sqrt_of_sq_le (by rw [sq]; exact hble)
  let spec : External.SelbergSliceSpec c (c.X_lo : ℝ) q0 q1 :=
    ⟨xiQLb.toReal, hQ.toReal, hxi1, hQ.toReal_nonneg, hqxi_s, hh_sqrt,
      sqUb.toReal, cntUb.toReal, jfLb.toReal, vFullLb.toReal, hsq, hcnt, hjPos, hjLe, hv_pos, hv_le⟩
  refine ⟨External.SliceEngine2c.selberg spec, ?_, ?_⟩
  · dsimp [External.SliceEngine2c.mSl, spec]
    exact Dyadic.div_le_of_ble_mulLb le_rfl (mul_pos hv_pos hjPos) (Dyadic.mulLb_le _ _) hmsl
  · dsimp [External.SliceEngine2c.eSl, spec]
    have hs3c_le : min (cntUb.toReal * xiQLb.toReal ^ 2) (sqUb.toReal * hQ.toReal) ≤ s3cUb.toReal := by
      rcases (Bool.or_eq_true _ _).mp hs3c with h1 | h2
      · have hsq_ub : xiQLb.toReal ^ 2 ≤ (xiQLb.mulUb xiQLb).toReal := by
          rw [sq]; exact Dyadic.le_mulUb _ _
        have hm := (mul_le_mul_of_nonneg_left hsq_ub cntUb.toReal_nonneg).trans
          ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound h1))
        exact (min_le_left _ _).trans hm
      · exact (min_le_right _ _).trans ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound h2))
    have hes1_le : (1 / 16 : ℝ) * min (cntUb.toReal * xiQLb.toReal ^ 2) (sqUb.toReal * hQ.toReal) *
        (2 * Real.log xiQLb.toReal + 6) ^ 2 * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤
        es1Ub.toReal := by
      have hlog0 : 0 ≤ 2 * Real.log xiQLb.toReal + 6 := by linarith [Real.log_nonneg hxi1]
      have hlog_ub : (2 * Real.log xiQLb.toReal + 6) ^ 2 ≤
          (((xiQLogUb.mulPow2 1).add (Dyadic.ofNat 6)).powUb 2).toReal := by
        have h1 : 2 * Real.log xiQLb.toReal + 6 ≤ ((xiQLogUb.mulPow2 1).add (Dyadic.ofNat 6)).toReal := by
          rw [Dyadic.add_toReal, Dyadic.mulPow2_toReal, pow_one, Dyadic.ofNat_toReal, Nat.cast_ofNat]
          linarith [hxiL.2]
        exact (pow_le_pow_left₀ hlog0 h1 2).trans (Dyadic.powUb_sound _ 2)
      have hm1 : (1 / 16 : ℝ) * min (cntUb.toReal * xiQLb.toReal ^ 2) (sqUb.toReal * hQ.toReal) ≤
          (s3cUb.divPow2Ub 4).toReal := by
        have hd := Dyadic.le_divPow2Ub s3cUb 4
        rw [show (2 : ℝ) ^ 4 = 16 by norm_num] at hd
        linarith
      have h2 := (mul_le_mul hlog_ub hepd hepd0 (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)
      have h3 := (mul_le_mul hm1 h2 (mul_nonneg (sq_nonneg _) hepd0) (Dyadic.toReal_nonneg _)).trans
        ((Dyadic.le_mulUb _ _).trans (Dyadic.ble_sound hes1))
      rwa [← mul_assoc] at h3
    have hf0_nn : 0 ≤ (1 / 2 : ℝ) * Real.log (xiQLb.toReal ^ 2) + BuchstabSwitching.alpha0 +
        BuchstabSwitching.C_F0 / xiQLb.toReal ^ 2 := by
      have hlog2 : Real.log (xiQLb.toReal ^ 2) = 2 * Real.log xiQLb.toReal := by rw [Real.log_pow]; ring
      have ha0 : 0 ≤ BuchstabSwitching.alpha0 := by linarith [alpha0_ge_63518]
      have hcf : BuchstabSwitching.C_F0 = (78 / 100 : ℝ) := rfl
      rw [hlog2, hcf]; positivity [Real.log_nonneg hxi1]
    have hf0_le : (1 / 2 : ℝ) * Real.log (xiQLb.toReal ^ 2) + BuchstabSwitching.alpha0 +
        BuchstabSwitching.C_F0 / xiQLb.toReal ^ 2 ≤ f0Ub.toReal := by
      have hlog2 : Real.log (xiQLb.toReal ^ 2) = 2 * Real.log xiQLb.toReal := by rw [Real.log_pow]; ring
      have hcf : BuchstabSwitching.C_F0 = (78 / 100 : ℝ) := rfl
      have h78 : (78 / 100 : ℝ) / xiQLb.toReal ^ 2 ≤ invXiSq78Ub.toReal :=
        Dyadic.div_le_of_ble_mulLb le_dy78e2Ub (by positivity)
          (by rw [sq]; exact Dyadic.mulLb_le _ _) hinv78
      have hble := Dyadic.ble_sound hf0
      rw [Dyadic.add_toReal, Dyadic.add_toReal] at hble
      rw [hlog2, hcf]; linarith [hxiL.2, le_a0UbDy, h78, hble]
    have hH_le : (BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (xiQLb.toReal ^ 2) +
        BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / xiQLb.toReal ^ 2)) ^ 3 ≤
        ((dy13e1Ub.mulUb f0Ub).powUb 3).toReal := by
      have hm : BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (xiQLb.toReal ^ 2) +
          BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / xiQLb.toReal ^ 2) ≤
          (dy13e1Ub.mulUb f0Ub).toReal :=
        (mul_le_mul H_tilde_le_dy13e1Ub hf0_le hf0_nn dy13e1Ub.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
      exact (pow_le_pow_left₀ (mul_nonneg BuchstabSwitching.H_tilde_nonneg hf0_nn) hm 3).trans
        (Dyadic.powUb_sound _ 3)
    set eNum := es1Ub.add ((cntUb.mulUb (dyOne.add ((dy13e1Ub.mulUb f0Ub).powUb 3))).mulUb epdUb)
    have hnum_le : (1 / 16 : ℝ) * min (cntUb.toReal * xiQLb.toReal ^ 2) (sqUb.toReal * hQ.toReal) *
          (2 * Real.log xiQLb.toReal + 6) ^ 2 * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) +
        cntUb.toReal * (1 + (BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (xiQLb.toReal ^ 2) +
          BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / xiQLb.toReal ^ 2)) ^ 3) *
          BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ eNum.toReal := by
      dsimp only [eNum]
      rw [Dyadic.add_toReal]
      have h1 : cntUb.toReal * (1 + (BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (xiQLb.toReal ^ 2) +
          BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / xiQLb.toReal ^ 2)) ^ 3) ≤
          (cntUb.mulUb (dyOne.add ((dy13e1Ub.mulUb f0Ub).powUb 3))).toReal := by
        refine (mul_le_mul_of_nonneg_left ?_ cntUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
        rw [Dyadic.add_toReal, dyOne_toReal]; linarith
      have h2 : cntUb.toReal * (1 + (BuchstabSwitching.H_tilde * ((1 / 2 : ℝ) * Real.log (xiQLb.toReal ^ 2) +
          BuchstabSwitching.alpha0 + BuchstabSwitching.C_F0 / xiQLb.toReal ^ 2)) ^ 3) *
          BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤
          ((cntUb.mulUb (dyOne.add ((dy13e1Ub.mulUb f0Ub).powUb 3))).mulUb epdUb).toReal :=
        (mul_le_mul h1 hepd hepd0 (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)
      linarith
    exact Dyadic.div_le_of_ble_mulLb hnum_le hv_pos le_rfl hesl

end SelbergSlice2c

section SquareAndMaster2c

/-- Unified Regime `2c` slice witness checker (`EvenBonf` or `Selberg`). -/
def checkSlice2cWitness (c : BuchstabSwitching.SlabCert) (zLogLo zLogUb epdUb vFullLb : Dyadic)
    (sl : Slice2cWitness) : Bool :=
  (if pExact ≤ sl.q0 then checkLogNat sl.q0 sl.wQ0Log sl.logQ0Lb sl.logQ0Ub else true) &&
  (if pExact < sl.q1 then checkLogNat sl.q1 sl.wQ1Log sl.logQ1Lb sl.logQ1Ub else true) &&
  checkSlice2abOr2cBounds sl.q0 sl.q1 sl.logQ0Lb sl.logQ0Ub sl.logQ1Lb sl.logQ1Ub sl.sqUb sl.cntUb sl.anW &&
  match sl.mode with
  | .selberg hQ xiQLb xiQUb xiQLogLb xiQLogUb jfLb s3cUb es1Ub f0Ub invXiSq78Ub wXiLog =>
    checkSelberg2c c zLogLo zLogUb epdUb vFullLb sl.q1 sl.sqUb sl.cntUb sl.mSl sl.eSl
      hQ xiQLb xiQUb xiQLogLb xiQLogUb jfLb s3cUb es1Ub f0Ub invXiSq78Ub wXiLog
  | .evenBonf zSub aQ mEv nD dMax ip2 vSubUb gSubLb ratUb mRatUb c2Ub errUb tailW =>
    checkEvenBonf2c c zLogLo zLogUb epdUb vFullLb sl.q1 sl.sqUb sl.cntUb sl.mSl sl.eSl
      zSub aQ mEv nD dMax ip2 vSubUb gSubLb ratUb mRatUb c2Ub errUb tailW

lemma checkSlice2cWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLo zLogUb epdUb vFullLb : Dyadic} {sl : Slice2cWitness}
    (hzL : zLogLo.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ zLogUb.toReal)
    (hcz : c.z ≤ sl.q0) (hqy : sl.q1 ≤ c.y)
    (hepd0 : 0 ≤ BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ))
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (hv_le : vFullLb.toReal ≤ External.VN 2 c.z)
    (h : checkSlice2cWitness c zLogLo zLogUb epdUb vFullLb sl = true) :
    ∃ s : External.SliceEngine2c c (c.X_lo : ℝ) sl.q0 sl.q1,
      s.mSl ≤ sl.mSl.toReal ∧ s.eSl consts.li2 ≤ sl.eSl.toReal := by
  unfold checkSlice2cWitness at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨h123, hsub⟩
  rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hbd⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨hl0, hl1⟩
  have hLog0 : 27000 ≤ sl.q0 →
      sl.logQ0Lb.toReal ≤ Real.log (sl.q0 : ℝ) ∧ Real.log (sl.q0 : ℝ) ≤ sl.logQ0Ub.toReal :=
    fun h27 => checkLogNat_sound consts (by have h27' : pExact ≤ sl.q0 := h27; simpa [h27'] using hl0)
  have hLog1 : 27000 < sl.q1 →
      sl.logQ1Lb.toReal ≤ Real.log (sl.q1 : ℝ) ∧ Real.log (sl.q1 : ℝ) ≤ sl.logQ1Ub.toReal :=
    fun h27 => checkLogNat_sound consts (by have h27' : pExact < sl.q1 := h27; simpa [h27'] using hl1)
  have hsc := checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hLog0 hLog1 hbd
  have hsq : ∑ q ∈ (Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime,
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sl.sqUb.toReal := by
    rw [max_eq_right hcz, min_eq_right hqy]; exact hsc.1
  have hcnt : (((Finset.Ico (max c.z sl.q0) (min c.y sl.q1)).filter Nat.Prime).card : ℝ) ≤ sl.cntUb.toReal := by
    rw [max_eq_right hcz, min_eq_right hqy]; exact hsc.2
  cases hm : sl.mode with
  | selberg hQ xiQLb xiQUb xiQLogLb xiQLogUb jfLb s3cUb es1Ub f0Ub invXiSq78Ub wXiLog =>
    rw [hm] at hsub
    exact selberg2c_sound consts hMert hzL hepd0 hepd hv_pos hv_le hsq hcnt hsub
  | evenBonf zSub aQ mEv nD dMax ip2 vSubUb gSubLb ratUb mRatUb c2Ub errUb tailW =>
    rw [hm] at hsub
    exact evenBonf2c_sound consts hGRH hCls hMert (fun _ => hzL) hepd hv_pos hv_le hsq hcnt hsub

/-- Regime `2c` prime-square witness checker (`SquareEngine2c`). -/
def checkSquare2cWitness (c : BuchstabSwitching.SlabCert) (w : Slab2cWitness) : Bool :=
  let sq := w.square
  let qEnd := min c.y (sq.qSq + 1)
  let sOk :=
    if c.z ≤ pExact then
      let sExact := exactInvMulPredSumUb c.z (min qEnd pExact)
      if pExact < qEnd then
        dyOne.ble (sq.invTailUb.mulLb (Dyadic.ofNat (pExact - 1))) &&
        (sExact.add sq.invTailUb).ble sq.sQ2Ub
      else sExact.ble sq.sQ2Ub
    else dyOne.ble (sq.sQ2Ub.mulLb (Dyadic.ofNat (c.z - 1)))
  let tailQ2Ok :=
    if c.y ≤ sq.qSq + 1 then true
    else w.xHiLogUb.ble (sq.tailQ2Ub.mulLb (Dyadic.ofNat sq.qSq))
  let tailQ2 := if c.y ≤ sq.qSq + 1 then dyZero else sq.tailQ2Ub
  let innerUb := sq.sQ2Ub.add ((sq.cntLoUb.mulUb w.epdUb).add tailQ2)
  decide (1 ≤ sq.qSq) && decide (sq.qSq ^ 4 ≤ c.X_lo) && sOk &&
  (if pExact < qEnd then checkLogNat qEnd sq.wLogEnd sq.logEndLb sq.logEndUb else true) &&
  tailQ2Ok &&
  checkSlice2abOr2cBounds c.z qEnd w.zLogLb w.zLogUb sq.logEndLb sq.logEndUb
    (Dyadic.ofNat 1000) sq.cntLoUb sq.anEndW &&
  innerUb.ble (sq.errQ2Ub.add sq.errQ2Ub) &&
  sq.errQ2Ub.ble (w.errQ2NormUb.mulLb w.vFullLb)

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
  unfold checkSquare2cWitness at h; dsimp only at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨h1_7, hnorm⟩
  rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, herr⟩
  rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hcnt⟩
  rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, htailOk⟩
  rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hlEnd⟩
  rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hsOk⟩
  rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hq1_b, hq4_b⟩
  have hq1 : 1 ≤ w.square.qSq := decide_eq_true_eq.mp hq1_b
  have hq4 : w.square.qSq ^ 4 ≤ c.X_lo := decide_eq_true_eq.mp hq4_b
  set sq := w.square; set qEnd := min c.y (sq.qSq + 1)
  have hq_rt : ((sq.qSq ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast ((show (sq.qSq ^ 2) ^ 2 = sq.qSq ^ 4 by ring).symm ▸ hq4 : (sq.qSq ^ 2) ^ 2 ≤ c.X_lo)
  have hs_q2 : ∑ q ∈ (Finset.Ico c.z qEnd).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤
      sq.sQ2Ub.toReal := by
    by_cases hzp : c.z ≤ pExact
    · simp only [hzp, ↓reduceIte] at hsOk
      have hsplit := BuchstabSwitching.sum_inv_mul_pred_split_le c.z qEnd pExact hz2 (by native_decide)
      have hex := sum_inv_mul_pred_le_exact (q0 := c.z) (q1 := min qEnd pExact) (min_le_right _ _)
      split_ifs at hsOk with hlt
      · rcases (Bool.and_eq_true _ _).mp hsOk with ⟨hinv_chk, hadd_chk⟩
        have hinv_le : 1 / ((pExact : ℝ) - 1) ≤ sq.invTailUb.toReal := by
          have hpos : (0 : ℝ) < (pExact : ℝ) - 1 := by unfold pExact; norm_num
          exact Dyadic.div_le_of_ble_mulLb (by rw [dyOne_toReal]) hpos
            (by rw [Dyadic.ofNat_toReal]; unfold pExact; norm_num) hinv_chk
        have hble := Dyadic.ble_sound hadd_chk; rw [Dyadic.add_toReal] at hble
        simp only [hlt, ↓reduceIte] at hsplit; linarith
      · simp only [hlt, ↓reduceIte, add_zero] at hsplit
        exact hsplit.trans (hex.trans (Dyadic.ble_sound hsOk))
    · simp only [hzp, ↓reduceIte] at hsOk
      have hle := BuchstabSwitching.sum_Ico_primes_inv_mul_pred_le c.z qEnd hz2
      have hpos : (0 : ℝ) < (c.z : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < c.z))
      have hsub : ((c.z - 1 : ℕ) : ℝ) = (c.z : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ c.z), Nat.cast_one]
      exact hle.trans (Dyadic.div_le_of_ble_mulLb (by rw [dyOne_toReal]) hpos
        (by rw [Dyadic.ofNat_toReal, hsub]) hsOk)
  have hLog1 : 27000 < qEnd → sq.logEndLb.toReal ≤ Real.log (qEnd : ℝ) ∧ Real.log (qEnd : ℝ) ≤ sq.logEndUb.toReal :=
    fun h27 => checkLogNat_sound consts (by have h27' : pExact < qEnd := h27; simpa [h27'] using hlEnd)
  let base : External.SquareEngine2ab c (c.X_lo : ℝ) :=
    ⟨sq.qSq, hq1, hq_rt, sq.sQ2Ub.toReal, hs_q2, sq.cntLoUb.toReal,
      (checkSlice2abOr2cBounds_sound consts hGRH hCls hMert hzLog hLog1 hcnt).2⟩
  let q2 : External.SquareEngine2c c (c.X_lo : ℝ) := ⟨base, w.vFullLb.toReal, hv_pos, hv_le⟩
  refine ⟨q2, ?_⟩
  have htail_le : (if c.y ≤ sq.qSq + 1 then (0 : ℝ) else Real.log (c.X_hi : ℝ) / (sq.qSq : ℝ)) ≤
      (if c.y ≤ sq.qSq + 1 then dyZero else sq.tailQ2Ub).toReal := by
    split_ifs with hy
    · rw [dyZero_toReal]
    · simp only [hy, ↓reduceIte] at htailOk
      exact Dyadic.div_le_of_ble_mulLb hlogHi (by exact_mod_cast hq1) (by rw [Dyadic.ofNat_toReal]) htailOk
  have herr_le := Dyadic.ble_sound herr
  rw [Dyadic.add_toReal, Dyadic.add_toReal, Dyadic.add_toReal] at herr_le
  have hcnt_epd : sq.cntLoUb.toReal * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤
      (sq.cntLoUb.mulUb w.epdUb).toReal :=
    (mul_le_mul_of_nonneg_left hepd sq.cntLoUb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
  have hbase_err : base.errQ2 consts.li2 (c.X_hi : ℝ) ≤ sq.errQ2Ub.toReal := by
    dsimp [External.SquareEngine2ab.errQ2, base]; linarith
  exact Dyadic.div_le_of_ble_mulLb hbase_err hv_pos le_rfl hnorm

private lemma sliceEngine2cCast {c : BuchstabSwitching.SlabCert} {X_lo : ℝ} {q0 q1 q0' q1' : ℕ}
    (h0 : q0 = q0') (h1 : q1 = q1') (s : External.SliceEngine2c c X_lo q0 q1) :
    ∃ s' : External.SliceEngine2c c X_lo q0' q1', s'.mSl = s.mSl ∧ ∀ li2, s'.eSl li2 = s.eSl li2 := by
  subst h0; subst h1; exact ⟨s, rfl, fun _ => rfl⟩

/-- Complete computable witness verifier for Regime `2c` slabs (`66` slabs). -/
def checkSlab2cWitness (c : BuchstabSwitching.SlabCert) (w : Slab2cWitness) : Bool :=
  let sumMSl := sumDyadicList2c (·.mSl) w.slices
  let sumESl := sumDyadicList2c (·.eSl) w.slices
  c.valid && decide (4 * 10 ^ 18 ≤ c.X_lo) &&
  checkLogNat c.X_lo w.wXLoLog w.xLoLogLb w.xLoLogUb &&
  checkLogNat c.X_hi w.wXHiLog dyZero w.xHiLogUb &&
  checkLogNat c.z w.wZLog w.zLogLb w.zLogUb &&
  checkEpdWitness c.X_lo w.xLoLogLb w.xLoLogUb w.epdUb w.epdW &&
  decide (0 < w.vFullLb.m) &&
  checkVFullLb2c c.z w.zLogLb w.zLogUb w.vFullLb w.vFullW &&
  checkLower2cWitness c w.zLogLb w.zLogUb w.epdUb w.vFullLb w.lower &&
  checkSliceChain2c c.z c.y w.slices &&
  w.slices.all (checkSlice2cWitness c w.zLogLb w.zLogUb w.epdUb w.vFullLb) &&
  checkSquare2cWitness c w &&
  ((Dyadic.ofNat (2 * c.main_num)).add ((Dyadic.ofNat c.den).mulUb sumMSl)).ble
    ((Dyadic.ofNat (2 * c.den)).mulLb w.lower.ratLb) &&
  ((((w.lower.remANormUb.add w.errQ2NormUb).mulPow2 1).add sumESl).mulUb
    (Dyadic.ofNat c.den)).ble (Dyadic.ofNat (2 * c.err_num))

/-- Master soundness theorem for `checkSlab2cWitness`: produces `Regime2cSlabBridge c`. -/
theorem checkSlab2cWitness_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {w : Slab2cWitness}
    (h : checkSlab2cWitness c w = true) :
    External.Regime2cSlabBridge c := by
  unfold checkSlab2cWitness at h; dsimp only at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨h1_13, herr⟩
  rcases (Bool.and_eq_true _ _).mp h1_13 with ⟨h1_12, hmain⟩
  rcases (Bool.and_eq_true _ _).mp h1_12 with ⟨h1_11, hsq⟩
  rcases (Bool.and_eq_true _ _).mp h1_11 with ⟨h1_10, hslices⟩
  rcases (Bool.and_eq_true _ _).mp h1_10 with ⟨h1_9, hchain⟩
  rcases (Bool.and_eq_true _ _).mp h1_9 with ⟨h1_8, hlo_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1_8 with ⟨h1_7, hvChk⟩
  rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, hvPos_b⟩
  rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hepd_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hzLog_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hlogHi_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hlogLo_chk⟩
  rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hval, hX4_b⟩
  have hX4 : 4 * 10 ^ 18 ≤ c.X_lo := decide_eq_true_eq.mp hX4_b
  have hvPos : 0 < w.vFullLb.m := decide_eq_true_eq.mp hvPos_b
  have hval_s := BuchstabSwitching.SlabCert.valid_sound hval
  have hden_pos : 0 < c.den := by
    have hnet : (0 : ℚ) < (c.net_num : ℚ) / (c.den : ℚ) := hval_s.2.2.2.2.2.1
    by_contra h0; simp [show c.den = 0 by omega] at hnet
  have hden_real : (0 : ℝ) < (c.den : ℝ) := by exact_mod_cast hden_pos
  have hlogXlo := checkLogNat_sound consts hlogLo_chk
  have hlogXhi := (checkLogNat_sound consts hlogHi_chk).2
  have hzL := checkLogNat_sound consts hzLog_chk
  have hepd0 : 0 ≤ BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) :=
    BuchstabSwitching.epdNormFn_nonneg_of_premises hGRH hCls (by exact_mod_cast hX4) le_rfl
  have hepd := checkEpdWitness_sound consts hlogXlo hepd_chk
  have hv_pos : 0 < w.vFullLb.toReal := Dyadic.toReal_pos_of_m hvPos
  have hv_le := checkVFullLb2c_sound consts hGRH hCls hMert (fun _ => hzL) hvChk
  obtain ⟨lo_eng, hlo_sa, hlo_rem⟩ :=
    lower2c_sound consts hGRH hCls hMert (fun _ => hzL) hepd hv_pos hv_le hlo_chk
  obtain ⟨q2_eng, hq2_err⟩ := checkSquare2cWitness_sound consts hGRH hCls hMert hval_s.2.1
    (fun _ => hzL) hlogXhi hepd hv_pos hv_le hsq
  have hsl_mem := List.all_eq_true.mp hslices
  have hcb := checkSliceChain2c_bounds w.slices c.z c.y hchain
  have hcast := checkSliceChain2c_castSucc w.slices c.z c.y hchain
  have hslice_ex : ∀ i : Fin w.slices.length,
      ∃ s' : External.SliceEngine2c c (c.X_lo : ℝ) (bptsOfSlices2c c.z w.slices i.castSucc)
        (bptsOfSlices2c c.z w.slices i.succ),
        s'.mSl ≤ w.slices[i].mSl.toReal ∧ s'.eSl consts.li2 ≤ w.slices[i].eSl.toReal := by
    intro i; have hbi := hcb i
    obtain ⟨s0, hm0, he0⟩ := checkSlice2cWitness_sound consts hGRH hCls hMert hzL hbi.1 hbi.2.2 hepd0 hepd
      hv_pos hv_le (hsl_mem w.slices[i] (List.getElem_mem i.2))
    obtain ⟨s', hm', he'⟩ := sliceEngine2cCast (hcast i).symm (bptsOfSlices2c_succ c.z w.slices i).symm s0
    exact ⟨s', hm'.trans_le hm0, (he' consts.li2).trans_le he0⟩
  let sl_eng := fun i : Fin w.slices.length => (hslice_ex i).choose
  have hm_sum := sum_fin_le_sumDyadicList2c (·.mSl) w.slices (fun i => (sl_eng i).mSl)
    fun i => (hslice_ex i).choose_spec.1
  have he_sum := sum_fin_le_sumDyadicList2c (·.eSl) w.slices (fun i => (sl_eng i).eSl consts.li2)
    fun i => (hslice_ex i).choose_spec.2
  set sumMSl := sumDyadicList2c (·.mSl) w.slices
  set sumESl := sumDyadicList2c (·.eSl) w.slices
  have hmain_dy := Dyadic.ble_sound hmain
  rw [Dyadic.add_toReal, Dyadic.ofNat_toReal] at hmain_dy
  have hmain_lhs : ((2 * c.main_num : ℕ) : ℝ) + (c.den : ℝ) * sumMSl.toReal ≤
      ((2 * c.main_num : ℕ) : ℝ) + ((Dyadic.ofNat c.den).mulUb sumMSl).toReal := by
    have hm : (c.den : ℝ) * sumMSl.toReal ≤ ((Dyadic.ofNat c.den).mulUb sumMSl).toReal := by
      rw [← Dyadic.ofNat_toReal]; exact Dyadic.le_mulUb _ _
    linarith
  have hmain_rhs : ((Dyadic.ofNat (2 * c.den)).mulLb w.lower.ratLb).toReal ≤
      ((2 * c.den : ℕ) : ℝ) * w.lower.ratLb.toReal :=
    (Dyadic.mulLb_le _ _).trans (by rw [Dyadic.ofNat_toReal])
  have hc_main : (c.main_num : ℝ) = (c.main_lb : ℝ) * (c.den : ℝ) := by
    simp only [BuchstabSwitching.SlabCert.main_lb]; push_cast; field_simp [hden_real.ne']
  have hmain_div : 2 * (c.main_lb : ℝ) + sumMSl.toReal ≤ 2 * w.lower.ratLb.toReal := by
    have hcomb := hmain_lhs.trans (hmain_dy.trans hmain_rhs)
    push_cast at hcomb; rw [hc_main] at hcomb
    exact le_of_mul_le_mul_left (by nlinarith) hden_real
  have hmain_le : (c.main_lb : ℝ) ≤ lo_eng.saNorm - (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).mSl := by
    linarith
  have herr_dy := (Dyadic.le_mulUb _ _).trans
    ((Dyadic.ble_sound herr).trans_eq (Dyadic.ofNat_toReal (2 * c.err_num)))
  rw [Dyadic.ofNat_toReal, Dyadic.add_toReal, Dyadic.mulPow2_toReal, pow_one, Dyadic.add_toReal] at herr_dy
  have hc_err : (c.err_num : ℝ) = (c.err_ub : ℝ) * (c.den : ℝ) := by
    simp only [BuchstabSwitching.SlabCert.err_ub]; push_cast; field_simp [hden_real.ne']
  have herr_div : 2 * (w.lower.remANormUb.toReal + w.errQ2NormUb.toReal) + sumESl.toReal ≤
      2 * (c.err_ub : ℝ) := by
    push_cast at herr_dy; rw [hc_err] at herr_dy
    exact le_of_mul_le_mul_right (by nlinarith) hden_real
  have herr_le : lo_eng.remANorm consts.li2 +
      (1 / 2 : ℝ) * ∑ i : Fin w.slices.length, (sl_eng i).eSl consts.li2 +
      q2_eng.errQ2 consts.li2 (c.X_hi : ℝ) ≤ (c.err_ub : ℝ) := by
    linarith
  exact External.Regime2cSlabBridge.of_sieveEngines hGRH hCls (by exact_mod_cast hX4) le_rfl le_rfl
    hval_s.2.1 hval_s.2.2.1 w.slices.length (bptsOfSlices2c c.z w.slices) (bptsOfSlices2c_zero c.z w.slices)
    (checkSliceChain2c_last w.slices c.z c.y hchain)
    (fun i => by rw [hcast i, bptsOfSlices2c_succ]; exact (hcb i).2.1)
    lo_eng sl_eng q2_eng hmain_le herr_le

end SquareAndMaster2c

end

end BuchstabSwitching.SieveInst
