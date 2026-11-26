import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cFastPrimes
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstElemBounds
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEngineWiring
import Mathlib.Tactic

/-!
# Soundness of Regime `2c` Odd-Bonferroni Lower-Sieve Witness Verification

Verifies `Lower2cWitness` with `isBrun = false` (`OddBonf`) for Regime `2c` slabs
(`10^84 ≤ c.X_lo < 10^600`) and exports shared `2c` tail/exponent/remainder helpers.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

private abbrev sn (m e : ℕ) : SciNat := ⟨m, e⟩

section TailAndExpHelpers

/-- Ceiling integer of a `SciNat`. -/
def sciCeilNat (x : SciNat) : ℕ := SciNat.ceilDiv x.m (10 ^ x.e)

private def piLo4L : SciNat := (sn 31415 4)

private def mertensAnalyticBounds2c (a b : ℕ) (aLogLo aLogHi bLogLo bLogHi : SciNat) :
    Bool × SciNat × ℕ :=
  let ratioUb := divUbSig bLogHi aLogLo 24
  let (okLL, _, llRatioUb) := ratLogBounds ratioUb.m (10 ^ ratioUb.e)
  let (okSa, _, aSqrtUb) := sqrtSciBounds a 18
  let (okSb2, _, bSqrtUb) := sqrtSciBounds b 18
  let (okSb, bSqrtLb, _) := sqrtSciBounds b 12
  let okBase := decide (27000 ≤ a) && decide (a < b) && (sn 3 0).blt aLogLo &&
    aLogLo.ble aLogHi && bLogLo.ble bLogHi && (sn 3 0).blt bLogLo &&
    (sn 1 0).ble ratioUb && okLL && okSa && okSb2
  if !okBase then (false, (sn 0 0), 0)
  else
    let loErrUb := divUbSig (sn 2964 9) aLogLo 24
    let (okHi, hiErrUb) :=
      if 10 ^ 12 < b then (true, divUbSig (sn 6836 9) bLogLo 24)
      else (okSb && decide (0 < bSqrtLb.m), divUbSig (sn 2 0) (bSqrtLb.mul bLogLo) 24)
    let sqUb := llRatioUb.add (hiErrUb.add (loErrUb.add (divUbSig (sn 1 0) (SciNat.ofNat (a - 1)) 24)))
    let piDiffUb := (divUbSig (SciNat.ofNat (b - a)) aLogLo 24).add
      ((divUbSig ((bSqrtUb.mul bLogHi).add (aSqrtUb.mul aLogHi)) ((sn 8 0).mul piLo4L) 24).add (sn 1 0))
    let piSingleUb := (divUbSig (SciNat.ofNat b) (bLogLo.subLb (sn 2 0)) 24).add
      ((sn 1045163780117493 15).add (divUbSig (bSqrtUb.mul bLogHi) ((sn 8 0).mul piLo4L) 24))
    (okHi, sqUb, min (sciCeilNat piDiffUb) (sciCeilNat piSingleUb))

/-- Compute `(ok, s1Ub, s2Ub, piUb)` over `[u, v)` using chunk-skipping exact sums and analytic tails. -/
def computeMertensTail2c (u v : ℕ) (uLogLo uLogHi vLogLo vLogHi : SciNat) :
    Bool × SciNat × SciNat × ℕ :=
  if v ≤ u then (true, (sn 0 0), (sn 0 0), 0)
  else if v ≤ 27000 then
    let (s1, s2, cnt) := fastExactMertens2c u v
    (true, s1, s2, cnt)
  else if 27000 ≤ u then
    let (ok, s1, piN) := mertensAnalyticBounds2c u v uLogLo uLogHi vLogLo vLogHi
    let s2 := divUbSig (sn 1 0) (SciNat.ofNat (u - 2)) 24
    (ok && checkMertensTailSums u v uLogLo uLogHi vLogLo vLogHi s1 s2 (SciNat.ofNat piN), s1, s2, piN)
  else
    let (s1Ex, s2Ex, cntEx) := fastExactMertens2c u 27000
    let (ok, s1An, piAn) := mertensAnalyticBounds2c 27000 v log27000Lo log27000Hi vLogLo vLogHi
    let s2An := divUbSig (sn 1 0) (SciNat.ofNat 26998) 24
    (ok && checkMertensTailSums 27000 v log27000Lo log27000Hi vLogLo vLogHi s1An s2An (SciNat.ofNat piAn),
      s1Ex.add s1An, s2Ex.add s2An, cntEx + piAn)

lemma computeMertensTail2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {u v : ℕ} {uLogLo uLogHi vLogLo vLogHi : SciNat}
    (hLogU : 27000 ≤ u → uLogLo.toReal ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ uLogHi.toReal)
    (hLogV : 27000 < v → vLogLo.toReal ≤ Real.log (v : ℝ) ∧ Real.log (v : ℝ) ≤ vLogHi.toReal)
    (h : (computeMertensTail2c u v uLogLo uLogHi vLogLo vLogHi).1 = true) :
    ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, BuchstabSwitching.gTot p ≤
        (computeMertensTail2c u v uLogLo uLogHi vLogLo vLogHi).2.1.toReal ∧
      ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, (BuchstabSwitching.gTot p) ^ 2 ≤
        (computeMertensTail2c u v uLogLo uLogHi vLogLo vLogHi).2.2.1.toReal ∧
      (((Finset.Ico u v).filter Nat.Prime).card : ℝ) ≤
        ((computeMertensTail2c u v uLogLo uLogHi vLogLo vLogHi).2.2.2 : ℝ) := by
  by_cases h1 : v ≤ u
  · unfold computeMertensTail2c; simp only [h1, ↓reduceIte, Finset.Ico_eq_empty_of_le h1,
      Finset.filter_empty, Finset.sum_empty, Finset.card_empty, SciNat.toReal]; norm_num
  · by_cases h2 : v ≤ 27000
    · unfold computeMertensTail2c; simp only [h1, h2, ↓reduceIte]
      exact fastExactMertens2c_sound h2
    · by_cases h3 : 27000 ≤ u
      · unfold computeMertensTail2c at h ⊢; simp only [h1, h2, h3, ↓reduceIte, Bool.and_eq_true] at h ⊢
        simpa [SciProofs.ofNat_toReal] using checkMertensTailSums_sound consts hGRH hCls hMert hLogU hLogV h.2
      · unfold computeMertensTail2c at h ⊢; simp only [h1, h2, h3, ↓reduceIte, Bool.and_eq_true] at h ⊢
        have hex := fastExactMertens2c_sound (u := u) (v := 27000) le_rfl
        have han := checkMertensTailSums_sound consts hGRH hCls hMert (fun _ => log27000_bounds consts) hLogV h.2
        rw [SciProofs.ofNat_toReal] at han
        have hsplit : (Finset.Ico u v).filter Nat.Prime =
            (Finset.Ico u 27000).filter Nat.Prime ∪ (Finset.Ico 27000 v).filter Nat.Prime := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
          exact ⟨fun ⟨⟨ha, hb⟩, hp⟩ => if hp27 : p < 27000 then Or.inl ⟨⟨ha, hp27⟩, hp⟩ else Or.inr ⟨⟨by omega, hb⟩, hp⟩,
            by rintro (⟨⟨ha, hb⟩, hp⟩ | ⟨⟨ha, hb⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩⟩
        have hdisj : Disjoint ((Finset.Ico u 27000).filter Nat.Prime) ((Finset.Ico 27000 v).filter Nat.Prime) :=
          Finset.disjoint_left.mpr fun p ha hb => by
            have := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
            have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).1; omega
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj,
          Nat.cast_add, Nat.cast_add, SciProofs.add_toReal, SciProofs.add_toReal]
        exact ⟨add_le_add hex.1 han.1, add_le_add hex.2.1 han.2.1, add_le_add hex.2.2 han.2.2⟩

/-- Compute and check a positive lower bound on `V2 gTot ((Ico u v).filter Prime)` (`3 ≤ u`). -/
def v2TailLb2c (u v : ℕ) (uLogLo uLogHi vLogLo vLogHi : SciNat) : Bool × SciNat :=
  if v ≤ u then (true, (sn 1 0))
  else if v ≤ 27000 then let lb := fastV2LbExact2c u v; (decide (0 < lb.m), lb)
  else if 27000 ≤ u then
    let mt := computeMertensTail2c u v uLogLo uLogHi vLogLo vLogHi
    let ex := expUbBounds (mt.2.1.add ((divUbSig (SciNat.ofNat (u - 1)) (SciNat.ofNat (2 * (u - 2))) 24).mul mt.2.2.1))
    let lb := divLbSig (sn 1 0) ex.2 24; (decide (3 ≤ u) && mt.1 && ex.1 && decide (0 < lb.m), lb)
  else
    let mt := computeMertensTail2c 27000 v log27000Lo log27000Hi vLogLo vLogHi
    let ex := expUbBounds (mt.2.1.add ((divUbSig (sn 26999 0) (sn 53996 0) 24).mul mt.2.2.1))
    let lb := ((fastV2LbExact2c u 27000).mul (divLbSig (sn 1 0) ex.2 24)).trimLb 24
    (decide (3 ≤ u) && mt.1 && ex.1 && decide (0 < lb.m), lb)

private lemma v2TailAnalyticPiece (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {a b : ℕ} {aLogLo aLogHi bLogLo bLogHi : SciNat}
    (ha3 : 3 ≤ a) (hm : (computeMertensTail2c a b aLogLo aLogHi bLogLo bLogHi).1 = true)
    (haL : aLogLo.toReal ≤ Real.log (a : ℝ) ∧ Real.log (a : ℝ) ≤ aLogHi.toReal)
    (hbL : 27000 < b → bLogLo.toReal ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ bLogHi.toReal) :
    let mt := computeMertensTail2c a b aLogLo aLogHi bLogLo bLogHi
    let arg := mt.2.1.add ((divUbSig (SciNat.ofNat (a - 1)) (SciNat.ofNat (2 * (a - 2))) 24).mul mt.2.2.1)
    (expUbBounds arg).1 = true →
    (divLbSig (sn 1 0) (expUbBounds arg).2 24).toReal ≤
      BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico a b).filter Nat.Prime) := by
  intro mt arg he1
  have hms := computeMertensTail2c_sound consts hGRH hCls hMert (fun _ => haL) hbL hm
  have hbonf := BuchstabSwitching.analytic_bonf_V2_lb ha3
    (fun p hp => ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1⟩) hms.1 hms.2.1
  have ha3r : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha3
  have hc2_le : 1 / (2 * (1 - 1 / ((a : ℝ) - 1))) ≤
      (divUbSig (SciNat.ofNat (a - 1)) (SciNat.ofNat (2 * (a - 2))) 24).toReal := by
    have h1m : 1 - 1 / ((a : ℝ) - 1) = ((a : ℝ) - 2) / ((a : ℝ) - 1) := by
      have : (a : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    have heq : 1 / (2 * (1 - 1 / ((a : ℝ) - 1))) = ((a : ℝ) - 1) / (2 * ((a : ℝ) - 2)) := by
      have : (a : ℝ) - 1 ≠ 0 := by linarith
      have : (a : ℝ) - 2 ≠ 0 := by linarith
      rw [h1m]; field_simp
    have hd := divUbSig_le (SciNat.ofNat (a - 1)) (SciNat.ofNat (2 * (a - 2))) 24
    rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, Nat.cast_sub (by omega : 1 ≤ a),
      Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ a)] at hd
    push_cast at hd
    exact heq.symm ▸ hd
  have harg_le : -(arg.toReal) ≤ -(mt.2.1.toReal + 1 / (2 * (1 - 1 / ((a : ℝ) - 1))) * mt.2.2.1.toReal) := by
    dsimp only [arg]; rw [SciProofs.add_toReal, SciProofs.mul_toReal]
    linarith [mul_le_mul_of_nonneg_right hc2_le (SciNat.toReal_nonneg mt.2.2.1)]
  have hinv : 1 / (expUbBounds arg).2.toReal ≤ Real.exp (-arg.toReal) := by
    rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos _) (expUbBounds_sound he1).1
  have hdiv := divLbSig_le (sn 1 0) (expUbBounds arg).2 24
  rw [show (sn 1 0).toReal = 1 by simp [SciNat.toReal]] at hdiv
  exact hdiv.trans (hinv.trans ((Real.exp_le_exp.mpr harg_le).trans hbonf))

lemma v2TailLb2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {u v : ℕ} {uLogLo uLogHi vLogLo vLogHi : SciNat}
    (hLogU : 27000 ≤ u → uLogLo.toReal ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ uLogHi.toReal)
    (hLogV : 27000 < v → vLogLo.toReal ≤ Real.log (v : ℝ) ∧ Real.log (v : ℝ) ≤ vLogHi.toReal)
    (h : (v2TailLb2c u v uLogLo uLogHi vLogLo vLogHi).1 = true) :
    0 < (v2TailLb2c u v uLogLo uLogHi vLogLo vLogHi).2.toReal ∧
      (v2TailLb2c u v uLogLo uLogHi vLogLo vLogHi).2.toReal ≤
        BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico u v).filter Nat.Prime) := by
  by_cases h1 : v ≤ u
  · unfold v2TailLb2c at h ⊢; simp only [h1, ↓reduceIte] at h ⊢
    simp [Finset.Ico_eq_empty_of_le h1, SciNat.toReal]
  · by_cases h2 : v ≤ 27000
    · unfold v2TailLb2c at h ⊢; simp only [h1, h2, ↓reduceIte, decide_eq_true_eq] at h ⊢
      have hprod : BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico u v).filter Nat.Prime) =
          ∏ p ∈ (Finset.Ico u v).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) := by
        unfold BuchstabSwitching.V2
        refine Finset.prod_congr rfl fun p hp => ?_
        rw [BuchstabSwitching.gTot_prime (Finset.mem_filter.mp hp).2]
      rw [hprod]
      exact ⟨by unfold SciNat.toReal; exact div_pos (by exact_mod_cast h) (by positivity),
        fastV2LbExact2c_sound h2⟩
    · by_cases h3 : 27000 ≤ u
      · unfold v2TailLb2c at h ⊢
        simp only [h1, h2, h3, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        exact ⟨by unfold SciNat.toReal; exact div_pos (by exact_mod_cast h.2) (by positivity),
          v2TailAnalyticPiece consts hGRH hCls hMert h.1.1.1 h.1.1.2 (hLogU h3) hLogV h.1.2⟩
      · unfold v2TailLb2c at h ⊢
        simp only [h1, h2, h3, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        have han := v2TailAnalyticPiece consts hGRH hCls hMert (by norm_num) h.1.1.2
          (log27000_bounds consts) hLogV
        have harg : (computeMertensTail2c 27000 v log27000Lo log27000Hi vLogLo vLogHi).2.1.add
            ((divUbSig (SciNat.ofNat (27000 - 1)) (SciNat.ofNat (2 * (27000 - 2))) 24).mul
              (computeMertensTail2c 27000 v log27000Lo log27000Hi vLogLo vLogHi).2.2.1) =
            (computeMertensTail2c 27000 v log27000Lo log27000Hi vLogLo vLogHi).2.1.add
            ((divUbSig (sn 26999 0) (sn 53996 0) 24).mul
              (computeMertensTail2c 27000 v log27000Lo log27000Hi vLogLo vLogHi).2.2.1) := by
          congr 2
        have han' := han (harg ▸ h.1.2)
        have hex_le := fastV2LbExact2c_sound (u := u) (v := 27000) le_rfl
        have hsplit : (Finset.Ico u v).filter Nat.Prime =
            (Finset.Ico u 27000).filter Nat.Prime ∪ (Finset.Ico 27000 v).filter Nat.Prime := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
          exact ⟨fun ⟨⟨hpu, hpv⟩, hpr⟩ => if hp27 : p < 27000 then Or.inl ⟨⟨hpu, hp27⟩, hpr⟩
              else Or.inr ⟨⟨by omega, hpv⟩, hpr⟩,
            by rintro (⟨⟨hpu, hp27⟩, hpr⟩ | ⟨⟨hp27, hpv⟩, hpr⟩) <;> exact ⟨⟨by omega, by omega⟩, hpr⟩⟩
        have hdisj : Disjoint ((Finset.Ico u 27000).filter Nat.Prime)
            ((Finset.Ico 27000 v).filter Nat.Prime) := Finset.disjoint_left.mpr fun p ha1 ha2 => by
          have a1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha1).1).2
          have a2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha2).1).1; omega
        refine ⟨by unfold SciNat.toReal; exact div_pos (by exact_mod_cast h.2) (by positivity),
          (SciProofs.trimLb_le _ 24).trans ?_⟩
        unfold BuchstabSwitching.V2
        rw [SciProofs.mul_toReal, hsplit, Finset.prod_union hdisj]
        have hprod1 : ∏ p ∈ (Finset.Ico u 27000).filter Nat.Prime, (1 - BuchstabSwitching.gTot p) =
            ∏ p ∈ (Finset.Ico u 27000).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) :=
          Finset.prod_congr rfl fun p hp => by rw [BuchstabSwitching.gTot_prime (Finset.mem_filter.mp hp).2]
        rw [hprod1]
        exact mul_le_mul hex_le (harg ▸ han') (SciNat.toReal_nonneg _) ((SciNat.toReal_nonneg _).trans hex_le)

/-- Outward upper bound on `∑ j ∈ Finset.range (k + 1), x^j / j!`. -/
def sumPowDivFactUb (x : SciNat) : ℕ → SciNat
  | 0 => (sn 1 0)
  | k + 1 => (sumPowDivFactUb x k).add
      (divUbSig (sciPowUb x (k + 1)) (SciNat.ofNat (Nat.factorial (k + 1))) 24)

lemma sumPowDivFactUb_sound (x : SciNat) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), x.toReal ^ j / (Nat.factorial j : ℝ) ≤
      (sumPowDivFactUb x k).toReal := by
  induction k with
  | zero => simp [sumPowDivFactUb, SciNat.toReal]
  | succ k ih =>
    rw [Finset.sum_range_succ, sumPowDivFactUb, SciProofs.add_toReal]
    have hdiv := divUbSig_le (sciPowUb x (k + 1)) (SciNat.ofNat (Nat.factorial (k + 1))) 24
    rw [SciProofs.ofNat_toReal] at hdiv
    exact add_le_add ih ((div_le_div_of_nonneg_right (sciPowUb_sound x (k + 1)) (Nat.cast_nonneg _)).trans hdiv)

lemma remNorm_le_of_ble {x y : ℝ} {nx epdUb vFullLb ub : SciNat}
    (hx0 : 0 ≤ x) (hx : x ≤ nx.toReal) (hy : y ≤ epdUb.toReal) (hv : 0 < vFullLb.toReal)
    (hble : (divUbSig (nx.mul epdUb) vFullLb 24).ble ub = true) :
    x * y / vFullLb.toReal ≤ ub.toReal := by
  have hnum : x * y ≤ (nx.mul epdUb).toReal := by
    rw [SciProofs.mul_toReal]
    exact (mul_le_mul_of_nonneg_left hy hx0).trans (mul_le_mul_of_nonneg_right hx (SciNat.toReal_nonneg _))
  exact ((div_le_div_of_nonneg_right hnum hv.le).trans (divUbSig_le _ _ 24)).trans (SciProofs.ble_sound hble)

lemma ratLb_of_sub_ble {err lb : SciNat} {errReal : ℝ}
    (herr1 : err.ble (sn 1 0) = true) (hrat : lb.ble ((sn 1 0).subLb err) = true)
    (herr_le : errReal ≤ err.toReal) : lb.toReal ≤ 1 - errReal := by
  have hsub := SciProofs.subLb_le (a := (sn 1 0)) (b := err)
    (by simpa [SciNat.toReal] using SciProofs.ble_sound herr1)
  rw [show (sn 1 0).toReal = 1 by simp [SciNat.toReal]] at hsub; linarith [SciProofs.ble_sound hrat]

end TailAndExpHelpers

section OddBonfLower2c

/-- Computable checker for `Lower2cWitness` with `isBrun = false`. -/
def checkOddBonfLower2c (c : BuchstabSwitching.SlabCert) (epdUb vFullLb : SciNat)
    (lo : Lower2cWitness) : Bool :=
  if h : lo.a < smallOddPrimes2c.length then
    let pMin := smallOddPrimes2c[lo.a]
    let (okM, s1, _, piN) := computeMertensTail2c pMin c.z (sn 0 0) (sn 0 0) lo.zLogLb lo.zLogUb
    let (okV, gLb) := v2TailLb2c pMin c.z (sn 0 0) (sn 0 0) lo.zLogLb lo.zLogUb
    let errTerm := divUbSig (sciPowUb lo.s1Ub (2 * lo.mOdd + 2))
      ((SciNat.ofNat (Nat.factorial (2 * lo.mOdd + 2))).mul lo.gLb) 24
    let ndUb := (SciNat.ofNat (2 ^ lo.a)).mul (sumPowDivFactUb lo.piZUb (2 * lo.mOdd + 1))
    decide (pMin < c.z) && (if 27000 < c.z then checkLogNat c.z lo.zLogLb lo.zLogUb else true) &&
    decide ((smallOddPrimes2c.take lo.a).prod * c.z ^ (2 * lo.mOdd + 1) ≤ lo.dMax) &&
    decide (lo.dMax ^ 2 ≤ c.X_lo) && okM && s1.ble lo.s1Ub && (SciNat.ofNat piN).ble lo.piZUb &&
    ndUb.ble (SciNat.ofNat lo.nD) && okV && decide (0 < lo.gLb.m) && lo.gLb.ble gLb &&
    errTerm.ble (sn 1 0) && lo.ratLb.ble ((sn 1 0).subLb errTerm) &&
    (divUbSig ((SciNat.ofNat lo.nD).mul epdUb) vFullLb 24).ble lo.remANormUb
  else false

lemma oddBonfLower2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {epdUb vFullLb : SciNat} {lo : Lower2cWitness}
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (h : checkOddBonfLower2c c epdUb vFullLb lo = true) :
    ∃ s : External.OddBonfLowerSpec c (c.X_lo : ℝ),
      lo.ratLb.toReal ≤ s.rat_lb ∧
      s.n_d * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) / vFullLb.toReal ≤
        lo.remANormUb.toReal := by
  by_cases ha_sm : lo.a < smallOddPrimes2c.length
  · have ha : lo.a < oddPrimesLt27000.length := lt_of_lt_of_le ha_sm smallOddPrimes2c_len_le
    unfold checkOddBonfLower2c at h; simp only [ha_sm, ↓reduceDIte] at h
    rw [smallOddPrimes2c_getElem ha_sm, smallOddPrimes2c_take ha_sm.le] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpz, hlogZ⟩, hd_le⟩, hd_sq⟩, hokM⟩, hs1⟩, hpi⟩, hnd⟩,
      hokV⟩, hg_pos⟩, hg_le⟩, herr1⟩, hrat⟩, hrem⟩
    set pMin := oddPrimesLt27000[lo.a]
    have hpa_lt : (if lo.a = 0 then 2 else oddPrimesLt27000[lo.a - 1]'(by omega)) < pMin := by
      split_ifs with ha0
      · exact lt_of_lt_of_le (by norm_num) (mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)).1
      · exact (List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt) (lo.a - 1) lo.a (by omega) ha (by omega)
    have hsplit := oddPrimesLt27000_split_props ha hpz.le hpa_lt le_rfl
    set Q₁ : Finset ℕ := (oddPrimesLt27000.take lo.a).toFinset
    set P₂ : Finset ℕ := (Finset.Ico pMin c.z).filter Nat.Prime
    have hLogZ : 27000 < c.z → lo.zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ lo.zLogUb.toReal :=
      fun hz27 => checkLogNat_sound consts (by simpa [hz27] using hlogZ)
    have hpMin_lt : pMin < 27000 := (mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)).2.1
    have hm := computeMertensTail2c_sound consts hGRH hCls hMert (fun _ => by omega) hLogZ hokM
    have hv := v2TailLb2c_sound consts hGRH hCls hMert (fun _ => by omega) hLogZ hokV
    have hnd_real : ((BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * lo.mOdd + 1)).card : ℝ) ≤ (lo.nD : ℝ) := by
      have hcard := BuchstabSwitching.card_bonfDivisors_le_factorial_sum hsplit.1
        (fun p hp => (hsplit.2.2.2.1 p hp).1) (fun p hp => (hsplit.2.2.2.2 p hp).1) (2 * lo.mOdd + 1)
        (hm.2.2.trans (by simpa [SciProofs.ofNat_toReal] using SciProofs.ble_sound hpi))
      rw [hsplit.2.2.1] at hcard
      have hble := SciProofs.ble_sound hnd; rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal, SciProofs.ofNat_toReal] at hble
      have h1 := mul_le_mul_of_nonneg_left (sumPowDivFactUb_sound lo.piZUb (2 * lo.mOdd + 1)) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ lo.a)
      push_cast at hble; linarith
    have hd_max_le : ∀ d ∈ BuchstabSwitching.bonfDivisors Q₁ P₂ (2 * lo.mOdd + 1), (d : ℝ) ≤ (lo.dMax : ℝ) := by
      intro d hd
      have hbd := BuchstabSwitching.bonfDivisors_le_prod_mul_pow_of_pos (by omega : 1 ≤ c.z)
        (fun p hp => (hsplit.2.2.2.1 p hp).1.pos) (fun p hp => (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2.le) hd
      have hqprod : ∏ p ∈ Q₁, p = (oddPrimesLt27000.take lo.a).prod := by
        simpa using List.prod_toFinset (fun x : ℕ => x) oddPrimesLt27000_nodup.take
      exact_mod_cast (hqprod ▸ hbd).trans hd_le
    have hg_pos_r : 0 < lo.gLb.toReal := by unfold SciNat.toReal; exact div_pos (by exact_mod_cast hg_pos) (by positivity)
    have hrat_bonf := BuchstabSwitching.analytic_bonf_RTrunc_odd_lb
      (fun p hp => ⟨(hsplit.2.2.2.2 p hp).1, (mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)).1.trans (hsplit.2.2.2.2 p hp).2.2⟩)
      lo.mOdd hg_pos_r ((SciProofs.ble_sound hg_le).trans hv.2) (hm.1.trans (SciProofs.ble_sound hs1))
    have hden_pos : 0 < ((SciNat.ofNat (Nat.factorial (2 * lo.mOdd + 2))).mul lo.gLb).toReal := by
      rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hg_pos_r
    have herr_le : lo.s1Ub.toReal ^ (2 * lo.mOdd + 2) / ((Nat.factorial (2 * lo.mOdd + 2) : ℝ) * lo.gLb.toReal) ≤
        (divUbSig (sciPowUb lo.s1Ub (2 * lo.mOdd + 2)) ((SciNat.ofNat (Nat.factorial (2 * lo.mOdd + 2))).mul lo.gLb) 24).toReal := by
      have h1 : lo.s1Ub.toReal ^ (2 * lo.mOdd + 2) / ((Nat.factorial (2 * lo.mOdd + 2) : ℝ) * lo.gLb.toReal) ≤
          (sciPowUb lo.s1Ub (2 * lo.mOdd + 2)).toReal / ((SciNat.ofNat (Nat.factorial (2 * lo.mOdd + 2))).mul lo.gLb).toReal := by
        rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal]
        exact div_le_div_of_nonneg_right (sciPowUb_sound lo.s1Ub (2 * lo.mOdd + 2))
          (by rw [← SciProofs.ofNat_toReal, ← SciProofs.mul_toReal]; exact hden_pos.le)
      exact h1.trans (divUbSig_le _ _ 24)
    exact ⟨⟨Q₁, P₂, hsplit.1, hsplit.2.1, lo.mOdd, lo.dMax, hd_max_le,
      Real.le_sqrt_of_sq_le (by exact_mod_cast hd_sq), lo.nD, lo.ratLb.toReal, hnd_real,
      (ratLb_of_sub_ble herr1 hrat herr_le).trans hrat_bonf⟩, le_rfl,
      remNorm_le_of_ble (Nat.cast_nonneg _) (by rw [SciProofs.ofNat_toReal]) hepd hv_pos hrem⟩
  · unfold checkOddBonfLower2c at h; simp only [ha_sm, ↓reduceDIte] at h; simp at h

end OddBonfLower2c

end

end BuchstabSwitching.SieveInst
