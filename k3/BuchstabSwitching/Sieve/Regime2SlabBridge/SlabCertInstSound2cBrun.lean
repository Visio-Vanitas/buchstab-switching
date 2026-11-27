import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cLower
import BuchstabSwitching.Sieve.BrunBlockSieve.MainTermAndModulus
import BuchstabSwitching.Sieve.BrunBlockSieve.CountAndSieveBound
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Soundness of Regime `2c` Brun-Block Lower-Sieve Witness Verification (`Dyadic`)

Verifies `Lower2cWitness` with `isBrun = true` (`checkBrunLower2c`, `brunLower2c_sound`)
via `BrunStepWitness` records and combines `OddBonf` and `BrunBlock` into
`checkLower2cWitness` / `lower2c_sound` for all `66` Regime `2c` slabs.
-/

namespace BuchstabSwitching.SieveInst

section

section BrunBlockLower2c

/-- Recursive blocks `[b, a)` of odd primes from descending endpoints `ends`. -/
def brunBlocksOfEnds : List ℕ → List (Finset ℕ)
  | a :: b :: t => ((BuchstabSwitching.fullOddPrimesBelow a).filter (b ≤ ·)) :: brunBlocksOfEnds (b :: t)
  | _ => []

def checkEndsDesc : List ℕ → Bool
  | a :: b :: t => decide (b < a) && checkEndsDesc (b :: t)
  | _ => true

def checkCapsMono : List ℕ → Bool
  | a :: b :: t => decide (a ≤ b) && checkCapsMono (b :: t)
  | _ => true

def brunModBoundAux : ℕ → List ℕ → List ℕ → ℕ
  | prev, m :: ms, z :: zs => z ^ (m - prev) * brunModBoundAux m ms zs
  | _, _, _ => 1

def brunAdmCountNat (szs caps : List ℕ) : ℕ :=
  ∑ c ∈ Finset.range (caps.getD (szs.length - 1) 0 + 1), BuchstabSwitching.brunAdmDPList (szs.zip caps) c

private def brunAdmStepAt (sz : ℕ) (dp : List ℕ) (c : ℕ) : ℕ :=
  (List.range (c + 1)).foldl (fun acc k => acc + dp.getD k 0 * fastChoose sz (c - k)) 0

private def brunAdmStepFast (sz cap : ℕ) (dp : List ℕ) : List ℕ :=
  (List.range (cap + 1)).map (brunAdmStepAt sz dp)

/-- `List ℕ`-memoized DP equivalent to `brunAdmCountNat` using `fastChoose`. -/
def brunAdmCountFast (szs caps : List ℕ) : ℕ :=
  let finalDp := (szs.zip caps).foldl (fun dp p => brunAdmStepFast p.1 p.2 dp) [1]
  (List.range (caps.getD (szs.length - 1) 0 + 1)).foldl (fun acc c => acc + finalDp.getD c 0) 0

private lemma brunAdmStepFast_getD (sz cap : ℕ) (dp : List ℕ) (c : ℕ) :
    (brunAdmStepFast sz cap dp).getD c 0 =
      BuchstabSwitching.brunAdmStep sz cap (fun k => dp.getD k 0) c := by
  unfold brunAdmStepFast BuchstabSwitching.brunAdmStep
  by_cases hc : c ≤ cap
  · have hlt : c < ((List.range (cap + 1)).map (brunAdmStepAt sz dp)).length := by simp; omega
    simp only [hc, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.getElem_map, List.getElem_range]
    unfold brunAdmStepAt; rw [foldl_range_sum_eq]
    exact Finset.sum_congr rfl fun k _ => by rw [fastChoose_eq_choose, List.getD_eq_getElem?_getD]
  · have hge : ((List.range (cap + 1)).map (brunAdmStepAt sz dp)).length ≤ c := by simp; omega
    simp only [hc, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]

private lemma brunAdmDPFast_getD : ∀ (pairs : List (ℕ × ℕ)) (dpL : List ℕ) (dpF : ℕ → ℕ),
    (∀ c, dpL.getD c 0 = dpF c) →
    ∀ c, (pairs.foldl (fun dp p => brunAdmStepFast p.1 p.2 dp) dpL).getD c 0 =
      pairs.foldl (fun dp p => BuchstabSwitching.brunAdmStep p.1 p.2 dp) dpF c
  | [], _, _, hdp, c => hdp c
  | p :: rest, dpL, dpF, hdp, c => by
    simp only [List.foldl_cons]
    refine brunAdmDPFast_getD rest (brunAdmStepFast p.1 p.2 dpL)
      (BuchstabSwitching.brunAdmStep p.1 p.2 dpF) (fun x => ?_) c
    rw [brunAdmStepFast_getD, (funext hdp : (fun k => dpL.getD k 0) = dpF)]

lemma brunAdmCountFast_eq_nat (szs caps : List ℕ) :
    brunAdmCountFast szs caps = brunAdmCountNat szs caps := by
  unfold brunAdmCountFast brunAdmCountNat BuchstabSwitching.brunAdmDPList
  rw [foldl_range_sum_eq]
  exact Finset.sum_congr rfl fun c _ => brunAdmDPFast_getD (szs.zip caps) [1]
    (fun x => if x = 0 then 1 else 0) (fun x => by cases x <;> rfl) c

def listLast : List ℕ → ℕ | [] => 0 | [x] => x | _ :: xs => listLast xs

private lemma brunBlocksOfEnds_length : ∀ ends : List ℕ, (brunBlocksOfEnds ends).length = ends.length - 1
  | [] | [_] => rfl
  | _ :: b :: t => by simp only [brunBlocksOfEnds, List.length_cons, brunBlocksOfEnds_length (b :: t)]; omega

private lemma brunBlocksOfEnds_getD : ∀ (ends : List ℕ) (i : ℕ), i < ends.length - 1 →
    (brunBlocksOfEnds ends).getD i ∅ =
      (BuchstabSwitching.fullOddPrimesBelow (ends.getD i 1)).filter (ends.getD (i + 1) 1 ≤ ·)
  | _ :: _ :: _, 0, _ => by simp [brunBlocksOfEnds]
  | _ :: b :: t, k + 1, hk => by
    simpa [brunBlocksOfEnds] using brunBlocksOfEnds_getD (b :: t) k (by simpa using Nat.lt_of_succ_lt_succ hk)
  | [], _, hk | [_], _, hk => by simp at hk

private lemma checkEndsDesc_getD : ∀ (xs : List ℕ), checkEndsDesc xs = true →
    (∀ i j, i ≤ j → j < xs.length → xs.getD j 1 ≤ xs.getD i 1) ∧
    (xs ≠ [] → ∀ i, i < xs.length → listLast xs ≤ xs.getD i 1)
  | [], _ => ⟨fun _ _ _ hj => by simp at hj, fun h => absurd rfl h⟩
  | [a], _ => ⟨fun i j _ hj => by simp at hj; rcases (by omega : i = 0) with rfl; rcases (by omega : j = 0) with rfl; exact le_rfl,
      fun _ i hi => by simp at hi; subst hi; simp [listLast]⟩
  | a :: b :: t, h => by
    simp only [checkEndsDesc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := checkEndsDesc_getD (b :: t) h.2
    refine ⟨fun i j hij hj => ?_, fun _ i hi => ?_⟩
    · cases i with
      | zero => cases j with
        | zero => exact le_rfl
        | succ k => have := ih.1 0 k (Nat.zero_le _) (by simpa using Nat.lt_of_succ_lt_succ hj); simp at this ⊢; omega
      | succ i' => cases j with
        | zero => omega
        | succ j' => simpa using ih.1 i' j' (Nat.succ_le_succ_iff.mp hij) (by simpa using Nat.lt_of_succ_lt_succ hj)
    · cases i with
      | zero => simpa [listLast] using (ih.2 (List.cons_ne_nil _ _) 0 (by simp)).trans h.1.le
      | succ i' => simpa [listLast] using ih.2 (List.cons_ne_nil _ _) i' (by simpa using Nat.lt_of_succ_lt_succ hi)

private lemma checkCapsMono_sound : ∀ (xs : List ℕ), checkCapsMono xs = true →
    ∀ i j, i ≤ j → j < xs.length → xs.getD i 0 ≤ xs.getD j 0
  | [], _, _, _, _, hj => by simp at hj
  | [_], _, i, j, _, hj => by simp at hj; rcases (by omega : i = 0) with rfl; rcases (by omega : j = 0) with rfl; exact le_rfl
  | a :: b :: t, h, i, j, hij, hj => by
    simp only [checkCapsMono, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := checkCapsMono_sound (b :: t) h.2
    cases i with
    | zero => cases j with
      | zero => simp
      | succ j' => have := ih 0 j' (Nat.zero_le _) (by simpa using Nat.lt_of_succ_lt_succ hj); simp at this ⊢; omega
    | succ i' => cases j with
      | zero => omega
      | succ j' => simpa using ih i' j' (Nat.succ_le_succ_iff.mp hij) (by simpa using Nat.lt_of_succ_lt_succ hj)

private lemma brunBlocks_props : ∀ (ends : List ℕ),
    checkEndsDesc ends = true → 3 ≤ listLast ends →
    (∀ B ∈ brunBlocksOfEnds ends, ∀ p ∈ B, p < ends.headD 0) ∧
    (brunBlocksOfEnds ends).Pairwise Disjoint ∧
    BuchstabSwitching.brunUnion (brunBlocksOfEnds ends) =
      (Finset.Ico (listLast ends) (ends.headD 0)).filter Nat.Prime
  | [], _, h3 => by simp [listLast] at h3
  | [a], _, _ => by simp [brunBlocksOfEnds, BuchstabSwitching.brunUnion, listLast]
  | a :: b :: t, h, h3 => by
    simp only [checkEndsDesc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := brunBlocks_props (b :: t) h.2 (by simpa [listLast] using h3)
    have hlb : listLast (a :: b :: t) ≤ b := (checkEndsDesc_getD (b :: t) h.2).2 (List.cons_ne_nil _ _) 0 (by simp)
    refine ⟨fun B hB p hp => ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hB with rfl | hB'
      · exact (BuchstabSwitching.fullOddPrimesBelow_mem_iff.mp (Finset.mem_filter.mp hp).1).1
      · have hbh : (b :: t).headD 0 = b := rfl
        exact ((ih.1 B hB' p hp).trans_eq hbh).trans h.1
    · rw [brunBlocksOfEnds, List.pairwise_cons]
      refine ⟨fun B hB => Finset.disjoint_left.mpr fun p h1 h2 => ?_, ih.2.1⟩
      have := (Finset.mem_filter.mp h1).2; have hlt := ih.1 B hB p h2
      have hbh : (b :: t).headD 0 = b := rfl
      omega
    · rw [brunBlocksOfEnds, BuchstabSwitching.brunUnion, List.foldr_cons]
      change ((BuchstabSwitching.fullOddPrimesBelow a).filter (b ≤ ·)) ∪
        BuchstabSwitching.brunUnion (brunBlocksOfEnds (b :: t)) = _
      rw [ih.2.2]; ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico,
        BuchstabSwitching.fullOddPrimesBelow_mem_iff, List.headD_cons] at hlb ⊢
      have hll : listLast (a :: b :: t) = listLast (b :: t) := rfl
      constructor
      · rintro (⟨⟨hpa, hp, _⟩, hbp⟩ | ⟨⟨hlp, hpb⟩, hp⟩)
        · exact ⟨⟨hll ▸ hlb.trans hbp, hpa⟩, hp⟩
        · exact ⟨⟨hll ▸ hlp, hpb.trans h.1⟩, hp⟩
      · rintro ⟨⟨hlp, hpa⟩, hp⟩
        by_cases hbp : b ≤ p
        · exact Or.inl ⟨⟨hpa, hp, by omega⟩, hbp⟩
        · exact Or.inr ⟨⟨hll ▸ hlp, by omega⟩, hp⟩

private lemma brunPrefix_blocks_eq : ∀ (ends : List ℕ),
    checkEndsDesc ends = true → 3 ≤ listLast ends →
    ∀ i, i < ends.length - 1 →
      BuchstabSwitching.brunPrefix (brunBlocksOfEnds ends) (i + 1) =
        (Finset.Ico (ends.getD (i + 1) 1) (ends.headD 0)).filter Nat.Prime
  | a :: b :: t, h, h3, 0, _ => by
    simp only [checkEndsDesc, Bool.and_eq_true, decide_eq_true_eq] at h
    have h3b := (by simpa [listLast] using h3 : 3 ≤ listLast (b :: t)).trans
      ((checkEndsDesc_getD (b :: t) h.2).2 (List.cons_ne_nil _ _) 0 (by simp))
    simp only [List.getD_cons_zero] at h3b
    rw [BuchstabSwitching.brunPrefix_succ _ (by simp [brunBlocksOfEnds]),
      BuchstabSwitching.brunPrefix_zero, Finset.empty_union]
    ext p; simp only [brunBlocksOfEnds, List.getD_cons_zero, List.getD_cons_succ, List.headD_cons,
      Finset.mem_filter, BuchstabSwitching.fullOddPrimesBelow_mem_iff, Finset.mem_Ico]
    exact ⟨fun ⟨⟨hpa, hp, _⟩, hbp⟩ => ⟨⟨hbp, hpa⟩, hp⟩, fun ⟨⟨hbp, hpa⟩, hp⟩ => ⟨⟨hpa, hp, by omega⟩, hbp⟩⟩
  | a :: b :: t, h, h3, k + 1, hk => by
    simp only [checkEndsDesc, Bool.and_eq_true, decide_eq_true_eq] at h
    have hk' : k < (b :: t).length - 1 := by simp only [List.length_cons] at hk ⊢; omega
    have hpref : BuchstabSwitching.brunPrefix (brunBlocksOfEnds (a :: b :: t)) (k + 2) =
        ((BuchstabSwitching.fullOddPrimesBelow a).filter (b ≤ ·)) ∪
          BuchstabSwitching.brunPrefix (brunBlocksOfEnds (b :: t)) (k + 1) := by
      simp [brunBlocksOfEnds, BuchstabSwitching.brunPrefix]
    rw [hpref, brunPrefix_blocks_eq (b :: t) h.2 (by simpa [listLast] using h3) k hk']
    have hle_b := (checkEndsDesc_getD (b :: t) h.2).1 0 (k + 1) (Nat.zero_le _) (by simpa using hk')
    have h3k := (by simpa [listLast] using h3 : 3 ≤ listLast (b :: t)).trans
      ((checkEndsDesc_getD (b :: t) h.2).2 (List.cons_ne_nil _ _) (k + 1) (by simpa using hk'))
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.headD_cons] at hle_b h3k ⊢
    ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico, BuchstabSwitching.fullOddPrimesBelow_mem_iff]
    constructor
    · rintro (⟨⟨hpa, hp, _⟩, hbp⟩ | ⟨⟨hkp, hpb⟩, hp⟩)
      · exact ⟨⟨hle_b.trans hbp, hpa⟩, hp⟩
      · exact ⟨⟨hkp, hpb.trans h.1⟩, hp⟩
    · rintro ⟨⟨hkp, hpa⟩, hp⟩
      by_cases hbp : b ≤ p
      · exact Or.inl ⟨⟨hpa, hp, by omega⟩, hbp⟩
      · exact Or.inr ⟨⟨hkp, by omega⟩, hp⟩
  | [], _, _, _, hk | [_], _, _, _, hk => by simp at hk

private lemma brunModBoundAux_eq : ∀ (caps ends : List ℕ) (prev : ℕ),
    caps.length < ends.length →
    ∏ i ∈ Finset.range caps.length,
      (ends.getD i 1) ^ (caps.getD i 0 - if i = 0 then prev else caps.getD (i - 1) 0) =
    brunModBoundAux prev caps ends
  | [], _, _, _ => by simp [brunModBoundAux]
  | m :: ms, z :: zs, prev, hlen => by
    simp only [List.length_cons] at hlen ⊢; rw [Finset.prod_range_succ']
    simp only [List.getD_cons_zero, ↓reduceIte, brunModBoundAux]
    rw [mul_comm, ← brunModBoundAux_eq ms zs m (by omega)]
    congr 1; refine Finset.prod_congr rfl fun i _ => ?_; cases i <;> simp
  | _ :: _, [], _, hlen => by simp at hlen

private lemma brunAdmDPList_mono : ∀ (l₁ l₂ : List (ℕ × ℕ)) (dp₁ dp₂ : ℕ → ℕ)
    (hlen : l₁.length = l₂.length),
    (∀ i (hi : i < l₁.length), (l₁[i]).1 ≤ (l₂[i]'(hlen ▸ hi)).1 ∧ (l₁[i]).2 = (l₂[i]'(hlen ▸ hi)).2) →
    (∀ c, dp₁ c ≤ dp₂ c) →
    ∀ c, l₁.foldl (fun dp p => BuchstabSwitching.brunAdmStep p.1 p.2 dp) dp₁ c ≤
      l₂.foldl (fun dp p => BuchstabSwitching.brunAdmStep p.1 p.2 dp) dp₂ c
  | [], [], _, _, _, _, hdp, c => hdp c
  | _ :: t₁, _ :: t₂, dp₁, dp₂, hlen, hpair, hdp, c => by
    have h0 := hpair 0 (by simp); simp only [List.getElem_cons_zero] at h0
    refine brunAdmDPList_mono t₁ t₂ _ _ (by simpa using hlen)
      (fun i hi => hpair (i + 1) (Nat.succ_lt_succ hi)) (fun x => by
        dsimp only; rw [h0.2]; unfold BuchstabSwitching.brunAdmStep; split_ifs
        · exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul (hdp k) (Nat.choose_le_choose (x - k) h0.1)
        · exact le_rfl) c
  | [], _ :: _, _, _, hlen, _, _, _ | _ :: _, [], _, _, hlen, _, _, _ => by simp at hlen

private lemma brunAdmCount_le_nat {blocks : List (Finset ℕ)} {szs caps : List ℕ}
    (hlen_sz : szs.length = blocks.length) (hlen_c : caps.length = blocks.length)
    (hsz : ∀ i (hi : i < blocks.length), (blocks[i]).card ≤ szs[i]'(by omega)) :
    BuchstabSwitching.brunAdmCount blocks caps ≤ brunAdmCountNat szs caps := by
  unfold BuchstabSwitching.brunAdmCount brunAdmCountNat BuchstabSwitching.brunAdmDPList; rw [hlen_sz]
  refine Finset.sum_le_sum fun c _ => brunAdmDPList_mono _ _ _ _
    (by simp [List.length_zip, hlen_sz, hlen_c]) (fun i hi => by
      simp only [List.length_zip, List.length_map, hlen_c, min_self] at hi
      exact ⟨by simpa [List.getElem_zip, List.getElem_map] using hsz i hi, by simp [List.getElem_zip]⟩)
    (fun _ => le_rfl) c

private def checkBrunBlocksLoop (z : ℕ) (zLogLb zLogUb : Dyadic) :
    List ℕ → List ℕ → List BrunStepWitness → Bool × List ℕ × Dyadic
  | cur :: nxt :: rest, cap :: caps, st :: steps =>
    let nxtLo := st.bTail.uLogLb
    let nxtHi := st.bTail.uLogUb
    let curLo := if cur == z then zLogLb else st.bTail.vLogLb
    let curHi := if cur == z then zLogUb else st.bTail.vLogUb
    let okNxtLog := if 27000 ≤ nxt then checkLogNat nxt st.wNxtLog nxtLo nxtHi else true
    let okCurLog :=
      if cur == z then true
      else if 27000 < cur then checkLogNat cur st.wCurLog curLo curHi
      else true
    let okB := checkMertensTailWithLogs nxt cur nxtLo nxtHi curLo curHi st.bTail
    let okT := checkMertensTailWithLogs nxt z nxtLo nxtHi zLogLb zLogUb st.tTail
    let errDen := (Dyadic.ofNat (Nat.factorial (cap + 1))).mulLb st.tTail.gLb
    let okTerm := decide (0 < st.tTail.gLb.m) &&
      (st.tTail.s1Ub.powUb (cap + 1)).ble (st.termUb.mulLb errDen)
    let recRes := checkBrunBlocksLoop z zLogLb zLogUb (nxt :: rest) caps steps
    (okNxtLog && okCurLog && okB && okT && okTerm && recRes.1,
     st.bTail.piUb :: recRes.2.1,
     st.termUb.add recRes.2.2)
  | [_], [], [] => (true, [], dyZero)
  | _, _, _ => (false, [], dyZero)

private lemma checkBrunBlocksLoop_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {z : ℕ} {zLogLb zLogUb : Dyadic}
    (hzLog : 27000 < z → zLogLb.toReal ≤ Real.log (z : ℝ) ∧ Real.log (z : ℝ) ≤ zLogUb.toReal) :
    ∀ (ends caps : List ℕ) (steps : List BrunStepWitness),
      ends.length = caps.length + 1 →
      checkEndsDesc ends = true →
      3 ≤ listLast ends →
      ends.headD 0 ≤ z →
      (checkBrunBlocksLoop z zLogLb zLogUb ends caps steps).1 = true →
      let res := checkBrunBlocksLoop z zLogLb zLogUb ends caps steps
      res.2.1.length = caps.length ∧
      (∀ i, i < caps.length →
        (((Finset.Ico (ends.getD (i + 1) 1) (ends.getD i 1)).filter Nat.Prime).card : ℝ) ≤
          (res.2.1.getD i 0 : ℝ)) ∧
      (∑ i ∈ Finset.range caps.length,
        (∑ p ∈ (Finset.Ico (ends.getD (i + 1) 1) z).filter Nat.Prime, BuchstabSwitching.gTot p) ^
            (caps.getD i 0 + 1) /
          ((Nat.factorial (caps.getD i 0 + 1) : ℝ) *
            BuchstabSwitching.V2 BuchstabSwitching.gTot
              ((Finset.Ico (ends.getD (i + 1) 1) z).filter Nat.Prime))) ≤ res.2.2.toReal
  | [_], [], [], _, _, _, _, _ => by simp [checkBrunBlocksLoop, dyZero_toReal]
  | [_], [], _ :: _, _, _, _, _, h => by simp [checkBrunBlocksLoop] at h
  | _ :: _ :: _, _ :: _, [], _, _, _, _, h => by simp [checkBrunBlocksLoop] at h
  | cur :: nxt :: rest, cap :: caps, st :: steps, hlen, hdesc, h3_last, hhead, h => by
    unfold checkBrunBlocksLoop at h
    dsimp only at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨h1_5, hokRec⟩
    rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hokTerm⟩
    rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hokT⟩
    rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, hokB⟩
    rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hokNxt, hokCur⟩
    rcases (Bool.and_eq_true _ _).mp hokTerm with ⟨hgPos_b, hterm_ble⟩
    simp only [checkEndsDesc, Bool.and_eq_true, decide_eq_true_eq] at hdesc
    have h3_rest : 3 ≤ listLast (nxt :: rest) := by simpa [listLast] using h3_last
    have h3_nxt : 3 ≤ nxt := by
      have hlb := (checkEndsDesc_getD (nxt :: rest) hdesc.2).2 (List.cons_ne_nil _ _) 0 (by simp)
      simpa using h3_rest.trans hlb
    have hrec := checkBrunBlocksLoop_sound consts hGRH hCls hMert hzLog (nxt :: rest) caps steps
      (by simpa using hlen) hdesc.2 h3_rest (le_trans hdesc.1.le hhead) hokRec
    have hNxtLog : 27000 ≤ nxt →
        st.bTail.uLogLb.toReal ≤ Real.log (nxt : ℝ) ∧ Real.log (nxt : ℝ) ≤ st.bTail.uLogUb.toReal :=
      fun hge => checkLogNat_sound consts (by simpa [hge] using hokNxt)
    set curLo := if cur == z then zLogLb else st.bTail.vLogLb
    set curHi := if cur == z then zLogUb else st.bTail.vLogUb
    have hCurLog : 27000 < cur →
        curLo.toReal ≤ Real.log (cur : ℝ) ∧ Real.log (cur : ℝ) ≤ curHi.toReal := by
      intro hgt
      by_cases hcz : (cur == z) = true
      · have heq : cur = z := beq_iff_eq.mp hcz
        dsimp only [curLo, curHi]; simp only [hcz, ↓reduceIte]
        subst heq; exact hzLog hgt
      · dsimp only [curLo, curHi] at hokCur ⊢
        simp only [hcz, Bool.false_eq_true, ↓reduceIte, hgt] at hokCur ⊢
        exact checkLogNat_sound consts hokCur
    have hB := checkMertensTailWithLogs_sound consts hGRH hCls hMert hNxtLog hCurLog hokB
    have hT := checkMertensTailWithLogs_sound consts hGRH hCls hMert hNxtLog hzLog hokT
    have hV_pos : 0 < st.tTail.gLb.toReal := Dyadic.toReal_pos_of_m (decide_eq_true_eq.mp hgPos_b)
    have hV_le := hT.2.2.2 h3_nxt
    refine ⟨by simp only [checkBrunBlocksLoop, List.length_cons]; exact congrArg (· + 1) hrec.1,
      fun i hi => ?_, ?_⟩
    · cases i with
      | zero => simp only [checkBrunBlocksLoop, List.getD_cons_zero]; exact hB.2.2.1
      | succ k =>
        simp only [checkBrunBlocksLoop, List.getD_cons_succ]
        exact hrec.2.1 k (by simpa using Nat.lt_of_succ_lt_succ hi)
    · rw [List.length_cons, Finset.sum_range_succ', add_comm]
      simp only [List.getD_cons_zero, List.getD_cons_succ, checkBrunBlocksLoop, Dyadic.add_toReal]
      have hS1_nn : 0 ≤ ∑ p ∈ (Finset.Ico nxt z).filter Nat.Prime, BuchstabSwitching.gTot p :=
        Finset.sum_nonneg fun p _ => BuchstabSwitching.gTot_nonneg p
      have hnum : (∑ p ∈ (Finset.Ico nxt z).filter Nat.Prime, BuchstabSwitching.gTot p) ^ (cap + 1) ≤
          (st.tTail.s1Ub.powUb (cap + 1)).toReal :=
        (pow_le_pow_left₀ hS1_nn hT.1 _).trans (Dyadic.powUb_sound _ _)
      have hden_pos : 0 < (Nat.factorial (cap + 1) : ℝ) *
          BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico nxt z).filter Nat.Prime) :=
        mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (lt_of_lt_of_le hV_pos hV_le)
      have hden_le : ((Dyadic.ofNat (Nat.factorial (cap + 1))).mulLb st.tTail.gLb).toReal ≤
          (Nat.factorial (cap + 1) : ℝ) *
            BuchstabSwitching.V2 BuchstabSwitching.gTot ((Finset.Ico nxt z).filter Nat.Prime) :=
        (Dyadic.mulLb_le _ _).trans (by
          rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left hV_le (Nat.cast_nonneg _))
      exact add_le_add (Dyadic.div_le_of_ble_mulLb hnum hden_pos hden_le hterm_ble) hrec.2.2
  | [], _, _, hlen, _, _, _, _ | [_], _ :: _, _, hlen, _, _, _, _ => by simp at hlen
  | _ :: _ :: _, [], _, _, _, _, _, h => by simp [checkBrunBlocksLoop] at h

/-- Computable binary witness checker for `Lower2cWitness` with `isBrun = true`. -/
def checkBrunLower2c (c : BuchstabSwitching.SlabCert)
    (zLogLb zLogUb epdUb vFullLb : Dyadic) (lo : Lower2cWitness) : Bool :=
  if h : lo.a < smallOddPrimes40.length then
    let pMin := smallOddPrimes40[lo.a]
    let pA := if lo.a = 0 then 2 else smallOddPrimes40[lo.a - 1]!
    let loopRes := checkBrunBlocksLoop c.z zLogLb zLogUb lo.ends lo.caps lo.brunSteps
    decide (1 ≤ lo.caps.length) &&
    decide (lo.ends.length = lo.caps.length + 1) &&
    decide (lo.ends.headD 0 = c.z) &&
    checkEndsDesc lo.ends &&
    decide (pA < listLast lo.ends) &&
    decide (listLast lo.ends ≤ pMin) &&
    decide (pMin < c.z) &&
    lo.caps.all (fun m => decide (m % 2 = 1)) &&
    checkCapsMono lo.caps &&
    decide ((smallOddPrimes40.take lo.a).prod * brunModBoundAux 0 lo.caps lo.ends ≤ lo.dMax) &&
    decide (lo.dMax ^ 2 ≤ c.X_lo) &&
    loopRes.1 &&
    decide ((1 <<< lo.a) * brunAdmCountFast loopRes.2.1 lo.caps ≤ lo.nD) &&
    (lo.ratLb.add loopRes.2.2).ble dyOne &&
    ((Dyadic.ofNat lo.nD).mulUb epdUb).ble (lo.remANormUb.mulLb vFullLb)
  else false

lemma brunLower2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLb zLogUb epdUb vFullLb : Dyadic} {lo : Lower2cWitness}
    (hzLog : 27000 < c.z → zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ zLogUb.toReal)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal)
    (h : checkBrunLower2c c zLogLb zLogUb epdUb vFullLb lo = true) :
    ∃ s : External.BrunBlockLowerSpec c (c.X_lo : ℝ),
      lo.ratLb.toReal ≤ s.rat_lb ∧
      s.n_d * BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) / vFullLb.toReal ≤
        lo.remANormUb.toReal := by
  by_cases ha_sm : lo.a < smallOddPrimes40.length
  · have ha : lo.a < oddPrimesLt27000.length := lt_of_lt_of_le ha_sm smallOddPrimes40_len_le
    unfold checkBrunLower2c at h
    simp only [ha_sm, ↓reduceDIte] at h
    rw [smallOddPrimes40_getElem ha_sm, smallOddPrimes40_take ha_sm.le, brunAdmCountFast_eq_nat] at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨h1_14, hrem⟩
    rcases (Bool.and_eq_true _ _).mp h1_14 with ⟨h1_13, hrat⟩
    rcases (Bool.and_eq_true _ _).mp h1_13 with ⟨h1_12, hnd_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_12 with ⟨h1_11, hokL⟩
    rcases (Bool.and_eq_true _ _).mp h1_11 with ⟨h1_10, hd_sq_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_10 with ⟨h1_9, hd_le_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_9 with ⟨h1_8, hmono_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_8 with ⟨h1_7, hodd_all⟩
    rcases (Bool.and_eq_true _ _).mp h1_7 with ⟨h1_6, hpz_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_6 with ⟨h1_5, hb2_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_5 with ⟨h1_4, hb1_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_4 with ⟨h1_3, hdesc⟩
    rcases (Bool.and_eq_true _ _).mp h1_3 with ⟨h1_2, he0_b⟩
    rcases (Bool.and_eq_true _ _).mp h1_2 with ⟨hc1_b, hlen_b⟩
    have hlen : lo.ends.length = lo.caps.length + 1 := decide_eq_true_eq.mp hlen_b
    have he0 : lo.ends.headD 0 = c.z := decide_eq_true_eq.mp he0_b
    have hb1 := decide_eq_true_eq.mp hb1_b
    have hb2 : listLast lo.ends ≤ oddPrimesLt27000[lo.a] := decide_eq_true_eq.mp hb2_b
    have hpz : oddPrimesLt27000[lo.a] < c.z := decide_eq_true_eq.mp hpz_b
    have hodd_b : ∀ m ∈ lo.caps, m % 2 = 1 :=
      fun m hm => decide_eq_true_eq.mp (List.all_eq_true.mp hodd_all m hm)
    have hd_le := decide_eq_true_eq.mp hd_le_b
    have hd_sq := decide_eq_true_eq.mp hd_sq_b
    have hnd_nat : 2 ^ lo.a * brunAdmCountNat (checkBrunBlocksLoop c.z zLogLb zLogUb lo.ends lo.caps lo.brunSteps).2.1 lo.caps ≤ lo.nD := by
      have hsh := decide_eq_true_eq.mp hnd_b
      rwa [Nat.shiftLeft_eq, Nat.one_mul] at hsh
    set pMin := oddPrimesLt27000[lo.a]
    set bLast := listLast lo.ends
    have hpA_lt : (if lo.a = 0 then 2 else oddPrimesLt27000[lo.a - 1]'(by omega)) < bLast := by
      by_cases ha0 : lo.a = 0
      · simpa [ha0, bLast] using hb1
      · have hprev : smallOddPrimes40[lo.a - 1]! = oddPrimesLt27000[lo.a - 1]'(by omega) := by
          simp only [getElem!_pos smallOddPrimes40 (lo.a - 1) (by omega)]
          exact smallOddPrimes40_getElem (by omega)
        simpa [ha0, bLast, hprev] using hb1
    have hsplit := oddPrimesLt27000_split_props ha (le_trans hb2 hpz.le) hpA_lt hb2
    have h3_last : 3 ≤ bLast := by
      by_cases ha0 : lo.a = 0
      · simp only [ha0, ↓reduceIte] at hpA_lt; omega
      · simp only [ha0, ↓reduceIte] at hpA_lt
        exact (mem_oddPrimesLt27000_iff.mp
          (List.getElem_mem (by omega : lo.a - 1 < oddPrimesLt27000.length))).2.2.trans hpA_lt.le
    set Q₁ : Finset ℕ := (oddPrimesLt27000.take lo.a).toFinset
    set blocks := brunBlocksOfEnds lo.ends
    have hlen_blocks : lo.caps.length = blocks.length := by simp [blocks, brunBlocksOfEnds_length, hlen]
    have hbp := brunBlocks_props lo.ends hdesc h3_last
    have hmono := checkCapsMono_sound lo.caps hmono_b
    have hEnds_prop := checkEndsDesc_getD lo.ends hdesc
    have hd_le_real : ∀ d ∈ BuchstabSwitching.brunDivisors Q₁ blocks lo.caps, (d : ℝ) ≤ (lo.dMax : ℝ) := by
      intro d hd; rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
      rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
      have hS₁_prod : ∏ p ∈ S₁, p ≤ (oddPrimesLt27000.take lo.a).prod := by
        have h1 := Finset.prod_le_prod_of_subset_of_one_le (Finset.mem_powerset.mp hS₁)
          fun p hp _ => (hsplit.2.2.2.1 p hp).1.one_lt.le
        have h2 : ∏ p ∈ Q₁, p = (oddPrimesLt27000.take lo.a).prod := by
          simpa using List.prod_toFinset (fun x : ℕ => x) oddPrimesLt27000_nodup.take
        exact h2 ▸ h1
      have hmod := BuchstabSwitching.brun_block_modbound blocks lo.caps (fun i => lo.ends.getD i 1)
        S₂ hbp.2.1 hlen_blocks
        (fun i hi => le_trans (by omega : 1 ≤ 3) (h3_last.trans
          (hEnds_prop.2 (fun h0 => by simp [h0] at hlen) i (by rw [← hlen_blocks] at hi; omega))))
        (fun i j hij hj => hEnds_prop.1 i j hij (by rw [← hlen_blocks] at hj; omega))
        (fun i j hij hj => hmono i j hij (hlen_blocks ▸ hj))
        (fun i hi p hp => by
          rw [brunBlocksOfEnds_getD lo.ends i (by rw [← hlen_blocks] at hi; omega), Finset.mem_filter,
            BuchstabSwitching.fullOddPrimesBelow_mem_iff] at hp; exact hp.1.1.le) (Finset.mem_filter.mp hS₂).2
      rw [← hlen_blocks] at hmod
      exact_mod_cast (Nat.mul_le_mul hS₁_prod (hmod.trans_eq (brunModBoundAux_eq lo.caps lo.ends 0 (by omega)))).trans hd_le
    have hloop := checkBrunBlocksLoop_sound consts hGRH hCls hMert hzLog lo.ends lo.caps lo.brunSteps
      hlen hdesc h3_last he0.le hokL
    have hnd_real : ((BuchstabSwitching.brunDivisors Q₁ blocks lo.caps).card : ℝ) ≤ (lo.nD : ℝ) := by
      have hcard_le : (BuchstabSwitching.brunDivisors Q₁ blocks lo.caps).card ≤
          2 ^ lo.a * (BuchstabSwitching.brunAdmSubsets blocks lo.caps).card :=
        Finset.card_image_le.trans (by rw [Finset.card_product, Finset.card_powerset, hsplit.2.2.1])
      rw [BuchstabSwitching.brun_block_adm_count_eq blocks lo.caps hbp.2.1 hlen_blocks] at hcard_le
      set szL := (checkBrunBlocksLoop c.z zLogLb zLogUb lo.ends lo.caps lo.brunSteps).2.1
      have hsz_nat : ∀ i (hi : i < blocks.length),
          (blocks[i]).card ≤ szL[i]'(by rw [hloop.1, hlen_blocks]; exact hi) := by
        intro i hi; have hreal := hloop.2.1 i (by omega)
        have heq_b : blocks[i] = (Finset.Ico (lo.ends.getD (i + 1) 1) (lo.ends.getD i 1)).filter Nat.Prime := by
          have hget : blocks[i] = blocks.getD i ∅ := by simp [List.getD_eq_getElem?_getD, hi]
          rw [hget, brunBlocksOfEnds_getD lo.ends i (by omega)]
          have h3 := h3_last.trans (hEnds_prop.2 (fun h0 => by simp [h0] at hlen) (i + 1) (by omega))
          ext p; simp only [Finset.mem_filter, BuchstabSwitching.fullOddPrimesBelow_mem_iff, Finset.mem_Ico]
          exact ⟨fun ⟨⟨hpa, hp, _⟩, hbp⟩ => ⟨⟨hbp, hpa⟩, hp⟩, fun ⟨⟨hbp, hpa⟩, hp⟩ => ⟨⟨hpa, hp, by omega⟩, hbp⟩⟩
        have hi_sz : i < szL.length := by rw [hloop.1, hlen_blocks]; exact hi
        have hget_sz : szL.getD i 0 = szL[i]'hi_sz := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_sz]
        rw [← heq_b, hget_sz] at hreal; exact_mod_cast hreal
      exact_mod_cast (hcard_le.trans (Nat.mul_le_mul_left _
        (brunAdmCount_le_nat (by rw [hloop.1, hlen_blocks]) hlen_blocks hsz_nat))).trans hnd_nat
    have herr_le : BuchstabSwitching.brunErrorBound blocks lo.caps BuchstabSwitching.gTot ≤
        (checkBrunBlocksLoop c.z zLogLb zLogUb lo.ends lo.caps lo.brunSteps).2.2.toReal := by
      unfold BuchstabSwitching.brunErrorBound; rw [← hlen_blocks]
      refine (Finset.sum_congr rfl fun i hi => ?_).trans_le hloop.2.2
      rw [brunPrefix_blocks_eq lo.ends hdesc h3_last i (by rw [Finset.mem_range] at hi; omega), he0]
    exact ⟨⟨Q₁, blocks, lo.caps, by rw [hbp.2.2, he0]; exact hsplit.1, hbp.2.1, hlen_blocks,
      fun m hm => Nat.odd_iff.mpr (hodd_b m hm), hmono, by rw [hbp.2.2, he0]; exact hsplit.2.1,
      lo.dMax, hd_le_real, Real.le_sqrt_of_sq_le (by exact_mod_cast hd_sq),
      lo.nD, lo.ratLb.toReal, hnd_real, ratLb_of_add_ble hrat herr_le⟩, le_rfl,
      remNorm_le_of_ble (Nat.cast_nonneg _) (by rw [Dyadic.ofNat_toReal]) hepd hv_pos hrem⟩
  · unfold checkBrunLower2c at h; simp only [ha_sm, ↓reduceDIte] at h; simp at h

end BrunBlockLower2c

section CombinedLower2c

/-- Unified Regime `2c` lower-sieve witness checker (`OddBonf` or `BrunBlock`). -/
def checkLower2cWitness (c : BuchstabSwitching.SlabCert)
    (zLogLb zLogUb epdUb vFullLb : Dyadic) (lo : Lower2cWitness) : Bool :=
  if lo.isBrun then checkBrunLower2c c zLogLb zLogUb epdUb vFullLb lo
  else checkOddBonfLower2c c zLogLb zLogUb epdUb vFullLb lo

lemma lower2c_sound (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {zLogLb zLogUb epdUb vFullLb : Dyadic} {lo : Lower2cWitness}
    (hzLog : 27000 < c.z → zLogLb.toReal ≤ Real.log (c.z : ℝ) ∧ Real.log (c.z : ℝ) ≤ zLogUb.toReal)
    (hepd : BuchstabSwitching.epdNormFn (c.X_lo : ℝ) consts.li2 (c.X_lo : ℝ) ≤ epdUb.toReal)
    (hv_pos : 0 < vFullLb.toReal) (hv_le : vFullLb.toReal ≤ External.VN 2 c.z)
    (h : checkLower2cWitness c zLogLb zLogUb epdUb vFullLb lo = true) :
    ∃ loEng : External.LowerEngine2c c (c.X_lo : ℝ),
      lo.ratLb.toReal ≤ loEng.saNorm ∧ loEng.remANorm consts.li2 ≤ lo.remANormUb.toReal := by
  unfold checkLower2cWitness at h; split_ifs at h with hbr
  · rcases brunLower2c_sound consts hGRH hCls hMert hzLog hepd hv_pos h with ⟨s, hs1, hs2⟩
    exact ⟨External.LowerEngine2c.brunBlock s vFullLb.toReal hv_pos hv_le, hs1, hs2⟩
  · rcases oddBonfLower2c_sound consts hGRH hCls hMert hzLog hepd hv_pos h with ⟨s, hs1, hs2⟩
    exact ⟨External.LowerEngine2c.oddBonf s vFullLb.toReal hv_pos hv_le, hs1, hs2⟩

end CombinedLower2c

end

end BuchstabSwitching.SieveInst
