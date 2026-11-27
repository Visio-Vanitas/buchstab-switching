import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTable
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstExpProofs
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTreeData

/-!
# Verified Static `OddPrimeTree` (`O(log N)` Range Queries `< 27000`)
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

def checkPrimeLeafEntry (e : PrimeLeafEntry) : Bool :=
  decide (3 ≤ e.p) &&
  decide (e.gLb64 * (e.p - 1) ≤ q64Scale) && decide (q64Scale ≤ e.gUb64 * (e.p - 1)) &&
  decide (q64Scale ≤ e.mulUb64 * (e.p * (e.p - 1))) &&
  decide (q64Scale ≤ e.sqUb64 * ((e.p - 1) ^ 2)) &&
  decide (e.vLb64 * (e.p - 1) ≤ (e.p - 2) * q64Scale) &&
  decide ((e.p - 2) * q64Scale ≤ e.vUb64 * (e.p - 1)) &&
  decide (e.p * q64Scale ≤ e.phiUb64 * (e.p - 1))

private def isStrictIncList : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictIncList (b :: rest)

private lemma isStrictIncList_pairwise :
    ∀ {xs : List ℕ}, isStrictIncList xs = true → xs.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [isStrictIncList, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := isStrictIncList_pairwise h.2
    exact List.pairwise_cons.mpr ⟨fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hmem
      · exact h.1
      · exact lt_trans h.1 ((List.pairwise_cons.mp ih).1 y hmem), ih⟩

private def addEntrySummary (s : TreeSummary) (x : PrimeLeafEntry) : TreeSummary :=
  ⟨s.lo, x.p, s.cnt + 1,
   s.s1Ub.add (Dyadic.ofQ64 x.gUb64),
   s.sMulUb.add (Dyadic.ofQ64 x.mulUb64),
   s.sSqUb.add (Dyadic.ofQ64 x.sqUb64),
   s.vLb.mulLb (Dyadic.ofQ64 x.vLb64),
   s.vUb.mulUb (Dyadic.ofQ64 x.vUb64)⟩

def leafSummary (es : List PrimeLeafEntry) : TreeSummary :=
  match es with
  | [] => ⟨0, 0, 0, Dyadic.zero, Dyadic.zero, Dyadic.zero, Dyadic.one, Dyadic.one⟩
  | e :: _ =>
    es.foldl addEntrySummary
      ⟨e.p, e.p, 0, Dyadic.zero, Dyadic.zero, Dyadic.zero, Dyadic.one, Dyadic.one⟩

def mergeSummary (sl sr : TreeSummary) : TreeSummary :=
  ⟨sl.lo, sr.hi, sl.cnt + sr.cnt,
   sl.s1Ub.add sr.s1Ub, sl.sMulUb.add sr.sMulUb, sl.sSqUb.add sr.sSqUb,
   sl.vLb.mulLb sr.vLb, sl.vUb.mulUb sr.vUb⟩

def OddPrimeTree.summary : OddPrimeTree → TreeSummary
  | .leaf s _ => s
  | .node s _ _ => s

def checkOddPrimeTree : OddPrimeTree → Bool
  | .leaf s es =>
    decide (es ≠ []) && (s == leafSummary es) &&
    es.all checkPrimeLeafEntry && isStrictIncList (es.map (·.p))
  | .node s l r =>
    decide (l.summary.hi < r.summary.lo) && (s == mergeSummary l.summary r.summary) &&
    checkOddPrimeTree l && checkOddPrimeTree r

def treeFlatten : OddPrimeTree → List PrimeLeafEntry
  | .leaf _ es => es
  | .node _ l r => treeFlatten l ++ treeFlatten r

set_option maxRecDepth 200000 in
private lemma oddPrimeTree_ok : checkOddPrimeTree oddPrimeTree = true := by decide
set_option maxRecDepth 200000 in
private lemma oddPrimeTree_primes_eq : (treeFlatten oddPrimeTree).map (·.p) = oddPrimesLt27000 := by decide

lemma checkPrimeLeafEntry_props {e : PrimeLeafEntry} (h : checkPrimeLeafEntry e = true) :
    3 ≤ e.p ∧
    ((e.gLb64 : ℝ) / (q64Scale : ℝ)) ≤ 1 / ((e.p : ℝ) - 1) ∧
    1 / ((e.p : ℝ) - 1) ≤ ((e.gUb64 : ℝ) / (q64Scale : ℝ)) ∧
    1 / ((e.p : ℝ) * ((e.p : ℝ) - 1)) ≤ ((e.mulUb64 : ℝ) / (q64Scale : ℝ)) ∧
    1 / ((e.p : ℝ) - 1) ^ 2 ≤ ((e.sqUb64 : ℝ) / (q64Scale : ℝ)) ∧
    ((e.vLb64 : ℝ) / (q64Scale : ℝ)) ≤ 1 - 1 / ((e.p : ℝ) - 1) ∧
    1 - 1 / ((e.p : ℝ) - 1) ≤ ((e.vUb64 : ℝ) / (q64Scale : ℝ)) ∧
    (e.p : ℝ) / ((e.p : ℝ) - 1) ≤ ((e.phiUb64 : ℝ) / (q64Scale : ℝ)) := by
  simp only [checkPrimeLeafEntry, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hp3, hg1⟩, hg2⟩, hmul⟩, hsq⟩, hv1⟩, hv2⟩, hphi⟩
  have hp1 : (0 : ℝ) < (e.p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < e.p))
  have hq : (0 : ℝ) < (q64Scale : ℝ) := q64Scale_pos
  have hpsub1 : ((e.p - 1 : ℕ) : ℝ) = (e.p : ℝ) - 1 := Nat.cast_sub (by omega)
  have hpsub2 : ((e.p - 2 : ℕ) : ℝ) = (e.p : ℝ) - 2 := Nat.cast_sub (by omega)
  have h1m : (1 : ℝ) - 1 / ((e.p : ℝ) - 1) = ((e.p - 2 : ℕ) : ℝ) / ((e.p - 1 : ℕ) : ℝ) := by
    rw [hpsub1, hpsub2]; field_simp [hp1.ne']; ring
  have hm_pos : (0 : ℝ) < (e.p : ℝ) * ((e.p : ℝ) - 1) :=
    mul_pos (by exact_mod_cast (by omega : 0 < e.p)) hp1
  refine ⟨hp3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hq hp1, one_mul, ← hpsub1]; exact_mod_cast hg1
  · rw [div_le_div_iff₀ hp1 hq, one_mul, ← hpsub1]; exact_mod_cast hg2
  · rw [div_le_div_iff₀ hm_pos hq, one_mul, ← hpsub1, ← Nat.cast_mul]; exact_mod_cast hmul
  · rw [div_le_div_iff₀ (sq_pos_of_pos hp1) hq, one_mul, ← hpsub1, ← Nat.cast_pow]; exact_mod_cast hsq
  · rw [h1m, div_le_div_iff₀ hq (by rw [hpsub1]; exact hp1)]; exact_mod_cast hv1
  · rw [h1m, div_le_div_iff₀ (by rw [hpsub1]; exact hp1) hq]; exact_mod_cast hv2
  · rw [div_le_div_iff₀ hp1 hq, ← hpsub1]; exact_mod_cast hphi

private structure TreeInvs (t : OddPrimeTree) : Prop where
  lo_le : ∀ e ∈ treeFlatten t, t.summary.lo ≤ e.p ∧ e.p ≤ t.summary.hi
  lo_le_hi : t.summary.lo ≤ t.summary.hi
  entry_ok : ∀ e ∈ treeFlatten t, checkPrimeLeafEntry e = true
  pw : ((treeFlatten t).map (·.p)).Pairwise (· < ·)
  cnt_eq : (treeFlatten t).length = t.summary.cnt
  s1_ok : ((treeFlatten t).map (fun e => (Dyadic.ofQ64 e.gUb64).toReal)).sum ≤ t.summary.s1Ub.toReal
  sm_ok : ((treeFlatten t).map (fun e => (Dyadic.ofQ64 e.mulUb64).toReal)).sum ≤ t.summary.sMulUb.toReal
  sq_ok : ((treeFlatten t).map (fun e => (Dyadic.ofQ64 e.sqUb64).toReal)).sum ≤ t.summary.sSqUb.toReal
  vl_ok : t.summary.vLb.toReal ≤ ((treeFlatten t).map (fun e => (Dyadic.ofQ64 e.vLb64).toReal)).prod
  vu_ok : ((treeFlatten t).map (fun e => (Dyadic.ofQ64 e.vUb64).toReal)).prod ≤ t.summary.vUb.toReal

private lemma checkOddPrimeTree_invs : ∀ (t : OddPrimeTree), checkOddPrimeTree t = true → TreeInvs t := by
  intro t
  induction t with
  | leaf s es =>
    intro h
    simp only [checkOddPrimeTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨⟨⟨hne, rfl⟩, hall⟩, hinc⟩
    have hpw := isStrictIncList_pairwise hinc
    have hall_m := List.all_eq_true.mp hall
    cases es with
    | nil => exact absurd rfl hne
    | cons e0 tl =>
      have hfold : ∀ (xs : List PrimeLeafEntry) (acc : TreeSummary),
          (xs.map (·.p)).Pairwise (· < ·) → (∀ y ∈ xs, acc.hi < y.p) → acc.lo ≤ acc.hi →
          ∀ (r : TreeSummary), r = xs.foldl addEntrySummary acc →
          r.lo = acc.lo ∧ r.lo ≤ r.hi ∧ (∀ y ∈ xs, acc.lo ≤ y.p ∧ y.p ≤ r.hi) ∧
          xs.length + acc.cnt = r.cnt ∧
          (xs.map (fun e => (Dyadic.ofQ64 e.gUb64).toReal)).sum + acc.s1Ub.toReal = r.s1Ub.toReal ∧
          (xs.map (fun e => (Dyadic.ofQ64 e.mulUb64).toReal)).sum + acc.sMulUb.toReal = r.sMulUb.toReal ∧
          (xs.map (fun e => (Dyadic.ofQ64 e.sqUb64).toReal)).sum + acc.sSqUb.toReal = r.sSqUb.toReal ∧
          r.vLb.toReal ≤ acc.vLb.toReal * (xs.map (fun e => (Dyadic.ofQ64 e.vLb64).toReal)).prod ∧
          acc.vUb.toReal * (xs.map (fun e => (Dyadic.ofQ64 e.vUb64).toReal)).prod ≤ r.vUb.toReal := by
        intro xs
        induction xs with
        | nil => intro acc _ _ hle r hr; subst hr; simp [hle]
        | cons z zs ih =>
          intro acc hz_pw hgt hle r hr
          have hz_lt := hgt z List.mem_cons_self
          have hztail : ∀ y ∈ zs, (addEntrySummary acc z).hi < y.p := fun y hy =>
            (List.pairwise_cons.mp hz_pw).1 y.p (List.mem_map_of_mem hy)
          have hle1 : (addEntrySummary acc z).lo ≤ (addEntrySummary acc z).hi := by
            dsimp [addEntrySummary]; omega
          have hih := ih (addEntrySummary acc z) (List.pairwise_cons.mp hz_pw).2 hztail hle1 r hr
          have hpnn1 : 0 ≤ (zs.map (fun e => (Dyadic.ofQ64 e.vLb64).toReal)).prod :=
            List.prod_nonneg fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _
          have hpnn2 : 0 ≤ (zs.map (fun e => (Dyadic.ofQ64 e.vUb64).toReal)).prod :=
            List.prod_nonneg fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _
          refine ⟨hih.1, hih.2.1, fun y hy => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rcases List.mem_cons.mp hy with rfl | hzm
            · cases zs with
              | nil => simp only [List.foldl_cons, List.foldl_nil, addEntrySummary] at hr; subst hr; exact ⟨by omega, le_rfl⟩
              | cons w ws =>
                have hw := hih.2.2.1 w List.mem_cons_self
                have hzw := hztail w List.mem_cons_self
                dsimp [addEntrySummary] at hw hzw
                exact ⟨by omega, le_trans hzw.le hw.2⟩
            · have hlo : (addEntrySummary acc z).lo = acc.lo := rfl
              exact ⟨hlo ▸ (hih.2.2.1 y hzm).1, (hih.2.2.1 y hzm).2⟩
          · have hcnt := hih.2.2.2.1; dsimp [addEntrySummary] at hcnt; rw [List.length_cons]; omega
          · rw [List.map_cons, List.sum_cons]; have h1 := hih.2.2.2.2.1; dsimp [addEntrySummary] at h1; rw [Dyadic.add_toReal] at h1; linarith
          · rw [List.map_cons, List.sum_cons]; have h1 := hih.2.2.2.2.2.1; dsimp [addEntrySummary] at h1; rw [Dyadic.add_toReal] at h1; linarith
          · rw [List.map_cons, List.sum_cons]; have h1 := hih.2.2.2.2.2.2.1; dsimp [addEntrySummary] at h1; rw [Dyadic.add_toReal] at h1; linarith
          · have h1 := hih.2.2.2.2.2.2.2.1; dsimp [addEntrySummary] at h1
            exact h1.trans ((mul_le_mul_of_nonneg_right (Dyadic.mulLb_le _ _) hpnn1).trans_eq (by rw [List.map_cons, List.prod_cons]; ring))
          · have h1 := hih.2.2.2.2.2.2.2.2; dsimp [addEntrySummary] at h1
            exact ((by rw [List.map_cons, List.prod_cons]; ring : _ = _).trans_le
              (mul_le_mul_of_nonneg_right (Dyadic.le_mulUb _ _) hpnn2)).trans h1
      set init : TreeSummary := ⟨e0.p, e0.p, 0, Dyadic.zero, Dyadic.zero, Dyadic.zero, Dyadic.one, Dyadic.one⟩
      have htl_pw := (List.pairwise_cons.mp hpw).2
      have htl_gt : ∀ y ∈ tl, (addEntrySummary init e0).hi < y.p := fun y hy =>
        (List.pairwise_cons.mp hpw).1 y.p (List.mem_map_of_mem hy)
      have hf := hfold tl (addEntrySummary init e0) htl_pw htl_gt (by dsimp [addEntrySummary, init]; omega)
        (leafSummary (e0 :: tl)) rfl
      refine ⟨fun e he => ?_, hf.2.1, hall_m, hpw, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [OddPrimeTree.summary]
        rcases List.mem_cons.mp he with rfl | hm
        · cases tl with
          | nil => simp only [leafSummary, List.foldl_cons, List.foldl_nil, addEntrySummary]; exact ⟨le_rfl, le_rfl⟩
          | cons w ws =>
            have hlo : (leafSummary (e :: w :: ws)).lo = e.p := by rw [hf.1]; rfl
            have hw := hf.2.2.1 w List.mem_cons_self
            exact ⟨hlo.le, le_trans (by dsimp [addEntrySummary, init] at hw; omega) hw.2⟩
        · exact ⟨by rw [hf.1]; exact (hf.2.2.1 e hm).1, (hf.2.2.1 e hm).2⟩
      · dsimp only [OddPrimeTree.summary, treeFlatten]; rw [List.length_cons]
        have hc := hf.2.2.2.1; dsimp [addEntrySummary, init] at hc; omega
      · dsimp only [OddPrimeTree.summary, treeFlatten]; rw [List.map_cons, List.sum_cons]
        have h1 := hf.2.2.2.2.1; dsimp [addEntrySummary, init] at h1
        rw [Dyadic.add_toReal, Dyadic.zero_toReal, zero_add] at h1; linarith
      · dsimp only [OddPrimeTree.summary, treeFlatten]; rw [List.map_cons, List.sum_cons]
        have h1 := hf.2.2.2.2.2.1; dsimp [addEntrySummary, init] at h1
        rw [Dyadic.add_toReal, Dyadic.zero_toReal, zero_add] at h1; linarith
      · dsimp only [OddPrimeTree.summary, treeFlatten]; rw [List.map_cons, List.sum_cons]
        have h1 := hf.2.2.2.2.2.2.1; dsimp [addEntrySummary, init] at h1
        rw [Dyadic.add_toReal, Dyadic.zero_toReal, zero_add] at h1; linarith
      · dsimp only [treeFlatten]; rw [List.map_cons, List.prod_cons]
        have h1 := hf.2.2.2.2.2.2.2.1; dsimp [addEntrySummary, init] at h1
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ (List.prod_nonneg fun _ hx => by
          rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _))
        exact (Dyadic.mulLb_le _ _).trans (by rw [Dyadic.one_toReal, one_mul])
      · dsimp only [treeFlatten]; rw [List.map_cons, List.prod_cons]
        have h1 := hf.2.2.2.2.2.2.2.2; dsimp [addEntrySummary, init] at h1
        refine le_trans (mul_le_mul_of_nonneg_right ?_ (List.prod_nonneg fun _ hx => by
          rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _)) h1
        simpa [Dyadic.one_toReal] using Dyadic.le_mulUb Dyadic.one (Dyadic.ofQ64 e0.vUb64)
  | node s l r ihl ihr =>
    intro h
    simp only [checkOddPrimeTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨⟨⟨hlr, rfl⟩, hl⟩, hr⟩
    have ⟨hl_lo, hl_hi, hl_ok, hl_pw, hl_cnt, hl_s1, hl_sm, hl_sq, hl_vl, hl_vu⟩ := ihl hl
    have ⟨hr_lo, hr_hi, hr_ok, hr_pw, hr_cnt, hr_s1, hr_sm, hr_sq, hr_vl, hr_vu⟩ := ihr hr
    refine ⟨fun e he => ?_, by change l.summary.lo ≤ r.summary.hi; exact hl_hi.trans (hlr.le.trans hr_hi), fun e he => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [treeFlatten, List.mem_append] at he
      rcases he with hel | her
      · exact ⟨(hl_lo e hel).1, (hl_lo e hel).2.trans (hlr.le.trans hr_hi)⟩
      · exact ⟨(hl_hi.trans hlr.le).trans (hr_lo e her).1, (hr_lo e her).2⟩
    · rw [treeFlatten, List.mem_append] at he; exact he.elim (hl_ok e) (hr_ok e)
    · rw [treeFlatten, List.map_append, List.pairwise_append]
      refine ⟨hl_pw, hr_pw, fun x hx y hy => ?_⟩
      rcases List.mem_map.mp hx with ⟨ex, hex, rfl⟩
      rcases List.mem_map.mp hy with ⟨ey, hey, rfl⟩
      exact lt_of_le_of_lt (hl_lo ex hex).2 (lt_of_lt_of_le hlr (hr_lo ey hey).1)
    · simp only [treeFlatten, List.length_append, OddPrimeTree.summary, mergeSummary, hl_cnt, hr_cnt]
    · simp only [treeFlatten, List.map_append, List.sum_append, OddPrimeTree.summary, mergeSummary, Dyadic.add_toReal]
      exact add_le_add hl_s1 hr_s1
    · simp only [treeFlatten, List.map_append, List.sum_append, OddPrimeTree.summary, mergeSummary, Dyadic.add_toReal]
      exact add_le_add hl_sm hr_sm
    · simp only [treeFlatten, List.map_append, List.sum_append, OddPrimeTree.summary, mergeSummary, Dyadic.add_toReal]
      exact add_le_add hl_sq hr_sq
    · simp only [treeFlatten, List.map_append, List.prod_append, OddPrimeTree.summary, mergeSummary]
      exact (Dyadic.mulLb_le _ _).trans (mul_le_mul hl_vl hr_vl (Dyadic.toReal_nonneg _)
        (List.prod_nonneg fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _))
    · simp only [treeFlatten, List.map_append, List.prod_append, OddPrimeTree.summary, mergeSummary]
      exact (mul_le_mul hl_vu hr_vu (List.prod_nonneg fun _ hx => by
        rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _) (Dyadic.toReal_nonneg _)).trans
        (Dyadic.le_mulUb _ _)

def treeFilterRange (q0 q1 : ℕ) : OddPrimeTree → List PrimeLeafEntry
  | .leaf s es =>
    if q1 ≤ s.lo || s.hi < q0 then []
    else if q0 ≤ s.lo && s.hi < q1 then es
    else es.filter (fun e => q0 ≤ e.p && e.p < q1)
  | .node s l r =>
    if q1 ≤ s.lo || s.hi < q0 then []
    else treeFilterRange q0 q1 l ++ treeFilterRange q0 q1 r

private lemma treeFilterRange_eq (q0 q1 : ℕ) :
    ∀ (t : OddPrimeTree), checkOddPrimeTree t = true →
      treeFilterRange q0 q1 t = (treeFlatten t).filter (fun e => q0 ≤ e.p && e.p < q1)
  | .leaf s es, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    unfold treeFilterRange treeFlatten
    split_ifs with hdis hsub
    · symm; rw [List.filter_eq_nil_iff]; intro e he
      have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_and] at hdis ⊢
      rcases hdis with h1 | h2 <;> omega
    · symm; rw [List.filter_eq_self]; intro e he
      have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢
      omega
    · rfl
  | .node s l r, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    simp only [checkOddPrimeTree, Bool.and_eq_true] at ht
    unfold treeFilterRange treeFlatten
    split_ifs with hdis
    · symm; rw [List.filter_eq_nil_iff]; intro e he
      have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_and] at hdis ⊢
      rcases hdis with h1 | h2 <;> omega
    · rw [List.filter_append, treeFilterRange_eq q0 q1 l ht.1.2, treeFilterRange_eq q0 q1 r ht.2]

private lemma filter_oddIco_eq (q0 q1 : ℕ) (hq1 : q1 ≤ 27000) :
    ((Finset.Ico (max 3 q0) q1).filter Nat.Prime) =
      ((treeFilterRange q0 q1 oddPrimeTree).map (·.p)).toFinset := by
  rw [treeFilterRange_eq q0 q1 oddPrimeTree oddPrimeTree_ok]
  ext q
  have hmem := @mem_oddPrimesLt27000_iff q
  rw [← oddPrimeTree_primes_eq, List.mem_map] at hmem
  simp only [Finset.mem_filter, Finset.mem_Ico, List.mem_toFinset, List.mem_map,
    List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hqm, hq1'⟩, hpr⟩
    rcases hmem.mpr ⟨lt_of_lt_of_le hq1' hq1, hpr, (le_max_left 3 q0).trans hqm⟩ with ⟨e, he, rfl⟩
    exact ⟨e, ⟨he, (le_max_right 3 q0).trans hqm, hq1'⟩, rfl⟩
  · rintro ⟨e, ⟨he, hq0e, hq1e⟩, rfl⟩
    have hpr := (hmem.mp ⟨e, he, rfl⟩)
    exact ⟨⟨max_le hpr.2.2 hq0e, hq1e⟩, hpr.2.1⟩

def oddPrimeEntriesList (z : ℕ) : List PrimeLeafEntry := treeFilterRange 0 z oddPrimeTree
def oddPrimesList (z : ℕ) : List ℕ := (oddPrimeEntriesList z).map (·.p)

lemma oddPrimeEntriesList_ok (z : ℕ) :
    ∀ e ∈ oddPrimeEntriesList z, checkPrimeLeafEntry e = true ∧ e.p.Prime ∧ 3 ≤ e.p ∧ e.p < z := by
  intro e he
  unfold oddPrimeEntriesList at he
  rw [treeFilterRange_eq 0 z oddPrimeTree oddPrimeTree_ok, List.mem_filter] at he
  have hinvs := checkOddPrimeTree_invs _ oddPrimeTree_ok
  have hchk := hinvs.entry_ok e he.1
  have hprops := checkPrimeLeafEntry_props hchk
  have hmem : e.p ∈ oddPrimesLt27000 := oddPrimeTree_primes_eq ▸ List.mem_map_of_mem he.1
  have hpr := (mem_oddPrimesLt27000_iff.mp hmem).2.1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  exact ⟨hchk, hpr, hprops.1, he.2.2⟩

private lemma pairwise_lt_map_filter {p : PrimeLeafEntry → Bool} :
    ∀ {xs : List PrimeLeafEntry}, (xs.map (·.p)).Pairwise (· < ·) →
      ((xs.filter p).map (·.p)).Pairwise (· < ·)
  | [], _ => .nil
  | x :: xs, h => by
    rw [List.map_cons, List.pairwise_cons] at h
    rw [List.filter_cons]
    split_ifs
    · rw [List.map_cons, List.pairwise_cons]
      exact ⟨fun y hy => by
        rcases List.mem_map.mp hy with ⟨e, he, rfl⟩
        exact h.1 e.p (List.mem_map_of_mem (List.mem_of_mem_filter he)),
        pairwise_lt_map_filter h.2⟩
    · exact pairwise_lt_map_filter h.2

private lemma nodup_treeFilterRange (q0 q1 : ℕ) :
    ((treeFilterRange q0 q1 oddPrimeTree).map (·.p)).Nodup := by
  rw [treeFilterRange_eq q0 q1 oddPrimeTree oddPrimeTree_ok]
  exact (pairwise_lt_map_filter (checkOddPrimeTree_invs _ oddPrimeTree_ok).pw).nodup

private lemma list_map_prod_le_prod {α : Type*} (f g : α → ℝ) :
    ∀ (xs : List α), (∀ x ∈ xs, 0 ≤ f x) → (∀ x ∈ xs, f x ≤ g x) →
      (xs.map f).prod ≤ (xs.map g).prod
  | [], _, _ => le_rfl
  | x :: xs, hnn, hle => by
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    exact mul_le_mul (hle x List.mem_cons_self)
      (list_map_prod_le_prod f g xs (fun y hy => hnn y (List.mem_cons_of_mem x hy))
        (fun y hy => hle y (List.mem_cons_of_mem x hy)))
      (List.prod_nonneg fun _ hy => by
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact hnn z (List.mem_cons_of_mem x hz))
      ((hnn x List.mem_cons_self).trans (hle x List.mem_cons_self))

lemma oddPrimesList_pairwise_lt (z : ℕ) : (oddPrimesList z).Pairwise (· < ·) := by
  unfold oddPrimesList oddPrimeEntriesList
  rw [treeFilterRange_eq 0 z oddPrimeTree oddPrimeTree_ok]
  exact pairwise_lt_map_filter (checkOddPrimeTree_invs _ oddPrimeTree_ok).pw

lemma oddPrimesList_props (z : ℕ) : ∀ p ∈ oddPrimesList z, p.Prime ∧ 2 < p ∧ p < z := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨e, he, rfl⟩
  have h := oddPrimeEntriesList_ok z e he
  exact ⟨h.2.1, by omega, h.2.2.2⟩

lemma oddPrimesList_toFinset {z : ℕ} (hz : z ≤ 27000) :
    (oddPrimesList z).toFinset = BuchstabSwitching.fullOddPrimesBelow z := by
  unfold oddPrimesList oddPrimeEntriesList
  rw [← filter_oddIco_eq 0 z hz]
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ico, BuchstabSwitching.fullOddPrimesBelow_mem_iff]
  constructor
  · rintro ⟨⟨hp3, hpz⟩, hpr⟩; exact ⟨hpz, hpr, by omega⟩
  · rintro ⟨hpz, hpr, hp2⟩; exact ⟨⟨by omega, hpz⟩, hpr⟩

def treeQueryCount (q0 q1 : ℕ) : OddPrimeTree → ℕ
  | .leaf s es =>
    if q1 ≤ s.lo || s.hi < q0 then 0
    else if q0 ≤ s.lo && s.hi < q1 then s.cnt
    else (es.filter (fun e => q0 ≤ e.p && e.p < q1)).length
  | .node s l r =>
    if q1 ≤ s.lo || s.hi < q0 then 0
    else if q0 ≤ s.lo && s.hi < q1 then s.cnt
    else treeQueryCount q0 q1 l + treeQueryCount q0 q1 r

private lemma treeQueryCount_eq (q0 q1 : ℕ) :
    ∀ (t : OddPrimeTree), checkOddPrimeTree t = true →
      treeQueryCount q0 q1 t = ((treeFlatten t).filter (fun e => q0 ≤ e.p && e.p < q1)).length
  | .leaf s es, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    unfold treeQueryCount treeFlatten
    split_ifs with hdis hsub
    · symm; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; intro e he
      have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega
    · have hcnt := hinvs.cnt_eq; dsimp only [OddPrimeTree.summary] at hcnt
      rw [← hcnt]; symm; congr 1; dsimp only [treeFlatten]; rw [List.filter_eq_self]; intro e he
      have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega
    · rfl
  | .node s l r, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    simp only [checkOddPrimeTree, Bool.and_eq_true] at ht
    unfold treeQueryCount treeFlatten
    split_ifs with hdis hsub
    · symm; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; intro e he
      have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega
    · have hcnt := hinvs.cnt_eq; dsimp only [OddPrimeTree.summary] at hcnt
      rw [← hcnt]; symm; congr 1; dsimp only [treeFlatten]; rw [List.filter_eq_self]; intro e he
      have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega
    · rw [List.filter_append, List.length_append, treeQueryCount_eq q0 q1 l ht.1.2, treeQueryCount_eq q0 q1 r ht.2]

private def treeQuerySumAux (proj : PrimeLeafEntry → ℕ) (sproj : TreeSummary → Dyadic)
    (q0 q1 : ℕ) : OddPrimeTree → Dyadic
  | .leaf s es =>
    if q1 ≤ s.lo || s.hi < q0 then Dyadic.zero
    else if q0 ≤ s.lo && s.hi < q1 then sproj s
    else (es.filter (fun e => q0 ≤ e.p && e.p < q1)).foldl
      (fun a e => a.add (Dyadic.ofQ64 (proj e))) Dyadic.zero
  | .node s l r =>
    if q1 ≤ s.lo || s.hi < q0 then Dyadic.zero
    else if q0 ≤ s.lo && s.hi < q1 then sproj s
    else (treeQuerySumAux proj sproj q0 q1 l).add (treeQuerySumAux proj sproj q0 q1 r)

private lemma foldl_dyadic_add_eq (f : PrimeLeafEntry → ℕ) (es : List PrimeLeafEntry) (acc : Dyadic) :
    (es.foldl (fun a e => a.add (Dyadic.ofQ64 (f e))) acc).toReal =
      acc.toReal + (es.map (fun e => (Dyadic.ofQ64 (f e)).toReal)).sum := by
  induction es generalizing acc with
  | nil => simp
  | cons e tl ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, Dyadic.add_toReal]; ring

private lemma treeQuerySumAux_sound (proj : PrimeLeafEntry → ℕ) (sproj : TreeSummary → Dyadic)
    (hs : ∀ t, checkOddPrimeTree t = true →
      ((treeFlatten t).map (fun e => (Dyadic.ofQ64 (proj e)).toReal)).sum ≤ (sproj t.summary).toReal)
    (q0 q1 : ℕ) :
    ∀ (t : OddPrimeTree), checkOddPrimeTree t = true →
      (((treeFlatten t).filter (fun e => q0 ≤ e.p && e.p < q1)).map
        (fun e => (Dyadic.ofQ64 (proj e)).toReal)).sum ≤ (treeQuerySumAux proj sproj q0 q1 t).toReal
  | .leaf s es, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    unfold treeQuerySumAux
    split_ifs with hdis hsub
    · rw [Dyadic.zero_toReal, show ((treeFlatten (.leaf s es)).filter _) = [] by
        rw [List.filter_eq_nil_iff]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega]
      simp
    · rw [show ((treeFlatten (.leaf s es)).filter _) = treeFlatten (.leaf s es) by
        rw [List.filter_eq_self]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega]
      exact hs (.leaf s es) ht
    · rw [foldl_dyadic_add_eq, Dyadic.zero_toReal, zero_add]; rfl
  | .node s l r, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    have ht' := ht
    simp only [checkOddPrimeTree, Bool.and_eq_true, beq_iff_eq] at ht'
    unfold treeQuerySumAux
    split_ifs with hdis hsub
    · rw [Dyadic.zero_toReal, show ((treeFlatten (.node s l r)).filter _) = [] by
        rw [List.filter_eq_nil_iff]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega]
      simp
    · rw [show ((treeFlatten (.node s l r)).filter _) = treeFlatten (.node s l r) by
        rw [List.filter_eq_self]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega]
      exact hs (.node s l r) ht
    · rw [treeFlatten, List.filter_append, List.map_append, List.sum_append, Dyadic.add_toReal]
      exact add_le_add (treeQuerySumAux_sound proj sproj hs q0 q1 l ht'.1.2)
        (treeQuerySumAux_sound proj sproj hs q0 q1 r ht'.2)

def exactPrimeCount (q0 q1 : ℕ) : ℕ :=
  (if q0 ≤ 2 && 2 < q1 then 1 else 0) + treeQueryCount q0 q1 oddPrimeTree

def exactInvSubOneSumUb (q0 q1 : ℕ) : Dyadic :=
  let base := treeQuerySumAux (·.gUb64) (·.s1Ub) q0 q1 oddPrimeTree
  if q0 ≤ 2 && 2 < q1 then Dyadic.one.add base else base

def exactInvMulPredSumUb (q0 q1 : ℕ) : Dyadic :=
  let base := treeQuerySumAux (·.mulUb64) (·.sMulUb) q0 q1 oddPrimeTree
  if q0 ≤ 2 && 2 < q1 then (Dyadic.ofQ64 (q64Scale / 2)).add base else base

def exactInvPredSqSumUb (q0 q1 : ℕ) : Dyadic :=
  let base := treeQuerySumAux (·.sqUb64) (·.sSqUb) q0 q1 oddPrimeTree
  if q0 ≤ 2 && 2 < q1 then Dyadic.one.add base else base

private lemma ico_primes_split_two {q0 q1 : ℕ} (_hq1 : q1 ≤ 27000) :
    (Finset.Ico q0 q1).filter Nat.Prime =
      (if q0 ≤ 2 ∧ 2 < q1 then {2} else ∅) ∪ ((Finset.Ico (max 3 q0) q1).filter Nat.Prime) := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hq0, hq1'⟩, hpr⟩
    rcases eq_or_lt_of_le hpr.two_le with rfl | hp2
    · exact Or.inl (by simp [hq0, hq1'])
    · exact Or.inr ⟨⟨max_le hp2 hq0, hq1'⟩, hpr⟩
  · rintro (h2 | ⟨⟨hp3, hq1'⟩, hpr⟩)
    · split_ifs at h2 with hc
      · rw [Finset.mem_singleton] at h2; subst h2; exact ⟨hc, Nat.prime_two⟩
      · simp at h2
    · exact ⟨⟨(le_max_right 3 q0).trans hp3, hq1'⟩, hpr⟩

private lemma ico_two_disjoint (q0 q1 : ℕ) :
    Disjoint (if q0 ≤ 2 ∧ 2 < q1 then ({2} : Finset ℕ) else ∅) ((Finset.Ico (max 3 q0) q1).filter Nat.Prime) := by
  rw [Finset.disjoint_left]; intro p hp1 hp2; rw [Finset.mem_filter, Finset.mem_Ico] at hp2
  split_ifs at hp1 with h
  · rw [Finset.mem_singleton] at hp1; subst hp1; omega
  · simp at hp1

theorem card_ico_primes_eq_exact {q0 q1 : ℕ} (hq1 : q1 ≤ 27000) :
    ((Finset.Ico q0 q1).filter Nat.Prime).card = exactPrimeCount q0 q1 := by
  rw [ico_primes_split_two hq1, Finset.card_union_of_disjoint (ico_two_disjoint q0 q1),
    filter_oddIco_eq q0 q1 hq1, exactPrimeCount, treeQueryCount_eq q0 q1 oddPrimeTree oddPrimeTree_ok,
    List.toFinset_card_of_nodup (nodup_treeFilterRange q0 q1), List.length_map,
    treeFilterRange_eq q0 q1 oddPrimeTree oddPrimeTree_ok]
  by_cases h : q0 ≤ 2 ∧ 2 < q1 <;> simp [h]

private lemma sum_ico_tree_aux (proj : PrimeLeafEntry → ℕ) (sproj : TreeSummary → Dyadic)
    (hs : ∀ t, checkOddPrimeTree t = true →
      ((treeFlatten t).map (fun e => (Dyadic.ofQ64 (proj e)).toReal)).sum ≤ (sproj t.summary).toReal)
    (f : ℕ → ℝ) (hf : ∀ e ∈ treeFlatten oddPrimeTree, f e.p ≤ ((proj e : ℝ) / (q64Scale : ℝ)))
    {q0 q1 : ℕ} (hq1 : q1 ≤ 27000) :
    ∑ q ∈ (Finset.Ico (max 3 q0) q1).filter Nat.Prime, f q ≤
      (treeQuerySumAux proj sproj q0 q1 oddPrimeTree).toReal := by
  rw [filter_oddIco_eq q0 q1 hq1]
  have hflt := treeFilterRange_eq q0 q1 oddPrimeTree oddPrimeTree_ok
  rw [List.sum_toFinset _ (nodup_treeFilterRange q0 q1), List.map_map, hflt]
  have hsum_le : (((treeFlatten oddPrimeTree).filter (fun e => q0 ≤ e.p && e.p < q1)).map (fun e => f e.p)).sum ≤
      (((treeFlatten oddPrimeTree).filter (fun e => q0 ≤ e.p && e.p < q1)).map
        (fun e => (Dyadic.ofQ64 (proj e)).toReal)).sum := by
    apply List.sum_le_sum; intro e he
    rw [Dyadic.ofQ64_toReal]; exact hf e (List.mem_of_mem_filter he)
  exact hsum_le.trans (treeQuerySumAux_sound proj sproj hs q0 q1 oddPrimeTree oddPrimeTree_ok)

theorem sum_inv_sub_one_le_exact {q0 q1 : ℕ} (hq1 : q1 ≤ 27000) :
    ∑ q ∈ (Finset.Ico q0 q1).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ≤
      (exactInvSubOneSumUb q0 q1).toReal := by
  rw [ico_primes_split_two hq1, Finset.sum_union (ico_two_disjoint q0 q1)]
  have hodd := sum_ico_tree_aux (·.gUb64) (·.s1Ub) (fun t ht => (checkOddPrimeTree_invs t ht).s1_ok)
    (fun q => (1 : ℝ) / ((q : ℝ) - 1))
    (fun e he => (checkPrimeLeafEntry_props ((checkOddPrimeTree_invs _ oddPrimeTree_ok).entry_ok e he)).2.2.1)
    (q0 := q0) hq1
  unfold exactInvSubOneSumUb
  split_ifs with hc1 hc2 <;> simp_all [Dyadic.add_toReal, Dyadic.one_toReal] <;> linarith

theorem sum_inv_mul_pred_le_exact {q0 q1 : ℕ} (hq1 : q1 ≤ 27000) :
    ∑ q ∈ (Finset.Ico q0 q1).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)) ≤
      (exactInvMulPredSumUb q0 q1).toReal := by
  rw [ico_primes_split_two hq1, Finset.sum_union (ico_two_disjoint q0 q1)]
  have hodd := sum_ico_tree_aux (·.mulUb64) (·.sMulUb) (fun t ht => (checkOddPrimeTree_invs t ht).sm_ok)
    (fun q => (1 : ℝ) / ((q : ℝ) * ((q : ℝ) - 1)))
    (fun e he => (checkPrimeLeafEntry_props ((checkOddPrimeTree_invs _ oddPrimeTree_ok).entry_ok e he)).2.2.2.1)
    (q0 := q0) hq1
  unfold exactInvMulPredSumUb
  have hhalf : (1 : ℝ) / ((2 : ℝ) * ((2 : ℝ) - 1)) ≤ (Dyadic.ofQ64 (q64Scale / 2)).toReal := by
    rw [Dyadic.ofQ64_toReal, Dyadic.q64Scale_real_eq]; unfold q64Scale; rw [Nat.shiftLeft_eq, Nat.one_mul]; norm_num
  split_ifs with hc1 hc2 <;> simp_all [Dyadic.add_toReal] <;> linarith

theorem sum_inv_pred_sq_le_exact {q0 q1 : ℕ} (hq1 : q1 ≤ 27000) :
    ∑ q ∈ (Finset.Ico q0 q1).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1) ^ 2 ≤
      (exactInvPredSqSumUb q0 q1).toReal := by
  rw [ico_primes_split_two hq1, Finset.sum_union (ico_two_disjoint q0 q1)]
  have hodd := sum_ico_tree_aux (·.sqUb64) (·.sSqUb) (fun t ht => (checkOddPrimeTree_invs t ht).sq_ok)
    (fun q => (1 : ℝ) / ((q : ℝ) - 1) ^ 2)
    (fun e he => (checkPrimeLeafEntry_props ((checkOddPrimeTree_invs _ oddPrimeTree_ok).entry_ok e he)).2.2.2.2.1)
    (q0 := q0) hq1
  unfold exactInvPredSqSumUb
  split_ifs with hc1 hc2 <;> simp_all [Dyadic.add_toReal, Dyadic.one_toReal] <;> linarith

private def treeQueryProdLb (q0 q1 : ℕ) : OddPrimeTree → Dyadic
  | .leaf s es =>
    if q1 ≤ s.lo || s.hi < q0 then Dyadic.one
    else if q0 ≤ s.lo && s.hi < q1 then s.vLb
    else (es.filter (fun e => q0 ≤ e.p && e.p < q1)).foldl
      (fun a e => a.mulLb (Dyadic.ofQ64 e.vLb64)) Dyadic.one
  | .node s l r =>
    if q1 ≤ s.lo || s.hi < q0 then Dyadic.one
    else if q0 ≤ s.lo && s.hi < q1 then s.vLb
    else (treeQueryProdLb q0 q1 l).mulLb (treeQueryProdLb q0 q1 r)

private def treeQueryProdUb (q0 q1 : ℕ) : OddPrimeTree → Dyadic
  | .leaf s es =>
    if q1 ≤ s.lo || s.hi < q0 then Dyadic.one
    else if q0 ≤ s.lo && s.hi < q1 then s.vUb
    else (es.filter (fun e => q0 ≤ e.p && e.p < q1)).foldl
      (fun a e => a.mulUb (Dyadic.ofQ64 e.vUb64)) Dyadic.one
  | .node s l r =>
    if q1 ≤ s.lo || s.hi < q0 then Dyadic.one
    else if q0 ≤ s.lo && s.hi < q1 then s.vUb
    else (treeQueryProdUb q0 q1 l).mulUb (treeQueryProdUb q0 q1 r)

private lemma foldl_dyadic_mulLb_le (f : PrimeLeafEntry → ℕ) (es : List PrimeLeafEntry) (acc : Dyadic) :
    (es.foldl (fun a e => a.mulLb (Dyadic.ofQ64 (f e))) acc).toReal ≤
      acc.toReal * (es.map (fun e => (Dyadic.ofQ64 (f e)).toReal)).prod := by
  induction es generalizing acc with
  | nil => simp
  | cons e tl ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    have hnn : 0 ≤ (tl.map (fun x => (Dyadic.ofQ64 (f x)).toReal)).prod :=
      List.prod_nonneg fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _
    exact (ih _).trans ((mul_le_mul_of_nonneg_right (Dyadic.mulLb_le _ _) hnn).trans_eq (by ring))

private lemma prod_le_foldl_dyadic_mulUb (f : PrimeLeafEntry → ℕ) (es : List PrimeLeafEntry) (acc : Dyadic) :
    acc.toReal * (es.map (fun e => (Dyadic.ofQ64 (f e)).toReal)).prod ≤
      (es.foldl (fun a e => a.mulUb (Dyadic.ofQ64 (f e))) acc).toReal := by
  induction es generalizing acc with
  | nil => simp
  | cons e tl ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    have hnn : 0 ≤ (tl.map (fun x => (Dyadic.ofQ64 (f x)).toReal)).prod :=
      List.prod_nonneg fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _
    exact (le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_right (Dyadic.le_mulUb _ _) hnn)).trans (ih _)

private lemma treeQueryProdLb_sound (q0 q1 : ℕ) :
    ∀ (t : OddPrimeTree), checkOddPrimeTree t = true →
      (treeQueryProdLb q0 q1 t).toReal ≤
        (((treeFlatten t).filter (fun e => q0 ≤ e.p && e.p < q1)).map
          (fun e => (Dyadic.ofQ64 e.vLb64).toReal)).prod
  | .leaf s es, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    unfold treeQueryProdLb
    split_ifs with hdis hsub
    · rw [Dyadic.one_toReal, show ((treeFlatten (.leaf s es)).filter _) = [] by
        rw [List.filter_eq_nil_iff]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega]; simp
    · rw [show ((treeFlatten (.leaf s es)).filter _) = treeFlatten (.leaf s es) by
        rw [List.filter_eq_self]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega]; exact hinvs.vl_ok
    · exact (foldl_dyadic_mulLb_le _ _ _).trans_eq (by rw [Dyadic.one_toReal, one_mul]; rfl)
  | .node s l r, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    have ht' := ht; simp only [checkOddPrimeTree, Bool.and_eq_true] at ht'
    unfold treeQueryProdLb
    split_ifs with hdis hsub
    · rw [Dyadic.one_toReal, show ((treeFlatten (.node s l r)).filter _) = [] by
        rw [List.filter_eq_nil_iff]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega]; simp
    · rw [show ((treeFlatten (.node s l r)).filter _) = treeFlatten (.node s l r) by
        rw [List.filter_eq_self]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega]; exact hinvs.vl_ok
    · rw [treeFlatten, List.filter_append, List.map_append, List.prod_append]
      exact (Dyadic.mulLb_le _ _).trans (mul_le_mul (treeQueryProdLb_sound q0 q1 l ht'.1.2)
        (treeQueryProdLb_sound q0 q1 r ht'.2) (Dyadic.toReal_nonneg _) (List.prod_nonneg fun _ hx => by
          rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _))

private lemma treeQueryProdUb_sound (q0 q1 : ℕ) :
    ∀ (t : OddPrimeTree), checkOddPrimeTree t = true →
      (((treeFlatten t).filter (fun e => q0 ≤ e.p && e.p < q1)).map
        (fun e => (Dyadic.ofQ64 e.vUb64).toReal)).prod ≤ (treeQueryProdUb q0 q1 t).toReal
  | .leaf s es, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    unfold treeQueryProdUb
    split_ifs with hdis hsub
    · rw [Dyadic.one_toReal, show ((treeFlatten (.leaf s es)).filter _) = [] by
        rw [List.filter_eq_nil_iff]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega]; simp
    · rw [show ((treeFlatten (.leaf s es)).filter _) = treeFlatten (.leaf s es) by
        rw [List.filter_eq_self]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega]; exact hinvs.vu_ok
    · exact (by rw [Dyadic.one_toReal, one_mul]; rfl : _ ≤ (Dyadic.one.toReal * _)).trans
        (prod_le_foldl_dyadic_mulUb _ _ _)
  | .node s l r, ht => by
    have hinvs := checkOddPrimeTree_invs _ ht
    have ht' := ht; simp only [checkOddPrimeTree, Bool.and_eq_true] at ht'
    unfold treeQueryProdUb
    split_ifs with hdis hsub
    · rw [Dyadic.one_toReal, show ((treeFlatten (.node s l r)).filter _) = [] by
        rw [List.filter_eq_nil_iff]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hdis ⊢; omega]; simp
    · rw [show ((treeFlatten (.node s l r)).filter _) = treeFlatten (.node s l r) by
        rw [List.filter_eq_self]; intro e he
        have hb := hinvs.lo_le e he; dsimp only [OddPrimeTree.summary] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsub ⊢; omega]; exact hinvs.vu_ok
    · rw [treeFlatten, List.filter_append, List.map_append, List.prod_append]
      exact (mul_le_mul (treeQueryProdUb_sound q0 q1 l ht'.1.2) (treeQueryProdUb_sound q0 q1 r ht'.2)
        (List.prod_nonneg fun _ hx => by rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; exact Dyadic.toReal_nonneg _)
        (Dyadic.toReal_nonneg _)).trans (Dyadic.le_mulUb _ _)

def exactProdOneSubInvPredLb (q0 q1 : ℕ) : Dyadic := treeQueryProdLb q0 q1 oddPrimeTree
def exactProdOneSubInvPredUb (q0 q1 : ℕ) : Dyadic := treeQueryProdUb q0 q1 oddPrimeTree

theorem exactProdOneSubInvPredLb_le {q0 q1 : ℕ} (hq0 : 3 ≤ q0) (hq1 : q1 ≤ 27000) :
    (exactProdOneSubInvPredLb q0 q1).toReal ≤
      ∏ p ∈ (Finset.Ico q0 q1).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) := by
  have hico := filter_oddIco_eq q0 q1 hq1
  rw [max_eq_right hq0] at hico; rw [hico]
  have hflt := treeFilterRange_eq q0 q1 oddPrimeTree oddPrimeTree_ok
  rw [List.prod_toFinset _ (nodup_treeFilterRange q0 q1), List.map_map, hflt]
  refine (treeQueryProdLb_sound q0 q1 oddPrimeTree oddPrimeTree_ok).trans
    (list_map_prod_le_prod _ _ _ (fun _ _ => Dyadic.toReal_nonneg _) fun e he => ?_)
  rw [Dyadic.ofQ64_toReal]
  exact (checkPrimeLeafEntry_props ((checkOddPrimeTree_invs _ oddPrimeTree_ok).entry_ok e (List.mem_of_mem_filter he))).2.2.2.2.2.1

theorem le_exactProdOneSubInvPredUb {q0 q1 : ℕ} (hq0 : 3 ≤ q0) (hq1 : q1 ≤ 27000) :
    ∏ p ∈ (Finset.Ico q0 q1).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) ≤
      (exactProdOneSubInvPredUb q0 q1).toReal := by
  have hico := filter_oddIco_eq q0 q1 hq1
  rw [max_eq_right hq0] at hico; rw [hico]
  have hflt := treeFilterRange_eq q0 q1 oddPrimeTree oddPrimeTree_ok
  rw [List.prod_toFinset _ (nodup_treeFilterRange q0 q1), List.map_map, hflt]
  refine le_trans (list_map_prod_le_prod _ _ _ (fun e he => ?_) fun e he => ?_)
    (treeQueryProdUb_sound q0 q1 oddPrimeTree oddPrimeTree_ok)
  · dsimp only [Function.comp_apply]
    have hp3 : 3 ≤ e.p :=
      (checkPrimeLeafEntry_props ((checkOddPrimeTree_invs _ oddPrimeTree_ok).entry_ok e (List.mem_of_mem_filter he))).1
    have hp1 : (1 : ℝ) / ((e.p : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (sub_pos.mpr (by exact_mod_cast (by omega : 1 < e.p)))]
      have hp2 : (2 : ℝ) ≤ (e.p : ℝ) := by exact_mod_cast (by omega : 2 ≤ e.p)
      linarith
    exact sub_nonneg.mpr hp1
  · rw [Dyadic.ofQ64_toReal]
    exact (checkPrimeLeafEntry_props ((checkOddPrimeTree_invs _ oddPrimeTree_ok).entry_ok e (List.mem_of_mem_filter he))).2.2.2.2.2.2.1

theorem VN_two_eq_prod_Ico (z : ℕ) :
    External.VN 2 z = ∏ p ∈ (Finset.Ico 3 z).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) := by
  unfold External.VN
  congr 1; ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hpz, hp_pr, hp2⟩; exact ⟨⟨lt_of_le_of_ne hp_pr.two_le (Ne.symm fun h : p = 2 => hp2 (h ▸ dvd_rfl)), hpz⟩, hp_pr⟩
  · rintro ⟨⟨hp3, hpz⟩, hp_pr⟩; exact ⟨hpz, hp_pr, fun h => by have := Nat.le_of_dvd (by norm_num) h; omega⟩

theorem exactProdOneSubInvPredLb_le_VN_two {z : ℕ} (hz : z ≤ 27000) :
    (exactProdOneSubInvPredLb 3 z).toReal ≤ External.VN 2 z := by
  rw [VN_two_eq_prod_Ico]; exact exactProdOneSubInvPredLb_le le_rfl hz

theorem VN_two_le_exactProdOneSubInvPredUb {z : ℕ} (hz : z ≤ 27000) :
    External.VN 2 z ≤ (exactProdOneSubInvPredUb 3 z).toReal := by
  rw [VN_two_eq_prod_Ico]; exact le_exactProdOneSubInvPredUb le_rfl hz

def vPrefix27000Lb : Dyadic := exactProdOneSubInvPredLb 3 27000

lemma vPrefix27000Lb_le_VN_two : vPrefix27000Lb.toReal ≤ External.VN 2 27000 :=
  exactProdOneSubInvPredLb_le_VN_two le_rfl

end

end BuchstabSwitching.SieveInst
