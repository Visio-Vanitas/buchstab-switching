import BuchstabSwitching.Sieve.AbstractSieve
import BuchstabSwitching.Sieve.BonferroniHybrid
import BuchstabSwitching.Sieve.BonferroniEstimates
import BuchstabSwitching.Sieve.BrunBlockSieve.SetupAndTopK
import BuchstabSwitching.Sieve.BrunBlockSieve.ParityDecomposition
import BuchstabSwitching.Sieve.BrunBlockSieve.MainTermAndModulus
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Combinatorial Brun Block Sieve: Admissible Subset Counting and Hybrid Lower Bound

Establishes the exact DP and combinatorial upper bounds on Brun-admissible subsets
(`brun_block_adm_count_eq`, `brun_block_adm_count_le`, `brun_block_adm_count_le_prod`)
and the complete hybrid `Q₁ × P₂` sieve lower bound (`brun_block_sieve_lower_bound`,
`brun_block_card_lower_bound`).
-/

namespace BuchstabSwitching

section AdmCount

/-- One dynamic-programming transition step for admissible subset counting. -/
def brunAdmStep (sz cap : ℕ) (dp : ℕ → ℕ) (c : ℕ) : ℕ :=
  if c ≤ cap then ∑ k ∈ Finset.range (c + 1), dp k * sz.choose (c - k) else 0

/-- Cumulative cardinality DP over `(size, cap)` pairs processed left-to-right. -/
def brunAdmDPList (pairs : List (ℕ × ℕ)) : ℕ → ℕ :=
  pairs.foldl (fun dp p => brunAdmStep p.1 p.2 dp) (fun c => if c = 0 then 1 else 0)

/-- Exact DP count of Brun-admissible subsets for `(blocks, caps)`. -/
def brunAdmCount (blocks : List (Finset ℕ)) (caps : List ℕ) : ℕ :=
  ∑ c ∈ Finset.range (caps.getD (blocks.length - 1) 0 + 1),
    brunAdmDPList ((blocks.map Finset.card).zip caps) c

private lemma brunAdmDPList_append (pairs : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    brunAdmDPList (pairs ++ [p]) = brunAdmStep p.1 p.2 (brunAdmDPList pairs) := by
  simp [brunAdmDPList, List.foldl_append]

private lemma take_getD_of_lt (xs : List ℕ) {i n : ℕ} (hi : i < n) :
    (xs.take n).getD i 0 = xs.getD i 0 := by
  induction n generalizing xs i with
  | zero => omega
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.take_succ_cons, List.getD_cons_succ]
        exact ih xs (Nat.lt_of_succ_lt_succ hi)

private lemma brunAdmDPList_eq_card_prefix (blocks : List (Finset ℕ)) (caps : List ℕ)
    (hdisj : blocks.Pairwise Disjoint) (hlen : caps.length = blocks.length) :
    ∀ n : ℕ, n ≤ blocks.length → ∀ c : ℕ,
      brunAdmDPList (((blocks.map Finset.card).zip caps).take n) c =
        ((brunAdmSubsets (blocks.take n) (caps.take n)).filter (fun S => S.card = c)).card := by
  intro n
  induction n with
  | zero =>
    intro _ c
    have h0 : brunAdmSubsets (blocks.take 0) (caps.take 0) = {∅} := by
      refine Finset.ext fun S => ?_
      rw [List.take_zero, brunAdmSubsets, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_singleton]
      have hU : brunUnion ([] : List (Finset ℕ)) = ∅ := rfl
      rw [hU, Finset.subset_empty]
      exact ⟨fun h => h.1, fun h => by
        subst h
        exact ⟨rfl, Finset.empty_subset _, fun _ hi => by simp at hi⟩⟩
    rw [List.take_zero, brunAdmDPList, List.foldl_nil, h0]
    by_cases hc : c = 0
    · subst hc
      have h1 : ({∅} : Finset (Finset ℕ)).filter (fun S => S.card = 0) = {∅} := by
        ext S; simp
      rw [h1, Finset.card_singleton]
      simp
    · have h1 : ({∅} : Finset (Finset ℕ)).filter (fun S => S.card = c) = ∅ := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        rintro rfl
        simpa using Ne.symm hc
      rw [h1, Finset.card_empty]
      simp [hc]
  | succ n ih =>
    intro hn c
    have hn_lt : n < blocks.length := hn
    have hn_le : n ≤ blocks.length := Nat.le_of_lt hn_lt
    have hn_caps : n < caps.length := hlen ▸ hn_lt
    let B := blocks[n]
    let m := caps[n]
    have hzip_take : (((blocks.map Finset.card).zip caps).take (n + 1)) =
        (((blocks.map Finset.card).zip caps).take n) ++ [(B.card, m)] := by
      have hn_zip : n < ((blocks.map Finset.card).zip caps).length := by
        simp [List.length_zip, hlen, hn_lt]
      rw [List.take_succ_eq_append_getElem hn_zip]
      simp [B, m]
    rw [hzip_take, brunAdmDPList_append, brunAdmStep]
    have hblocks_take : blocks.take (n + 1) = blocks.take n ++ [B] :=
      List.take_succ_eq_append_getElem hn_lt
    have hcaps_take : caps.take (n + 1) = caps.take n ++ [m] :=
      List.take_succ_eq_append_getElem hn_caps
    have hdisj_B : Disjoint (brunUnion (blocks.take n)) B := by
      have hd := disjoint_brunPrefix_block hdisj hn_lt
      change Disjoint (brunPrefix blocks n) (blocks.getD n ∅) at hd
      simpa [brunPrefix, brunUnion, List.getD_eq_getElem?_getD, hn_lt, B] using hd
    have hunion_eq : brunUnion (blocks.take (n + 1)) = brunUnion (blocks.take n) ∪ B := by
      rw [hblocks_take]
      unfold brunUnion
      rw [foldr_union_append]
      simp
    have hadm_iff : ∀ S : Finset ℕ, S ⊆ brunUnion (blocks.take n) ∪ B →
        (BrunAdmissible (blocks.take (n + 1)) (caps.take (n + 1)) S ↔
          BrunAdmissible (blocks.take n) (caps.take n) (S ∩ brunUnion (blocks.take n)) ∧
            S.card ≤ m) := by
      intro S hS_sub
      have hlen_bn : (blocks.take n).length = n := by simp [List.length_take, hn_le]
      have hlen_bn1 : (blocks.take (n + 1)).length = n + 1 := by simp [List.length_take, hn]
      have hpref_lt : ∀ i ≤ n, brunPrefix (blocks.take (n + 1)) i = brunPrefix (blocks.take n) i := by
        intro i hi
        simp [brunPrefix, List.take_take, min_eq_left hi, min_eq_left (hi.trans (Nat.le_succ n))]
      have hpref_n1 : brunPrefix (blocks.take (n + 1)) (n + 1) = brunUnion (blocks.take (n + 1)) :=
        brunPrefix_eq_brunUnion_of_le _ (by rw [hlen_bn1])
      constructor
      · intro hadm
        refine ⟨⟨Finset.inter_subset_right, fun i hi => ?_⟩, ?_⟩
        · rw [hlen_bn] at hi
          have hi1 : i < (blocks.take (n + 1)).length := by omega
          have h1 := hadm.2 i hi1
          have hpref_sub : brunPrefix (blocks.take n) (i + 1) ⊆ brunUnion (blocks.take n) :=
            brunPrefix_subset_brunUnion _ _
          have hinter : (S ∩ brunUnion (blocks.take n)) ∩ brunPrefix (blocks.take n) (i + 1) =
              S ∩ brunPrefix (blocks.take (n + 1)) (i + 1) := by
            rw [hpref_lt (i + 1) hi, Finset.inter_assoc, Finset.inter_eq_right.mpr hpref_sub]
          have hcap_eq : (caps.take n).getD i 0 = (caps.take (n + 1)).getD i 0 := by
            rw [take_getD_of_lt caps hi, take_getD_of_lt caps (Nat.lt_of_lt_of_le hi (Nat.le_succ n))]
          rwa [hinter, hcap_eq]
        · have h1 := hadm.2 n (by omega)
          rw [hpref_n1, hunion_eq, Finset.inter_eq_left.mpr hS_sub] at h1
          have hcap_n : (caps.take (n + 1)).getD n 0 = m := by
            rw [take_getD_of_lt caps (Nat.lt_succ_self n)]
            simp [List.getD_eq_getElem?_getD, hn_caps, m]
          rwa [hcap_n] at h1
      · rintro ⟨hadm_prev, hcard_m⟩
        refine ⟨hunion_eq ▸ hS_sub, fun i hi => ?_⟩
        rw [hlen_bn1] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | rfl
        · have h1 := hadm_prev.2 i (by omega)
          have hpref_sub : brunPrefix (blocks.take n) (i + 1) ⊆ brunUnion (blocks.take n) :=
            brunPrefix_subset_brunUnion _ _
          have hinter : (S ∩ brunUnion (blocks.take n)) ∩ brunPrefix (blocks.take n) (i + 1) =
              S ∩ brunPrefix (blocks.take (n + 1)) (i + 1) := by
            rw [hpref_lt (i + 1) hi_lt, Finset.inter_assoc, Finset.inter_eq_right.mpr hpref_sub]
          have hcap_eq : (caps.take n).getD i 0 = (caps.take (n + 1)).getD i 0 := by
            rw [take_getD_of_lt caps hi_lt,
              take_getD_of_lt caps (Nat.lt_of_lt_of_le hi_lt (Nat.le_succ n))]
          rwa [← hinter, ← hcap_eq]
        · rw [hpref_n1, hunion_eq, Finset.inter_eq_left.mpr hS_sub]
          have hcap_n : (caps.take (i + 1)).getD i 0 = m := by
            rw [take_getD_of_lt caps (Nat.lt_succ_self i)]
            simp [List.getD_eq_getElem?_getD, hn_caps, m]
          rwa [hcap_n]
    by_cases hcm : c ≤ m
    · simp only [hcm, ↓reduceIte]
      let target := (brunAdmSubsets (blocks.take (n + 1)) (caps.take (n + 1))).filter
        (fun S => S.card = c)
      let part : ℕ → Finset (Finset ℕ) := fun k =>
        ((brunAdmSubsets (blocks.take n) (caps.take n)).filter (fun S' => S'.card = k) ×ˢ
          B.powersetCard (c - k)).image (fun p => p.1 ∪ p.2)
      have htarget_eq : target = (Finset.range (c + 1)).biUnion part := by
        ext S
        simp only [target, part, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
          Finset.mem_product, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
          brunAdmSubsets]
        constructor
        · rintro ⟨⟨hS_sub, hadm⟩, hScard⟩
          have hS_sub' : S ⊆ brunUnion (blocks.take n) ∪ B := hunion_eq ▸ hS_sub
          rcases (hadm_iff S hS_sub').mp hadm with ⟨hadm_prev, _⟩
          let S' := S ∩ brunUnion (blocks.take n)
          let SB := S ∩ B
          have hS_split : S' ∪ SB = S := by
            rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub']
          have hdisj_S'B : Disjoint S' SB :=
            hdisj_B.mono Finset.inter_subset_right Finset.inter_subset_right
          have hcard_sum : S'.card + SB.card = c := by
            rw [← Finset.card_union_of_disjoint hdisj_S'B, hS_split, hScard]
          refine ⟨S'.card, Nat.lt_succ_of_le (by omega), ⟨S', SB⟩,
            ⟨⟨⟨Finset.inter_subset_right, hadm_prev⟩, rfl⟩, Finset.inter_subset_right, ?_⟩, hS_split⟩
          change SB.card = c - S'.card
          omega
        · rintro ⟨k, hk, ⟨S', SB⟩, ⟨⟨⟨hS'sub, hadm_prev⟩, hS'card⟩, hSBsub, hSBcard⟩, rfl⟩
          have hdisj_S'B : Disjoint S' SB := hdisj_B.mono hS'sub hSBsub
          have hS_sub' : S' ∪ SB ⊆ brunUnion (blocks.take n) ∪ B :=
            Finset.union_subset_union hS'sub hSBsub
          have hScard : (S' ∪ SB).card = c := by
            rw [Finset.card_union_of_disjoint hdisj_S'B, hS'card, hSBcard]
            have : k ≤ c := Nat.lt_succ_iff.mp hk
            omega
          have hinter_eq : (S' ∪ SB) ∩ brunUnion (blocks.take n) = S' := by
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS'sub,
              Finset.disjoint_iff_inter_eq_empty.mp (hdisj_B.symm.mono_left hSBsub),
              Finset.union_empty]
          refine ⟨⟨hunion_eq ▸ hS_sub', (hadm_iff _ hS_sub').mpr ⟨?_, ?_⟩⟩, hScard⟩
          · rwa [hinter_eq]
          · omega
      have hdisj_part : ((Finset.range (c + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint part := by
        intro k₁ _ k₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro S hS₁ hS₂
        simp only [part, Finset.mem_image, Finset.mem_product, Finset.mem_filter,
          Finset.mem_powerset, Finset.mem_powersetCard, brunAdmSubsets] at hS₁ hS₂
        rcases hS₁ with ⟨⟨S₁', SB₁⟩, ⟨⟨⟨hS₁'sub, _⟩, hS₁'card⟩, hSB₁sub, _⟩, rfl⟩
        rcases hS₂ with ⟨⟨S₂', SB₂⟩, ⟨⟨⟨hS₂'sub, _⟩, hS₂'card⟩, hSB₂sub, _⟩, hEq⟩
        have h1 : (S₁' ∪ SB₁) ∩ brunUnion (blocks.take n) = S₁' := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS₁'sub,
            Finset.disjoint_iff_inter_eq_empty.mp (hdisj_B.symm.mono_left hSB₁sub),
            Finset.union_empty]
        have h2 : (S₂' ∪ SB₂) ∩ brunUnion (blocks.take n) = S₂' := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS₂'sub,
            Finset.disjoint_iff_inter_eq_empty.mp (hdisj_B.symm.mono_left hSB₂sub),
            Finset.union_empty]
        have hS_eq : S₁' = S₂' := by
          rw [← h1, ← h2, hEq]
        exact hne (by rw [← hS₁'card, ← hS₂'card, hS_eq])
      change _ = target.card
      rw [htarget_eq, Finset.card_biUnion hdisj_part]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hinj_k : Set.InjOn (fun p : Finset ℕ × Finset ℕ => p.1 ∪ p.2)
          (((brunAdmSubsets (blocks.take n) (caps.take n)).filter (fun S' => S'.card = k) ×ˢ
            B.powersetCard (c - k)) : Finset (Finset ℕ × Finset ℕ)) := by
        intro ⟨S₁', SB₁⟩ h1 ⟨S₂', SB₂⟩ h2 hEq
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_powerset, Finset.mem_powersetCard, brunAdmSubsets] at h1 h2
        have hS₁'sub : S₁' ⊆ brunUnion (blocks.take n) := h1.1.1.1
        have hS₂'sub : S₂' ⊆ brunUnion (blocks.take n) := h2.1.1.1
        have hSB₁sub : SB₁ ⊆ B := h1.2.1
        have hSB₂sub : SB₂ ⊆ B := h2.2.1
        have hU0 : S₁' = S₂' := by
          have ha : (S₁' ∪ SB₁) ∩ brunUnion (blocks.take n) = S₁' := by
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS₁'sub,
              Finset.disjoint_iff_inter_eq_empty.mp (hdisj_B.symm.mono_left hSB₁sub),
              Finset.union_empty]
          have hb : (S₂' ∪ SB₂) ∩ brunUnion (blocks.take n) = S₂' := by
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS₂'sub,
              Finset.disjoint_iff_inter_eq_empty.mp (hdisj_B.symm.mono_left hSB₂sub),
              Finset.union_empty]
          rw [← ha, ← hb]
          exact congrArg (· ∩ brunUnion (blocks.take n)) hEq
        have hU1 : SB₁ = SB₂ := by
          have ha : (S₁' ∪ SB₁) ∩ B = SB₁ := by
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hSB₁sub,
              Finset.disjoint_iff_inter_eq_empty.mp (hdisj_B.mono_left hS₁'sub),
              Finset.empty_union]
          have hb : (S₂' ∪ SB₂) ∩ B = SB₂ := by
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hSB₂sub,
              Finset.disjoint_iff_inter_eq_empty.mp (hdisj_B.mono_left hS₂'sub),
              Finset.empty_union]
          rw [← ha, ← hb]
          exact congrArg (· ∩ B) hEq
        ext1 <;> [exact hU0; exact hU1]
      rw [Finset.card_image_of_injOn hinj_k, Finset.card_product, Finset.card_powersetCard,
        ih hn_le k]
    · simp only [hcm, ↓reduceIte]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S hS hScard
      have hS_sub : S ⊆ brunUnion (blocks.take n) ∪ B :=
        hunion_eq ▸ Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hadm := (Finset.mem_filter.mp hS).2
      have hle := (hadm_iff S hS_sub).mp hadm |>.2
      omega

/-- Exact DP equality for the number of Brun-admissible subsets. -/
theorem brun_block_adm_count_eq (blocks : List (Finset ℕ)) (caps : List ℕ)
    (hdisj : blocks.Pairwise Disjoint) (hlen : caps.length = blocks.length) :
    (brunAdmSubsets blocks caps).card = brunAdmCount blocks caps := by
  unfold brunAdmCount
  have hfib : (brunAdmSubsets blocks caps).card =
      ∑ c ∈ Finset.range (caps.getD (blocks.length - 1) 0 + 1),
        ((brunAdmSubsets blocks caps).filter (fun S => S.card = c)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun S hS => ?_
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    cases hlen0 : blocks.length with
    | zero =>
      have hS_sub : S ⊆ brunUnion blocks := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hU_empty : brunUnion blocks = ∅ := by
        rw [← brunPrefix_eq_brunUnion_of_le blocks (le_refl _), hlen0, brunPrefix_zero]
      have hSe : S = ∅ := Finset.subset_empty.mp (by rwa [← hU_empty])
      rw [hSe]
      simp
    | succ k =>
      have hk : k < blocks.length := by omega
      have hS_adm := (Finset.mem_filter.mp hS).2
      have hle := hS_adm.2 k hk
      have hpref : brunPrefix blocks (k + 1) = brunUnion blocks :=
        brunPrefix_eq_brunUnion_of_le blocks (by omega)
      rw [hpref, Finset.inter_eq_left.mpr hS_adm.1] at hle
      simpa [hlen0] using hle
  rw [hfib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have htake_zip : ((blocks.map Finset.card).zip caps).take blocks.length =
      (blocks.map Finset.card).zip caps := by
    refine List.take_of_length_le ?_
    simp [List.length_zip, hlen]
  have htake_b : blocks.take blocks.length = blocks := List.take_of_length_le (le_refl _)
  have htake_c : caps.take blocks.length = caps := List.take_of_length_le (hlen ▸ le_refl _)
  have hdp := brunAdmDPList_eq_card_prefix blocks caps hdisj hlen blocks.length (le_refl _) c
  rw [htake_zip, htake_b, htake_c] at hdp
  exact hdp.symm

/-- **Combinatorial Upper Bound on Brun-Admissible Subsets (`brun_block_adm_count_le`)**:
both the global cap binomial bound and the per-block product bound hold. -/
theorem brun_block_adm_count_le (blocks : List (Finset ℕ)) (caps : List ℕ) :
    (brunAdmSubsets blocks caps).card ≤
      ∑ j ∈ Finset.range (caps.getD (blocks.length - 1) 0 + 1),
        (brunUnion blocks).card.choose j := by
  let mLast := caps.getD (blocks.length - 1) 0
  have hsub : brunAdmSubsets blocks caps ⊆
      (brunUnion blocks).powerset.filter (fun S => S.card ≤ mLast) := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSP, hadm⟩
    refine Finset.mem_filter.mpr ⟨hSP, ?_⟩
    cases hlen0 : blocks.length with
    | zero =>
      have hU_empty : brunUnion blocks = ∅ := by
        rw [← brunPrefix_eq_brunUnion_of_le blocks (le_refl _), hlen0, brunPrefix_zero]
      have hSe : S = ∅ := Finset.subset_empty.mp (by rw [← hU_empty]; exact Finset.mem_powerset.mp hSP)
      rw [hSe]
      simp
    | succ k =>
      have hk : k < blocks.length := by omega
      have hle := hadm.2 k hk
      have hpref : brunPrefix blocks (k + 1) = brunUnion blocks :=
        brunPrefix_eq_brunUnion_of_le blocks (by omega)
      rw [hpref, Finset.inter_eq_left.mpr hadm.1] at hle
      simpa [mLast, hlen0] using hle
  refine (Finset.card_le_card hsub).trans ?_
  have hfib : ((brunUnion blocks).powerset.filter (fun S => S.card ≤ mLast)).card =
      ∑ j ∈ Finset.range (mLast + 1),
        (((brunUnion blocks).powerset.filter (fun S => S.card ≤ mLast)).filter
          (fun S => S.card = j)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun S hS => ?_
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2)
  rw [hfib]
  refine le_of_eq (Finset.sum_congr rfl fun j hj => ?_)
  have hjm : j ≤ mLast := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfilt : ((brunUnion blocks).powerset.filter (fun S => S.card ≤ mLast)).filter
      (fun S => S.card = j) = (brunUnion blocks).powersetCard j := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hS, _⟩, rfl⟩; exact ⟨hS, rfl⟩
    · rintro ⟨hS, rfl⟩; exact ⟨⟨hS, hjm⟩, rfl⟩
  rw [hfilt, Finset.card_powersetCard]

/-- Per-block product upper bound on `brunAdmSubsets`. -/
theorem brun_block_adm_count_le_prod (blocks : List (Finset ℕ)) (caps : List ℕ) :
    (brunAdmSubsets blocks caps).card ≤
      ∏ i ∈ Finset.range blocks.length,
        ∑ j ∈ Finset.range (caps.getD i 0 + 1), (blocks.getD i ∅).card.choose j := by
  let P_i : ℕ → Finset (Finset ℕ) := fun i =>
    (blocks.getD i ∅).powerset.filter (fun T => T.card ≤ caps.getD i 0)
  let box : Finset (∀ i : Finset.range blocks.length, Finset ℕ) :=
    Fintype.piFinset fun i => P_i i.1
  let proj : Finset ℕ → ∀ i : Finset.range blocks.length, Finset ℕ :=
    fun S i => S ∩ blocks.getD i.1 ∅
  have hcard_le : (brunAdmSubsets blocks caps).card ≤ box.card := by
    refine Finset.card_le_card_of_injOn proj ?_ ?_
    · intro S hS
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      rintro ⟨i, hi_mem⟩
      have hi : i < blocks.length := Finset.mem_range.mp hi_mem
      have hadm := (Finset.mem_filter.mp hS).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
      have hsub : blocks.getD i ∅ ⊆ brunPrefix blocks (i + 1) := by
        rw [brunPrefix_succ blocks hi]
        exact Finset.subset_union_right
      exact (Finset.card_le_card (Finset.inter_subset_inter_left hsub)).trans (hadm.2 i hi)
    · intro S₁ hS₁ S₂ hS₂ hEq
      have hS₁_sub : S₁ ⊆ brunUnion blocks := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₁).1
      have hS₂_sub : S₂ ⊆ brunUnion blocks := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
      ext p
      constructor
      · intro hp₁
        rcases mem_brunUnion_iff.mp (hS₁_sub hp₁) with ⟨i, hi, hpB⟩
        have hpi := congrFun hEq ⟨i, Finset.mem_range.mpr hi⟩
        have hp_mem : p ∈ proj S₁ ⟨i, Finset.mem_range.mpr hi⟩ := Finset.mem_inter.mpr ⟨hp₁, hpB⟩
        rw [hpi] at hp_mem
        exact (Finset.mem_inter.mp hp_mem).1
      · intro hp₂
        rcases mem_brunUnion_iff.mp (hS₂_sub hp₂) with ⟨i, hi, hpB⟩
        have hpi := congrFun hEq ⟨i, Finset.mem_range.mpr hi⟩
        have hp_mem : p ∈ proj S₂ ⟨i, Finset.mem_range.mpr hi⟩ := Finset.mem_inter.mpr ⟨hp₂, hpB⟩
        rw [← hpi] at hp_mem
        exact (Finset.mem_inter.mp hp_mem).1
  have hbox_card : box.card = ∏ i ∈ Finset.range blocks.length, (P_i i).card := by
    simp only [box, Fintype.card_piFinset]
    rw [← Finset.prod_coe_sort (Finset.range blocks.length) (fun i => (P_i i).card)]
  have hPi_card : ∀ i : ℕ, (P_i i).card =
      ∑ j ∈ Finset.range (caps.getD i 0 + 1), (blocks.getD i ∅).card.choose j := by
    intro i
    have hfib : (P_i i).card = ∑ j ∈ Finset.range (caps.getD i 0 + 1),
        ((P_i i).filter (fun T => T.card = j)).card := by
      refine Finset.card_eq_sum_card_fiberwise fun T hT => ?_
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2)
    rw [hfib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ caps.getD i 0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hfilt : (P_i i).filter (fun T => T.card = j) = (blocks.getD i ∅).powersetCard j := by
      ext T
      simp only [P_i, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hT, _⟩, rfl⟩; exact ⟨hT, rfl⟩
      · rintro ⟨hT, rfl⟩; exact ⟨⟨hT, hjm⟩, rfl⟩
    rw [hfilt, Finset.card_powersetCard]
  refine hcard_le.trans (le_of_eq ?_)
  rw [hbox_card]
  exact Finset.prod_congr rfl fun i _ => hPi_card i

end AdmCount

section HybridSieveLowerBound

/-- Squarefree moduli arising in the hybrid `Q₁ × P₂` Brun block sieve. -/
def brunDivisors (Q₁ : Finset ℕ) (blocks : List (Finset ℕ)) (caps : List ℕ) : Finset ℕ :=
  (Q₁.powerset ×ˢ brunAdmSubsets blocks caps).image
    (fun S => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)

private lemma prod_primes_dvd_iff_local {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {n : ℕ} :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    have hq_prime : q.Prime := hS q (Finset.mem_insert_self q S)
    have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ S, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hq_prime (hS_prime p hp)).mpr fun heq => hq (heq ▸ hp)
    rw [Finset.prod_insert hq]
    constructor
    · intro h p hp
      rcases Finset.mem_insert.mp hp with rfl | hpS
      · exact dvd_trans (dvd_mul_right p _) h
      · exact (ih hS_prime).mp (dvd_trans (dvd_mul_left _ q) h) p hpS
    · intro h
      exact hcop.mul_dvd_of_dvd_of_dvd (h q (Finset.mem_insert_self q S))
        ((ih hS_prime).mpr fun p hp => h p (Finset.mem_insert_of_mem hp))

private lemma prod_primes_mul_dvd_iff_local {S₁ S₂ : Finset ℕ}
    (hS₁ : ∀ p ∈ S₁, p.Prime) (hS₂ : ∀ p ∈ S₂, p.Prime) (hdisj : Disjoint S₁ S₂) {n : ℕ} :
    (∏ p ∈ S₁, p) * (∏ p ∈ S₂, p) ∣ n ↔ (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) := by
  have hcop : Nat.Coprime (∏ p ∈ S₁, p) (∏ p ∈ S₂, p) := by
    refine Nat.Coprime.prod_left fun p hp₁ => Nat.Coprime.prod_right fun q hq₂ => ?_
    exact (Nat.coprime_primes (hS₁ p hp₁) (hS₂ q hq₂)).mpr fun heq =>
      Finset.disjoint_left.mp hdisj hp₁ (heq ▸ hq₂)
  constructor
  · intro h
    exact ⟨(prod_primes_dvd_iff_local hS₁).mp (dvd_trans (dvd_mul_right _ _) h),
      (prod_primes_dvd_iff_local hS₂).mp (dvd_trans (dvd_mul_left _ _) h)⟩
  · rintro ⟨h₁, h₂⟩
    exact hcop.mul_dvd_of_dvd_of_dvd ((prod_primes_dvd_iff_local hS₁).mpr h₁)
      ((prod_primes_dvd_iff_local hS₂).mpr h₂)

private lemma prime_mem_of_dvd_prod_primes_local {p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hdvd : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Nat.dvd_one] at hdvd
    exact absurd hdvd hp.ne_one
  | @insert q S hq ih =>
    rw [Finset.prod_insert hq] at hdvd
    rcases hp.dvd_mul.mp hdvd with hpq | hpS
    · rcases (Nat.dvd_prime (hS q (Finset.mem_insert_self q S))).mp hpq with rfl | rfl
      · exact absurd rfl hp.ne_one
      · exact Finset.mem_insert_self p S
    · exact Finset.mem_insert_of_mem (ih (fun r hr => hS r (Finset.mem_insert_of_mem hr)) hpS)

private lemma injOn_prod_primes_mul_local {Q₁ P₂ : Finset ℕ}
    (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime) (hdisj : Disjoint Q₁ P₂) :
    Set.InjOn (fun S : Finset ℕ × Finset ℕ => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)
      (Q₁.powerset ×ˢ P₂.powerset : Finset (Finset ℕ × Finset ℕ)) := by
  intro S hS T hT hEq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset] at hS hT
  have hmem : ∀ {A₁ A₂ B₁ B₂ : Finset ℕ},
      A₁ ⊆ Q₁ → A₂ ⊆ P₂ → B₁ ⊆ Q₁ → B₂ ⊆ P₂ →
      (∏ p ∈ A₁, p) * ∏ p ∈ A₂, p = (∏ p ∈ B₁, p) * ∏ p ∈ B₂, p →
      A₁ ⊆ B₁ ∧ A₂ ⊆ B₂ := by
    intro A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hAB
    have hAB_all := (prod_primes_mul_dvd_iff_local (fun p hp => hQ₁ p (hA₁ hp))
      (fun p hp => hP₂ p (hA₂ hp)) (hdisj.mono hA₁ hA₂)).mp (dvd_of_eq hAB)
    constructor
    · intro p hpA₁
      have hp_prime := hQ₁ p (hA₁ hpA₁)
      rcases hp_prime.dvd_mul.mp (hAB_all.1 p hpA₁) with h₁ | h₂
      · exact prime_mem_of_dvd_prod_primes_local hp_prime (fun q hq => hQ₁ q (hB₁ hq)) h₁
      · have hpB₂ := prime_mem_of_dvd_prod_primes_local hp_prime (fun q hq => hP₂ q (hB₂ hq)) h₂
        exact absurd (hB₂ hpB₂) (Finset.disjoint_left.mp hdisj (hA₁ hpA₁))
    · intro p hpA₂
      have hp_prime := hP₂ p (hA₂ hpA₂)
      rcases hp_prime.dvd_mul.mp (hAB_all.2 p hpA₂) with h₁ | h₂
      · have hpB₁ := prime_mem_of_dvd_prod_primes_local hp_prime (fun q hq => hQ₁ q (hB₁ hq)) h₁
        exact absurd (hA₂ hpA₂) (Finset.disjoint_left.mp hdisj (hB₁ hpB₁))
      · exact prime_mem_of_dvd_prod_primes_local hp_prime (fun q hq => hP₂ q (hB₂ hq)) h₂
  have h1 := hmem hS.1 hS.2 hT.1 hT.2 hEq
  have h2 := hmem hT.1 hT.2 hS.1 hS.2 hEq.symm
  ext1
  · exact Finset.Subset.antisymm h1.1 h2.1
  · exact Finset.Subset.antisymm h1.2 h2.2

theorem sum_brunDivisors_eq {Q₁ : Finset ℕ} {blocks : List (Finset ℕ)} {caps : List ℕ}
    (hdisj : Disjoint Q₁ (brunUnion blocks))
    (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ brunUnion blocks, p.Prime) (f : ℕ → ℝ) :
    ∑ d ∈ brunDivisors Q₁ blocks caps, f d =
      ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
        f ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
  have hinj : Set.InjOn (fun S : Finset ℕ × Finset ℕ => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)
      ((Q₁.powerset ×ˢ brunAdmSubsets blocks caps) : Finset (Finset ℕ × Finset ℕ)) := by
    refine (injOn_prod_primes_mul_local hQ₁ hP₂ hdisj).mono ?_
    intro S hS
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, brunAdmSubsets,
      Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.1⟩
  rw [brunDivisors, Finset.sum_image hinj, Finset.sum_product]

theorem card_brunDivisors_eq {Q₁ : Finset ℕ} {blocks : List (Finset ℕ)} {caps : List ℕ}
    (hdisj : Disjoint Q₁ (brunUnion blocks))
    (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ brunUnion blocks, p.Prime) :
    (brunDivisors Q₁ blocks caps).card = 2 ^ Q₁.card * (brunAdmSubsets blocks caps).card := by
  have hinj : Set.InjOn (fun S : Finset ℕ × Finset ℕ => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)
      ((Q₁.powerset ×ˢ brunAdmSubsets blocks caps) : Finset (Finset ℕ × Finset ℕ)) := by
    refine (injOn_prod_primes_mul_local hQ₁ hP₂ hdisj).mono ?_
    intro S hS
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, brunAdmSubsets,
      Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.1⟩
  rw [brunDivisors, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_powerset]

theorem card_brunDivisors_le {Q₁ : Finset ℕ} {blocks : List (Finset ℕ)} {caps : List ℕ}
    (hdisj : Disjoint Q₁ (brunUnion blocks))
    (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ brunUnion blocks, p.Prime) :
    (brunDivisors Q₁ blocks caps).card ≤
      2 ^ Q₁.card *
        ∑ j ∈ Finset.range (caps.getD (blocks.length - 1) 0 + 1),
          (brunUnion blocks).card.choose j := by
  rw [card_brunDivisors_eq hdisj hQ₁ hP₂]
  exact Nat.mul_le_mul_left _ (brun_block_adm_count_le blocks caps)

/-- **Complete Hybrid `Q₁ × P₂` Brun Block Sieve Lower Bound (`brun_block_sieve_lower_bound`)**:
bounds `sieveCount I a (Q₁ ∪ brunUnion blocks)` from below by
`sieveMass I a * V2 g Q₁ * V2 g (brunUnion blocks) * (1 - brunErrorBound blocks caps g) - ∑ |sieveRem|`. -/
theorem brun_block_sieve_lower_bound (I Q₁ : Finset ℕ) (blocks : List (Finset ℕ)) (caps : List ℕ)
    (a g : ℕ → ℝ)
    (hdisj_Q : Disjoint Q₁ (brunUnion blocks))
    (hdisj_blocks : blocks.Pairwise Disjoint)
    (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hQ₁ : ∀ p ∈ Q₁, p.Prime)
    (hP₂ : ∀ p ∈ brunUnion blocks, p.Prime)
    (hg₁ : ∀ p ∈ Q₁, g p ≤ 1)
    (hg₂ : ∀ p ∈ brunUnion blocks, 0 ≤ g p ∧ g p < 1)
    (hg_mul : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ brunUnion blocks,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p)
    (ha : ∀ n ∈ I, 0 ≤ a n) :
    sieveMass I a * V2 g Q₁ * V2 g (brunUnion blocks) * (1 - brunErrorBound blocks caps g) -
      ∑ d ∈ brunDivisors Q₁ blocks caps, |sieveRem I a g d| ≤
      sieveCount I a (Q₁ ∪ brunUnion blocks) := by
  let P₂ := brunUnion blocks
  have hpoint : ∀ n ∈ I,
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
        if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℝ) ^ (S₁.card + S₂.card) * a n else 0) ≤
      if (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n) then a n else 0 := by
    intro n hn
    have hpt_z := brun_block_div_pointwise_lower Q₁ blocks caps n hdisj_blocks hlen hodd hmono
    have hpt_r :
        (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
          if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℝ) ^ (S₁.card + S₂.card) else 0) ≤
        if (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n) then (1 : ℝ) else 0 := by
      exact_mod_cast hpt_z
    have hmul := mul_le_mul_of_nonneg_right hpt_r (ha n hn)
    have hL :
        (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
          if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℝ) ^ (S₁.card + S₂.card) else 0) * a n =
        ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
          if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℝ) ^ (S₁.card + S₂.card) * a n else 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun S₁ _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun S₂ _ => ?_
      split_ifs <;> ring
    have hR : (if (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n) then (1 : ℝ) else 0) * a n =
        if (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n) then a n else 0 := by
      split_ifs <;> ring
    rwa [hL, hR] at hmul
  have hsum_ineq := Finset.sum_le_sum hpoint
  have hRHS : (∑ n ∈ I, if (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n) then a n else 0) =
      sieveCount I a (Q₁ ∪ P₂) := by
    unfold sieveCount
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hnI, h1, h2⟩
      refine ⟨hnI, fun p hp => ?_⟩
      rcases hp with hp1 | hp2
      · exact h1 p hp1
      · exact h2 p hp2
    · rintro ⟨hnI, h⟩
      exact ⟨hnI, fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  have hLHS :
      (∑ n ∈ I, ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
        if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℝ) ^ (S₁.card + S₂.card) * a n else 0) =
      ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
        (-1 : ℝ) ^ (S₁.card + S₂.card) * sieveDivMass I a ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S₁ hS₁ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    have hS₁Q : S₁ ⊆ Q₁ := Finset.mem_powerset.mp hS₁
    have hS₂P : S₂ ⊆ P₂ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
    have hdvd_eq : ∀ n, ((∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n)) ↔
        ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) ∣ n := fun n =>
      (prod_primes_mul_dvd_iff_local (fun p hp => hQ₁ p (hS₁Q hp))
        (fun p hp => hP₂ p (hS₂P hp)) (hdisj_Q.mono hS₁Q hS₂P)).symm
    unfold sieveDivMass
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hdiv : (∏ p ∈ S₁, p) * (∏ p ∈ S₂, p) ∣ n
    · have hdiv' := (hdvd_eq n).mpr hdiv
      have hL : (if (∀ p ∈ S₁, p ∣ n) ∧ ∀ p ∈ S₂, p ∣ n then (-1 : ℝ) ^ (S₁.card + S₂.card) * a n else 0) =
          (-1 : ℝ) ^ (S₁.card + S₂.card) * a n := by
        split_ifs; rfl
      have hR : (if (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p ∣ n then a n else 0) = a n := by
        split_ifs; rfl
      rw [hL, hR]
    · have hndiv : ¬ ((∀ p ∈ S₁, p ∣ n) ∧ ∀ p ∈ S₂, p ∣ n) := fun h => hdiv ((hdvd_eq n).mp h)
      have hL : (if (∀ p ∈ S₁, p ∣ n) ∧ ∀ p ∈ S₂, p ∣ n then (-1 : ℝ) ^ (S₁.card + S₂.card) * a n else 0) = 0 := by
        split_ifs; rfl
      have hR : (if (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p ∣ n then a n else 0) = 0 := by
        split_ifs; rfl
      rw [hL, hR, mul_zero]
  have hid :
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
        (-1 : ℝ) ^ (S₁.card + S₂.card) * sieveDivMass I a ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) =
      sieveMass I a *
        (V2 g Q₁ * ∑ S₂ ∈ brunAdmSubsets blocks caps, (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p) +
        ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
          (-1 : ℝ) ^ (S₁.card + S₂.card) * sieveRem I a g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
    rw [← brun_block_hybrid_main_term Q₁ blocks caps g hg_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S₁ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S₂ _ => ?_
    rw [sieveDivMass_eq_main_add_rem I a g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)]
    ring
  have hrem_abs :
      |∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
        (-1 : ℝ) ^ (S₁.card + S₂.card) * sieveRem I a g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)| ≤
      ∑ d ∈ brunDivisors Q₁ blocks caps, |sieveRem I a g d| := by
    rw [sum_brunDivisors_eq hdisj_Q hQ₁ hP₂ (fun d => |sieveRem I a g d|)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S₁ _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S₂ _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hmain_lb : V2 g P₂ * (1 - brunErrorBound blocks caps g) ≤
      ∑ S₂ ∈ brunAdmSubsets blocks caps, (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p :=
    brun_block_main_term_lb blocks caps g hdisj_blocks hlen hodd hmono hg₂
  have hmass_nonneg : 0 ≤ sieveMass I a := Finset.sum_nonneg ha
  have hV2Q_nonneg : 0 ≤ V2 g Q₁ := Finset.prod_nonneg fun p hp => sub_nonneg.mpr (hg₁ p hp)
  have hmain_scaled :
      sieveMass I a * V2 g Q₁ * V2 g P₂ * (1 - brunErrorBound blocks caps g) ≤
      sieveMass I a *
        (V2 g Q₁ * ∑ S₂ ∈ brunAdmSubsets blocks caps, (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p) := by
    have h1 := mul_le_mul_of_nonneg_left hmain_lb (mul_nonneg hmass_nonneg hV2Q_nonneg)
    linarith
  have hneg := neg_le_of_abs_le hrem_abs
  rw [hLHS, hRHS, hid] at hsum_ineq
  linarith

/-- Cardinality specialization (`a ≡ 1`) of `brun_block_sieve_lower_bound`. -/
theorem brun_block_card_lower_bound (A Q₁ : Finset ℕ) (blocks : List (Finset ℕ)) (caps : List ℕ)
    (g : ℕ → ℝ)
    (hdisj_Q : Disjoint Q₁ (brunUnion blocks))
    (hdisj_blocks : blocks.Pairwise Disjoint)
    (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hQ₁ : ∀ p ∈ Q₁, p.Prime)
    (hP₂ : ∀ p ∈ brunUnion blocks, p.Prime)
    (hg₁ : ∀ p ∈ Q₁, g p ≤ 1)
    (hg₂ : ∀ p ∈ brunUnion blocks, 0 ≤ g p ∧ g p < 1)
    (hg_mul : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ brunUnion blocks,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p) :
    (A.card : ℝ) * V2 g Q₁ * V2 g (brunUnion blocks) * (1 - brunErrorBound blocks caps g) -
      ∑ d ∈ brunDivisors Q₁ blocks caps,
        |((A.filter (fun n => d ∣ n)).card : ℝ) - (A.card : ℝ) * g d| ≤
      ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ brunUnion blocks, ¬ p ∣ n))).card : ℝ) := by
  have h := brun_block_sieve_lower_bound A Q₁ blocks caps (fun _ => (1 : ℝ)) g
    hdisj_Q hdisj_blocks hlen hodd hmono hQ₁ hP₂ hg₁ hg₂ hg_mul (fun _ _ => zero_le_one)
  have hrem_eq : ∀ d, sieveRem A (fun _ => (1 : ℝ)) g d =
      ((A.filter (fun n => d ∣ n)).card : ℝ) - (A.card : ℝ) * g d := by
    intro d
    rw [sieveRem, sieveDivMass_const_one, sieveMass_const_one]
    ring
  have hcnt_eq : sieveCount A (fun _ => (1 : ℝ)) (Q₁ ∪ brunUnion blocks) =
      ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ brunUnion blocks, ¬ p ∣ n))).card : ℝ) := by
    rw [sieveCount_const_one]
    congr 2
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hnA, h⟩
      exact ⟨hnA, fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨hnA, h1, h2⟩
      refine ⟨hnA, fun p hp => ?_⟩
      rcases hp with hp | hp
      · exact h1 p hp
      · exact h2 p hp
  simpa [sieveMass_const_one, hrem_eq, hcnt_eq] using h

end HybridSieveLowerBound

end BuchstabSwitching
