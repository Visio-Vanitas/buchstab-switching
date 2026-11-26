import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Combinatorial Brun Block Sieve: Block Setup and `topK`

Defines the cumulative block union/prefix primitives (`brunUnion`, `brunPrefix`),
Brun admissibility (`BrunAdmissible`, `brunAdmSubsets`, `brunBadSubsets`), block restriction
(`restrictBlocks`), and the canonical `topK` largest-elements operator.
-/

namespace BuchstabSwitching

section BlockSetup

/-- Union of all blocks `B₀ ∪ ... ∪ B_{r-1}`. -/
def brunUnion (blocks : List (Finset ℕ)) : Finset ℕ :=
  blocks.foldr (· ∪ ·) ∅

/-- Cumulative prefix union `B₀ ∪ ... ∪ B_{i-1}` (`T_{i-1}`, with `brunPrefix blocks 0 = ∅`
and `brunPrefix blocks (i + 1) = T_i`). -/
def brunPrefix (blocks : List (Finset ℕ)) (i : ℕ) : Finset ℕ :=
  (blocks.take i).foldr (· ∪ ·) ∅

/-- A subset `S ⊆ P₂` is Brun-admissible for `(blocks, caps)` if every cumulative prefix
`S ∩ T_i` has cardinality at most `m_i = caps.getD i 0`. -/
def BrunAdmissible (blocks : List (Finset ℕ)) (caps : List ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ brunUnion blocks ∧
    ∀ i : ℕ, i < blocks.length → (S ∩ brunPrefix blocks (i + 1)).card ≤ caps.getD i 0

instance decidableBrunAdmissible (blocks : List (Finset ℕ)) (caps : List ℕ) :
    DecidablePred (BrunAdmissible blocks caps) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ ∀ i < blocks.length, _))

/-- Finset of all Brun-admissible subsets of `brunUnion blocks`. -/
def brunAdmSubsets (blocks : List (Finset ℕ)) (caps : List ℕ) : Finset (Finset ℕ) :=
  (brunUnion blocks).powerset.filter (BrunAdmissible blocks caps)

/-- Finset of inadmissible subsets of `A`. -/
def brunBadSubsets (blocks : List (Finset ℕ)) (caps : List ℕ) (A : Finset ℕ) :
    Finset (Finset ℕ) :=
  A.powerset.filter (fun S => ¬ BrunAdmissible blocks caps S)

/-- Restrict each block in `blocks` to elements in `P'`. -/
def restrictBlocks (blocks : List (Finset ℕ)) (P' : Finset ℕ) : List (Finset ℕ) :=
  blocks.map (· ∩ P')

@[simp]
theorem brunPrefix_zero (blocks : List (Finset ℕ)) : brunPrefix blocks 0 = ∅ := by
  simp [brunPrefix]

theorem foldr_union_append (xs ys : List (Finset ℕ)) :
    (xs ++ ys).foldr (· ∪ ·) ∅ = xs.foldr (· ∪ ·) ∅ ∪ ys.foldr (· ∪ ·) ∅ := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Finset.union_assoc]

theorem mem_foldr_union_iff {p : ℕ} {xs : List (Finset ℕ)} :
    p ∈ xs.foldr (· ∪ ·) ∅ ↔ ∃ B ∈ xs, p ∈ B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [ih]

theorem brunPrefix_succ (blocks : List (Finset ℕ)) {i : ℕ} (hi : i < blocks.length) :
    brunPrefix blocks (i + 1) = brunPrefix blocks i ∪ blocks.getD i ∅ := by
  unfold brunPrefix
  have htake : blocks.take (i + 1) = blocks.take i ++ [blocks[i]] :=
    List.take_succ_eq_append_getElem hi
  have hget : blocks.getD i ∅ = blocks[i] := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [htake, foldr_union_append, hget]
  simp

theorem brunPrefix_eq_brunUnion_of_le (blocks : List (Finset ℕ)) {i : ℕ}
    (hi : blocks.length ≤ i) :
    brunPrefix blocks i = brunUnion blocks := by
  simp [brunPrefix, brunUnion, List.take_of_length_le hi]

theorem brunPrefix_subset_brunUnion (blocks : List (Finset ℕ)) (i : ℕ) :
    brunPrefix blocks i ⊆ brunUnion blocks := by
  intro p hp
  rw [brunPrefix, mem_foldr_union_iff] at hp
  rcases hp with ⟨B, hB, hpB⟩
  rw [brunUnion, mem_foldr_union_iff]
  exact ⟨B, List.mem_of_mem_take hB, hpB⟩

theorem brunPrefix_mono (blocks : List (Finset ℕ)) {i j : ℕ} (hij : i ≤ j) :
    brunPrefix blocks i ⊆ brunPrefix blocks j := by
  intro p hp
  rw [brunPrefix, mem_foldr_union_iff] at hp ⊢
  rcases hp with ⟨B, hB, hpB⟩
  have hsub : blocks.take i ⊆ blocks.take j := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨k, hk, rfl⟩
    have hki : k < i := by
      rw [List.length_take] at hk
      exact lt_of_lt_of_le hk (Nat.min_le_left _ _)
    have hklen : k < blocks.length := by
      rw [List.length_take] at hk
      exact lt_of_lt_of_le hk (Nat.min_le_right _ _)
    have hkj : k < min j blocks.length := lt_min (lt_of_lt_of_le hki hij) hklen
    rw [List.getElem_take]
    exact List.mem_iff_getElem.mpr ⟨k, by simpa [List.length_take] using hkj, by simp [List.getElem_take]⟩
  exact ⟨B, hsub hB, hpB⟩

theorem mem_brunUnion_iff {p : ℕ} {blocks : List (Finset ℕ)} :
    p ∈ brunUnion blocks ↔ ∃ i : ℕ, i < blocks.length ∧ p ∈ blocks.getD i ∅ := by
  rw [brunUnion, mem_foldr_union_iff]
  constructor
  · rintro ⟨B, hB, hpB⟩
    rcases List.mem_iff_getElem.mp hB with ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    simpa [List.getD_eq_getElem?_getD, hi] using hpB
  · rintro ⟨i, hi, hpB⟩
    refine ⟨blocks[i], List.getElem_mem hi, ?_⟩
    simpa [List.getD_eq_getElem?_getD, hi] using hpB

theorem disjoint_brunPrefix_block {blocks : List (Finset ℕ)}
    (hdisj : blocks.Pairwise Disjoint) {i : ℕ} (hi : i < blocks.length) :
    Disjoint (brunPrefix blocks i) (blocks.getD i ∅) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [brunPrefix, mem_foldr_union_iff] at hp1
  rcases hp1 with ⟨B, hB, hpB⟩
  rcases List.mem_iff_getElem.mp hB with ⟨k, hk, rfl⟩
  have hk_take : k < min i blocks.length := by simpa [List.length_take] using hk
  have hki : k < i := lt_of_lt_of_le hk_take (Nat.min_le_left _ _)
  have hklen : k < blocks.length := lt_of_lt_of_le hk_take (Nat.min_le_right _ _)
  have hget_k : (blocks.take i)[k] = blocks[k] := List.getElem_take
  have hpBk : p ∈ blocks[k] := by rwa [hget_k] at hpB
  have hpBi : p ∈ blocks[i] := by simpa [List.getD_eq_getElem?_getD, hi] using hp2
  have hdk : Disjoint blocks[k] blocks[i] := (List.pairwise_iff_getElem.mp hdisj) k i hklen hi hki
  exact Finset.disjoint_left.mp hdk hpBk hpBi

theorem brunPrefix_inter_card_eq_sum {blocks : List (Finset ℕ)}
    (hdisj : blocks.Pairwise Disjoint) (S : Finset ℕ) {i : ℕ} (hi : i ≤ blocks.length) :
    (S ∩ brunPrefix blocks i).card =
      ∑ s ∈ Finset.range i, (S ∩ blocks.getD s ∅).card := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi_lt : i < blocks.length := hi
    have hdisj_i : Disjoint (S ∩ brunPrefix blocks i) (S ∩ blocks.getD i ∅) :=
      (disjoint_brunPrefix_block hdisj hi_lt).mono Finset.inter_subset_right Finset.inter_subset_right
    rw [brunPrefix_succ blocks hi_lt, Finset.inter_union_distrib_left,
      Finset.card_union_of_disjoint hdisj_i, ih (Nat.le_of_lt hi_lt), Finset.sum_range_succ]

theorem brunAdmissible_iff_sum_blocks {blocks : List (Finset ℕ)} {caps : List ℕ}
    (hdisj : blocks.Pairwise Disjoint) (S : Finset ℕ) :
    BrunAdmissible blocks caps S ↔
      S ⊆ brunUnion blocks ∧
        ∀ i : ℕ, i < blocks.length →
          ∑ s ∈ Finset.range (i + 1), (S ∩ blocks.getD s ∅).card ≤ caps.getD i 0 := by
  unfold BrunAdmissible
  refine and_congr_right fun _ => ?_
  refine forall_congr' fun i => ?_
  refine imp_congr_right fun hi => ?_
  rw [brunPrefix_inter_card_eq_sum hdisj S hi]

@[simp]
theorem restrictBlocks_length (blocks : List (Finset ℕ)) (P' : Finset ℕ) :
    (restrictBlocks blocks P').length = blocks.length := by
  simp [restrictBlocks]

theorem restrictBlocks_getD (blocks : List (Finset ℕ)) (P' : Finset ℕ) (i : ℕ) :
    (restrictBlocks blocks P').getD i ∅ = blocks.getD i ∅ ∩ P' := by
  by_cases hi : i < blocks.length
  · simp [restrictBlocks, List.getD_eq_getElem?_getD, hi]
  · simp [restrictBlocks, List.getD_eq_getElem?_getD, hi]

theorem restrictBlocks_pairwise_disjoint {blocks : List (Finset ℕ)} (P' : Finset ℕ)
    (hdisj : blocks.Pairwise Disjoint) :
    (restrictBlocks blocks P').Pairwise Disjoint := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < blocks.length := by simpa using hi
  have hj' : j < blocks.length := by simpa using hj
  simp only [restrictBlocks, List.getElem_map]
  exact ((List.pairwise_iff_getElem.mp hdisj) i j hi' hj' hij).mono
    Finset.inter_subset_left Finset.inter_subset_left

theorem brunPrefix_restrictBlocks (blocks : List (Finset ℕ)) (P' : Finset ℕ) (i : ℕ) :
    brunPrefix (restrictBlocks blocks P') i = brunPrefix blocks i ∩ P' := by
  unfold brunPrefix restrictBlocks
  rw [← List.map_take]
  induction (blocks.take i) with
  | nil => simp
  | cons B Bs ih =>
    simp [ih, Finset.union_inter_distrib_right]

theorem brunUnion_restrictBlocks (blocks : List (Finset ℕ)) (P' : Finset ℕ) :
    brunUnion (restrictBlocks blocks P') = brunUnion blocks ∩ P' := by
  rw [← brunPrefix_eq_brunUnion_of_le (restrictBlocks blocks P') (le_refl _),
    ← brunPrefix_eq_brunUnion_of_le blocks (le_refl _),
    restrictBlocks_length, brunPrefix_restrictBlocks]

end BlockSetup

section TopK

/-- Canonical `k` largest elements of a finite set `T : Finset ℕ`. -/
def topK : ℕ → Finset ℕ → Finset ℕ
  | 0, _ => ∅
  | k + 1, T =>
      if h : T.Nonempty then
        insert (T.max' h) (topK k (T.erase (T.max' h)))
      else ∅

theorem topK_subset (k : ℕ) (T : Finset ℕ) : topK k T ⊆ T := by
  induction k generalizing T with
  | zero => simp [topK]
  | succ k ih =>
    unfold topK
    split_ifs with h
    · refine Finset.insert_subset_iff.mpr ⟨T.max'_mem h, ?_⟩
      exact (ih (T.erase (T.max' h))).trans (Finset.erase_subset _ _)
    · exact Finset.empty_subset _

theorem topK_card {k : ℕ} {T : Finset ℕ} (hk : k ≤ T.card) : (topK k T).card = k := by
  induction k generalizing T with
  | zero => simp [topK]
  | succ k ih =>
    have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos k) hk)
    have hnot : T.max' hT ∉ topK k (T.erase (T.max' hT)) := by
      intro hmem
      exact (Finset.notMem_erase (T.max' hT) T) (topK_subset k _ hmem)
    have hcard_erase : k ≤ (T.erase (T.max' hT)).card := by
      rw [Finset.card_erase_of_mem (T.max'_mem hT)]
      omega
    unfold topK
    simp [hT, hnot, ih hcard_erase]

theorem topK_lt {k : ℕ} {T : Finset ℕ} {x y : ℕ}
    (hx : x ∈ T \ topK k T) (hy : y ∈ topK k T) : x < y := by
  induction k generalizing T with
  | zero => simp [topK] at hy
  | succ k ih =>
    unfold topK at hx hy
    split_ifs at hx hy with h
    · have hx' := Finset.mem_sdiff.mp hx
      have hx_ne : x ≠ T.max' h := by
        rintro rfl
        exact hx'.2 (Finset.mem_insert_self _ _)
      have hx_erase : x ∈ T.erase (T.max' h) \ topK k (T.erase (T.max' h)) := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hx_ne, hx'.1⟩, ?_⟩
        intro hmem
        exact hx'.2 (Finset.mem_insert_of_mem hmem)
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact lt_of_le_of_ne (T.le_max' x hx'.1) hx_ne
      · exact ih hx_erase hy'
    · simp at hy

theorem eq_topK_of_lt {k : ℕ} {T U : Finset ℕ} (hUT : U ⊆ T) (hcard : U.card = k)
    (hlt : ∀ x ∈ T \ U, ∀ y ∈ U, x < y) : U = topK k T := by
  induction k generalizing T U with
  | zero =>
    rw [Finset.card_eq_zero.mp hcard]
    simp [topK]
  | succ k ih =>
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    have hTne : T.Nonempty := hUne.mono hUT
    have hmax_mem : T.max' hTne ∈ U := by
      by_contra hnot
      rcases hUne with ⟨y, hyU⟩
      have hlt_y : T.max' hTne < y := hlt (T.max' hTne) (Finset.mem_sdiff.mpr ⟨T.max'_mem hTne, hnot⟩) y hyU
      have hle : y ≤ T.max' hTne := T.le_max' y (hUT hyU)
      omega
    let U' := U.erase (T.max' hTne)
    let T' := T.erase (T.max' hTne)
    have hU'T' : U' ⊆ T' := Finset.erase_subset_erase _ hUT
    have hcard' : U'.card = k := by
      rw [Finset.card_erase_of_mem hmax_mem, hcard, Nat.add_sub_cancel]
    have hlt' : ∀ x ∈ T' \ U', ∀ y ∈ U', x < y := by
      intro x hx y hy
      have hx' : x ∈ T \ U := Finset.mem_sdiff.mpr
        ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).2,
          fun hmem => (Finset.mem_sdiff.mp hx).2 (Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp hx).1).1, hmem⟩)⟩
      exact hlt x hx' y (Finset.mem_erase.mp hy).2
    have heq' : U' = topK k T' := ih hU'T' hcard' hlt'
    unfold topK
    simp only [hTne, ↓reduceDIte]
    rw [← heq']
    exact (Finset.insert_erase hmax_mem).symm

end TopK

end BuchstabSwitching
