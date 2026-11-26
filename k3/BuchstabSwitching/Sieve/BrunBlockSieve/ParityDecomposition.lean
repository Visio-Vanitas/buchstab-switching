import BuchstabSwitching.Sieve.BrunBlockSieve.SetupAndTopK
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Combinatorial Brun Block Sieve: Parity Decomposition

Canonical prefix-tail bijection for inadmissible subsets (`badPrefixes`, `badTail`, `badPairs`)
and Brun Parity Theorem A (`brun_block_pointwise_lower`, `brun_block_div_pointwise_lower`).
-/

namespace BuchstabSwitching

section BrunDecomposition

/-- Canonical prefix triples `(i, U₀, U₁)` witnessing the first cap violation of subsets of `A`. -/
def badPrefixes (blocks : List (Finset ℕ)) (caps : List ℕ) (A : Finset ℕ) :
    Finset (ℕ × Finset ℕ × Finset ℕ) :=
  (Finset.range blocks.length).biUnion fun i =>
    ((A ∩ brunPrefix blocks i).powerset.filter
      (fun U₀ => U₀.card ≤ caps.getD i 0 ∧
        ∀ j < i, (U₀ ∩ brunPrefix blocks (j + 1)).card ≤ caps.getD j 0)).biUnion fun U₀ =>
      ((A ∩ blocks.getD i ∅).powersetCard (caps.getD i 0 + 1 - U₀.card)).image
        (fun U₁ => (i, U₀, U₁))

/-- Free tail elements below `U₁` in block `i` and beyond block `i`. -/
def badTail (blocks : List (Finset ℕ)) (A : Finset ℕ) (i : ℕ) (U₁ : Finset ℕ) : Finset ℕ :=
  ((A ∩ blocks.getD i ∅).filter (fun p => ∀ y ∈ U₁, p < y)) ∪ (A \ brunPrefix blocks (i + 1))

/-- Full bijection domain `((i, U₀, U₁), R)` decomposing `brunBadSubsets blocks caps A`. -/
def badPairs (blocks : List (Finset ℕ)) (caps : List ℕ) (A : Finset ℕ) :
    Finset ((ℕ × Finset ℕ × Finset ℕ) × Finset ℕ) :=
  (badPrefixes blocks caps A).biUnion fun t =>
    (badTail blocks A t.1 t.2.2).powerset.image (fun R => (t, R))

lemma badPrefixes_mem_iff {blocks : List (Finset ℕ)} {caps : List ℕ} {A : Finset ℕ}
    {i : ℕ} {U₀ U₁ : Finset ℕ} :
    (i, U₀, U₁) ∈ badPrefixes blocks caps A ↔
      i < blocks.length ∧
        U₀ ⊆ A ∩ brunPrefix blocks i ∧
        U₀.card ≤ caps.getD i 0 ∧
        (∀ j < i, (U₀ ∩ brunPrefix blocks (j + 1)).card ≤ caps.getD j 0) ∧
        U₁ ⊆ A ∩ blocks.getD i ∅ ∧
        U₁.card = caps.getD i 0 + 1 - U₀.card := by
  simp only [badPrefixes, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
    Finset.mem_powerset, Finset.mem_powersetCard, Finset.mem_image, Prod.ext_iff]
  constructor
  · rintro ⟨i', hi', U₀', ⟨hU₀'sub, hU₀'card, hU₀'prev⟩, U₁', ⟨hU₁'sub, hU₁'card⟩, rfl, rfl, rfl⟩
    exact ⟨hi', hU₀'sub, hU₀'card, hU₀'prev, hU₁'sub, hU₁'card⟩
  · rintro ⟨hi, hU₀sub, hU₀card, hU₀prev, hU₁sub, hU₁card⟩
    exact ⟨i, hi, U₀, ⟨hU₀sub, hU₀card, hU₀prev⟩, U₁, ⟨hU₁sub, hU₁card⟩, rfl, rfl, rfl⟩

private lemma badPairs_mem_iff {blocks : List (Finset ℕ)} {caps : List ℕ} {A : Finset ℕ}
    {t : ℕ × Finset ℕ × Finset ℕ} {R : Finset ℕ} :
    (t, R) ∈ badPairs blocks caps A ↔
      t ∈ badPrefixes blocks caps A ∧ R ⊆ badTail blocks A t.1 t.2.2 := by
  simp only [badPairs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨t', ht', R', hR', hEq⟩
    rcases Prod.ext_iff.mp hEq with ⟨rfl, rfl⟩
    exact ⟨ht', hR'⟩
  · rintro ⟨ht, hR⟩
    exact ⟨t, ht, R, hR, rfl⟩

private lemma badTriple_disjoint_and_first_fail {blocks : List (Finset ℕ)} {caps : List ℕ}
    {A : Finset ℕ} (hdisj : blocks.Pairwise Disjoint) (_hA : A ⊆ brunUnion blocks)
    {i : ℕ} {U₀ U₁ R : Finset ℕ} (ht : (i, U₀, U₁) ∈ badPrefixes blocks caps A)
    (hR : R ⊆ badTail blocks A i U₁) :
    Disjoint U₀ U₁ ∧ Disjoint (U₀ ∪ U₁) R ∧
      U₀ ∪ U₁ ∪ R ⊆ A ∧
      ¬ BrunAdmissible blocks caps (U₀ ∪ U₁ ∪ R) ∧
      (∀ j < i, ((U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks (j + 1)).card ≤ caps.getD j 0) ∧
      caps.getD i 0 < ((U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks (i + 1)).card ∧
      (U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks i = U₀ ∧
      (U₀ ∪ U₁ ∪ R) ∩ blocks.getD i ∅ = U₁ ∪ (R ∩ blocks.getD i ∅) := by
  rcases badPrefixes_mem_iff.mp ht with ⟨hi, hU₀sub, hU₀card, hU₀prev, hU₁sub, hU₁card⟩
  have hdisj_pref_block : Disjoint (brunPrefix blocks i) (blocks.getD i ∅) :=
    disjoint_brunPrefix_block hdisj hi
  have hU₀_pref : U₀ ⊆ brunPrefix blocks i := hU₀sub.trans Finset.inter_subset_right
  have hU₀_A : U₀ ⊆ A := hU₀sub.trans Finset.inter_subset_left
  have hU₁_block : U₁ ⊆ blocks.getD i ∅ := hU₁sub.trans Finset.inter_subset_right
  have hU₁_A : U₁ ⊆ A := hU₁sub.trans Finset.inter_subset_left
  have hdisj_01 : Disjoint U₀ U₁ := hdisj_pref_block.mono hU₀_pref hU₁_block
  have htail_A : badTail blocks A i U₁ ⊆ A := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · exact (Finset.mem_inter.mp (Finset.mem_filter.mp hp1).1).1
    · exact (Finset.mem_sdiff.mp hp2).1
  have hR_A : R ⊆ A := hR.trans htail_A
  have hdisj_0R : Disjoint U₀ R := by
    rw [Finset.disjoint_left]
    intro p hp0 hpR
    have hp_pref : p ∈ brunPrefix blocks i := hU₀_pref hp0
    have hp_next : p ∈ brunPrefix blocks (i + 1) :=
      brunPrefix_mono blocks (Nat.le_succ i) hp_pref
    rcases Finset.mem_union.mp (hR hpR) with hp1 | hp2
    · have hp_block : p ∈ blocks.getD i ∅ := (Finset.mem_inter.mp (Finset.mem_filter.mp hp1).1).2
      exact Finset.disjoint_left.mp hdisj_pref_block hp_pref hp_block
    · exact (Finset.mem_sdiff.mp hp2).2 hp_next
  have hdisj_1R : Disjoint U₁ R := by
    rw [Finset.disjoint_left]
    intro p hp1 hpR
    have hp_block : p ∈ blocks.getD i ∅ := hU₁_block hp1
    have hp_next : p ∈ brunPrefix blocks (i + 1) := by
      rw [brunPrefix_succ blocks hi]
      exact Finset.mem_union_right _ hp_block
    rcases Finset.mem_union.mp (hR hpR) with hp_f | hp_s
    · have hlt := (Finset.mem_filter.mp hp_f).2 p hp1
      exact lt_irrefl p hlt
    · exact (Finset.mem_sdiff.mp hp_s).2 hp_next
  have hdisj_01R : Disjoint (U₀ ∪ U₁) R := Finset.disjoint_union_left.mpr ⟨hdisj_0R, hdisj_1R⟩
  have hS_A : U₀ ∪ U₁ ∪ R ⊆ A := Finset.union_subset (Finset.union_subset hU₀_A hU₁_A) hR_A
  have hR_disj_pref : Disjoint R (brunPrefix blocks i) := by
    rw [Finset.disjoint_left]
    intro p hpR hp_pref
    have hp_next : p ∈ brunPrefix blocks (i + 1) :=
      brunPrefix_mono blocks (Nat.le_succ i) hp_pref
    rcases Finset.mem_union.mp (hR hpR) with hp1 | hp2
    · have hp_block : p ∈ blocks.getD i ∅ := (Finset.mem_inter.mp (Finset.mem_filter.mp hp1).1).2
      exact Finset.disjoint_left.mp hdisj_pref_block hp_pref hp_block
    · exact (Finset.mem_sdiff.mp hp2).2 hp_next
  have hU₁_disj_pref : Disjoint U₁ (brunPrefix blocks i) :=
    hdisj_pref_block.symm.mono_left hU₁_block
  have hS_pref : (U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks i = U₀ := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(hp0 | hp1) | hpR, hpp⟩
      · exact hp0
      · exact absurd hpp (Finset.disjoint_left.mp hU₁_disj_pref hp1)
      · exact absurd hpp (Finset.disjoint_left.mp hR_disj_pref hpR)
    · intro hp0
      exact ⟨Or.inl (Or.inl hp0), hU₀_pref hp0⟩
  have hS_block : (U₀ ∪ U₁ ∪ R) ∩ blocks.getD i ∅ = U₁ ∪ (R ∩ blocks.getD i ∅) := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(hp0 | hp1) | hpR, hpb⟩
      · exact absurd hpb (Finset.disjoint_left.mp hdisj_pref_block (hU₀_pref hp0))
      · exact Or.inl hp1
      · exact Or.inr ⟨hpR, hpb⟩
    · rintro (hp1 | ⟨hpR, hpb⟩)
      · exact ⟨Or.inl (Or.inr hp1), hU₁_block hp1⟩
      · exact ⟨Or.inr hpR, hpb⟩
  have hprev : ∀ j < i, ((U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks (j + 1)).card ≤ caps.getD j 0 := by
    intro j hj
    have hsub : brunPrefix blocks (j + 1) ⊆ brunPrefix blocks i := brunPrefix_mono blocks hj
    have hinter : (U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks (j + 1) = U₀ ∩ brunPrefix blocks (j + 1) := by
      calc
        (U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks (j + 1)
            = ((U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks i) ∩ brunPrefix blocks (j + 1) := by
                rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsub]
        _ = U₀ ∩ brunPrefix blocks (j + 1) := by rw [hS_pref]
    rw [hinter]
    exact hU₀prev j hj
  have hfail_i : caps.getD i 0 < ((U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks (i + 1)).card := by
    have hU01_sub : U₀ ∪ U₁ ⊆ (U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks (i + 1) := by
      refine Finset.subset_inter (Finset.subset_union_left) ?_
      rw [brunPrefix_succ blocks hi]
      exact Finset.union_subset_union hU₀_pref hU₁_block
    have hcard_01 : (U₀ ∪ U₁).card = caps.getD i 0 + 1 := by
      rw [Finset.card_union_of_disjoint hdisj_01, hU₁card]
      omega
    have hle := Finset.card_le_card hU01_sub
    omega
  have hnot_adm : ¬ BrunAdmissible blocks caps (U₀ ∪ U₁ ∪ R) := by
    intro hadm
    have hle := hadm.2 i hi
    omega
  exact ⟨hdisj_01, hdisj_01R, hS_A, hnot_adm, hprev, hfail_i, hS_pref, hS_block⟩

theorem sum_powerset_mul_neg_one {R : Type*} [CommRing R] (T : Finset ℕ) (w : ℕ → R) :
    ∑ S ∈ T.powerset, (-1 : R) ^ S.card * ∏ p ∈ S, w p = ∏ p ∈ T, (1 - w p) := by
  have h1 : ∏ p ∈ T, (1 - w p) = ∏ p ∈ T, (1 + -w p) := by
    refine Finset.prod_congr rfl fun p _ => by ring
  rw [h1, Finset.prod_one_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_neg]

theorem brun_bad_sum_eq {R : Type*} [CommRing R] (blocks : List (Finset ℕ)) (caps : List ℕ)
    (A : Finset ℕ) (w : ℕ → R)
    (hdisj : blocks.Pairwise Disjoint) (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hA : A ⊆ brunUnion blocks) :
    ∑ S ∈ brunBadSubsets blocks caps A, (-1 : R) ^ S.card * ∏ p ∈ S, w p =
      ∑ t ∈ badPrefixes blocks caps A,
        (∏ p ∈ t.2.1 ∪ t.2.2, w p) * ∏ p ∈ badTail blocks A t.1 t.2.2, (1 - w p) := by
  have hbij :
      ∑ S ∈ brunBadSubsets blocks caps A, (-1 : R) ^ S.card * ∏ p ∈ S, w p =
        ∑ x ∈ badPairs blocks caps A,
          (-1 : R) ^ (x.1.2.1 ∪ x.1.2.2 ∪ x.2).card * ∏ p ∈ (x.1.2.1 ∪ x.1.2.2 ∪ x.2), w p := by
    symm
    refine Finset.sum_bij (fun x _ => x.1.2.1 ∪ x.1.2.2 ∪ x.2) ?_ ?_ ?_ ?_
    · intro ⟨⟨i, U₀, U₁⟩, R⟩ hx
      rcases badPairs_mem_iff.mp hx with ⟨ht, hR⟩
      have hprop := badTriple_disjoint_and_first_fail hdisj hA ht hR
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hprop.2.2.1, hprop.2.2.2.1⟩
    · intro ⟨⟨i, U₀, U₁⟩, R⟩ hx ⟨⟨i', U₀', U₁'⟩, R'⟩ hx' heq
      dsimp only at heq
      rcases badPairs_mem_iff.mp hx with ⟨ht, hR⟩
      rcases badPairs_mem_iff.mp hx' with ⟨ht', hR'⟩
      have hprop := badTriple_disjoint_and_first_fail hdisj hA ht hR
      have hprop' := badTriple_disjoint_and_first_fail hdisj hA ht' hR'
      have hii' : i = i' := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have h1 := hprop'.2.2.2.2.1 i hlt
          have h2 := hprop.2.2.2.2.2.1
          rw [heq] at h2
          omega
        · have h1 := hprop.2.2.2.2.1 i' hlt
          have h2 := hprop'.2.2.2.2.2.1
          rw [← heq] at h2
          omega
      subst hii'
      have hU0 : U₀ = U₀' := by
        calc
          U₀ = (U₀ ∪ U₁ ∪ R) ∩ brunPrefix blocks i := hprop.2.2.2.2.2.2.1.symm
          _ = (U₀' ∪ U₁' ∪ R') ∩ brunPrefix blocks i := by rw [heq]
          _ = U₀' := hprop'.2.2.2.2.2.2.1
      subst hU0
      rcases badPrefixes_mem_iff.mp ht with ⟨hi, _, _, _, hU₁sub, hU₁card⟩
      rcases badPrefixes_mem_iff.mp ht' with ⟨_, _, _, _, hU₁'sub, hU₁'card⟩
      let S := U₀ ∪ U₁ ∪ R
      let T := S ∩ blocks.getD i ∅
      have hS_block : T = U₁ ∪ (R ∩ blocks.getD i ∅) := hprop.2.2.2.2.2.2.2
      have hS_block' : T = U₁' ∪ (R' ∩ blocks.getD i ∅) := by
        simpa [S, T, heq] using hprop'.2.2.2.2.2.2.2
      have hU₁_top : U₁ = topK (caps.getD i 0 + 1 - U₀.card) T := by
        refine eq_topK_of_lt (by rw [hS_block]; exact Finset.subset_union_left) hU₁card ?_
        intro x hx y hy
        rw [hS_block] at hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxnot⟩
        rcases Finset.mem_union.mp hxU with hx1 | hxR
        · exact absurd hx1 hxnot
        · have hxR_mem := (Finset.mem_inter.mp hxR).1
          rcases Finset.mem_union.mp (hR hxR_mem) with hxf | hxs
          · exact (Finset.mem_filter.mp hxf).2 y hy
          · have hx_next : x ∈ brunPrefix blocks (i + 1) := by
              rw [brunPrefix_succ blocks hi]
              exact Finset.mem_union_right _ (Finset.mem_inter.mp hxR).2
            exact absurd hx_next (Finset.mem_sdiff.mp hxs).2
      have hU₁'_top : U₁' = topK (caps.getD i 0 + 1 - U₀.card) T := by
        refine eq_topK_of_lt (by rw [hS_block']; exact Finset.subset_union_left) hU₁'card ?_
        intro x hx y hy
        rw [hS_block'] at hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxnot⟩
        rcases Finset.mem_union.mp hxU with hx1 | hxR
        · exact absurd hx1 hxnot
        · have hxR_mem := (Finset.mem_inter.mp hxR).1
          rcases Finset.mem_union.mp (hR' hxR_mem) with hxf | hxs
          · exact (Finset.mem_filter.mp hxf).2 y hy
          · have hx_next : x ∈ brunPrefix blocks (i + 1) := by
              rw [brunPrefix_succ blocks hi]
              exact Finset.mem_union_right _ (Finset.mem_inter.mp hxR).2
            exact absurd hx_next (Finset.mem_sdiff.mp hxs).2
      have hU1 : U₁ = U₁' := hU₁_top.trans hU₁'_top.symm
      subst hU1
      have hR_eq : R = R' := by
        have h1 : R = (U₀ ∪ U₁ ∪ R) \ (U₀ ∪ U₁) := (Finset.union_sdiff_cancel_left hprop.2.1).symm
        have h2 : R' = (U₀ ∪ U₁ ∪ R') \ (U₀ ∪ U₁) := (Finset.union_sdiff_cancel_left hprop'.2.1).symm
        rw [h1, heq, ← h2]
      subst hR_eq
      rfl
    · intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hSA, hnot_adm⟩
      have hSA' : S ⊆ A := Finset.mem_powerset.mp hSA
      have hSP : S ⊆ brunUnion blocks := hSA'.trans hA
      have hex : ∃ i : ℕ, i < blocks.length ∧ caps.getD i 0 < (S ∩ brunPrefix blocks (i + 1)).card := by
        by_contra hnone
        push Not at hnone
        exact hnot_adm ⟨hSP, hnone⟩
      classical
      let i : ℕ := Nat.find hex
      have hi_spec : i < blocks.length ∧ caps.getD i 0 < (S ∩ brunPrefix blocks (i + 1)).card :=
        Nat.find_spec hex
      have hi : i < blocks.length := hi_spec.1
      have hfail : caps.getD i 0 < (S ∩ brunPrefix blocks (i + 1)).card := hi_spec.2
      have hmin : ∀ j < i, (S ∩ brunPrefix blocks (j + 1)).card ≤ caps.getD j 0 := by
        intro j hj
        by_contra hlt
        push Not at hlt
        exact Nat.find_min hex hj ⟨lt_trans hj hi, hlt⟩
      let U₀ : Finset ℕ := S ∩ brunPrefix blocks i
      have hU₀sub : U₀ ⊆ A ∩ brunPrefix blocks i := Finset.inter_subset_inter_right hSA'
      have hU₀prev : ∀ j < i, (U₀ ∩ brunPrefix blocks (j + 1)).card ≤ caps.getD j 0 := by
        intro j hj
        have hsub : brunPrefix blocks (j + 1) ⊆ brunPrefix blocks i := brunPrefix_mono blocks hj
        have hinter : U₀ ∩ brunPrefix blocks (j + 1) = S ∩ brunPrefix blocks (j + 1) := by
          dsimp only [U₀]
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsub]
        rw [hinter]
        exact hmin j hj
      have hU₀card : U₀.card ≤ caps.getD i 0 := by
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · simp [U₀, hi0]
        · obtain ⟨k, hik⟩ := Nat.exists_eq_succ_of_ne_zero hipos.ne'
          have hsucc_len : k + 1 < caps.length := by omega
          have hle_k : U₀.card ≤ caps.getD k 0 := by
            have hk_lt : k < i := by omega
            simpa [U₀, hik, Finset.inter_self] using hmin k hk_lt
          rw [hik]
          exact hle_k.trans (hmono k (k + 1) (Nat.le_succ k) hsucc_len)
      let T : Finset ℕ := S ∩ blocks.getD i ∅
      have hdisj_i : Disjoint (brunPrefix blocks i) (blocks.getD i ∅) :=
        disjoint_brunPrefix_block hdisj hi
      have hdisj_U0T : Disjoint U₀ T := hdisj_i.mono Finset.inter_subset_right Finset.inter_subset_right
      have hS_next : S ∩ brunPrefix blocks (i + 1) = U₀ ∪ T := by
        rw [brunPrefix_succ blocks hi, Finset.inter_union_distrib_left]
      have hcard_need : caps.getD i 0 + 1 - U₀.card ≤ T.card := by
        have hsum : (S ∩ brunPrefix blocks (i + 1)).card = U₀.card + T.card := by
          rw [hS_next, Finset.card_union_of_disjoint hdisj_U0T]
        omega
      let k : ℕ := caps.getD i 0 + 1 - U₀.card
      let U₁ : Finset ℕ := topK k T
      have hU₁sub_T : U₁ ⊆ T := topK_subset k T
      have hU₁sub : U₁ ⊆ A ∩ blocks.getD i ∅ :=
        hU₁sub_T.trans (Finset.inter_subset_inter_right hSA')
      have hU₁card : U₁.card = k := topK_card hcard_need
      let R : Finset ℕ := S \ (U₀ ∪ U₁)
      have ht_mem : (i, U₀, U₁) ∈ badPrefixes blocks caps A :=
        badPrefixes_mem_iff.mpr ⟨hi, hU₀sub, hU₀card, hU₀prev, hU₁sub, hU₁card⟩
      have hR_sub : R ⊆ badTail blocks A i U₁ := by
        intro p hp
        rcases Finset.mem_sdiff.mp hp with ⟨hpS, hpnot⟩
        by_cases hp_next : p ∈ brunPrefix blocks (i + 1)
        · rw [brunPrefix_succ blocks hi] at hp_next
          rcases Finset.mem_union.mp hp_next with hp_pref | hp_block
          · exact absurd (Finset.mem_union_left U₁ (Finset.mem_inter.mpr ⟨hpS, hp_pref⟩)) hpnot
          · have hpT : p ∈ T := Finset.mem_inter.mpr ⟨hpS, hp_block⟩
            have hp_not_U1 : p ∉ U₁ := fun h => hpnot (Finset.mem_union_right U₀ h)
            refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hSA' hpS, hp_block⟩, ?_⟩)
            intro y hy
            exact topK_lt (Finset.mem_sdiff.mpr ⟨hpT, hp_not_U1⟩) hy
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hSA' hpS, hp_next⟩)
      refine ⟨((i, U₀, U₁), R), badPairs_mem_iff.mpr ⟨ht_mem, hR_sub⟩, ?_⟩
      have h01S : U₀ ∪ U₁ ⊆ S :=
        Finset.union_subset Finset.inter_subset_left (hU₁sub_T.trans Finset.inter_subset_left)
      exact Finset.union_sdiff_of_subset h01S
    · intro x _
      rfl
  rw [hbij]
  have hdisj_pairs :
      ((badPrefixes blocks caps A : Finset (ℕ × Finset ℕ × Finset ℕ)) :
          Set (ℕ × Finset ℕ × Finset ℕ)).PairwiseDisjoint
        (fun t => (badTail blocks A t.1 t.2.2).powerset.image (fun R => (t, R))) := by
    intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨R₁, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨R₂, _, hEq⟩
    exact hne (congrArg Prod.fst hEq).symm
  rw [badPairs, Finset.sum_biUnion hdisj_pairs]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hinj_t : Set.InjOn (fun R : Finset ℕ => (t, R))
      ((badTail blocks A t.1 t.2.2).powerset : Set (Finset ℕ)) := by
    intro R₁ _ R₂ _ hEq
    exact congrArg Prod.snd hEq
  rw [Finset.sum_image hinj_t, ← sum_powerset_mul_neg_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_
  rcases t with ⟨i, U₀, U₁⟩
  have hprop := badTriple_disjoint_and_first_fail hdisj hA ht (Finset.mem_powerset.mp hR)
  rcases badPrefixes_mem_iff.mp ht with ⟨hi, _, hU₀card, _, _, hU₁card⟩
  have hi_caps : i < caps.length := by omega
  have hodd_i : Odd (caps.getD i 0) := by
    apply hodd
    have : caps.getD i 0 = caps[i] := by simp [List.getD_eq_getElem?_getD, hi_caps]
    rw [this]
    exact List.getElem_mem hi_caps
  have heven_i : Even (caps.getD i 0 + 1) := hodd_i.add_one
  have hcard_01 : (U₀ ∪ U₁).card = caps.getD i 0 + 1 := by
    rw [Finset.card_union_of_disjoint hprop.1, hU₁card]
    omega
  have hcard_all : (U₀ ∪ U₁ ∪ R).card = (caps.getD i 0 + 1) + R.card := by
    rw [Finset.card_union_of_disjoint hprop.2.1, hcard_01]
  have hprod_all : ∏ p ∈ U₀ ∪ U₁ ∪ R, w p = (∏ p ∈ U₀ ∪ U₁, w p) * ∏ p ∈ R, w p :=
    Finset.prod_union hprop.2.1
  rw [hcard_all, pow_add, heven_i.neg_one_pow, one_mul, hprod_all]
  ring

/-- **Brun Parity Theorem A (`brun_block_pointwise_lower`)**:
for any `A ⊆ brunUnion blocks`, the alternating sum over Brun-admissible subsets of `A` is at most
`1[A = ∅]`. -/
theorem brun_block_pointwise_lower (blocks : List (Finset ℕ)) (caps : List ℕ) (A : Finset ℕ)
    (hdisj : blocks.Pairwise Disjoint) (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hA : A ⊆ brunUnion blocks) :
    ∑ S ∈ A.powerset.filter (BrunAdmissible blocks caps), (-1 : ℤ) ^ S.card ≤
      if A = ∅ then 1 else 0 := by
  have hfull : ∑ S ∈ A.powerset, (-1 : ℤ) ^ S.card = if A = ∅ then 1 else 0 := by
    have h := sum_powerset_mul_neg_one A (fun _ => (1 : ℤ))
    simp only [Finset.prod_const_one, mul_one] at h
    rw [h]
    by_cases hAe : A = ∅
    · subst hAe; simp
    · rcases Finset.ne_empty_iff_nonempty.mp hAe with ⟨p, hp⟩
      simp [hAe, Finset.prod_eq_zero hp]
  have hsplit : ∑ S ∈ A.powerset, (-1 : ℤ) ^ S.card =
      ∑ S ∈ A.powerset.filter (BrunAdmissible blocks caps), (-1 : ℤ) ^ S.card +
        ∑ S ∈ brunBadSubsets blocks caps A, (-1 : ℤ) ^ S.card := by
    symm
    exact Finset.sum_filter_add_sum_filter_not A.powerset (BrunAdmissible blocks caps)
      (fun S => (-1 : ℤ) ^ S.card)
  have hbad_eq : ∑ S ∈ brunBadSubsets blocks caps A, (-1 : ℤ) ^ S.card =
      ∑ t ∈ badPrefixes blocks caps A, ∏ _p ∈ badTail blocks A t.1 t.2.2, (0 : ℤ) := by
    have h := brun_bad_sum_eq (R := ℤ) blocks caps A (fun _ => (1 : ℤ)) hdisj hlen hodd hmono hA
    simpa [Finset.prod_const_one, one_mul] using h
  have hbad_nonneg : 0 ≤ ∑ S ∈ brunBadSubsets blocks caps A, (-1 : ℤ) ^ S.card := by
    rw [hbad_eq]
    refine Finset.sum_nonneg fun t _ => ?_
    by_cases ht : badTail blocks A t.1 t.2.2 = ∅
    · simp [ht]
    · rcases Finset.ne_empty_iff_nonempty.mp ht with ⟨p, hp⟩
      simp [Finset.prod_eq_zero hp]
  linarith

/-- Hybrid `Q₁ × P₂` divisibility pointwise Brun lower bound. -/
theorem brun_block_div_pointwise_lower (Q₁ : Finset ℕ) (blocks : List (Finset ℕ)) (caps : List ℕ)
    (n : ℕ) (hdisj : blocks.Pairwise Disjoint) (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0) :
    (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
      if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) ≤
      if (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ brunUnion blocks, ¬ p ∣ n) then 1 else 0 := by
  let P₂ := brunUnion blocks
  let A₁ := Q₁.filter (fun p => p ∣ n)
  let A₂ := P₂.filter (fun p => p ∣ n)
  have hsub₁ : A₁.powerset ⊆ Q₁.powerset := Finset.powerset_mono.mpr (Finset.filter_subset _ _)
  have hsub₂ : A₂.powerset.filter (BrunAdmissible blocks caps) ⊆ brunAdmSubsets blocks caps :=
    Finset.filter_subset_filter _ (Finset.powerset_mono.mpr (Finset.filter_subset _ _))
  have hmem₁ : ∀ S₁ ∈ Q₁.powerset, (∀ p ∈ S₁, p ∣ n) ↔ S₁ ∈ A₁.powerset := by
    intro S₁ hS₁
    rw [Finset.mem_powerset] at hS₁ ⊢
    simp only [A₁, Finset.subset_iff, Finset.mem_filter]
    exact ⟨fun h p hp => ⟨hS₁ hp, h p hp⟩, fun h p hp => (h hp).2⟩
  have hmem₂ : ∀ S₂ ∈ brunAdmSubsets blocks caps,
      (∀ p ∈ S₂, p ∣ n) ↔ S₂ ∈ A₂.powerset.filter (BrunAdmissible blocks caps) := by
    intro S₂ hS₂
    have hS₂' := Finset.mem_filter.mp hS₂
    have hS₂P := Finset.mem_powerset.mp hS₂'.1
    simp only [A₂, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
    exact ⟨fun h => ⟨fun p hp => ⟨hS₂P hp, h p hp⟩, hS₂'.2⟩, fun h p hp => (h.1 hp).2⟩
  have hfactor :
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
        if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) =
      (∑ S₁ ∈ A₁.powerset, (-1 : ℤ) ^ S₁.card) *
        (∑ S₂ ∈ A₂.powerset.filter (BrunAdmissible blocks caps), (-1 : ℤ) ^ S₂.card) := by
    have h1 : ∀ S₁ ∈ Q₁.powerset,
        (∑ S₂ ∈ brunAdmSubsets blocks caps,
          if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) =
        (if ∀ p ∈ S₁, p ∣ n then (-1 : ℤ) ^ S₁.card else 0) *
          (∑ S₂ ∈ brunAdmSubsets blocks caps,
            if ∀ p ∈ S₂, p ∣ n then (-1 : ℤ) ^ S₂.card else 0) := by
      intro S₁ _
      by_cases h1 : ∀ p ∈ S₁, p ∣ n
      · have hL : (if ∀ p ∈ S₁, p ∣ n then (-1 : ℤ) ^ S₁.card else 0) = (-1 : ℤ) ^ S₁.card := by
          split_ifs; rfl
        rw [hL, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S₂ _ => ?_
        by_cases h2 : ∀ p ∈ S₂, p ∣ n
        · have hR : (if ∀ p ∈ S₂, p ∣ n then (-1 : ℤ) ^ S₂.card else 0) = (-1 : ℤ) ^ S₂.card := by
            split_ifs; rfl
          have hLR : (if (∀ p ∈ S₁, p ∣ n) ∧ ∀ p ∈ S₂, p ∣ n then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) =
              (-1 : ℤ) ^ (S₁.card + S₂.card) := by
            split_ifs with h
            · rfl
            · exact absurd ⟨h1, h2⟩ h
          rw [hR, hLR, pow_add]
        · have hR : (if ∀ p ∈ S₂, p ∣ n then (-1 : ℤ) ^ S₂.card else 0) = 0 := by
            split_ifs; rfl
          have hLR : (if (∀ p ∈ S₁, p ∣ n) ∧ ∀ p ∈ S₂, p ∣ n then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) = 0 := by
            split_ifs with h
            · exact absurd h.2 h2
            · rfl
          rw [hR, hLR, mul_zero]
      · have hL : (if ∀ p ∈ S₁, p ∣ n then (-1 : ℤ) ^ S₁.card else 0) = 0 := by
          split_ifs; rfl
        rw [hL, zero_mul]
        refine Finset.sum_eq_zero fun S₂ _ => ?_
        split_ifs with h12
        · exact absurd h12.1 h1
        · rfl
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
    congr 1
    · rw [← Finset.sum_subset hsub₁]
      · refine Finset.sum_congr rfl fun S₁ hS₁ => ?_
        split_ifs with hdiv
        · rfl
        · exact absurd ((hmem₁ S₁ (hsub₁ hS₁)).mpr hS₁) hdiv
      · intro S₁ hS₁ hnA₁
        split_ifs with hdiv
        · exact absurd ((hmem₁ S₁ hS₁).mp hdiv) hnA₁
        · rfl
    · rw [← Finset.sum_subset hsub₂]
      · refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
        split_ifs with hdiv
        · rfl
        · exact absurd ((hmem₂ S₂ (hsub₂ hS₂)).mpr hS₂) hdiv
      · intro S₂ hS₂ hnA₂
        split_ifs with hdiv
        · exact absurd ((hmem₂ S₂ hS₂).mp hdiv) hnA₂
        · rfl
  have hfull₁ : (∑ S₁ ∈ A₁.powerset, (-1 : ℤ) ^ S₁.card) = if A₁ = ∅ then 1 else 0 := by
    have h := sum_powerset_mul_neg_one A₁ (fun _ => (1 : ℤ))
    simp only [Finset.prod_const_one, mul_one] at h
    rw [h]
    by_cases hA1 : A₁ = ∅
    · simp [hA1]
    · rcases Finset.ne_empty_iff_nonempty.mp hA1 with ⟨p, hp⟩
      simp [hA1, Finset.prod_eq_zero hp]
  have hbrun₂ : (∑ S₂ ∈ A₂.powerset.filter (BrunAdmissible blocks caps), (-1 : ℤ) ^ S₂.card) ≤
      if A₂ = ∅ then 1 else 0 :=
    brun_block_pointwise_lower blocks caps A₂ hdisj hlen hodd hmono (Finset.filter_subset _ _)
  have hcop₁ : (∀ p ∈ Q₁, ¬ p ∣ n) ↔ A₁ = ∅ := by simp [A₁, Finset.filter_eq_empty_iff]
  have hcop₂ : (∀ p ∈ P₂, ¬ p ∣ n) ↔ A₂ = ∅ := by simp [A₂, Finset.filter_eq_empty_iff]
  change (∀ p ∈ brunUnion blocks, ¬ p ∣ n) ↔ A₂ = ∅ at hcop₂
  have hbrun₂' : (∑ S₂ ∈ A₂.powerset.filter (BrunAdmissible blocks caps), (-1 : ℤ) ^ S₂.card) ≤
      if ∀ p ∈ brunUnion blocks, ¬ p ∣ n then 1 else 0 := by
    simpa [hcop₂] using hbrun₂
  rw [hfactor, hfull₁]
  simp only [hcop₁]
  by_cases h1 : A₁ = ∅ <;> by_cases h2 : ∀ p ∈ brunUnion blocks, ¬ p ∣ n <;>
    simp [h1, h2] at hbrun₂' ⊢ <;> linarith

end BrunDecomposition

end BuchstabSwitching
