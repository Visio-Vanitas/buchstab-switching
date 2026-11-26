import BuchstabSwitching.Sieve.AbstractSieve
import BuchstabSwitching.Sieve.BonferroniHybrid
import BuchstabSwitching.Sieve.BonferroniEstimates
import BuchstabSwitching.Sieve.BrunBlockSieve.SetupAndTopK
import BuchstabSwitching.Sieve.BrunBlockSieve.ParityDecomposition
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Combinatorial Brun Block Sieve: Main Term, Modulus Bound, and Omission Monotonicity

Establishes the analytic main-term lower bound (`brun_block_main_term_lb`,
`brun_block_hybrid_main_term`), the Abel-summation modulus upper bound (`brun_block_modbound`),
and divisor-omission monotonicity (`brun_block_omission_mono`,
`brun_block_main_term_omission_mono`).
-/

namespace BuchstabSwitching

section BrunMainTerm

/-- Explicit Brun lower-bound error sum
`E⁻ = ∑ i < r, S(T_i)^(m_i + 1) / ((m_i + 1)! * V(T_i))`. -/
noncomputable def brunErrorBound (blocks : List (Finset ℕ)) (caps : List ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range blocks.length,
    (∑ p ∈ brunPrefix blocks (i + 1), w p) ^ (caps.getD i 0 + 1) /
      ((Nat.factorial (caps.getD i 0 + 1) : ℝ) * V2 w (brunPrefix blocks (i + 1)))

/-- **Brun Analytic Main-Term Lower Bound (`brun_block_main_term_lb`)**:
for nonnegative weights `w p ∈ [0, 1)` on `P₂ = brunUnion blocks`,
`V(P₂) * (1 - E⁻) ≤ ∑ S ∈ brunAdmSubsets, (-1)^|S| ∏_{p ∈ S} w_p`. -/
theorem brun_block_main_term_lb (blocks : List (Finset ℕ)) (caps : List ℕ) (w : ℕ → ℝ)
    (hdisj : blocks.Pairwise Disjoint) (hlen : caps.length = blocks.length)
    (hodd : ∀ m ∈ caps, Odd m)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hw : ∀ p ∈ brunUnion blocks, 0 ≤ w p ∧ w p < 1) :
    V2 w (brunUnion blocks) * (1 - brunErrorBound blocks caps w) ≤
      ∑ S ∈ brunAdmSubsets blocks caps, (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p := by
  let P₂ := brunUnion blocks
  have hfull : ∑ S ∈ P₂.powerset, (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p = V2 w P₂ := by
    rw [sum_powerset_mul_neg_one]
    rfl
  have hsplit : ∑ S ∈ P₂.powerset, (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p =
      ∑ S ∈ brunAdmSubsets blocks caps, (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p +
        ∑ S ∈ brunBadSubsets blocks caps P₂, (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p := by
    symm
    exact Finset.sum_filter_add_sum_filter_not P₂.powerset (BrunAdmissible blocks caps)
      (fun S => (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p)
  have hbad_eq : ∑ S ∈ brunBadSubsets blocks caps P₂, (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p =
      ∑ t ∈ badPrefixes blocks caps P₂,
        (∏ p ∈ t.2.1 ∪ t.2.2, w p) * V2 w (badTail blocks P₂ t.1 t.2.2) := by
    simpa [V2] using
      brun_bad_sum_eq (R := ℝ) blocks caps P₂ w hdisj hlen hodd hmono (Finset.Subset.rfl)
  have hbad_ub_term : ∀ t ∈ badPrefixes blocks caps P₂,
      (∏ p ∈ t.2.1 ∪ t.2.2, w p) * V2 w (badTail blocks P₂ t.1 t.2.2) ≤
        (∏ p ∈ t.2.1 ∪ t.2.2, w p) * (V2 w P₂ / V2 w (brunPrefix blocks (t.1 + 1))) := by
    rintro ⟨i, U₀, U₁⟩ ht
    rcases badPrefixes_mem_iff.mp ht with ⟨hi, hU₀sub, _, _, hU₁sub, _⟩
    have hU₀P : U₀ ⊆ P₂ := hU₀sub.trans Finset.inter_subset_left
    have hU₁P : U₁ ⊆ P₂ := hU₁sub.trans Finset.inter_subset_left
    have hprod_nonneg : 0 ≤ ∏ p ∈ U₀ ∪ U₁, w p := by
      refine Finset.prod_nonneg fun p hp => ?_
      exact (hw p ((Finset.union_subset hU₀P hU₁P) hp)).1
    have hT_sub : brunPrefix blocks (i + 1) ⊆ P₂ := brunPrefix_subset_brunUnion blocks (i + 1)
    have hsdiff_sub : P₂ \ brunPrefix blocks (i + 1) ⊆ badTail blocks P₂ i U₁ :=
      Finset.subset_union_right
    have htail_sub : badTail blocks P₂ i U₁ ⊆ P₂ := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp1 | hp2
      · exact (Finset.mem_inter.mp (Finset.mem_filter.mp hp1).1).1
      · exact (Finset.mem_sdiff.mp hp2).1
    have hV2_anti : V2 w (badTail blocks P₂ i U₁) ≤ V2 w (P₂ \ brunPrefix blocks (i + 1)) :=
      V2_anti hsdiff_sub (fun p hp => hw p (htail_sub hp))
    have hV2_sdiff : V2 w (P₂ \ brunPrefix blocks (i + 1)) =
        V2 w P₂ / V2 w (brunPrefix blocks (i + 1)) := by
      have hmul : V2 w (P₂ \ brunPrefix blocks (i + 1)) * V2 w (brunPrefix blocks (i + 1)) =
          V2 w P₂ := by
        simpa [V2] using Finset.prod_sdiff hT_sub
      have hpos : 0 < V2 w (brunPrefix blocks (i + 1)) :=
        V2_pos fun p hp => (hw p (hT_sub hp)).2
      exact eq_div_of_mul_eq hpos.ne' hmul
    rw [← hV2_sdiff]
    exact mul_le_mul_of_nonneg_left hV2_anti hprod_nonneg
  let fiber : ℕ → Finset (ℕ × Finset ℕ × Finset ℕ) := fun i =>
    ((P₂ ∩ brunPrefix blocks i).powerset.filter
      (fun U₀ => U₀.card ≤ caps.getD i 0 ∧
        ∀ j < i, (U₀ ∩ brunPrefix blocks (j + 1)).card ≤ caps.getD j 0)).biUnion fun U₀ =>
      ((P₂ ∩ blocks.getD i ∅).powersetCard (caps.getD i 0 + 1 - U₀.card)).image
        (fun U₁ => (i, U₀, U₁))
  have hdisj_fib : ((Finset.range blocks.length : Finset ℕ) : Set ℕ).PairwiseDisjoint fiber := by
    intro i _ j _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro ⟨k, U₀, U₁⟩ hk₁ hk₂
    simp only [fiber, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff] at hk₁ hk₂
    rcases hk₁ with ⟨_, _, _, _, rfl, _, _⟩
    rcases hk₂ with ⟨_, _, _, _, hEq, _, _⟩
    exact hne hEq.symm
  have hfib_sum :
      (∑ t ∈ badPrefixes blocks caps P₂,
        (∏ p ∈ t.2.1 ∪ t.2.2, w p) * (V2 w P₂ / V2 w (brunPrefix blocks (t.1 + 1)))) =
      ∑ i ∈ Finset.range blocks.length,
        (V2 w P₂ / V2 w (brunPrefix blocks (i + 1))) *
          ∑ t ∈ fiber i, ∏ p ∈ t.2.1 ∪ t.2.2, w p := by
    change (∑ t ∈ (Finset.range blocks.length).biUnion fiber, _) = _
    rw [Finset.sum_biUnion hdisj_fib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [fiber, Finset.mem_biUnion, Finset.mem_image] at ht
    rcases ht with ⟨_, _, _, _, rfl⟩
    dsimp only
    ring
  have hfib_ub : ∀ i ∈ Finset.range blocks.length,
      ∑ t ∈ fiber i, ∏ p ∈ t.2.1 ∪ t.2.2, w p ≤
        (∑ p ∈ brunPrefix blocks (i + 1), w p) ^ (caps.getD i 0 + 1) /
          (Nat.factorial (caps.getD i 0 + 1) : ℝ) := by
    intro i hi_mem
    have hi : i < blocks.length := Finset.mem_range.mp hi_mem
    let f : ℕ × Finset ℕ × Finset ℕ → Finset ℕ := fun t => t.2.1 ∪ t.2.2
    have hmap_sub : (fiber i).image f ⊆ (brunPrefix blocks (i + 1)).powersetCard (caps.getD i 0 + 1) := by
      intro U hU
      rcases Finset.mem_image.mp hU with ⟨t, ht, rfl⟩
      simp only [fiber, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard, Finset.mem_image] at ht
      rcases ht with ⟨U₀, ⟨hU₀sub, hU₀card, _⟩, U₁, ⟨hU₁sub, hU₁card⟩, rfl⟩
      have hU₀_pref : U₀ ⊆ brunPrefix blocks i := hU₀sub.trans Finset.inter_subset_right
      have hU₁_block : U₁ ⊆ blocks.getD i ∅ := hU₁sub.trans Finset.inter_subset_right
      have hdisj_01 : Disjoint U₀ U₁ := (disjoint_brunPrefix_block hdisj hi).mono hU₀_pref hU₁_block
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · rw [brunPrefix_succ blocks hi]
        exact Finset.union_subset_union hU₀_pref hU₁_block
      · dsimp only [f]
        rw [Finset.card_union_of_disjoint hdisj_01, hU₁card]
        omega
    have hinj : Set.InjOn f (fiber i : Set (ℕ × Finset ℕ × Finset ℕ)) := by
      intro t₁ ht₁ t₂ ht₂ hEq
      simp only [Finset.mem_coe, fiber, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard, Finset.mem_image] at ht₁ ht₂
      rcases ht₁ with ⟨U₀₁, ⟨hU₀₁sub, _⟩, U₁₁, ⟨hU₁₁sub, _⟩, rfl⟩
      rcases ht₂ with ⟨U₀₂, ⟨hU₀₂sub, _⟩, U₁₂, ⟨hU₁₂sub, _⟩, rfl⟩
      dsimp only [f] at hEq
      have hdisj_pb : Disjoint (brunPrefix blocks i) (blocks.getD i ∅) :=
        disjoint_brunPrefix_block hdisj hi
      have hU₀₁_pref : U₀₁ ⊆ brunPrefix blocks i := hU₀₁sub.trans Finset.inter_subset_right
      have hU₀₂_pref : U₀₂ ⊆ brunPrefix blocks i := hU₀₂sub.trans Finset.inter_subset_right
      have hU₁₁_block : U₁₁ ⊆ blocks.getD i ∅ := hU₁₁sub.trans Finset.inter_subset_right
      have hU₁₂_block : U₁₂ ⊆ blocks.getD i ∅ := hU₁₂sub.trans Finset.inter_subset_right
      have hU0_eq : U₀₁ = U₀₂ := by
        have h1 : (U₀₁ ∪ U₁₁) ∩ brunPrefix blocks i = U₀₁ := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hU₀₁_pref,
            (Finset.disjoint_iff_inter_eq_empty.mp (hdisj_pb.symm.mono_left hU₁₁_block)),
            Finset.union_empty]
        have h2 : (U₀₂ ∪ U₁₂) ∩ brunPrefix blocks i = U₀₂ := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hU₀₂_pref,
            (Finset.disjoint_iff_inter_eq_empty.mp (hdisj_pb.symm.mono_left hU₁₂_block)),
            Finset.union_empty]
        rw [← h1, ← h2]
        exact congrArg (· ∩ brunPrefix blocks i) hEq
      have hU1_eq : U₁₁ = U₁₂ := by
        have h1 : (U₀₁ ∪ U₁₁) ∩ blocks.getD i ∅ = U₁₁ := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hU₁₁_block,
            (Finset.disjoint_iff_inter_eq_empty.mp (hdisj_pb.mono_left hU₀₁_pref)),
            Finset.empty_union]
        have h2 : (U₀₂ ∪ U₁₂) ∩ blocks.getD i ∅ = U₁₂ := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hU₁₂_block,
            (Finset.disjoint_iff_inter_eq_empty.mp (hdisj_pb.mono_left hU₀₂_pref)),
            Finset.empty_union]
        rw [← h1, ← h2]
        exact congrArg (· ∩ blocks.getD i ∅) hEq
      simp [hU0_eq, hU1_eq]
    have hsum_img : ∑ t ∈ fiber i, ∏ p ∈ t.2.1 ∪ t.2.2, w p =
        ∑ U ∈ (fiber i).image f, ∏ p ∈ U, w p := by
      rw [Finset.sum_image hinj]
    have hsum_le : ∑ U ∈ (fiber i).image f, ∏ p ∈ U, w p ≤
        elemSym w (brunPrefix blocks (i + 1)) (caps.getD i 0 + 1) := by
      unfold elemSym
      refine Finset.sum_le_sum_of_subset_of_nonneg hmap_sub fun U hU _ => ?_
      refine Finset.prod_nonneg fun p hp => ?_
      exact (hw p (brunPrefix_subset_brunUnion blocks (i + 1)
        ((Finset.mem_powersetCard.mp hU).1 hp))).1
    have helem_le : elemSym w (brunPrefix blocks (i + 1)) (caps.getD i 0 + 1) ≤
        (∑ p ∈ brunPrefix blocks (i + 1), w p) ^ (caps.getD i 0 + 1) /
          (Nat.factorial (caps.getD i 0 + 1) : ℝ) :=
      elemSym_le_pow_div_factorial
        (fun p hp => (hw p (brunPrefix_subset_brunUnion blocks (i + 1) hp)).1)
        (caps.getD i 0 + 1)
    exact hsum_img.symm ▸ hsum_le.trans helem_le
  have hbad_le : ∑ S ∈ brunBadSubsets blocks caps P₂, (-1 : ℝ) ^ S.card * ∏ p ∈ S, w p ≤
      V2 w P₂ * brunErrorBound blocks caps w := by
    rw [hbad_eq]
    calc
      ∑ t ∈ badPrefixes blocks caps P₂,
          (∏ p ∈ t.2.1 ∪ t.2.2, w p) * V2 w (badTail blocks P₂ t.1 t.2.2)
        ≤ ∑ t ∈ badPrefixes blocks caps P₂,
            (∏ p ∈ t.2.1 ∪ t.2.2, w p) * (V2 w P₂ / V2 w (brunPrefix blocks (t.1 + 1))) :=
          Finset.sum_le_sum hbad_ub_term
      _ = ∑ i ∈ Finset.range blocks.length,
            (V2 w P₂ / V2 w (brunPrefix blocks (i + 1))) *
              ∑ t ∈ fiber i, ∏ p ∈ t.2.1 ∪ t.2.2, w p := hfib_sum
      _ ≤ ∑ i ∈ Finset.range blocks.length,
            (V2 w P₂ / V2 w (brunPrefix blocks (i + 1))) *
              ((∑ p ∈ brunPrefix blocks (i + 1), w p) ^ (caps.getD i 0 + 1) /
                (Nat.factorial (caps.getD i 0 + 1) : ℝ)) := by
          refine Finset.sum_le_sum fun i hi_mem => ?_
          have hT_sub : brunPrefix blocks (i + 1) ⊆ P₂ := brunPrefix_subset_brunUnion blocks (i + 1)
          have hV2P : 0 ≤ V2 w P₂ := (V2_pos fun p hp => (hw p hp).2).le
          have hV2T : 0 < V2 w (brunPrefix blocks (i + 1)) :=
            V2_pos fun p hp => (hw p (hT_sub hp)).2
          exact mul_le_mul_of_nonneg_left (hfib_ub i hi_mem) (div_nonneg hV2P hV2T.le)
      _ = V2 w P₂ * brunErrorBound blocks caps w := by
          rw [brunErrorBound, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  linarith

/-- Factorization of the hybrid `Q₁ × P₂` Brun main term. -/
theorem brun_block_hybrid_main_term (Q₁ : Finset ℕ) (blocks : List (Finset ℕ)) (caps : List ℕ)
    (g : ℕ → ℝ)
    (hg : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ brunUnion blocks,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p) :
    (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ brunAdmSubsets blocks caps,
      (-1 : ℝ) ^ (S₁.card + S₂.card) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) =
      V2 g Q₁ * ∑ S₂ ∈ brunAdmSubsets blocks caps, (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p := by
  have hcongr : ∀ S₁ ∈ Q₁.powerset,
      (∑ S₂ ∈ brunAdmSubsets blocks caps,
        (-1 : ℝ) ^ (S₁.card + S₂.card) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) =
      ((-1 : ℝ) ^ S₁.card * ∏ p ∈ S₁, g p) *
        ∑ S₂ ∈ brunAdmSubsets blocks caps, (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p := by
    intro S₁ hS₁
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    rw [hg S₁ (Finset.mem_powerset.mp hS₁) S₂
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1), pow_add]
    ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
  congr 1
  unfold V2
  rw [← sum_powerset_mul_neg_one Q₁ g]

end BrunMainTerm

section ModulusBound

private lemma abel_pow_sum_le_aux (a z m : ℕ → ℕ) :
    ∀ n : ℕ, n ≠ 0 →
      (∀ i < n, 1 ≤ z i) →
      (∀ i j, i ≤ j → j < n → z j ≤ z i) →
      (∀ i < n, ∑ s ∈ Finset.range (i + 1), a s ≤ m i) →
      (∀ i j, i ≤ j → j < n → m i ≤ m j) →
      (∏ i ∈ Finset.range n, (z i) ^ (a i)) *
          (z (n - 1)) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s) ≤
        ∏ i ∈ Finset.range n, (z i) ^ (m i - if i = 0 then 0 else m (i - 1)) := by
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ k ih =>
    intro _ hz_pos hz_anti hc_le hm_mono
    cases k with
    | zero =>
      have h0 : a 0 ≤ m 0 := by simpa using hc_le 0 Nat.zero_lt_one
      simp [Finset.range_one, ← pow_add, Nat.add_sub_cancel' h0]
    | succ k' =>
      let n := k' + 1
      have hn_ne : n ≠ 0 := Nat.succ_ne_zero k'
      have hn_lt : n < n + 1 := Nat.lt_succ_self n
      have hprev := ih hn_ne
        (fun i hi => hz_pos i (lt_trans hi hn_lt))
        (fun i j hij hj => hz_anti i j hij (lt_trans hj hn_lt))
        (fun i hi => hc_le i (lt_trans hi hn_lt))
        (fun i j hij hj => hm_mono i j hij (lt_trans hj hn_lt))
      have hz_le : z n ≤ z (n - 1) := hz_anti (n - 1) n (Nat.sub_le n 1) hn_lt
      have hc_prev : ∑ s ∈ Finset.range n, a s ≤ m (n - 1) := by
        simpa [n, Nat.add_sub_cancel] using hc_le (n - 1) (lt_trans (Nat.sub_lt (Nat.succ_pos k') Nat.zero_lt_one) hn_lt)
      have hm_le : m (n - 1) ≤ m n := hm_mono (n - 1) n (Nat.sub_le n 1) hn_lt
      have hc_curr : ∑ s ∈ Finset.range (n + 1), a s ≤ m n := hc_le n hn_lt
      have hsum_split : ∑ s ∈ Finset.range (n + 1), a s =
          (∑ s ∈ Finset.range n, a s) + a n := Finset.sum_range_succ a n
      have hexp_eq : a n + (m n - ∑ s ∈ Finset.range (n + 1), a s) =
          (m (n - 1) - ∑ s ∈ Finset.range n, a s) + (m n - m (n - 1)) := by
        rw [hsum_split]
        omega
      have hpow_le : (z n) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s) ≤
          (z (n - 1)) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s) :=
        Nat.pow_le_pow_left hz_le _
      have hstep :
          (∏ i ∈ Finset.range (n + 1), (z i) ^ (a i)) *
            (z n) ^ (m n - ∑ s ∈ Finset.range (n + 1), a s) =
          (∏ i ∈ Finset.range n, (z i) ^ (a i)) *
            ((z n) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s) * (z n) ^ (m n - m (n - 1))) := by
        rw [Finset.prod_range_succ, mul_assoc, ← pow_add, hexp_eq, pow_add]
      have hlast :
          (∏ i ∈ Finset.range n, (z i) ^ (a i)) *
            ((z n) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s) * (z n) ^ (m n - m (n - 1))) ≤
          (∏ i ∈ Finset.range n, (z i) ^ (m i - if i = 0 then 0 else m (i - 1))) *
            (z n) ^ (m n - m (n - 1)) := by
        calc
          (∏ i ∈ Finset.range n, (z i) ^ (a i)) *
              ((z n) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s) * (z n) ^ (m n - m (n - 1)))
            ≤ (∏ i ∈ Finset.range n, (z i) ^ (a i)) *
                ((z (n - 1)) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s) * (z n) ^ (m n - m (n - 1))) := by
                gcongr
          _ = ((∏ i ∈ Finset.range n, (z i) ^ (a i)) *
                (z (n - 1)) ^ (m (n - 1) - ∑ s ∈ Finset.range n, a s)) * (z n) ^ (m n - m (n - 1)) := by
                ring
          _ ≤ (∏ i ∈ Finset.range n, (z i) ^ (m i - if i = 0 then 0 else m (i - 1))) *
                (z n) ^ (m n - m (n - 1)) := by
                gcongr
      have hn_ne0 : n ≠ 0 := hn_ne
      rw [← hstep] at hlast
      simpa [n, Finset.prod_range_succ, hn_ne0, Nat.add_sub_cancel] using hlast

/-- **Brun Modulus Bound (`brun_block_modbound`)**:
if `S` is Brun-admissible for `(blocks, caps)` and every `p ∈ B_i` satisfies `p ≤ z i` with
descending positive upper bounds `z 0 ≥ z 1 ≥ ... ≥ 1` and monotone caps `m_0 ≤ m_1 ≤ ...`,
then `∏ p ∈ S, p ≤ ∏ i < r, (z i) ^ (m_i - m_{i-1})` (with `m_{-1} = 0`). -/
theorem brun_block_modbound (blocks : List (Finset ℕ)) (caps : List ℕ) (z : ℕ → ℕ)
    (S : Finset ℕ) (hdisj : blocks.Pairwise Disjoint) (hlen : caps.length = blocks.length)
    (hz_pos : ∀ i < blocks.length, 1 ≤ z i)
    (hz_anti : ∀ i j : ℕ, i ≤ j → j < blocks.length → z j ≤ z i)
    (hmono : ∀ i j : ℕ, i ≤ j → j < caps.length → caps.getD i 0 ≤ caps.getD j 0)
    (hblock_ub : ∀ i < blocks.length, ∀ p ∈ blocks.getD i ∅, p ≤ z i)
    (hS : BrunAdmissible blocks caps S) :
    ∏ p ∈ S, p ≤
      ∏ i ∈ Finset.range blocks.length,
        (z i) ^ (caps.getD i 0 - if i = 0 then 0 else caps.getD (i - 1) 0) := by
  have hS_decomp : S = (Finset.range blocks.length).biUnion (fun i => S ∩ blocks.getD i ∅) := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_inter]
    constructor
    · intro hpS
      rcases mem_brunUnion_iff.mp (hS.1 hpS) with ⟨i, hi, hpB⟩
      exact ⟨i, hi, hpS, hpB⟩
    · rintro ⟨_, _, hpS, _⟩
      exact hpS
  have hdisj_S : ((Finset.range blocks.length : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i => S ∩ blocks.getD i ∅) := by
    intro i hi j hj hne
    have hi' : i < blocks.length := Finset.mem_range.mp hi
    have hj' : j < blocks.length := Finset.mem_range.mp hj
    have hbij : Disjoint (blocks.getD i ∅) (blocks.getD j ∅) := by
      have hd := (List.pairwise_iff_getElem.mp hdisj)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simpa [List.getD_eq_getElem?_getD, hi', hj'] using hd i j hi' hj' hlt
      · simpa [List.getD_eq_getElem?_getD, hi', hj'] using (hd j i hj' hi' hlt).symm
    exact hbij.mono Finset.inter_subset_right Finset.inter_subset_right
  have hprod_eq : ∏ p ∈ S, p =
      ∏ i ∈ Finset.range blocks.length, ∏ p ∈ S ∩ blocks.getD i ∅, p := by
    conv_lhs => rw [hS_decomp]
    exact Finset.prod_biUnion hdisj_S
  have hprod_ub : ∏ i ∈ Finset.range blocks.length, ∏ p ∈ S ∩ blocks.getD i ∅, p ≤
      ∏ i ∈ Finset.range blocks.length, (z i) ^ (S ∩ blocks.getD i ∅).card := by
    refine Finset.prod_le_prod fun i hi => ?_
    have hi' : i < blocks.length := Finset.mem_range.mp hi
    calc
      ∏ p ∈ S ∩ blocks.getD i ∅, p ≤ ∏ _p ∈ S ∩ blocks.getD i ∅, z i :=
        Finset.prod_le_prod fun p hp => hblock_ub i hi' p (Finset.mem_inter.mp hp).2
      _ = (z i) ^ (S ∩ blocks.getD i ∅).card := by simp
  rw [hprod_eq]
  refine hprod_ub.trans ?_
  by_cases hlen0 : blocks.length = 0
  · simp [hlen0]
  · have haux := abel_pow_sum_le_aux (fun i => (S ∩ blocks.getD i ∅).card) z
      (fun i => caps.getD i 0) blocks.length hlen0 hz_pos hz_anti
      (fun i hi => by
        rw [← brunPrefix_inter_card_eq_sum hdisj S hi]
        exact hS.2 i hi)
      (fun i j hij hj => hmono i j hij (hlen ▸ hj))
    have hpow_pos : 1 ≤ (z (blocks.length - 1)) ^
        (caps.getD (blocks.length - 1) 0 -
          ∑ s ∈ Finset.range blocks.length, (S ∩ blocks.getD s ∅).card) :=
      Nat.one_le_pow _ _ (hz_pos (blocks.length - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hlen0) Nat.zero_lt_one))
    have hle_mul : ∏ i ∈ Finset.range blocks.length, (z i) ^ (S ∩ blocks.getD i ∅).card ≤
        (∏ i ∈ Finset.range blocks.length, (z i) ^ (S ∩ blocks.getD i ∅).card) *
          (z (blocks.length - 1)) ^ (caps.getD (blocks.length - 1) 0 -
            ∑ s ∈ Finset.range blocks.length, (S ∩ blocks.getD s ∅).card) :=
      Nat.le_mul_of_pos_right _ hpow_pos
    exact hle_mul.trans haux

end ModulusBound

section OmissionMonotonicity

/-- **Brun Error Omission Monotonicity (`brun_block_omission_mono`)**:
omitting elements outside `P'` (replacing `blocks` by `restrictBlocks blocks P'`) never increases
`brunErrorBound` and never decreases `V2`. -/
theorem brun_block_omission_mono (blocks : List (Finset ℕ)) (caps : List ℕ) (P' : Finset ℕ)
    (w : ℕ → ℝ) (hw : ∀ p ∈ brunUnion blocks, 0 ≤ w p ∧ w p < 1) :
    brunErrorBound (restrictBlocks blocks P') caps w ≤ brunErrorBound blocks caps w ∧
      V2 w (brunUnion blocks) ≤ V2 w (brunUnion (restrictBlocks blocks P')) := by
  constructor
  · unfold brunErrorBound
    rw [restrictBlocks_length]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [brunPrefix_restrictBlocks]
    let T := brunPrefix blocks (i + 1)
    have hT_sub : T ⊆ brunUnion blocks := brunPrefix_subset_brunUnion blocks (i + 1)
    have hT'_sub : T ∩ P' ⊆ T := Finset.inter_subset_left
    have hS_nonneg : 0 ≤ ∑ p ∈ T ∩ P', w p :=
      Finset.sum_nonneg fun p hp => (hw p (hT_sub (hT'_sub hp))).1
    have hS_le : ∑ p ∈ T ∩ P', w p ≤ ∑ p ∈ T, w p :=
      Finset.sum_le_sum_of_subset_of_nonneg hT'_sub fun p hp _ => (hw p (hT_sub hp)).1
    have hnum_le : (∑ p ∈ T ∩ P', w p) ^ (caps.getD i 0 + 1) ≤
        (∑ p ∈ T, w p) ^ (caps.getD i 0 + 1) :=
      pow_le_pow_left₀ hS_nonneg hS_le _
    have hV2_pos : 0 < V2 w T := V2_pos fun p hp => (hw p (hT_sub hp)).2
    have hV2_anti : V2 w T ≤ V2 w (T ∩ P') :=
      V2_anti hT'_sub fun p hp => hw p (hT_sub hp)
    have hfact_pos : (0 : ℝ) < (Nat.factorial (caps.getD i 0 + 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hden_pos : 0 < (Nat.factorial (caps.getD i 0 + 1) : ℝ) * V2 w T :=
      mul_pos hfact_pos hV2_pos
    have hden_le : (Nat.factorial (caps.getD i 0 + 1) : ℝ) * V2 w T ≤
        (Nat.factorial (caps.getD i 0 + 1) : ℝ) * V2 w (T ∩ P') :=
      mul_le_mul_of_nonneg_left hV2_anti hfact_pos.le
    exact div_le_div₀ (pow_nonneg (hS_nonneg.trans hS_le) _) hnum_le hden_pos hden_le
  · rw [brunUnion_restrictBlocks]
    exact V2_anti Finset.inter_subset_left hw

theorem brun_block_main_term_omission_mono (blocks : List (Finset ℕ)) (caps : List ℕ)
    (P' : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ brunUnion blocks, 0 ≤ w p ∧ w p < 1)
    (herr : brunErrorBound blocks caps w ≤ 1) :
    V2 w (brunUnion blocks) * (1 - brunErrorBound blocks caps w) ≤
      V2 w (brunUnion (restrictBlocks blocks P')) *
        (1 - brunErrorBound (restrictBlocks blocks P') caps w) := by
  have hmono := brun_block_omission_mono blocks caps P' w hw
  have hV2_nonneg : 0 ≤ V2 w (brunUnion blocks) := (V2_pos fun p hp => (hw p hp).2).le
  have h1_nonneg : 0 ≤ 1 - brunErrorBound blocks caps w := sub_nonneg.mpr herr
  have h2_le : 1 - brunErrorBound blocks caps w ≤
      1 - brunErrorBound (restrictBlocks blocks P') caps w := by linarith [hmono.1]
  exact mul_le_mul hmono.2 h2_le h1_nonneg ((hV2_nonneg).trans hmono.2)

end OmissionMonotonicity

end BuchstabSwitching
