import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Hybrid `Q₁ × P₂` Bonferroni Upper and Lower Sieve Identities

Proves the pointwise and summed integer Bonferroni inequalities with exact inclusion-exclusion
over the small prime block `Q₁` and truncated alternating sum (`2*m + 1` lower / `2*m` upper)
over the medium prime block `P₂`, together with disjoint multiplicative product factoring.
-/

namespace BuchstabSwitching

/-- Pointwise Bonferroni hybrid sieve inequality for disjoint prime sets `Q₁` and `P₂`. -/
theorem bonferroni_hybrid_pointwise (Q₁ P₂ : Finset ℕ) (n m : ℕ) (_hdisj : Disjoint Q₁ P₂) :
    let dividesAll : Finset ℕ → ℕ → Prop := fun S k => ∀ p ∈ S, p ∣ k
    let coprimeTo : Finset ℕ → ℕ → Prop := fun S k => ∀ p ∈ S, ¬ p ∣ k
    (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m + 1),
      if dividesAll S₁ n ∧ dividesAll S₂ n then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) ≤
        (if coprimeTo Q₁ n ∧ coprimeTo P₂ n then (1 : ℤ) else 0) ∧
    (if coprimeTo Q₁ n ∧ coprimeTo P₂ n then (1 : ℤ) else 0) ≤
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m),
        if dividesAll S₁ n ∧ dividesAll S₂ n then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) := by
  dsimp only
  set A₁ : Finset ℕ := Q₁.filter (fun p => p ∣ n)
  set A₂ : Finset ℕ := P₂.filter (fun p => p ∣ n)
  have hsub₁ : A₁.powerset ⊆ Q₁.powerset := Finset.powerset_mono.mpr (Finset.filter_subset _ _)
  have hsub₂ : A₂.powerset ⊆ P₂.powerset := Finset.powerset_mono.mpr (Finset.filter_subset _ _)
  have hmem₁ : ∀ S₁ ∈ Q₁.powerset, (∀ p ∈ S₁, p ∣ n) ↔ S₁ ∈ A₁.powerset := by
    intro S₁ hS₁
    rw [Finset.mem_powerset] at hS₁ ⊢
    simp only [A₁, Finset.subset_iff, Finset.mem_filter]
    exact ⟨fun h p hp => ⟨hS₁ hp, h p hp⟩, fun h p hp => (h hp).2⟩
  have hmem₂ : ∀ S₂ ∈ P₂.powerset, (∀ p ∈ S₂, p ∣ n) ↔ S₂ ∈ A₂.powerset := by
    intro S₂ hS₂
    rw [Finset.mem_powerset] at hS₂ ⊢
    simp only [A₂, Finset.subset_iff, Finset.mem_filter]
    exact ⟨fun h p hp => ⟨hS₂ hp, h p hp⟩, fun h p hp => (h hp).2⟩
  have hfactor : ∀ k : ℕ,
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) =
      (∑ S₁ ∈ A₁.powerset, (-1 : ℤ) ^ S₁.card) *
        (∑ S₂ ∈ A₂.powerset.filter (fun S₂ => S₂.card ≤ k), (-1 : ℤ) ^ S₂.card) := by
    intro k
    have h1 : ∀ S₁ ∈ Q₁.powerset,
        (∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
          if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0) =
        (if ∀ p ∈ S₁, p ∣ n then (-1 : ℤ) ^ S₁.card else 0) *
          (∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
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
        split_ifs with h
        · exact absurd h.1 h1
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
    · have hsubk : A₂.powerset.filter (fun S₂ => S₂.card ≤ k) ⊆
          P₂.powerset.filter (fun S₂ => S₂.card ≤ k) :=
        Finset.filter_subset_filter _ hsub₂
      rw [← Finset.sum_subset hsubk]
      · refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
        have hS₂P := (Finset.mem_filter.mp (hsubk hS₂)).1
        have hS₂A := (Finset.mem_filter.mp hS₂).1
        split_ifs with hdiv
        · rfl
        · exact absurd ((hmem₂ S₂ hS₂P).mpr hS₂A) hdiv
      · intro S₂ hS₂ hnA₂
        split_ifs with hdiv
        · have hS₂' := Finset.mem_filter.mp hS₂
          exact absurd (Finset.mem_filter.mpr ⟨(hmem₂ S₂ hS₂'.1).mp hdiv, hS₂'.2⟩) hnA₂
        · rfl
  have hfull : ∀ A : Finset ℕ,
      (∑ S ∈ A.powerset, (-1 : ℤ) ^ S.card) = if A = ∅ then 1 else 0 := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.powerset_insert, Finset.sum_union]
      · have himg : ∑ S ∈ s.powerset.image (insert a), (-1 : ℤ) ^ S.card =
            - ∑ S ∈ s.powerset, (-1 : ℤ) ^ S.card := by
          rw [Finset.sum_image]
          · rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun t ht => ?_
            have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
            rw [Finset.card_insert_of_notMem hat, pow_succ]
            ring
          · intro x hx y hy hxy
            have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
            have hay : a ∉ y := fun h => ha (Finset.mem_powerset.mp hy h)
            ext z
            have hz := Finset.ext_iff.mp hxy z
            simp only [Finset.mem_insert] at hz
            constructor
            · intro hzx
              rcases hz.mp (Or.inr hzx) with rfl | hzy
              · exact absurd hzx hax
              · exact hzy
            · intro hzy
              rcases hz.mpr (Or.inr hzy) with rfl | hzx
              · exact absurd hzy hay
              · exact hzx
        rw [himg, add_neg_cancel]
        simp [(Finset.insert_nonempty a s).ne_empty]
      · rw [Finset.disjoint_left]
        intro t ht hti
        rcases Finset.mem_image.mp hti with ⟨u, _, rfl⟩
        exact ha (Finset.mem_powerset.mp ht (Finset.mem_insert_self a u))
  have htrunc : ∀ (A : Finset ℕ) (k : ℕ),
      (∑ S ∈ A.powerset.filter (fun S => S.card ≤ k), (-1 : ℤ) ^ S.card) =
        if A = ∅ then 1 else (-1 : ℤ) ^ k * ((A.card - 1).choose k : ℤ) := by
    intro A k
    have hfib : ∑ S ∈ A.powerset.filter (fun S => S.card ≤ k), (-1 : ℤ) ^ S.card =
        ∑ j ∈ Finset.range (k + 1),
          ∑ S ∈ (A.powerset.filter (fun S => S.card ≤ k)).filter (fun S => S.card = j),
            (-1 : ℤ) ^ S.card := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S hS
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2)
    rw [hfib]
    have hbin : ∑ j ∈ Finset.range (k + 1),
          ∑ S ∈ (A.powerset.filter (fun S => S.card ≤ k)).filter (fun S => S.card = j),
            (-1 : ℤ) ^ S.card =
        ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (A.card.choose j : ℤ) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hfilt : (A.powerset.filter (fun S => S.card ≤ k)).filter (fun S => S.card = j) =
          A.powersetCard j := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hSA, _⟩, rfl⟩
          exact ⟨hSA, rfl⟩
        · rintro ⟨hSA, rfl⟩
          exact ⟨⟨hSA, hjk⟩, rfl⟩
      rw [hfilt]
      have hconst : ∑ S ∈ A.powersetCard j, (-1 : ℤ) ^ S.card =
          ∑ _S ∈ A.powersetCard j, (-1 : ℤ) ^ j := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [(Finset.mem_powersetCard.mp hS).2]
      rw [hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
    rw [hbin]
    have hpascal : ∀ (N k : ℕ),
        (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (N.choose j : ℤ)) =
          if N = 0 then 1 else (-1 : ℤ) ^ k * ((N - 1).choose k : ℤ) := by
      intro N
      cases N with
      | zero =>
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          simp
      | succ N =>
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Nat.add_sub_cancel]
          rw [Nat.choose_succ_succ N k]
          push_cast
          rw [pow_succ (-1 : ℤ) k]
          ring
    rw [hpascal A.card k]
    by_cases hA : A = ∅
    · subst hA; simp
    · have hne : A.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.ne_empty_iff_nonempty.mp hA)
      simp [hA, hne]
  have hcop₁ : (∀ p ∈ Q₁, ¬ p ∣ n) ↔ A₁ = ∅ := by
    simp [A₁, Finset.filter_eq_empty_iff]
  have hcop₂ : (∀ p ∈ P₂, ¬ p ∣ n) ↔ A₂ = ∅ := by
    simp [A₂, Finset.filter_eq_empty_iff]
  constructor
  · rw [hfactor (2 * m + 1), hfull A₁, htrunc A₂ (2 * m + 1)]
    simp only [hcop₁, hcop₂]
    by_cases h1 : A₁ = ∅ <;> by_cases h2 : A₂ = ∅ <;> simp [h1, h2, pow_add, pow_mul]
  · rw [hfactor (2 * m), hfull A₁, htrunc A₂ (2 * m)]
    simp only [hcop₁, hcop₂]
    by_cases h1 : A₁ = ∅ <;> by_cases h2 : A₂ = ∅ <;> simp [h1, h2, pow_mul]

/-- Summed Bonferroni hybrid sieve bounds over a finite sequence `A`. -/
theorem bonferroni_hybrid_sum (A Q₁ P₂ : Finset ℕ) (m : ℕ) (hdisj : Disjoint Q₁ P₂) :
    (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m + 1),
      (-1 : ℤ) ^ (S₁.card + S₂.card) *
        ((A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n))).card : ℤ)) ≤
      ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℤ) ∧
    ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℤ) ≤
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m),
        (-1 : ℤ) ^ (S₁.card + S₂.card) *
          ((A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n))).card : ℤ)) := by
  have hexpand : ∀ k : ℕ,
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        (-1 : ℤ) ^ (S₁.card + S₂.card) *
          ((A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n))).card : ℤ)) =
      ∑ n ∈ A, ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0 := by
    intro k
    trans ∑ S₁ ∈ Q₁.powerset, ∑ n ∈ A, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        if (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) then (-1 : ℤ) ^ (S₁.card + S₂.card) else 0
    · refine Finset.sum_congr rfl fun S₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S₂ _ => ?_
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    · exact Finset.sum_comm
  have hcount : ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℤ) =
      ∑ n ∈ A, if (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n) then (1 : ℤ) else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rfl
  rw [hexpand (2 * m + 1), hexpand (2 * m), hcount]
  constructor
  · exact Finset.sum_le_sum fun n _ => (bonferroni_hybrid_pointwise Q₁ P₂ n m hdisj).1
  · exact Finset.sum_le_sum fun n _ => (bonferroni_hybrid_pointwise Q₁ P₂ n m hdisj).2

end BuchstabSwitching
