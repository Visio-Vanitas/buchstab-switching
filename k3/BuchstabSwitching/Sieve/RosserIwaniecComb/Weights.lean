import Mathlib.Data.Finset.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Combinatorial Rosser–Iwaniec Sieve Weights (`β = 2`)

Formalizes the combinatorial Rosser–Iwaniec upper and lower sieve weights (`DPlus`, `DMinus`)
for `β = 2` (linear-sieve / switching-compatible exponent `3` in `p_1 ⋯ p_m · p_m^2 < D`)
and proves their product bounds `DPlus_prod_lt` and `DMinus_prod_lt`.
-/

namespace BuchstabSwitching

noncomputable section

/-! ### 1. Combinatorial Rosser–Iwaniec Weights (`β = 2`) -/

/-- Elements of `S` listed in descending order. -/
def descPrimes (S : Finset ℕ) : List ℕ := S.sort (· ≥ ·)

/-- Recursive Rosser–Iwaniec (`β = 2`) truncation predicate on a descending list of integers.
When `parity = true`, the current head element `p` (at 0-based index `i` with `acc = ∏_{j < i} p_j`)
must satisfy `acc * p^3 < D` before flipping parity for the tail. -/
def riCond (parity : Bool) (D : ℝ) : ℝ → List ℕ → Prop
  | _, [] => True
  | acc, p :: L =>
      if parity then acc * (p : ℝ) ^ 3 < D ∧ riCond false D (acc * (p : ℝ)) L
      else riCond true D (acc * (p : ℝ)) L

/-- Rosser–Iwaniec upper-bound sieve support `D⁺(D)` (`β = 2`):
at every 0-based even index `i` (`i = 0, 2, 4, ...`), `(∏_{j ≤ i} p_j) * p_i^2 < D`. -/
def DPlus (D : ℝ) (S : Finset ℕ) : Prop := riCond true D 1 (descPrimes S)

/-- Rosser–Iwaniec lower-bound sieve support `D⁻(D)` (`β = 2`):
at every 0-based odd index `i` (`i = 1, 3, 5, ...`), `(∏_{j ≤ i} p_j) * p_i^2 < D`. -/
def DMinus (D : ℝ) (S : Finset ℕ) : Prop := riCond false D 1 (descPrimes S)

noncomputable instance instDecidablePredDPlus (D : ℝ) : DecidablePred (DPlus D) :=
  Classical.decPred _

noncomputable instance instDecidablePredDMinus (D : ℝ) : DecidablePred (DMinus D) :=
  Classical.decPred _

lemma prod_range_cons_getD (p : ℕ) (L : List ℕ) (m : ℕ) :
    (∏ j ∈ Finset.range (m + 1), ((p :: L).getD j 0 : ℝ)) =
      (p : ℝ) * ∏ j ∈ Finset.range m, (L.getD j 0 : ℝ) := by
  rw [Finset.prod_range_succ']
  simp [mul_comm]

lemma riCond_iff_forall (b : Bool) (D acc : ℝ) (L : List ℕ) :
    riCond b D acc L ↔
      ∀ (i : ℕ), i < L.length →
        (if b then i % 2 = 0 else i % 2 = 1) →
          acc * (∏ j ∈ Finset.range (i + 1), (L.getD j 0 : ℝ)) * (L.getD i 0 : ℝ) ^ 2 < D := by
  induction L generalizing b acc with
  | nil =>
      simp [riCond]
  | cons p L ih =>
      constructor
      · intro h i hi hpar
        cases i with
        | zero =>
            cases b
            · simp at hpar
            · simp only [riCond, ↓reduceIte] at h
              simpa [Finset.prod_range_one, List.getD_cons_zero, mul_assoc, pow_succ] using h.1
        | succ i' =>
            have hi' : i' < L.length := Nat.lt_of_succ_lt_succ hi
            have htail : riCond (!b) D (acc * (p : ℝ)) L := by
              cases b <;> simp only [riCond, ↓reduceIte] at h
              · exact h
              · exact h.2
            have hrec := (ih (!b) (acc * (p : ℝ))).mp htail i' hi'
            have hpar' : if (!b) then i' % 2 = 0 else i' % 2 = 1 := by
              cases b <;> simp at hpar ⊢ <;> omega
            have hlt := hrec hpar'
            rw [prod_range_cons_getD, List.getD_cons_succ]
            simpa [mul_assoc] using hlt
      · intro h
        cases b
        · simp only [riCond]
          refine (ih true (acc * (p : ℝ))).mpr fun i' hi' hpar' => ?_
          have hi : i' + 1 < (p :: L).length := Nat.succ_lt_succ hi'
          have hpar : (i' + 1) % 2 = 1 := by simp at hpar'; omega
          have hlt := h (i' + 1) hi hpar
          rw [prod_range_cons_getD, List.getD_cons_succ] at hlt
          simpa [mul_assoc] using hlt
        · simp only [riCond, ↓reduceIte]
          constructor
          · have h0 := h 0 (by simp) (by simp)
            simpa [Finset.prod_range_one, List.getD_cons_zero, mul_assoc, pow_succ] using h0
          · refine (ih false (acc * (p : ℝ))).mpr fun i' hi' hpar' => ?_
            have hi : i' + 1 < (p :: L).length := Nat.succ_lt_succ hi'
            have hpar : (i' + 1) % 2 = 0 := by simp at hpar'; omega
            have hlt := h (i' + 1) hi hpar
            rw [prod_range_cons_getD, List.getD_cons_succ] at hlt
            simpa [mul_assoc] using hlt

lemma DPlus_iff_forall (D : ℝ) (S : Finset ℕ) :
    DPlus D S ↔
      ∀ (i : ℕ), i < (descPrimes S).length → i % 2 = 0 →
        (∏ j ∈ Finset.range (i + 1), ((descPrimes S).getD j 0 : ℝ)) *
          ((descPrimes S).getD i 0 : ℝ) ^ 2 < D := by
  simpa [DPlus] using riCond_iff_forall true D 1 (descPrimes S)

lemma DMinus_iff_forall (D : ℝ) (S : Finset ℕ) :
    DMinus D S ↔
      ∀ (i : ℕ), i < (descPrimes S).length → i % 2 = 1 →
        (∏ j ∈ Finset.range (i + 1), ((descPrimes S).getD j 0 : ℝ)) *
          ((descPrimes S).getD i 0 : ℝ) ^ 2 < D := by
  simpa [DMinus] using riCond_iff_forall false D 1 (descPrimes S)

lemma riCond_mul (b : Bool) (D c acc : ℝ) (hc : 0 < c) (L : List ℕ) :
    riCond b D (c * acc) L ↔ riCond b (D / c) acc L := by
  induction L generalizing b acc with
  | nil => simp [riCond]
  | cons p L ih =>
      cases b <;> simp only [riCond, ↓reduceIte]
      · simpa [mul_assoc] using ih true (acc * (p : ℝ))
      · constructor
        · rintro ⟨h1, h2⟩
          refine ⟨(lt_div_iff₀ hc).mpr ?_, ?_⟩
          · linarith [show c * acc * (p : ℝ) ^ 3 = acc * (p : ℝ) ^ 3 * c by ring]
          · exact (ih false (acc * (p : ℝ))).mp (by simpa [mul_assoc] using h2)
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · have h1' := (lt_div_iff₀ hc).mp h1
            linarith [show c * acc * (p : ℝ) ^ 3 = acc * (p : ℝ) ^ 3 * c by ring]
          · simpa [mul_assoc] using (ih false (acc * (p : ℝ))).mpr h2

lemma descPrimes_empty : descPrimes ∅ = [] := by
  simp [descPrimes]

lemma descPrimes_singleton (p : ℕ) : descPrimes {p} = [p] := by
  simp [descPrimes]

lemma descPrimes_insert {p : ℕ} {S : Finset ℕ} (hp_gt : ∀ q ∈ S, q < p) :
    descPrimes (insert p S) = p :: descPrimes S := by
  have hp_ge : ∀ q ∈ S, p ≥ q := fun q hq => le_of_lt (hp_gt q hq)
  have hp_nmem : p ∉ S := fun h => Nat.lt_irrefl p (hp_gt p h)
  exact Finset.sort_insert (· ≥ ·) hp_ge hp_nmem

lemma DPlus_empty (D : ℝ) : DPlus D ∅ := by
  simp [DPlus, descPrimes, riCond]

lemma DMinus_empty (D : ℝ) : DMinus D ∅ := by
  simp [DMinus, descPrimes, riCond]

lemma DPlus_insert {D : ℝ} {p : ℕ} {S : Finset ℕ}
    (hp_pos : 0 < p) (hp_gt : ∀ q ∈ S, q < p) :
    DPlus D (insert p S) ↔ (p : ℝ) ^ 3 < D ∧ DMinus (D / (p : ℝ)) S := by
  have hp_real : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
  rw [DPlus, descPrimes_insert hp_gt, riCond]
  simp only [↓reduceIte, one_mul]
  have hsc := riCond_mul false D (p : ℝ) 1 hp_real (descPrimes S)
  simpa [mul_one, DMinus] using and_congr_right fun _ => hsc

lemma DMinus_insert {D : ℝ} {p : ℕ} {S : Finset ℕ}
    (hp_pos : 0 < p) (hp_gt : ∀ q ∈ S, q < p) :
    DMinus D (insert p S) ↔ DPlus (D / (p : ℝ)) S := by
  have hp_real : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
  rw [DMinus, descPrimes_insert hp_gt, riCond]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  have hsc := riCond_mul true D (p : ℝ) 1 hp_real (descPrimes S)
  simpa [mul_one, DPlus] using hsc

private lemma list_prod_range_eq_map_prod (L : List ℕ) :
    (∏ j ∈ Finset.range L.length, (L.getD j 0 : ℝ)) = (L.map (fun p : ℕ => (p : ℝ))).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.length_cons, prod_range_cons_getD, ih]
      simp

private lemma prod_descPrimes_range (S : Finset ℕ) :
    (∏ j ∈ Finset.range (descPrimes S).length, ((descPrimes S).getD j 0 : ℝ)) =
      ∏ p ∈ S, (p : ℝ) := by
  rw [list_prod_range_eq_map_prod]
  have hperm : List.Perm (descPrimes S) S.toList := Finset.sort_perm_toList S (· ≥ ·)
  rw [(hperm.map (fun p : ℕ => (p : ℝ))).prod_eq]
  change (S.toList.map (fun p : ℕ => (p : ℝ))).prod = (S.val.map (fun p : ℕ => (p : ℝ))).prod
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]

lemma getD_eq_getElem {L : List ℕ} {k : ℕ} (hk : k < L.length) :
    L.getD k 0 = L[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

private lemma descPrimes_ge_last_two {S : Finset ℕ} (hcard : 2 ≤ (descPrimes S).length) :
    (descPrimes S).getD ((descPrimes S).length - 1) 0 ≤
      (descPrimes S).getD ((descPrimes S).length - 2) 0 := by
  have hpair : (descPrimes S).Pairwise (· ≥ ·) := Finset.pairwise_sort S (· ≥ ·)
  have h1 : (descPrimes S).length - 1 < (descPrimes S).length := by omega
  have h2 : (descPrimes S).length - 2 < (descPrimes S).length := by omega
  rw [getD_eq_getElem h1, getD_eq_getElem h2]
  exact hpair.rel_get_of_lt (by omega : (descPrimes S).length - 2 < (descPrimes S).length - 1)

private lemma prod_lt_of_prefix_bound {D : ℝ} {S : Finset ℕ}
    (_hD : 1 < D) (hpos : ∀ p ∈ S, 1 ≤ p)
    (hi_bound : ∃ i < (descPrimes S).length,
      (descPrimes S).length - 2 ≤ i ∧
      (∏ j ∈ Finset.range (i + 1), ((descPrimes S).getD j 0 : ℝ)) *
        ((descPrimes S).getD i 0 : ℝ) ^ 2 < D) :
    (∏ p ∈ S, (p : ℝ)) < D := by
  rcases hi_bound with ⟨i, hi_lt, hi_ge, hlt⟩
  set L := descPrimes S
  have hL_ge1 : ∀ k (hk : k < L.length), (1 : ℝ) ≤ (L.getD k 0 : ℝ) := by
    intro k hk
    rw [getD_eq_getElem hk]
    have hk_mem : L[k] ∈ S := (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hk)
    exact Nat.one_le_cast.mpr (hpos L[k] hk_mem)
  have hLi_ge1 : (1 : ℝ) ≤ (L.getD i 0 : ℝ) := hL_ge1 i hi_lt
  have hprod_nonneg : ∀ m : ℕ, 0 ≤ ∏ j ∈ Finset.range m, (L.getD j 0 : ℝ) := by
    intro m
    exact Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
  rw [← prod_descPrimes_range S]
  by_cases hlast : i = L.length - 1
  · subst hlast
    have hi1 : L.length - 1 + 1 = L.length := Nat.sub_add_cancel (by omega)
    rw [hi1] at hlt
    have hsq : (1 : ℝ) ≤ (L.getD (L.length - 1) 0 : ℝ) ^ 2 := by nlinarith
    have hle : (∏ j ∈ Finset.range L.length, (L.getD j 0 : ℝ)) ≤
        (∏ j ∈ Finset.range L.length, (L.getD j 0 : ℝ)) *
          (L.getD (L.length - 1) 0 : ℝ) ^ 2 :=
      le_mul_of_one_le_right (hprod_nonneg L.length) hsq
    exact lt_of_le_of_lt hle hlt
  · have hlen2 : 2 ≤ L.length := by omega
    have hi_eq : i = L.length - 2 := by omega
    subst hi_eq
    have hi1 : L.length - 2 + 1 = L.length - 1 := by omega
    rw [hi1] at hlt
    have hstep : (∏ j ∈ Finset.range L.length, (L.getD j 0 : ℝ)) =
        (∏ j ∈ Finset.range (L.length - 1), (L.getD j 0 : ℝ)) *
          (L.getD (L.length - 1) 0 : ℝ) := by
      conv_lhs => rw [show L.length = (L.length - 1) + 1 by omega, Finset.prod_range_succ]
    rw [hstep]
    have hmono : (L.getD (L.length - 1) 0 : ℝ) ≤ (L.getD (L.length - 2) 0 : ℝ) :=
      Nat.cast_le.mpr (descPrimes_ge_last_two hlen2)
    have hL2_ge1 : (1 : ℝ) ≤ (L.getD (L.length - 2) 0 : ℝ) := hL_ge1 (L.length - 2) (by omega)
    have hsq : (L.getD (L.length - 1) 0 : ℝ) ≤ (L.getD (L.length - 2) 0 : ℝ) ^ 2 := by
      nlinarith
    have hle : (∏ j ∈ Finset.range (L.length - 1), (L.getD j 0 : ℝ)) *
          (L.getD (L.length - 1) 0 : ℝ) ≤
        (∏ j ∈ Finset.range (L.length - 1), (L.getD j 0 : ℝ)) *
          (L.getD (L.length - 2) 0 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (hprod_nonneg (L.length - 1))
    exact lt_of_le_of_lt hle hlt

/-- Every `S ∈ DPlus D` (with `1 < D`) satisfies `∏_{p ∈ S} p < D`. -/
theorem DPlus_prod_lt (D : ℝ) (S : Finset ℕ) (hD : 1 < D) (hS : DPlus D S) :
    (∏ p ∈ S, (p : ℝ)) < D := by
  by_cases h0 : 0 ∈ S
  · have hzero : (∏ p ∈ S, (p : ℝ)) = 0 :=
      Finset.prod_eq_zero h0 (by simp)
    linarith
  · have hpos : ∀ p ∈ S, 1 ≤ p := fun p hp => Nat.pos_of_ne_zero fun h => h0 (h ▸ hp)
    by_cases hne : S = ∅
    · subst hne; simpa using hD
    · have hlen_pos : 0 < (descPrimes S).length := by
        rw [descPrimes, Finset.length_sort]
        exact Finset.card_pos.mpr (Finset.ne_empty_iff_nonempty.mp hne)
      have hall := (DPlus_iff_forall D S).mp hS
      refine prod_lt_of_prefix_bound hD hpos ?_
      by_cases hpar : ((descPrimes S).length - 1) % 2 = 0
      · exact ⟨(descPrimes S).length - 1, by omega, by omega, hall _ (by omega) hpar⟩
      · have hlen2 : 2 ≤ (descPrimes S).length := by omega
        have hpar2 : ((descPrimes S).length - 2) % 2 = 0 := by omega
        exact ⟨(descPrimes S).length - 2, by omega, le_rfl, hall _ (by omega) hpar2⟩

/-- Every `S ∈ DMinus D` with `S.card ≠ 1` (and `1 < D`) satisfies `∏_{p ∈ S} p < D`. -/
theorem DMinus_prod_lt_of_card_ne_one (D : ℝ) (S : Finset ℕ) (hD : 1 < D)
    (hcard : S.card ≠ 1) (hS : DMinus D S) :
    (∏ p ∈ S, (p : ℝ)) < D := by
  by_cases h0 : 0 ∈ S
  · have hzero : (∏ p ∈ S, (p : ℝ)) = 0 :=
      Finset.prod_eq_zero h0 (by simp)
    linarith
  · have hpos : ∀ p ∈ S, 1 ≤ p := fun p hp => Nat.pos_of_ne_zero fun h => h0 (h ▸ hp)
    by_cases hne : S = ∅
    · subst hne; simpa using hD
    · have hcard_ge2 : 2 ≤ S.card := by
        have := Finset.card_pos.mpr (Finset.ne_empty_iff_nonempty.mp hne)
        omega
      have hlen2 : 2 ≤ (descPrimes S).length := by
        rw [descPrimes, Finset.length_sort]; exact hcard_ge2
      have hall := (DMinus_iff_forall D S).mp hS
      refine prod_lt_of_prefix_bound hD hpos ?_
      by_cases hpar : ((descPrimes S).length - 1) % 2 = 1
      · exact ⟨(descPrimes S).length - 1, by omega, by omega, hall _ (by omega) hpar⟩
      · have hpar2 : ((descPrimes S).length - 2) % 2 = 1 := by omega
        exact ⟨(descPrimes S).length - 2, by omega, le_rfl, hall _ (by omega) hpar2⟩

/-- Every `S ∈ DMinus D` whose singleton elements are `< D` (e.g. `S ⊆ P` with `∀ p ∈ P, p < D`)
satisfies `∏_{p ∈ S} p < D` when `1 < D`. -/
theorem DMinus_prod_lt (D : ℝ) (S : Finset ℕ) (hD : 1 < D) (hS : DMinus D S)
    (hlt : S.card = 1 → ∀ p ∈ S, (p : ℝ) < D) :
    (∏ p ∈ S, (p : ℝ)) < D := by
  by_cases hcard : S.card = 1
  · rcases Finset.card_eq_one.mp hcard with ⟨p, rfl⟩
    simpa using hlt hcard p (Finset.mem_singleton_self p)
  · exact DMinus_prod_lt_of_card_ne_one D S hD hcard hS

end

end BuchstabSwitching
