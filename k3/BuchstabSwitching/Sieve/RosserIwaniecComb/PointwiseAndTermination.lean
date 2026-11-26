import BuchstabSwitching.Sieve.RosserIwaniecComb.Weights
import BuchstabSwitching.Sieve.RosserIwaniecComb.MainTermIdentity
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Combinatorial Rosser–Iwaniec Pointwise Inequalities and Finite Termination (`β = 2`)

Proves:
1. The fundamental combinatorial Rosser–Iwaniec inequalities `rosser_iwaniec_pointwise_lower`,
   `rosser_iwaniec_pointwise_upper`, and `rosser_iwaniec_pointwise_upper_int`.
2. The finite-terminating vanishing lemma `T_sum_eq_zero_of_prod_ge` and its range variant
   `T_sum_eq_zero_of_mem_range_prod_ge` (matching `NOTES_K3_DERIVATION.md` §4 and
   `linear_sieve.py:compute_n_term`).
-/

namespace BuchstabSwitching

noncomputable section

/-! ### 3. Fundamental Combinatorial Rosser–Iwaniec Sieve Inequalities -/

private lemma sieveV_ones (P : Finset ℕ) :
    sieveV (fun _ => (1 : ℝ)) P = if P = ∅ then 1 else 0 := by
  by_cases hP : P = ∅
  · subst hP; simp [sieveV]
  · obtain ⟨p, hp⟩ := Finset.ne_empty_iff_nonempty.mp hP
    have hzero : sieveV (fun _ => (1 : ℝ)) P = 0 :=
      Finset.prod_eq_zero hp (by norm_num)
    simp [hP, hzero]

private lemma T_sum_ones_nonneg (n : ℕ) (D : ℝ) (P : Finset ℕ) :
    0 ≤ T_sum (fun _ => (1 : ℝ)) n D P := by
  rw [T_sum]
  refine Finset.sum_nonneg fun S _ => ?_
  split_ifs with hS
  · rw [Finset.prod_const_one, one_mul, sieveV_ones]
    split_ifs <;> norm_num
  · exact le_rfl

/-- Fundamental combinatorial Rosser–Iwaniec lower-bound sieve inequality (`β = 2`). -/
theorem rosser_iwaniec_pointwise_lower (P : Finset ℕ) (D : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (_hD : 1 ≤ D) :
    ∑ S ∈ P.powerset.filter (DMinus D), (-1 : ℤ) ^ S.card ≤ if P = ∅ then 1 else 0 := by
  have hreal : (∑ S ∈ P.powerset.filter (DMinus D), (-1 : ℝ) ^ S.card) ≤
      if P = ∅ then (1 : ℝ) else 0 := by
    have heq := ri_main_term_lower_eq (fun _ => (1 : ℝ)) D P hP
    simp only [Finset.prod_const_one, mul_one] at heq
    rw [heq, sieveV_ones]
    have hT : 0 ≤ ∑ k ∈ Finset.Icc 1 P.card, T_sum (fun _ => (1 : ℝ)) (2 * k) D P :=
      Finset.sum_nonneg fun k _ => T_sum_ones_nonneg (2 * k) D P
    linarith
  have hcast : ((∑ S ∈ P.powerset.filter (DMinus D), (-1 : ℤ) ^ S.card : ℤ) : ℝ) ≤
      ((if P = ∅ then (1 : ℤ) else 0 : ℤ) : ℝ) := by
    push_cast
    simpa [apply_ite (Int.cast : ℤ → ℝ)] using hreal
  exact Int.cast_le.mp hcast

/-- Fundamental combinatorial Rosser–Iwaniec upper-bound sieve inequality (`β = 2`). -/
theorem rosser_iwaniec_pointwise_upper (P : Finset ℕ) (D : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (_hD : 1 ≤ D) :
    (if P = ∅ then (1 : ℝ) else 0) ≤
      ∑ S ∈ P.powerset.filter (DPlus D), (-1 : ℝ) ^ S.card := by
  have heq := ri_main_term_upper_eq (fun _ => (1 : ℝ)) D P hP
  simp only [Finset.prod_const_one, mul_one] at heq
  rw [heq, sieveV_ones]
  have hT : 0 ≤ ∑ k ∈ Finset.Icc 1 P.card, T_sum (fun _ => (1 : ℝ)) (2 * k - 1) D P :=
    Finset.sum_nonneg fun k _ => T_sum_ones_nonneg (2 * k - 1) D P
  linarith

/-- Integer-valued version of `rosser_iwaniec_pointwise_upper`. -/
theorem rosser_iwaniec_pointwise_upper_int (P : Finset ℕ) (D : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hD : 1 ≤ D) :
    (if P = ∅ then (1 : ℤ) else 0) ≤
      ∑ S ∈ P.powerset.filter (DPlus D), (-1 : ℤ) ^ S.card := by
  have hreal := rosser_iwaniec_pointwise_upper P D hP hD
  have hcast : ((if P = ∅ then (1 : ℤ) else 0 : ℤ) : ℝ) ≤
      ((∑ S ∈ P.powerset.filter (DPlus D), (-1 : ℤ) ^ S.card : ℤ) : ℝ) := by
    push_cast
    simpa [apply_ite (Int.cast : ℤ → ℝ)] using hreal
  exact Int.cast_le.mp hcast

/-! ### 4. Finite-Terminating Vanishing Lemma (`T_sum_eq_zero_of_prod_ge`) -/

private lemma sort_sublist_of_subset {S P : Finset ℕ} (hSP : S ⊆ P) :
    (S.sort (· ≤ ·)).Sublist (P.sort (· ≤ ·)) := by
  have hfilt : (P.sort (· ≤ ·)).filter (fun x => decide (x ∈ S)) = S.sort (· ≤ ·) := by
    have hnodup : ((P.sort (· ≤ ·)).filter (fun x => decide (x ∈ S))).Nodup :=
      (P.sort_nodup (· ≤ ·)).filter _
    have hsort : ((P.sort (· ≤ ·)).filter (fun x => decide (x ∈ S))).Pairwise (· ≤ ·) :=
      (P.pairwise_sort (· ≤ ·)).filter _
    have htoFin : ((P.sort (· ≤ ·)).filter (fun x => decide (x ∈ S))).toFinset = S := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hSP h, h⟩⟩
    have hres := (List.toFinset_sort (· ≤ ·) hnodup).mpr hsort
    rw [htoFin] at hres
    exact hres.symm
  rw [← hfilt]
  exact List.filter_sublist

private lemma sublist_getElem_le {L₁ L₂ : List ℕ} (hsub : L₁.Sublist L₂) :
    L₂.Pairwise (· ≤ ·) →
      ∀ (j : ℕ) (hj : j < L₁.length),
        ∃ (k : ℕ) (hk : k < L₂.length), j ≤ k ∧ L₁[j] = L₂[k] := by
  induction hsub with
  | slnil =>
      intro _ j hj; simp at hj
  | cons a _ ih =>
      intro hsorted j hj
      have hsorted' := (List.pairwise_cons.mp hsorted).2
      rcases ih hsorted' j hj with ⟨k, hk, hjk, heq⟩
      exact ⟨k + 1, Nat.succ_lt_succ hk, by omega, heq⟩
  | cons_cons a _ ih =>
      intro hsorted j hj
      have hsorted' := (List.pairwise_cons.mp hsorted).2
      cases j with
      | zero =>
          exact ⟨0, by simp, le_rfl, rfl⟩
      | succ j' =>
          rcases ih hsorted' j' (Nat.lt_of_succ_lt_succ hj) with ⟨k, hk, hjk, heq⟩
          exact ⟨k + 1, Nat.succ_lt_succ hk, Nat.succ_le_succ hjk, heq⟩

private lemma getElem_le_of_sublist {L₁ L₂ : List ℕ} (hsub : L₁.Sublist L₂)
    (hsorted : L₂.Pairwise (· ≤ ·)) (j : ℕ) (hj₁ : j < L₁.length) (hj₂ : j < L₂.length) :
    L₂[j] ≤ L₁[j] := by
  rcases sublist_getElem_le hsub hsorted j hj₁ with ⟨k, hk, hjk, heq⟩
  rw [heq]
  exact hsorted.rel_get_of_le hjk

private lemma sort_asc_eq_reverse_desc (S : Finset ℕ) :
    S.sort (· ≤ ·) = (descPrimes S).reverse := by
  have hlt : (descPrimes S).SortedGT := S.sortedGT_sort
  have hrev_lt : (descPrimes S).reverse.SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_reverse]
    simpa [descPrimes, List.sortedGT_iff_pairwise] using hlt
  have htoFin : (descPrimes S).reverse.toFinset = S := by
    ext x
    simp [descPrimes]
  calc S.sort (· ≤ ·)
    _ = (descPrimes S).reverse.toFinset.sort (· ≤ ·) := by rw [htoFin]
    _ = (descPrimes S).reverse := hrev_lt.sort_toFinset

/-- **Finite-terminating Rosser–Iwaniec vanishing lemma** (`NOTES_K3_DERIVATION.md` §4 &
`linear_sieve.py:compute_n_term`):
For `n ≥ 3`, if `q 0, q 1, ..., q (n - 1)` lower-bound the `n` smallest elements of `P`
(in 0-based indexing, `q_3` is `q 2` and `∏_{j=4}^n q_j` is `∏ j ∈ Finset.Ico 3 n, q j`)
and `(q 2 : ℝ) ^ 3 * ∏ j ∈ Finset.Ico 3 n, (q j : ℝ) ≥ D`, then `T_sum g n D P = 0`. -/
theorem T_sum_eq_zero_of_prod_ge (g : ℕ → ℝ) (n : ℕ) (hn : 3 ≤ n) (D : ℝ) (P : Finset ℕ)
    (q : ℕ → ℕ)
    (hq_le : ∀ (j : ℕ) (hj : j < P.card), j < n → q j ≤ (P.sort (· ≤ ·))[j]'(by simpa using hj))
    (hprod_ge : D ≤ (q 2 : ℝ) ^ 3 * ∏ j ∈ Finset.Ico 3 n, (q j : ℝ)) :
    T_sum g n D P = 0 := by
  by_cases hcard : P.card < n
  · exact T_sum_eq_zero_of_card_lt hcard
  · have hn_le : n ≤ P.card := not_lt.mp hcard
    rw [T_sum]
    refine Finset.sum_eq_zero fun S hS => ?_
    exfalso
    have hmem := Finset.mem_filter.mp hS
    rcases Finset.mem_powersetCard.mp hmem.1 with ⟨hSP, hScard⟩
    have hlen : (descPrimes S).length = n := by
      rw [descPrimes, Finset.length_sort, hScard]
    have hfor := (riTermCond_iff_forall D 1 (descPrimes S) (by omega)).mp hmem.2
    have hi_lt : n - 3 < (descPrimes S).length - 1 := by omega
    have hi_par : (n - 3) % 2 = ((descPrimes S).length - 1) % 2 := by rw [hlen]; omega
    have hlt := hfor.1 (n - 3) hi_lt hi_par
    rw [one_mul] at hlt
    have hrev : S.sort (· ≤ ·) = (descPrimes S).reverse := sort_asc_eq_reverse_desc S
    have hsub : (S.sort (· ≤ ·)).Sublist (P.sort (· ≤ ·)) := sort_sublist_of_subset hSP
    have hq_S : ∀ (j : ℕ) (hj : j < n),
        q j ≤ (descPrimes S).getD (n - 1 - j) 0 := by
      intro j hj
      have hjP : j < P.card := lt_of_lt_of_le hj hn_le
      have hjS : j < (S.sort (· ≤ ·)).length := by rw [Finset.length_sort, hScard]; exact hj
      have h1 : q j ≤ (P.sort (· ≤ ·))[j]'(by simpa using hjP) := hq_le j hjP hj
      have h2 : (P.sort (· ≤ ·))[j]'(by simpa using hjP) ≤ (S.sort (· ≤ ·))[j]'hjS :=
        getElem_le_of_sublist hsub (P.pairwise_sort (· ≤ ·)) j hjS (by simpa using hjP)
      have hjrev : j < (descPrimes S).reverse.length := by rw [List.length_reverse, hlen]; exact hj
      have h3 : (S.sort (· ≤ ·))[j]'hjS = (descPrimes S).getD (n - 1 - j) 0 := by
        simp only [hrev]
        rw [List.getElem_reverse hjrev, getD_eq_getElem (by rw [hlen]; omega)]
        congr 1
        rw [hlen]
      omega
    have hq2 : (q 2 : ℝ) ≤ ((descPrimes S).getD (n - 3) 0 : ℝ) := by
      have := hq_S 2 (by omega)
      simpa [show n - 1 - 2 = n - 3 by omega] using (Nat.cast_le (α := ℝ)).mpr this
    have hpow : (q 2 : ℝ) ^ 3 ≤ ((descPrimes S).getD (n - 3) 0 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hq2 3
    have hprod_nat :
        ∏ j ∈ Finset.Ico 3 n, q j ≤
          ∏ k ∈ Finset.range (n - 3), (descPrimes S).getD k 0 := by
      have hrew :
          ∏ k ∈ Finset.range (n - 3), (descPrimes S).getD k 0 =
            ∏ j ∈ Finset.Ico 3 n, (descPrimes S).getD (n - 1 - j) 0 := by
        refine Finset.prod_bij (fun k _ => n - 1 - k) ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_range] at hk
          rw [Finset.mem_Ico]; omega
        · intro k₁ hk₁ k₂ hk₂ heq
          rw [Finset.mem_range] at hk₁ hk₂; omega
        · intro j hj
          rw [Finset.mem_Ico] at hj
          refine ⟨n - 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
        · intro k hk
          rw [Finset.mem_range] at hk
          congr 1; omega
      rw [hrew]
      refine Finset.prod_le_prod fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      exact hq_S j hj.2
    have hprod_bij :
        ∏ j ∈ Finset.Ico 3 n, (q j : ℝ) ≤
          ∏ k ∈ Finset.range (n - 3), ((descPrimes S).getD k 0 : ℝ) := by
      have hle_cast : ((∏ j ∈ Finset.Ico 3 n, q j : ℕ) : ℝ) ≤
          ((∏ k ∈ Finset.range (n - 3), (descPrimes S).getD k 0 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hprod_nat
      simpa [Nat.cast_prod] using hle_cast
    have hsplit_prod :
        (∏ j ∈ Finset.range (n - 3 + 1), ((descPrimes S).getD j 0 : ℝ)) *
            ((descPrimes S).getD (n - 3) 0 : ℝ) ^ 2 =
          ((descPrimes S).getD (n - 3) 0 : ℝ) ^ 3 *
            ∏ k ∈ Finset.range (n - 3), ((descPrimes S).getD k 0 : ℝ) := by
      rw [Finset.prod_range_succ]
      ring
    rw [hsplit_prod] at hlt
    have hle_all :
        (q 2 : ℝ) ^ 3 * ∏ j ∈ Finset.Ico 3 n, (q j : ℝ) ≤
          ((descPrimes S).getD (n - 3) 0 : ℝ) ^ 3 *
            ∏ k ∈ Finset.range (n - 3), ((descPrimes S).getD k 0 : ℝ) :=
      mul_le_mul hpow hprod_bij (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
    linarith

private lemma le_sort_of_strictMono_range {P : Finset ℕ} {q : ℕ → ℕ}
    (hq_mono : StrictMono q) (hPq : ∀ p ∈ P, ∃ k, q k = p) :
    ∀ (j : ℕ) (hj : j < P.card), q j ≤ (P.sort (· ≤ ·))[j]'(by simpa using hj) := by
  set L := P.sort (· ≤ ·)
  have hlen : L.length = P.card := P.length_sort (· ≤ ·)
  have hsort : L.SortedLT := P.sortedLT_sort
  have hidx : ∀ j (hj : j < L.length), ∃ k, j ≤ k ∧ L[j] = q k := by
    intro j
    induction j with
    | zero =>
        intro hj
        have hmem : L[0] ∈ P := (P.mem_sort (· ≤ ·)).mp (List.getElem_mem hj)
        rcases hPq L[0] hmem with ⟨k, hk⟩
        exact ⟨k, Nat.zero_le k, hk.symm⟩
    | succ j ih =>
        intro hj
        have hj' : j < L.length := Nat.lt_of_succ_lt hj
        rcases ih hj' with ⟨k₀, hk₀_ge, hk₀_eq⟩
        have hmem : L[j + 1] ∈ P := (P.mem_sort (· ≤ ·)).mp (List.getElem_mem hj)
        rcases hPq L[j + 1] hmem with ⟨k₁, hk₁_eq⟩
        have hlt_val : q k₀ < q k₁ := by
          rw [← hk₀_eq, hk₁_eq]
          exact hsort.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self j)
        have hlt_idx : k₀ < k₁ := hq_mono.lt_iff_lt.mp hlt_val
        exact ⟨k₁, by omega, hk₁_eq.symm⟩
  intro j hj
  have hjL : j < L.length := by simpa [L] using hj
  rcases hidx j hjL with ⟨k, hjk, heq⟩
  rw [show (P.sort (· ≤ ·))[j]'(by simpa using hj) = L[j] from rfl, heq]
  exact hq_mono.monotone hjk

/-- Variant of `T_sum_eq_zero_of_prod_ge` when `P` is a finite subset of the range of a strictly
increasing sequence `q : ℕ → ℕ` (such as primes `≥ p_*` in `compute_n_term`). -/
theorem T_sum_eq_zero_of_mem_range_prod_ge (g : ℕ → ℝ) (n : ℕ) (hn : 3 ≤ n) (D : ℝ) (P : Finset ℕ)
    (q : ℕ → ℕ) (hq_mono : StrictMono q) (hPq : ∀ p ∈ P, ∃ k, q k = p)
    (hprod_ge : D ≤ (q 2 : ℝ) ^ 3 * ∏ j ∈ Finset.Ico 3 n, (q j : ℝ)) :
    T_sum g n D P = 0 :=
  T_sum_eq_zero_of_prod_ge g n hn D P q
    (fun j hj _ => le_sort_of_strictMono_range hq_mono hPq j hj) hprod_ge

end

end BuchstabSwitching
