import BuchstabSwitching.Sieve.LinearSieveInduction.MertensCond
import BuchstabSwitching.Sieve.AbstractSieve
import Mathlib.Tactic

/-!
# Finite Telescoping Abel Summation Comparison (Nathanson Lemma 9.8 / BJS Lemma 10)

Proves `sum_filter_ge_mul_sieveV_eq` and `abel_summation_bjs` via discrete summation by parts
and integral comparison for antitone nonnegative functions `φ` on `[1, ∞)`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 2. Finite Telescoping Abel Summation Comparison (Nathanson Lemma 9.8 / BJS Lemma 10) -/

/-- Exact telescoping identity `∑_{p ∈ P, u ≤ p} g(p) V(P_{< p}) = V(P_{< u}) - V(P)`. -/
theorem sum_filter_ge_mul_sieveV_eq (g : ℕ → ℝ) (P : Finset ℕ) (u : ℝ) :
    ∑ p ∈ P.filter (fun p : ℕ => u ≤ (p : ℝ)), g p * sieveV g (P.filter (· < p)) =
      sieveV g (P.filter (fun p : ℕ => (p : ℝ) < u)) - sieveV g P := by
  induction hn : P.card using Nat.strong_induction_on generalizing P with
  | ind m ih =>
    by_cases hP : P = ∅
    · subst hP; simp [sieveV]
    · have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP
      have hcard_pos : 0 < P.card := Finset.card_pos.mpr hPne
      set p := P.max' hPne
      set P' := P.erase p
      have hpP : p ∈ P := Finset.max'_mem P hPne
      have hP'card : P'.card < m := by rw [← hn, Finset.card_erase_of_mem hpP]; omega
      have hlt_eq : P.filter (· < p) = P' := by
        ext q
        simp only [P', Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun ⟨hqP, hqp⟩ => ⟨ne_of_lt hqp, hqP⟩,
          fun ⟨hqne, hqP⟩ => ⟨hqP, lt_of_le_of_ne (Finset.le_max' P q hqP) hqne⟩⟩
      have hV_split : sieveV g P = sieveV g P' - g p * sieveV g P' := by
        have hins : insert p P' = P := Finset.insert_erase hpP
        have hnp : p ∉ P' := Finset.notMem_erase p P
        calc sieveV g P
            = ∏ q ∈ insert p P', (1 - g q) := by rw [sieveV, hins]
          _ = (1 - g p) * sieveV g P' := by rw [Finset.prod_insert hnp, sieveV]
          _ = sieveV g P' - g p * sieveV g P' := by ring
      have ihP' := ih P'.card hP'card P' rfl
      by_cases hup : u ≤ (p : ℝ)
      · have hge_eq : P.filter (fun q : ℕ => u ≤ (q : ℝ)) =
            insert p (P'.filter (fun q : ℕ => u ≤ (q : ℝ))) := by
          ext q
          simp only [Finset.mem_insert, Finset.mem_filter, P', Finset.mem_erase]
          constructor
          · rintro ⟨hqP, huq⟩
            by_cases hqp : q = p
            · exact Or.inl hqp
            · exact Or.inr ⟨⟨hqp, hqP⟩, huq⟩
          · rintro (rfl | ⟨⟨_, hqP⟩, huq⟩)
            · exact ⟨hpP, hup⟩
            · exact ⟨hqP, huq⟩
        have hp_nf : p ∉ P'.filter (fun q : ℕ => u ≤ (q : ℝ)) := fun h =>
          Finset.notMem_erase p P (Finset.mem_filter.mp h).1
        have hlt_u_eq : P.filter (fun q : ℕ => (q : ℝ) < u) =
            P'.filter (fun q : ℕ => (q : ℝ) < u) := by
          ext q
          simp only [Finset.mem_filter, P', Finset.mem_erase]
          exact ⟨fun ⟨hqP, hqu⟩ => ⟨⟨fun h => by linarith [h ▸ hup, hqu], hqP⟩, hqu⟩,
            fun ⟨⟨_, hqP⟩, hqu⟩ => ⟨hqP, hqu⟩⟩
        have hcongr :
            ∑ q ∈ P'.filter (fun q : ℕ => u ≤ (q : ℝ)), g q * sieveV g (P.filter (· < q)) =
              ∑ q ∈ P'.filter (fun q : ℕ => u ≤ (q : ℝ)), g q * sieveV g (P'.filter (· < q)) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          have hq' := Finset.mem_erase.mp (Finset.mem_filter.mp hq).1
          have hqp : q < p := lt_of_le_of_ne (Finset.le_max' P q hq'.2) hq'.1
          have hf : P.filter (· < q) = P'.filter (· < q) := by
            ext r
            simp only [Finset.mem_filter, P', Finset.mem_erase]
            exact ⟨fun ⟨hrP, hrq⟩ => ⟨⟨by omega, hrP⟩, hrq⟩, fun ⟨⟨_, hrP⟩, hrq⟩ => ⟨hrP, hrq⟩⟩
          rw [hf]
        rw [hge_eq, Finset.sum_insert hp_nf, hlt_eq, hcongr, ihP', hlt_u_eq, hV_split]
        ring
      · have hpu : (p : ℝ) < u := lt_of_not_ge hup
        have hge_empty : P.filter (fun q : ℕ => u ≤ (q : ℝ)) = ∅ := by
          ext q
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hqP huq
          have hqp : (q : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (Finset.le_max' P q hqP)
          linarith
        have hlt_u_eq : P.filter (fun q : ℕ => (q : ℝ) < u) = P := by
          ext q
          simp only [Finset.mem_filter]
          refine ⟨fun h => h.1, fun hqP => ⟨hqP, ?_⟩⟩
          have hqp : (q : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (Finset.le_max' P q hqP)
          linarith
        rw [hge_empty, Finset.sum_empty, hlt_u_eq, sub_self]

private lemma sum_sub_mul_eq_abel (k : ℕ) (V a : ℕ → ℝ) :
    ∑ i ∈ Finset.range k, (V i - V (i + 1)) * a i =
      V 0 * a 0 - V k * a k + ∑ i ∈ Finset.range k, V (i + 1) * (a (i + 1) - a i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

private lemma abel_recombine_t (k : ℕ) (t a : ℕ → ℝ) :
    t 0 * a 0 + ∑ i ∈ Finset.range k, t (i + 1) * (a (i + 1) - a i) =
      t k * a k + ∑ i ∈ Finset.range k, a i * (t i - t (i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith [ih]

private lemma abel_algebraic_bound (k : ℕ) (V t a : ℕ → ℝ) (K s : ℝ)
    (hs : 0 < s) (hVk : 0 ≤ V k) (htk : t k = s)
    (ha0 : 0 ≤ a 0) (ha_mono : ∀ i < k, 0 ≤ a (i + 1) - a i)
    (hV_ub : ∀ i ≤ k, V i ≤ (K / s) * V k * t i) :
    ∑ i ∈ Finset.range k, (V i - V (i + 1)) * a i ≤
      V k * ((K - 1) * a k + (K / s) * ∑ i ∈ Finset.range k, a i * (t i - t (i + 1))) := by
  rw [sum_sub_mul_eq_abel]
  have h0 : V 0 * a 0 ≤ ((K / s) * V k * t 0) * a 0 :=
    mul_le_mul_of_nonneg_right (hV_ub 0 (Nat.zero_le k)) ha0
  have hsum : ∑ i ∈ Finset.range k, V (i + 1) * (a (i + 1) - a i) ≤
      ∑ i ∈ Finset.range k, ((K / s) * V k * t (i + 1)) * (a (i + 1) - a i) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonneg_right (hV_ub (i + 1) hik) (ha_mono i hik)
  have hmul : ∑ i ∈ Finset.range k, ((K / s) * V k * t (i + 1)) * (a (i + 1) - a i) =
      V k * ((K / s) * ∑ i ∈ Finset.range k, t (i + 1) * (a (i + 1) - a i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hs0 : s ≠ 0 := hs.ne'
  have _ := hVk
  calc V 0 * a 0 - V k * a k + ∑ i ∈ Finset.range k, V (i + 1) * (a (i + 1) - a i)
      ≤ ((K / s) * V k * t 0) * a 0 - V k * a k +
          ∑ i ∈ Finset.range k, ((K / s) * V k * t (i + 1)) * (a (i + 1) - a i) := by linarith
    _ = V k * (-a k + (K / s) * (t 0 * a 0 + ∑ i ∈ Finset.range k, t (i + 1) * (a (i + 1) - a i))) := by
          rw [hmul]; ring
    _ = V k * (-a k + (K / s) * (t k * a k + ∑ i ∈ Finset.range k, a i * (t i - t (i + 1)))) := by
          rw [abel_recombine_t]
    _ = V k * ((K - 1) * a k + (K / s) * ∑ i ∈ Finset.range k, a i * (t i - t (i + 1))) := by
          rw [htk]; field_simp [hs0]; ring

private lemma t_chain_le_zero (j : ℕ) (t : ℕ → ℝ) (ht_anti : ∀ i < j, t (i + 1) ≤ t i) :
    t j ≤ t 0 := by
  induction j with
  | zero => exact le_rfl
  | succ m ih =>
    exact (ht_anti m (Nat.lt_succ_self m)).trans (ih fun i hi => ht_anti i (Nat.lt_succ_of_lt hi))

private lemma sum_range_integral_telescope (k : ℕ) (t : ℕ → ℝ) (f : ℝ → ℝ)
    (ht_ge : ∀ i ≤ k, 2 ≤ t i)
    (ht_anti : ∀ i < k, t (i + 1) ≤ t i)
    (hf_int : ∀ a b, 2 ≤ a → a ≤ b → IntervalIntegrable f volume a b) :
    ∑ i ∈ Finset.range k, ∫ x in (t (i + 1))..(t i), f x = ∫ x in (t k)..(t 0), f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun i hi => ht_ge i (Nat.le_succ_of_le hi))
      (fun i hi => ht_anti i (Nat.lt_succ_of_lt hi))
    have ht_chain1 : t (k + 1) ≤ t k := ht_anti k (Nat.lt_succ_self k)
    have ht_chain2 : t k ≤ t 0 := t_chain_le_zero k t fun i hi => ht_anti i (Nat.lt_succ_of_lt hi)
    have h1 := hf_int (t (k + 1)) (t k) (ht_ge (k + 1) (le_refl _)) ht_chain1
    have h2 := hf_int (t k) (t 0) (ht_ge k (by omega)) ht_chain2
    have hadd := integral_add_adjacent_intervals h1 h2
    linarith

/-- **Finite Telescoping Abel Summation Comparison Lemma** (Nathanson Lemma 9.8 / BJS Lemma 10):
For `1 < z ≤ D` with `s = log D / log z ≥ 2`, `1 ≤ K`, `1 ≤ u`, `s ≤ M`, if `P` satisfies
`AllLevelsMertensCondFrom g P u K` and `φ : ℝ → ℝ` is nonnegative, antitone on `[1, ∞)`,
and vanishes for `M ≤ t` (`φ (t - 1) = 0`), then
`∑_{p ∈ P, u ≤ p} g(p) V(P_{< p}) φ(log(D/p)/log p) ≤ V(P) ((K - 1) φ(s - 1) + (K / s) ∫_s^M φ(t - 1) dt)`. -/
theorem abel_summation_bjs {g : ℕ → ℝ} {P : Finset ℕ} {z D u K M : ℝ}
    (hz : 1 < z) (hDz : z ^ 2 ≤ D) (hK : 1 ≤ K) (_hu : 1 ≤ u)
    (hsM : Real.log D / Real.log z ≤ M)
    (hP_ge2 : ∀ p ∈ P, 2 ≤ p) (hP_ltz : ∀ p ∈ P, (p : ℝ) < z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1)
    (hCond : AllLevelsMertensCondFrom g P u K)
    {φ : ℝ → ℝ} (hφ_nn : ∀ t, 1 ≤ t → 0 ≤ φ t)
    (hφ_anti : AntitoneOn φ (Set.Ici 1))
    (hφ_supp : ∀ t, M ≤ t → φ (t - 1) = 0) :
    ∑ p ∈ P.filter (fun p : ℕ => u ≤ (p : ℝ)),
      g p * sieveV g (P.filter (· < p)) * φ (Real.log (D / (p : ℝ)) / Real.log (p : ℝ)) ≤
      sieveV g P *
        ((K - 1) * φ (Real.log D / Real.log z - 1) +
          (K / (Real.log D / Real.log z)) * ∫ t in (Real.log D / Real.log z)..M, φ (t - 1)) := by
  set s : ℝ := Real.log D / Real.log z
  have hlogz_pos : 0 < Real.log z := Real.log_pos hz
  have hD_ge_z : z ≤ D := by nlinarith
  have hD_gt1 : 1 < D := lt_of_lt_of_le hz hD_ge_z
  have hlogD_pos : 0 < Real.log D := Real.log_pos hD_gt1
  have hs_ge2 : 2 ≤ s := by
    rw [show s = Real.log D / Real.log z from rfl, le_div_iff₀ hlogz_pos]
    have hlog_sq : Real.log (z ^ 2) ≤ Real.log D := Real.log_le_log (by positivity) hDz
    rw [Real.log_pow] at hlog_sq
    push_cast at hlog_sq
    linarith
  have hs_pos : 0 < s := by linarith
  have hshift_int : ∀ a b, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun t => φ (t - 1)) volume a b := by
    intro a b ha hab
    refine AntitoneOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hφ_anti (by simp only [Set.mem_Ici]; linarith [hx.1])
      (by simp only [Set.mem_Ici]; linarith [hy.1]) (by linarith)
  set Psub : Finset ℕ := P.filter (fun p : ℕ => u ≤ (p : ℝ))
  by_cases hPsub_empty : Psub = ∅
  · rw [hPsub_empty, Finset.sum_empty]
    have hVP : 0 ≤ sieveV g P := sieveV_nonneg fun p hp => (hg p hp).2
    have hφs : 0 ≤ φ (s - 1) := hφ_nn (s - 1) (by linarith)
    have hI_nn : 0 ≤ ∫ t in s..M, φ (t - 1) := by
      refine intervalIntegral.integral_nonneg hsM fun t ht => ?_
      exact hφ_nn (t - 1) (by linarith [ht.1])
    refine mul_nonneg hVP (add_nonneg (mul_nonneg (by linarith) hφs) (mul_nonneg (by positivity) hI_nn))
  · have hPsub_ne : Psub.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPsub_empty
    set L : List ℕ := Psub.sort (· ≤ ·)
    set k : ℕ := L.length
    have hk_pos : 0 < k := by
      dsimp [k, L]
      rw [Finset.length_sort]
      exact Finset.card_pos.mpr hPsub_ne
    have hL_sorted : L.SortedLT := Psub.sortedLT_sort
    have hL_mem_Psub : ∀ i (hi : i < k), L[i] ∈ Psub := fun i hi =>
      (Psub.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)
    have hL_mem_P : ∀ i (hi : i < k), L[i] ∈ P := fun i hi =>
      (Finset.mem_filter.mp (hL_mem_Psub i hi)).1
    have hL_ge_u : ∀ i (hi : i < k), u ≤ (L[i] : ℝ) := fun i hi =>
      (Finset.mem_filter.mp (hL_mem_Psub i hi)).2
    have hL_ge2 : ∀ i (hi : i < k), 2 ≤ L[i] := fun i hi => hP_ge2 _ (hL_mem_P i hi)
    have hL_ltz : ∀ i (hi : i < k), (L[i] : ℝ) < z := fun i hi => hP_ltz _ (hL_mem_P i hi)
    let V : ℕ → ℝ := fun i =>
      if hi : i < k then sieveV g (P.filter (· < L[i])) else sieveV g P
    let t : ℕ → ℝ := fun i =>
      if hi : i < k then Real.log D / Real.log (L[i] : ℝ) else s
    let a : ℕ → ℝ := fun i => φ (t i - 1)
    have hsum_eq_L :
        ∑ p ∈ Psub, g p * sieveV g (P.filter (· < p)) * φ (Real.log (D / (p : ℝ)) / Real.log (p : ℝ)) =
          ∑ i ∈ Finset.range k, (V i - V (i + 1)) * a i := by
      symm
      refine Finset.sum_bij (fun i hi => L[i]'(Finset.mem_range.mp hi)) ?_ ?_ ?_ ?_
      · intro i hi
        exact hL_mem_Psub i (Finset.mem_range.mp hi)
      · intro i₁ hi₁ i₂ hi₂ heq
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact (Nat.ne_of_lt (hL_sorted.getElem_lt_getElem_iff.mpr hlt)) heq
        · exact (Nat.ne_of_gt (hL_sorted.getElem_lt_getElem_iff.mpr hlt)) heq
      · intro p hp
        have hpL : p ∈ L := (Psub.mem_sort (· ≤ ·)).mpr hp
        rcases List.mem_iff_getElem.mp hpL with ⟨i, hi, rfl⟩
        exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
      · intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have hV_diff : V i - V (i + 1) = g (L[i]) * sieveV g (P.filter (· < L[i])) := by
          by_cases hi1 : i + 1 < k
          · have hflt : P.filter (· < L[i + 1]) = insert (L[i]) (P.filter (· < L[i])) := by
              ext q
              simp only [Finset.mem_insert, Finset.mem_filter]
              constructor
              · rintro ⟨hqP, hq_lt⟩
                rcases lt_trichotomy q (L[i]) with hlt | rfl | hgt
                · exact Or.inr ⟨hqP, hlt⟩
                · exact Or.inl rfl
                · exfalso
                  have hqu : u ≤ (q : ℝ) := (hL_ge_u i hik).trans (Nat.cast_le.mpr hgt.le)
                  have hq_sub : q ∈ Psub := Finset.mem_filter.mpr ⟨hqP, hqu⟩
                  have hq_L : q ∈ L := (Psub.mem_sort (· ≤ ·)).mpr hq_sub
                  rcases List.mem_iff_getElem.mp hq_L with ⟨j, hj, hqj⟩
                  have hij : i < j := hL_sorted.getElem_lt_getElem_iff.mp (by omega)
                  have hji1 : j < i + 1 := hL_sorted.getElem_lt_getElem_iff.mp (by omega)
                  omega
              · rintro (rfl | ⟨hqP, hq_lt⟩)
                · exact ⟨hL_mem_P i hik, hL_sorted.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self i)⟩
                · exact ⟨hqP, lt_trans hq_lt (hL_sorted.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self i))⟩
            have hnmem : L[i] ∉ P.filter (· < L[i]) := fun h =>
              Nat.lt_irrefl _ (Finset.mem_filter.mp h).2
            simp only [V, hik, hi1, ↓reduceDIte, hflt, sieveV, Finset.prod_insert hnmem]
            ring
          · have hi_last : i + 1 = k := by omega
            have hflt : P = insert (L[i]) (P.filter (· < L[i])) := by
              ext q
              simp only [Finset.mem_insert, Finset.mem_filter]
              constructor
              · intro hqP
                rcases lt_trichotomy q (L[i]) with hlt | rfl | hgt
                · exact Or.inr ⟨hqP, hlt⟩
                · exact Or.inl rfl
                · exfalso
                  have hqu : u ≤ (q : ℝ) := (hL_ge_u i hik).trans (Nat.cast_le.mpr hgt.le)
                  have hq_sub : q ∈ Psub := Finset.mem_filter.mpr ⟨hqP, hqu⟩
                  have hq_L : q ∈ L := (Psub.mem_sort (· ≤ ·)).mpr hq_sub
                  rcases List.mem_iff_getElem.mp hq_L with ⟨j, hj, hqj⟩
                  have hij : i < j := hL_sorted.getElem_lt_getElem_iff.mp (by omega)
                  omega
              · rintro (rfl | ⟨hqP, _⟩)
                · exact hL_mem_P i hik
                · exact hqP
            have hnmem : L[i] ∉ P.filter (· < L[i]) := fun h =>
              Nat.lt_irrefl _ (Finset.mem_filter.mp h).2
            simp only [V, hik, hi1, ↓reduceDIte]
            conv_lhs => rhs; rw [hflt]
            simp only [sieveV, Finset.prod_insert hnmem]
            ring
        have ha_eq : a i = φ (Real.log (D / (L[i] : ℝ)) / Real.log (L[i] : ℝ)) := by
          have hLi_ge2 := hL_ge2 i hik
          have hLi_pos : (0 : ℝ) < (L[i] : ℝ) := by exact_mod_cast (by omega : 0 < L[i])
          have hLi_gt1 : (1 : ℝ) < (L[i] : ℝ) := by exact_mod_cast (by omega : 1 < L[i])
          have hlogp_ne : Real.log (L[i] : ℝ) ≠ 0 := (Real.log_pos hLi_gt1).ne'
          have hsub : Real.log (D / (L[i] : ℝ)) / Real.log (L[i] : ℝ) =
              Real.log D / Real.log (L[i] : ℝ) - 1 := by
            rw [Real.log_div (by linarith) hLi_pos.ne', sub_div, div_self hlogp_ne]
          simp only [a, t, hik, ↓reduceDIte, hsub]
        rw [hV_diff, ha_eq]
    rw [hsum_eq_L]
    have ht_ge2 : ∀ i ≤ k, 2 ≤ t i := by
      intro i hik
      by_cases hi : i < k
      · simp only [t, hi, ↓reduceDIte]
        have hLi_ge2 := hL_ge2 i hi
        have hLi_gt1 : (1 : ℝ) < (L[i] : ℝ) := by exact_mod_cast (by omega : 1 < L[i])
        have hlogp_pos : 0 < Real.log (L[i] : ℝ) := Real.log_pos hLi_gt1
        have hlogp_lt : Real.log (L[i] : ℝ) < Real.log z := Real.log_lt_log (by linarith) (hL_ltz i hi)
        have h1 : s < Real.log D / Real.log (L[i] : ℝ) :=
          div_lt_div_of_pos_left hlogD_pos hlogp_pos hlogp_lt
        linarith
      · simp only [t, hi, ↓reduceDIte]
        exact hs_ge2
    have ht_anti : ∀ i < k, t (i + 1) ≤ t i := by
      intro i hik
      by_cases hi1 : i + 1 < k
      · simp only [t, hik, hi1, ↓reduceDIte]
        have hLi_ge2 := hL_ge2 i hik
        have hLi_gt1 : (1 : ℝ) < (L[i] : ℝ) := by exact_mod_cast (by omega : 1 < L[i])
        have hlogp_pos : 0 < Real.log (L[i] : ℝ) := Real.log_pos hLi_gt1
        have hlt : (L[i] : ℝ) < (L[i + 1] : ℝ) :=
          Nat.cast_lt.mpr (hL_sorted.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self i))
        have hlog_le : Real.log (L[i] : ℝ) ≤ Real.log (L[i + 1] : ℝ) :=
          Real.log_le_log (by linarith) hlt.le
        exact div_le_div_of_nonneg_left hlogD_pos.le hlogp_pos hlog_le
      · simp only [t, hik, hi1, ↓reduceDIte]
        have hLi_ge2 := hL_ge2 i hik
        have hLi_gt1 : (1 : ℝ) < (L[i] : ℝ) := by exact_mod_cast (by omega : 1 < L[i])
        have hlogp_pos : 0 < Real.log (L[i] : ℝ) := Real.log_pos hLi_gt1
        have hlog_le : Real.log (L[i] : ℝ) ≤ Real.log z :=
          Real.log_le_log (by linarith) (hL_ltz i hik).le
        exact div_le_div_of_nonneg_left hlogD_pos.le hlogp_pos hlog_le
    have hVk_nonneg : 0 ≤ V k := by
      simp only [V, lt_irrefl, ↓reduceDIte]
      exact sieveV_nonneg fun p hp => (hg p hp).2
    have hVk_eq : V k = sieveV g P := by simp [V]
    have htk_eq : t k = s := by simp [t]
    have ha0_nn : 0 ≤ a 0 := hφ_nn (t 0 - 1) (by linarith [ht_ge2 0 (Nat.zero_le k)])
    have ha_mono : ∀ i < k, 0 ≤ a (i + 1) - a i := by
      intro i hik
      have h1 : 1 ≤ t (i + 1) - 1 := by linarith [ht_ge2 (i + 1) hik]
      have h2 : t (i + 1) - 1 ≤ t i - 1 := by linarith [ht_anti i hik]
      have hle : φ (t i - 1) ≤ φ (t (i + 1) - 1) :=
        hφ_anti (by simp only [Set.mem_Ici]; exact h1)
          (by simp only [Set.mem_Ici]; exact h1.trans h2) h2
      dsimp [a]
      linarith
    have hV_ub : ∀ i ≤ k, V i ≤ (K / s) * V k * t i := by
      intro i hik
      by_cases hi : i < k
      · simp only [V, t, hi, ↓reduceDIte, hVk_eq]
        have hLi_ge2 := hL_ge2 i hi
        have hw : 1 < (L[i] : ℝ) := by exact_mod_cast (by omega : 1 < L[i])
        have huw : u ≤ (L[i] : ℝ) := hL_ge_u i hi
        have hwz : (L[i] : ℝ) ≤ z := (hL_ltz i hi).le
        have hcond := hCond hw huw hwz
        have hflt_w : P.filter (fun p : ℕ => (p : ℝ) < (L[i] : ℝ)) = P.filter (· < L[i]) := by
          ext p; simp [Nat.cast_lt]
        have hflt_z : P.filter (fun p : ℕ => (p : ℝ) < z) = P := by
          ext p
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.1, fun hp => ⟨hp, hP_ltz p hp⟩⟩
        rw [hflt_w, hflt_z] at hcond
        have hlogp_ne : Real.log (L[i] : ℝ) ≠ 0 := (Real.log_pos hw).ne'
        have hlogD_ne : Real.log D ≠ 0 := hlogD_pos.ne'
        have hlogz_ne : Real.log z ≠ 0 := hlogz_pos.ne'
        have heq_ratio : (K / s) * sieveV g P * (Real.log D / Real.log (L[i] : ℝ)) =
            K * (Real.log z / Real.log (L[i] : ℝ)) * sieveV g P := by
          dsimp [s]
          field_simp [hlogp_ne, hlogD_ne, hlogz_ne]
        linarith
      · have heq : i = k := by omega
        subst heq
        simp only [htk_eq]
        have hs_ne : s ≠ 0 := hs_pos.ne'
        have hrhs : (K / s) * V k * s = K * V k := by field_simp [hs_ne]
        rw [hrhs]
        exact le_mul_of_one_le_left hVk_nonneg hK
    have habel := abel_algebraic_bound k V t a K s hs_pos hVk_nonneg htk_eq ha0_nn ha_mono hV_ub
    have hsum_int : ∑ i ∈ Finset.range k, a i * (t i - t (i + 1)) ≤
        ∫ x in s..M, φ (x - 1) := by
      have hpiece : ∑ i ∈ Finset.range k, a i * (t i - t (i + 1)) ≤
          ∑ i ∈ Finset.range k, ∫ x in (t (i + 1))..(t i), φ (x - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i < k := Finset.mem_range.mp hi
        have hti_le := ht_anti i hik
        have hc : a i * (t i - t (i + 1)) = ∫ _ in (t (i + 1))..(t i), a i := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        rw [hc]
        refine intervalIntegral.integral_mono_on hti_le intervalIntegrable_const
          (hshift_int (t (i + 1)) (t i) (ht_ge2 (i + 1) hik) hti_le) fun x hx => ?_
        have hx1 : 1 ≤ x - 1 := by linarith [ht_ge2 (i + 1) hik, hx.1]
        have hxi : x - 1 ≤ t i - 1 := by linarith [hx.2]
        exact hφ_anti (by simp only [Set.mem_Ici]; exact hx1)
          (by simp only [Set.mem_Ici]; exact hx1.trans hxi) hxi
      have htele := sum_range_integral_telescope k t (fun x => φ (x - 1)) ht_ge2 ht_anti hshift_int
      rw [htk_eq] at htele
      have ht0_ge_s : s ≤ t 0 := by
        rw [← htk_eq]
        exact t_chain_le_zero k t ht_anti
      have htail_le : ∫ x in s..(t 0), φ (x - 1) ≤ ∫ x in s..M, φ (x - 1) := by
        rcases le_or_gt (t 0) M with ht0M | hMt0
        · have hadd := integral_add_adjacent_intervals
            (hshift_int s (t 0) hs_ge2 ht0_ge_s) (hshift_int (t 0) M (hs_ge2.trans ht0_ge_s) ht0M)
          have hnn : 0 ≤ ∫ x in (t 0)..M, φ (x - 1) :=
            intervalIntegral.integral_nonneg ht0M fun x hx =>
              hφ_nn (x - 1) (by linarith [hs_ge2, ht0_ge_s, hx.1])
          linarith
        · have hadd := integral_add_adjacent_intervals
            (hshift_int s M hs_ge2 hsM) (hshift_int M (t 0) (hs_ge2.trans hsM) hMt0.le)
          have hzero : ∫ x in M..(t 0), φ (x - 1) = 0 := by
            have hEq : EqOn (fun x => φ (x - 1)) (fun _ => 0) (uIcc M (t 0)) := by
              intro x hx
              rw [uIcc_of_le hMt0.le] at hx
              exact hφ_supp x hx.1
            rw [integral_congr hEq, intervalIntegral.integral_zero]
          linarith
      exact hpiece.trans (htele.le.trans htail_le)
    have hbracket : (K - 1) * a k + (K / s) * ∑ i ∈ Finset.range k, a i * (t i - t (i + 1)) ≤
        (K - 1) * φ (s - 1) + (K / s) * ∫ x in s..M, φ (x - 1) := by
      have ha_k : a k = φ (s - 1) := by simp [a, htk_eq]
      rw [ha_k]
      have hK_div : 0 ≤ K / s := by positivity
      linarith [mul_le_mul_of_nonneg_left hsum_int hK_div]
    rw [← hVk_eq]
    exact habel.trans (mul_le_mul_of_nonneg_left hbracket hVk_nonneg)

end

end BuchstabSwitching
