import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Buchstab Functions `F, f`: Recursive Construction, Delay Equations, and Closed Forms

Formalizes the stepwise recursive construction `buchstabPairAux`, `buchstabPair`, `buchstabF`,
`buchstabf`, continuity on `(0, ∞)`, the delay integral equations for `2 ≤ a ≤ s`, the BJS
Lemma 19 / Cai Lemma 2 closed forms on `[2, 4]`, `[3, 5]`, and `[4, 6]`, and scaling linearity
in `c`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter
open scoped Topology

section BuchstabFunctions

private theorem continuousOn_Ioc_union_Icc {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (h1 : ContinuousOn g (Set.Ioc 0 a)) (h2 : ContinuousOn g (Set.Icc a b)) :
    ContinuousOn g (Set.Ioc 0 a ∪ Set.Icc a b) := by
  intro x hx
  refine .union ?_ ?_
  · by_cases hx1 : x ∈ Set.Ioc 0 a
    · exact h1 x hx1
    · refine continuousWithinAt_of_notMem_closure ?_
      rw [closure_Ioc ha.ne]
      simp only [Set.mem_Ioc, not_and, not_le] at hx1
      rcases hx with hx0 | hxab
      · exact False.elim ((hx1 hx0.1).not_ge hx0.2)
      · rintro ⟨_, hxa⟩
        exact (hx1 (lt_of_lt_of_le ha hxab.1)).not_ge hxa
  · by_cases hx2 : x ∈ Set.Icc a b
    · exact h2 x hx2
    · refine continuousWithinAt_of_notMem_closure ?_
      rwa [isClosed_Icc.closure_eq]

/-- Stepwise recursive auxiliary construction for the Buchstab pair `(F, f)` valid on `(-∞, n + 2]`. -/
noncomputable def buchstabPairAux (c : ℝ) : ℕ → ℝ → ℝ × ℝ
  | 0, s => if s ≤ 0 then (0, 0) else (c / s, 0)
  | n + 1, s =>
    let prev := buchstabPairAux c n
    if s ≤ (n : ℝ) + 2 then prev s
    else if n = 0 then
      (c / s, (1 / s) * ∫ t in (2 : ℝ)..s, (prev (t - 1)).1)
    else
      let k : ℝ := (n : ℝ) + 2
      ((k * (prev k).1 + ∫ t in k..s, (prev (t - 1)).2) / s,
       (k * (prev k).2 + ∫ t in k..s, (prev (t - 1)).1) / s)

/-- The Buchstab pair `(F(c, s), f(c, s))`. -/
noncomputable def buchstabPair (c s : ℝ) : ℝ × ℝ :=
  buchstabPairAux c (Nat.ceil s) s

/-- Upper Buchstab function `F(c, s)` (with parameter `c > 0`, where `c = 2 e^γ` is canonical). -/
noncomputable def buchstabF (c s : ℝ) : ℝ := (buchstabPair c s).1

/-- Lower Buchstab function `f(c, s)` (with parameter `c > 0`, where `c = 2 e^γ` is canonical). -/
noncomputable def buchstabf (c s : ℝ) : ℝ := (buchstabPair c s).2

theorem buchstabPairAux_eq_of_le {c : ℝ} :
    ∀ {m n : ℕ} {s : ℝ}, s ≤ (m : ℝ) + 2 → m ≤ n →
      buchstabPairAux c n s = buchstabPairAux c m s := by
  intro m n s hsm hmn
  induction n with
  | zero =>
    have hm0 : m = 0 := Nat.le_zero.mp hmn
    subst hm0
    rfl
  | succ n ih =>
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · rfl
    · have hmn' : m ≤ n := Nat.lt_succ_iff.mp hlt
      have hsn : s ≤ (n : ℝ) + 2 := by
        have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn'
        linarith
      conv_lhs => rw [buchstabPairAux]
      split_ifs with h
      · exact ih hmn'
      · exact absurd hsn h

private theorem buchstabPairAux_step_eq (c : ℝ) (n : ℕ) {s : ℝ}
    (hs : ¬ s ≤ (n : ℝ) + 2) (hn : n ≠ 0) :
    buchstabPairAux c (n + 1) s =
      let prev := buchstabPairAux c n
      let k : ℝ := (n : ℝ) + 2
      ((k * (prev k).1 + ∫ t in k..s, (prev (t - 1)).2) / s,
       (k * (prev k).2 + ∫ t in k..s, (prev (t - 1)).1) / s) := by
  conv_lhs => rw [buchstabPairAux]
  split_ifs <;> first | contradiction | rfl

theorem buchstabPair_eq_aux {c : ℝ} {n : ℕ} {s : ℝ} (hs : s ≤ (n : ℝ) + 2) :
    buchstabPair c s = buchstabPairAux c n s := by
  unfold buchstabPair
  have hceil : s ≤ (Nat.ceil s : ℝ) + 2 := by
    have := Nat.le_ceil s
    linarith
  have h1 := buchstabPairAux_eq_of_le (c := c) hs (le_max_left n (Nat.ceil s))
  have h2 := buchstabPairAux_eq_of_le (c := c) hceil (le_max_right n (Nat.ceil s))
  exact h2.symm.trans h1

theorem buchstabF_le_zero (c : ℝ) {s : ℝ} (hs : s ≤ 0) : buchstabF c s = 0 := by
  unfold buchstabF
  rw [buchstabPair_eq_aux (n := 0) (by linarith)]
  simp [buchstabPairAux, hs]

theorem buchstabf_le_two (c : ℝ) {s : ℝ} (hs : s ≤ 2) : buchstabf c s = 0 := by
  unfold buchstabf
  rw [buchstabPair_eq_aux (n := 0) (by linarith)]
  simp only [buchstabPairAux]
  split_ifs <;> rfl

theorem buchstabF_on_zero_two (c : ℝ) {s : ℝ} (hs0 : 0 < s) (hs2 : s ≤ 2) :
    buchstabF c s = c / s := by
  unfold buchstabF
  rw [buchstabPair_eq_aux (n := 0) (by linarith)]
  have hnot : ¬ s ≤ 0 := not_le.mpr hs0
  simp [buchstabPairAux, hnot]

theorem buchstabF_on_zero_three (c : ℝ) {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) :
    buchstabF c s = c / s := by
  by_cases hs2 : s ≤ 2
  · exact buchstabF_on_zero_two c hs0 hs2
  · unfold buchstabF
    rw [buchstabPair_eq_aux (n := 1) (by norm_num; exact hs3)]
    simp [buchstabPairAux, hs2]

theorem buchstabf_on_two_three (c : ℝ) {s : ℝ} (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    buchstabf c s = (1 / s) * ∫ t in (2 : ℝ)..s, buchstabF c (t - 1) := by
  by_cases hlt : 2 < s
  · unfold buchstabf
    rw [buchstabPair_eq_aux (n := 1) (by norm_num; exact hs3)]
    have hnot : ¬ s ≤ ((0 : ℕ) : ℝ) + 2 := by norm_num; linarith
    conv_lhs => rw [buchstabPairAux]
    split_ifs with h1 h2
    · exact absurd h1 hnot
    · dsimp only
      congr 1
      refine integral_congr fun t ht => ?_
      rw [uIcc_of_le hs2] at ht
      have ht1 : t - 1 ≤ ((0 : ℕ) : ℝ) + 2 := by norm_num; linarith [ht.2]
      unfold buchstabF
      rw [buchstabPair_eq_aux (n := 0) ht1]
    · exact absurd rfl h2
  · have heq : s = 2 := le_antisymm (le_of_not_gt hlt) hs2
    subst heq
    rw [buchstabf_le_two c (le_refl 2), integral_same, mul_zero]

theorem buchstabF_step (c : ℝ) {k : ℕ} (hk : 3 ≤ k) {s : ℝ}
    (hks : (k : ℝ) < s) (hs : s ≤ (k : ℝ) + 1) :
    buchstabF c s = ((k : ℝ) * buchstabF c k + ∫ t in (k : ℝ)..s, buchstabf c (t - 1)) / s := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  unfold buchstabF
  have hs' : s ≤ ((m + 2 : ℕ) : ℝ) + 2 := by push_cast at hs ⊢; linarith
  rw [buchstabPair_eq_aux (n := m + 2) hs']
  have hnot : ¬ s ≤ ((m + 1 : ℕ) : ℝ) + 2 := by push_cast at hks ⊢; linarith
  have hm0 : m + 1 ≠ 0 := by omega
  rw [buchstabPairAux_step_eq c (m + 1) hnot hm0]
  dsimp only
  have hk_cast : ((m + 1 : ℕ) : ℝ) + 2 = ((m + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [hk_cast]
  have hFk : (buchstabPairAux c (m + 1) ((m + 3 : ℕ) : ℝ)).1 = buchstabF c ((m + 3 : ℕ) : ℝ) := by
    unfold buchstabF
    rw [buchstabPair_eq_aux (n := m + 1) (by push_cast; linarith)]
  rw [hFk]
  congr 2
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hks.le] at ht
  unfold buchstabf
  rw [buchstabPair_eq_aux (n := m + 1) (by push_cast at ht hs ⊢; linarith [ht.2, hs])]

theorem buchstabf_step (c : ℝ) {k : ℕ} (hk : 3 ≤ k) {s : ℝ}
    (hks : (k : ℝ) < s) (hs : s ≤ (k : ℝ) + 1) :
    buchstabf c s = ((k : ℝ) * buchstabf c k + ∫ t in (k : ℝ)..s, buchstabF c (t - 1)) / s := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  unfold buchstabf
  have hs' : s ≤ ((m + 2 : ℕ) : ℝ) + 2 := by push_cast at hs ⊢; linarith
  rw [buchstabPair_eq_aux (n := m + 2) hs']
  have hnot : ¬ s ≤ ((m + 1 : ℕ) : ℝ) + 2 := by push_cast at hks ⊢; linarith
  have hm0 : m + 1 ≠ 0 := by omega
  rw [buchstabPairAux_step_eq c (m + 1) hnot hm0]
  dsimp only
  have hk_cast : ((m + 1 : ℕ) : ℝ) + 2 = ((m + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [hk_cast]
  have hfk : (buchstabPairAux c (m + 1) ((m + 3 : ℕ) : ℝ)).2 = buchstabf c ((m + 3 : ℕ) : ℝ) := by
    unfold buchstabf
    rw [buchstabPair_eq_aux (n := m + 1) (by push_cast; linarith)]
  rw [hfk]
  congr 2
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hks.le] at ht
  unfold buchstabF
  rw [buchstabPair_eq_aux (n := m + 1) (by push_cast at ht hs ⊢; linarith [ht.2, hs])]

theorem buchstabF_step_all (c : ℝ) {k : ℕ} (hk : 2 ≤ k) {s : ℝ}
    (hks : (k : ℝ) ≤ s) (hs : s ≤ (k : ℝ) + 1) :
    buchstabF c s = ((k : ℝ) * buchstabF c k + ∫ t in (k : ℝ)..s, buchstabf c (t - 1)) / s := by
  have hk0 : (0 : ℝ) < k := by positivity
  rcases eq_or_lt_of_le hks with rfl | hlt
  · rw [integral_same, add_zero]
    field_simp
  · by_cases hk2 : k = 2
    · subst hk2
      push_cast at hlt hs ⊢
      have hs3 : s ≤ 3 := by linarith
      have hF2 : buchstabF c 2 = c / 2 := buchstabF_on_zero_two c (by norm_num) (le_refl 2)
      have hFs : buchstabF c s = c / s := buchstabF_on_zero_three c (by linarith) hs3
      have hEq : EqOn (fun t => buchstabf c (t - 1)) (fun _ => 0) (uIcc (2 : ℝ) s) := by
        intro t ht
        rw [uIcc_of_le hlt.le] at ht
        exact buchstabf_le_two c (by linarith [ht.2])
      rw [hFs, hF2, integral_congr hEq, intervalIntegral.integral_zero]
      field_simp
      ring
    · exact buchstabF_step c (by omega) hlt hs

theorem buchstabf_step_all (c : ℝ) {k : ℕ} (hk : 2 ≤ k) {s : ℝ}
    (hks : (k : ℝ) ≤ s) (hs : s ≤ (k : ℝ) + 1) :
    buchstabf c s = ((k : ℝ) * buchstabf c k + ∫ t in (k : ℝ)..s, buchstabF c (t - 1)) / s := by
  have hk0 : (0 : ℝ) < k := by positivity
  rcases eq_or_lt_of_le hks with rfl | hlt
  · rw [integral_same, add_zero]
    field_simp
  · by_cases hk2 : k = 2
    · subst hk2
      push_cast at hlt hs ⊢
      have hs3 : s ≤ 3 := by linarith
      rw [buchstabf_le_two c (le_refl 2), buchstabf_on_two_three c hlt.le hs3]
      ring
    · exact buchstabf_step c (by omega) hlt hs

private theorem buchstab_continuousOn_Ioc_aux (c : ℝ) :
    ∀ n : ℕ,
      ContinuousOn (buchstabF c) (Set.Ioc 0 ((n : ℝ) + 2)) ∧
      ContinuousOn (buchstabf c) (Set.Ioc 0 ((n : ℝ) + 2)) := by
  intro n
  induction n with
  | zero =>
    constructor
    · refine ((continuousOn_const (c := c)).div continuousOn_id fun x hx =>
        ne_of_gt (Set.mem_Ioc.mp hx).1).congr ?_
      intro x hx
      have hx' := Set.mem_Ioc.mp hx
      exact buchstabF_on_zero_two c hx'.1 (by norm_num at hx'; exact hx'.2)
    · refine (continuousOn_const (c := (0 : ℝ))).congr ?_
      intro x hx
      have hx' := Set.mem_Ioc.mp hx
      exact buchstabf_le_two c (by norm_num at hx'; exact hx'.2)
  | succ n ih =>
    have hF_prev := ih.1
    have hf_prev := ih.2
    have hF_sub : ContinuousOn (fun t => buchstabF c (t - 1)) (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
      refine hF_prev.comp (continuousOn_id.sub continuousOn_const) fun t ht => ?_
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hf_sub : ContinuousOn (fun t => buchstabf c (t - 1)) (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
      refine hf_prev.comp (continuousOn_id.sub continuousOn_const) fun t ht => ?_
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hI_F : ContinuousOn (fun s => ∫ t in ((n : ℝ) + 2)..s, buchstabF c (t - 1))
        (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
      have hint : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume ((n : ℝ) + 2) ((n : ℝ) + 3) :=
        hF_sub.intervalIntegrable_of_Icc (by linarith)
      simpa [uIcc_of_le (by linarith : (n : ℝ) + 2 ≤ (n : ℝ) + 3)] using
        intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    have hI_f : ContinuousOn (fun s => ∫ t in ((n : ℝ) + 2)..s, buchstabf c (t - 1))
        (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
      have hint : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume ((n : ℝ) + 2) ((n : ℝ) + 3) :=
        hf_sub.intervalIntegrable_of_Icc (by linarith)
      simpa [uIcc_of_le (by linarith : (n : ℝ) + 2 ≤ (n : ℝ) + 3)] using
        intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    have hk : 2 ≤ n + 2 := by omega
    have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hR_F : ContinuousOn (buchstabF c) (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
      let G : ℝ → ℝ := fun s =>
        (((n : ℝ) + 2) * buchstabF c ((n : ℝ) + 2) +
          ∫ t in ((n : ℝ) + 2)..s, buchstabf c (t - 1)) / s
      have hG : ContinuousOn G (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
        refine ContinuousOn.div ?_ continuousOn_id fun x hx => by linarith [hx.1]
        exact continuousOn_const.add hI_f
      refine hG.congr ?_
      intro x hx
      have hx1 : ((n + 2 : ℕ) : ℝ) ≤ x := by rw [hcast]; exact hx.1
      have hx2 : x ≤ ((n + 2 : ℕ) : ℝ) + 1 := by rw [hcast]; linarith [hx.2]
      have hx' := buchstabF_step_all c hk hx1 hx2
      dsimp [G]
      rwa [← hcast]
    have hR_f : ContinuousOn (buchstabf c) (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
      let g : ℝ → ℝ := fun s =>
        (((n : ℝ) + 2) * buchstabf c ((n : ℝ) + 2) +
          ∫ t in ((n : ℝ) + 2)..s, buchstabF c (t - 1)) / s
      have hg : ContinuousOn g (Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) := by
        refine ContinuousOn.div ?_ continuousOn_id fun x hx => by linarith [hx.1]
        exact continuousOn_const.add hI_F
      refine hg.congr ?_
      intro x hx
      have hx1 : ((n + 2 : ℕ) : ℝ) ≤ x := by rw [hcast]; exact hx.1
      have hx2 : x ≤ ((n + 2 : ℕ) : ℝ) + 1 := by rw [hcast]; linarith [hx.2]
      have hx' := buchstabf_step_all c hk hx1 hx2
      dsimp [g]
      rwa [← hcast]
    have hcov : Set.Ioc (0 : ℝ) (((n + 1 : ℕ) : ℝ) + 2) =
        Set.Ioc 0 ((n : ℝ) + 2) ∪ Set.Icc ((n : ℝ) + 2) ((n : ℝ) + 3) := by
      ext x
      simp only [Set.mem_Ioc, Set.mem_union, Set.mem_Icc, Nat.cast_succ]
      constructor
      · rintro ⟨hx0, hx3⟩
        rcases le_or_gt x ((n : ℝ) + 2) with hx2 | hx2
        · exact Or.inl ⟨hx0, hx2⟩
        · exact Or.inr ⟨hx2.le, by linarith⟩
      · rintro (⟨hx0, hx2⟩ | ⟨hx2, hx3⟩)
        · exact ⟨hx0, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
    rw [hcov]
    exact ⟨continuousOn_Ioc_union_Icc (by positivity) hF_prev hR_F,
      continuousOn_Ioc_union_Icc (by positivity) hf_prev hR_f⟩

theorem buchstabF_continuousOn (c : ℝ) : ContinuousOn (buchstabF c) (Set.Ioi 0) := by
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_gt s
  have hcont := (buchstab_continuousOn_Ioc_aux c n).1
  have hmem : s ∈ Set.Ioo (0 : ℝ) ((n : ℝ) + 2) := ⟨hs, by linarith⟩
  have hca : ContinuousAt (buchstabF c) s :=
    hcont.continuousAt (Ioc_mem_nhds hmem.1 hmem.2)
  exact hca.continuousWithinAt

theorem buchstabf_continuousOn (c : ℝ) : ContinuousOn (buchstabf c) (Set.Ioi 0) := by
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_gt s
  have hcont := (buchstab_continuousOn_Ioc_aux c n).2
  have hmem : s ∈ Set.Ioo (0 : ℝ) ((n : ℝ) + 2) := ⟨hs, by linarith⟩
  have hca : ContinuousAt (buchstabf c) s :=
    hcont.continuousAt (Ioc_mem_nhds hmem.1 hmem.2)
  exact hca.continuousWithinAt

theorem buchstabF_continuousOn_two (c : ℝ) : ContinuousOn (buchstabF c) (Set.Ici 2) :=
  (buchstabF_continuousOn c).mono fun _ hx => by simp only [Set.mem_Ioi]; linarith [Set.mem_Ici.mp hx]

theorem buchstabf_continuousOn_two (c : ℝ) : ContinuousOn (buchstabf c) (Set.Ici 2) :=
  (buchstabf_continuousOn c).mono fun _ hx => by simp only [Set.mem_Ioi]; linarith [Set.mem_Ici.mp hx]

theorem buchstab_intervalIntegrable_shift {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0)) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t => g (t - 1)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine hg.comp (continuousOn_id.sub continuousOn_const) fun t ht => ?_
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ioi] <;> linarith

theorem buchstabF_integral_eq_from_two (c : ℝ) {s : ℝ} (hs : 2 ≤ s) :
    s * buchstabF c s - 2 * buchstabF c 2 = ∫ t in (2 : ℝ)..s, buchstabf c (t - 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (s - 2)
  have hsN : s ≤ (N : ℝ) + 2 := by linarith
  clear hN
  induction N generalizing s with
  | zero =>
    have heq : s = 2 := le_antisymm (by simpa using hsN) hs
    subst heq
    simp
  | succ N ih =>
    by_cases hle : s ≤ (N : ℝ) + 2
    · exact ih hs hle
    · have hgt : (N : ℝ) + 2 < s := lt_of_not_ge hle
      have hN2 : 2 ≤ N + 2 := by omega
      have hstep := buchstabF_step_all c hN2 (by push_cast; exact hgt.le) (by push_cast at hsN ⊢; linarith)
      have hs0 : 0 < s := by linarith
      have hsEq : s * buchstabF c s = ((N + 2 : ℕ) : ℝ) * buchstabF c ((N + 2 : ℕ) : ℝ) +
          ∫ t in ((N + 2 : ℕ) : ℝ)..s, buchstabf c (t - 1) := by
        rw [hstep]
        field_simp
      have ihN := ih (s := ((N + 2 : ℕ) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
      have hi1 : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume 2 ((N + 2 : ℕ) : ℝ) :=
        buchstab_intervalIntegrable_shift (buchstabf_continuousOn c) (by norm_num) (by push_cast; linarith)
      have hi2 : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume ((N + 2 : ℕ) : ℝ) s :=
        buchstab_intervalIntegrable_shift (buchstabf_continuousOn c) (by push_cast; linarith) (by linarith)
      have hadd := integral_add_adjacent_intervals hi1 hi2
      linarith

theorem buchstabf_integral_eq_from_two (c : ℝ) {s : ℝ} (hs : 2 ≤ s) :
    s * buchstabf c s - 2 * buchstabf c 2 = ∫ t in (2 : ℝ)..s, buchstabF c (t - 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (s - 2)
  have hsN : s ≤ (N : ℝ) + 2 := by linarith
  clear hN
  induction N generalizing s with
  | zero =>
    have heq : s = 2 := le_antisymm (by simpa using hsN) hs
    subst heq
    simp
  | succ N ih =>
    by_cases hle : s ≤ (N : ℝ) + 2
    · exact ih hs hle
    · have hgt : (N : ℝ) + 2 < s := lt_of_not_ge hle
      have hN2 : 2 ≤ N + 2 := by omega
      have hstep := buchstabf_step_all c hN2 (by push_cast; exact hgt.le) (by push_cast at hsN ⊢; linarith)
      have hs0 : 0 < s := by linarith
      have hsEq : s * buchstabf c s = ((N + 2 : ℕ) : ℝ) * buchstabf c ((N + 2 : ℕ) : ℝ) +
          ∫ t in ((N + 2 : ℕ) : ℝ)..s, buchstabF c (t - 1) := by
        rw [hstep]
        field_simp
      have ihN := ih (s := ((N + 2 : ℕ) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
      have hi1 : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume 2 ((N + 2 : ℕ) : ℝ) :=
        buchstab_intervalIntegrable_shift (buchstabF_continuousOn c) (by norm_num) (by push_cast; linarith)
      have hi2 : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume ((N + 2 : ℕ) : ℝ) s :=
        buchstab_intervalIntegrable_shift (buchstabF_continuousOn c) (by push_cast; linarith) (by linarith)
      have hadd := integral_add_adjacent_intervals hi1 hi2
      linarith

/-- Delay integral equation for `F`: for `2 ≤ a ≤ s`,
`s * F(c, s) - a * F(c, a) = ∫ t in a..s, f(c, t - 1)`. -/
theorem buchstabF_integral_eq (c : ℝ) {a s : ℝ} (ha : 2 ≤ a) (has : a ≤ s) :
    s * buchstabF c s - a * buchstabF c a = ∫ t in a..s, buchstabf c (t - 1) := by
  have hs : 2 ≤ s := le_trans ha has
  have h1 := buchstabF_integral_eq_from_two c ha
  have h2 := buchstabF_integral_eq_from_two c hs
  have hi1 : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume 2 a :=
    buchstab_intervalIntegrable_shift (buchstabf_continuousOn c) (by norm_num) (by linarith)
  have hi2 : IntervalIntegrable (fun t => buchstabf c (t - 1)) volume a s :=
    buchstab_intervalIntegrable_shift (buchstabf_continuousOn c) (by linarith) (by linarith)
  have hadd := integral_add_adjacent_intervals hi1 hi2
  linarith

/-- Delay integral equation for `f`: for `2 ≤ a ≤ s`,
`s * f(c, s) - a * f(c, a) = ∫ t in a..s, F(c, t - 1)`. -/
theorem buchstabf_integral_eq (c : ℝ) {a s : ℝ} (ha : 2 ≤ a) (has : a ≤ s) :
    s * buchstabf c s - a * buchstabf c a = ∫ t in a..s, buchstabF c (t - 1) := by
  have hs : 2 ≤ s := le_trans ha has
  have h1 := buchstabf_integral_eq_from_two c ha
  have h2 := buchstabf_integral_eq_from_two c hs
  have hi1 : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume 2 a :=
    buchstab_intervalIntegrable_shift (buchstabF_continuousOn c) (by norm_num) (by linarith)
  have hi2 : IntervalIntegrable (fun t => buchstabF c (t - 1)) volume a s :=
    buchstab_intervalIntegrable_shift (buchstabF_continuousOn c) (by linarith) (by linarith)
  have hadd := integral_add_adjacent_intervals hi1 hi2
  linarith

/-- Exact closed form of `f(c, s)` on `[2, 4]` (BJS Lemma 19 / Cai Lemma 2). -/
theorem buchstabf_eq_on_2_4 (c : ℝ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    buchstabf c s = c * Real.log (s - 1) / s := by
  have hEq := buchstabf_integral_eq_from_two c hs2
  rw [buchstabf_le_two c (le_refl 2), mul_zero, sub_zero] at hEq
  have hcongr : ∫ t in (2 : ℝ)..s, buchstabF c (t - 1) = ∫ t in (2 : ℝ)..s, c * (t - 1)⁻¹ := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hs2] at ht
    rw [buchstabF_on_zero_three c (by linarith [ht.1]) (by linarith [ht.2]), div_eq_mul_inv]
  rw [hcongr, intervalIntegral.integral_const_mul] at hEq
  have hlog : ∫ t in (2 : ℝ)..s, (t - 1)⁻¹ = Real.log (s - 1) := by
    have hderiv : ∀ t ∈ uIcc (2 : ℝ) s, HasDerivAt (fun x : ℝ => Real.log (x - 1)) (t - 1)⁻¹ t := by
      intro t ht
      rw [uIcc_of_le hs2] at ht
      have hsub : HasDerivAt (fun x : ℝ => x - 1) 1 t := by
        simpa using (hasDerivAt_id t).sub_const (1 : ℝ)
      have hlog' := hsub.log (by linarith [ht.1])
      simpa using hlog'
    have hint : IntervalIntegrable (fun t : ℝ => (t - 1)⁻¹) volume 2 s := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (continuousOn_id.sub continuousOn_const).inv₀ fun t ht => ?_
      rw [uIcc_of_le hs2] at ht
      show t - 1 ≠ 0
      linarith [ht.1]
    rw [integral_eq_sub_of_hasDerivAt hderiv hint]
    norm_num
  rw [hlog] at hEq
  have hs0 : 0 < s := by linarith
  calc buchstabf c s = (s * buchstabf c s) / s := by field_simp
    _ = (c * Real.log (s - 1)) / s := by rw [hEq]

/-- Exact closed form of `F(c, s)` on `[3, 5]` (BJS Lemma 19 / Cai Lemma 2). -/
theorem buchstabF_eq_on_3_5 (c : ℝ) {s : ℝ} (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    buchstabF c s = (c / s) * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) := by
  have hEq := buchstabF_integral_eq c (by norm_num : (2 : ℝ) ≤ 3) hs3
  have hF3 : buchstabF c 3 = c / 3 := buchstabF_on_zero_three c (by norm_num) (le_refl 3)
  rw [hF3] at hEq
  have h3c : 3 * (c / 3) = c := by ring
  rw [h3c] at hEq
  have hcongr : ∫ t in (3 : ℝ)..s, buchstabf c (t - 1) =
      ∫ t in (3 : ℝ)..s, c * (Real.log ((t - 1) - 1) / (t - 1)) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hs3] at ht
    rw [buchstabf_eq_on_2_4 c (by linarith [ht.1]) (by linarith [ht.2])]
    ring
  rw [hcongr] at hEq
  have hshift := intervalIntegral.integral_comp_sub_right
    (fun u : ℝ => c * (Real.log (u - 1) / u)) (1 : ℝ) (a := 3) (b := s)
  rw [show (3 : ℝ) - 1 = 2 by norm_num] at hshift
  rw [hshift, intervalIntegral.integral_const_mul] at hEq
  have hs0 : 0 < s := by linarith
  have hnum : s * buchstabF c s = c + c * ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t := by
    linarith
  calc buchstabF c s = (s * buchstabF c s) / s := by field_simp
    _ = (c + c * ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) / s := by rw [hnum]
    _ = (c / s) * (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) := by ring

/-- Exact closed form of `f(c, s)` on `[4, 6]` (BJS Lemma 19 / Cai Lemma 2). -/
theorem buchstabf_eq_on_4_6 (c : ℝ) {s : ℝ} (hs4 : 4 ≤ s) (hs6 : s ≤ 6) :
    buchstabf c s =
      (c / s) * (Real.log (s - 1) +
        ∫ t in (3 : ℝ)..(s - 1), (1 / t) * ∫ u in (2 : ℝ)..(t - 1), Real.log (u - 1) / u) := by
  have hEq := buchstabf_integral_eq c (by norm_num : (2 : ℝ) ≤ 4) hs4
  have hf4 : 4 * buchstabf c 4 = c * Real.log 3 := by
    rw [buchstabf_eq_on_2_4 c (by norm_num) (le_refl 4)]
    norm_num
    ring
  rw [hf4] at hEq
  have hcongr : ∫ t in (4 : ℝ)..s, buchstabF c (t - 1) =
      ∫ t in (4 : ℝ)..s, c * (1 / (t - 1) + (1 / (t - 1)) * ∫ u in (2 : ℝ)..((t - 1) - 1), Real.log (u - 1) / u) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hs4] at ht
    rw [buchstabF_eq_on_3_5 c (by linarith [ht.1]) (by linarith [ht.2])]
    ring
  rw [hcongr] at hEq
  have hshift := intervalIntegral.integral_comp_sub_right
    (fun v : ℝ => c * (1 / v + (1 / v) * ∫ u in (2 : ℝ)..(v - 1), Real.log (u - 1) / u))
    (1 : ℝ) (a := 4) (b := s)
  rw [show (4 : ℝ) - 1 = 3 by norm_num] at hshift
  rw [hshift, intervalIntegral.integral_const_mul] at hEq
  have hi_inner : ContinuousOn (fun v : ℝ => ∫ u in (2 : ℝ)..(v - 1), Real.log (u - 1) / u)
      (Set.Icc 3 (s - 1)) := by
    have hlog : ContinuousOn (fun u : ℝ => Real.log (u - 1) / u) (Set.Icc 2 (s - 2)) := by
      refine ContinuousOn.div ?_ continuousOn_id fun u hu => by linarith [hu.1]
      exact ContinuousOn.log (continuousOn_id.sub continuousOn_const) fun u hu => by
        linarith [hu.1]
    have hint : IntervalIntegrable (fun u : ℝ => Real.log (u - 1) / u) volume 2 (s - 2) :=
      hlog.intervalIntegrable_of_Icc (by linarith)
    have hprim : ContinuousOn (fun w : ℝ => ∫ u in (2 : ℝ)..w, Real.log (u - 1) / u)
        (Set.Icc 2 (s - 2)) := by
      simpa [uIcc_of_le (by linarith : (2 : ℝ) ≤ s - 2)] using
        intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    refine hprim.comp (continuousOn_id.sub continuousOn_const) fun v hv => ?_
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hi1 : IntervalIntegrable (fun v : ℝ => 1 / v) volume 3 (s - 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact continuousOn_const.div continuousOn_id fun v hv => by show v ≠ 0; linarith [hv.1]
  have hi2 : IntervalIntegrable
      (fun v : ℝ => (1 / v) * ∫ u in (2 : ℝ)..(v - 1), Real.log (u - 1) / u) volume 3 (s - 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact (continuousOn_const.div continuousOn_id fun v hv => by show v ≠ 0; linarith [hv.1]).mul hi_inner
  rw [intervalIntegral.integral_add hi1 hi2] at hEq
  have hlogv : ∫ v in (3 : ℝ)..(s - 1), 1 / v = Real.log (s - 1) - Real.log 3 := by
    have hderiv : ∀ v ∈ uIcc (3 : ℝ) (s - 1), HasDerivAt Real.log (1 / v) v := by
      intro v hv
      rw [uIcc_of_le (by linarith)] at hv
      simpa [one_div] using Real.hasDerivAt_log (by linarith [hv.1])
    rw [integral_eq_sub_of_hasDerivAt hderiv hi1]
  rw [hlogv] at hEq
  have hs0 : 0 < s := by linarith
  have hnum : s * buchstabf c s = c * (Real.log (s - 1) +
      ∫ t in (3 : ℝ)..(s - 1), (1 / t) * ∫ u in (2 : ℝ)..(t - 1), Real.log (u - 1) / u) := by
    linarith
  calc buchstabf c s = (s * buchstabf c s) / s := by field_simp
    _ = (c * (Real.log (s - 1) +
          ∫ t in (3 : ℝ)..(s - 1), (1 / t) * ∫ u in (2 : ℝ)..(t - 1), Real.log (u - 1) / u)) / s := by
        rw [hnum]
    _ = (c / s) * (Real.log (s - 1) +
          ∫ t in (3 : ℝ)..(s - 1), (1 / t) * ∫ u in (2 : ℝ)..(t - 1), Real.log (u - 1) / u) := by
        ring

/-- Scaling linearity of `buchstabF` and `buchstabf` in `c`. -/
private theorem buchstabPairAux_smul (c : ℝ) :
    ∀ n s, (buchstabPairAux c n s).1 = c * (buchstabPairAux 1 n s).1 ∧
      (buchstabPairAux c n s).2 = c * (buchstabPairAux 1 n s).2 := by
  intro n
  induction n with
  | zero =>
    intro s
    simp only [buchstabPairAux]
    split_ifs
    · simp
    · simp [div_eq_mul_inv]
  | succ n ih =>
    intro s
    simp only [buchstabPairAux]
    split_ifs with h1 h2
    · exact ih s
    · constructor
      · ring
      · have hcongr : ∫ t in (2 : ℝ)..s, (buchstabPairAux c n (t - 1)).1 =
            ∫ t in (2 : ℝ)..s, c * (buchstabPairAux 1 n (t - 1)).1 := by
          refine integral_congr fun t _ => (ih (t - 1)).1
        rw [hcongr, intervalIntegral.integral_const_mul]
        ring
    · constructor
      · have hcongr : ∫ t in ((n : ℝ) + 2)..s, (buchstabPairAux c n (t - 1)).2 =
            ∫ t in ((n : ℝ) + 2)..s, c * (buchstabPairAux 1 n (t - 1)).2 := by
          refine integral_congr fun t _ => (ih (t - 1)).2
        rw [(ih ((n : ℝ) + 2)).1, hcongr, intervalIntegral.integral_const_mul]
        ring
      · have hcongr : ∫ t in ((n : ℝ) + 2)..s, (buchstabPairAux c n (t - 1)).1 =
            ∫ t in ((n : ℝ) + 2)..s, c * (buchstabPairAux 1 n (t - 1)).1 := by
          refine integral_congr fun t _ => (ih (t - 1)).1
        rw [(ih ((n : ℝ) + 2)).2, hcongr, intervalIntegral.integral_const_mul]
        ring

theorem buchstabF_smul (c s : ℝ) : buchstabF c s = c * buchstabF 1 s :=
  (buchstabPairAux_smul c (Nat.ceil s) s).1

theorem buchstabf_smul (c s : ℝ) : buchstabf c s = c * buchstabf 1 s :=
  (buchstabPairAux_smul c (Nat.ceil s) s).2

end BuchstabFunctions

end BuchstabSwitching
