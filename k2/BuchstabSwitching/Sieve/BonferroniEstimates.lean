import BuchstabSwitching.Sieve.BonferroniHybrid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Bonferroni Hybrid Sieve Estimates, Prime-Omission Monotonicity, and Analytic Tail Bounds

Lifts the combinatorial hybrid `Q₁ × P₂` Bonferroni inequalities from `ℤ` to `ℝ` with a
multiplicative density `g`, proves the shifted `A_q` error bound, establishes prime-omission
monotonicity for `RTrunc` and `V2` (including `V2_ratio_mono`), and proves the analytic
`S₁`-tail bounds used in `bonferroni_engine.py`.
-/

namespace BuchstabSwitching

section Definitions

/-- `k`-th elementary symmetric polynomial of weights `w` over a finite set `T`. -/
noncomputable def elemSym (w : ℕ → ℝ) (T : Finset ℕ) : ℕ → ℝ :=
  fun k => ∑ S ∈ T.powersetCard k, ∏ p ∈ S, w p

/-- Alternating Bonferroni truncation of order `m` for weights `w` over `T`. -/
noncomputable def gTrunc (w : ℕ → ℝ) (T : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * elemSym w T j

/-- Full sieve product `∏ p ∈ T, (1 - w p)`. -/
noncomputable def V2 (w : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∏ p ∈ T, (1 - w p)

/-- Ratio `gTrunc w T m / V2 w T`. -/
noncomputable def RTrunc (w : ℕ → ℝ) (T : Finset ℕ) (m : ℕ) : ℝ :=
  gTrunc w T m / V2 w T

/-- Squarefree moduli arising in the hybrid `Q₁ × P₂` Bonferroni truncation of order `k`. -/
def bonfDivisors (Q₁ P₂ : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Q₁.powerset ×ˢ P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).image
    (fun S => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)

@[simp]
theorem elemSym_zero (w : ℕ → ℝ) (T : Finset ℕ) : elemSym w T 0 = 1 := by
  simp [elemSym]

theorem elemSym_one (w : ℕ → ℝ) (T : Finset ℕ) : elemSym w T 1 = ∑ p ∈ T, w p := by
  simp [elemSym, Finset.powersetCard_one]

theorem elemSym_eq_zero_of_lt {w : ℕ → ℝ} {T : Finset ℕ} {k : ℕ} (hk : T.card < k) :
    elemSym w T k = 0 := by
  simp [elemSym, Finset.powersetCard_eq_empty.mpr hk]

theorem elemSym_nonneg {w : ℕ → ℝ} {T : Finset ℕ} (hw : ∀ p ∈ T, 0 ≤ w p) (k : ℕ) :
    0 ≤ elemSym w T k := by
  refine Finset.sum_nonneg fun S hS => Finset.prod_nonneg fun p hp => ?_
  exact hw p ((Finset.mem_powersetCard.mp hS).1 hp)

@[simp]
theorem V2_empty (w : ℕ → ℝ) : V2 w ∅ = 1 := by
  simp [V2]

theorem V2_insert {w : ℕ → ℝ} {p : ℕ} {T : Finset ℕ} (hp : p ∉ T) :
    V2 w (insert p T) = (1 - w p) * V2 w T := by
  simp [V2, Finset.prod_insert hp]

theorem V2_pos {w : ℕ → ℝ} {T : Finset ℕ} (hw : ∀ p ∈ T, w p < 1) : 0 < V2 w T := by
  refine Finset.prod_pos fun p hp => sub_pos.mpr (hw p hp)

theorem V2_ne_zero {w : ℕ → ℝ} {T : Finset ℕ} (hw : ∀ p ∈ T, w p < 1) : V2 w T ≠ 0 :=
  (V2_pos hw).ne'

@[simp]
theorem gTrunc_empty (w : ℕ → ℝ) (m : ℕ) : gTrunc w ∅ m = 1 := by
  induction m with
  | zero => simp [gTrunc]
  | succ m ih =>
    rw [gTrunc, Finset.sum_range_succ]
    change gTrunc w ∅ m + (-1 : ℝ) ^ (m + 1) * elemSym w ∅ (m + 1) = 1
    rw [ih, elemSym_eq_zero_of_lt (by simp), mul_zero, add_zero]

@[simp]
theorem RTrunc_empty (w : ℕ → ℝ) (m : ℕ) : RTrunc w ∅ m = 1 := by
  simp [RTrunc]

@[simp]
theorem gTrunc_zero (w : ℕ → ℝ) (T : Finset ℕ) : gTrunc w T 0 = 1 := by
  simp [gTrunc]

theorem gTrunc_succ (w : ℕ → ℝ) (T : Finset ℕ) (m : ℕ) :
    gTrunc w T (m + 1) = gTrunc w T m + (-1 : ℝ) ^ (m + 1) * elemSym w T (m + 1) := by
  simpa [gTrunc] using Finset.sum_range_succ (fun j => (-1 : ℝ) ^ j * elemSym w T j) (m + 1)

theorem prod_one_add_eq_sum_elemSym (w : ℕ → ℝ) (T : Finset ℕ) (n : ℕ) (hn : T.card ≤ n) :
    ∏ p ∈ T, (1 + w p) = ∑ j ∈ Finset.range (n + 1), elemSym w T j := by
  rw [Finset.prod_one_add]
  have hfib : ∑ S ∈ T.powerset, ∏ p ∈ S, w p =
      ∑ j ∈ Finset.range (n + 1), ∑ S ∈ T.powerset.filter (fun S => S.card = j), ∏ p ∈ S, w p := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro S hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.card_le_card (Finset.mem_powerset.mp hS)).trans hn))
  rw [hfib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfilt : T.powerset.filter (fun S => S.card = j) = T.powersetCard j := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [hfilt]
  rfl

theorem gTrunc_eq_V2_of_card_le (w : ℕ → ℝ) (T : Finset ℕ) (n : ℕ) (hn : T.card ≤ n) :
    gTrunc w T n = V2 w T := by
  have h := prod_one_add_eq_sum_elemSym (fun p => -w p) T n hn
  have hV2 : ∏ p ∈ T, (1 + -w p) = V2 w T := by
    refine Finset.prod_congr rfl fun p _ => by ring
  rw [hV2] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [elemSym, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.prod_neg, (Finset.mem_powersetCard.mp hS).2]

end Definitions

section Monotonicity

theorem elemSym_insert (w : ℕ → ℝ) {p : ℕ} {T : Finset ℕ} (hp : p ∉ T) (j : ℕ) :
    elemSym w (insert p T) (j + 1) = elemSym w T (j + 1) + w p * elemSym w T j := by
  classical
  simp only [elemSym]
  have hsplit : (insert p T).powersetCard (j + 1) =
      T.powersetCard (j + 1) ∪ (T.powersetCard j).image (insert p) := by
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hST, hcard⟩
      by_cases hpS : p ∈ S
      · right
        refine ⟨S.erase p, ⟨?_, ?_⟩, Finset.insert_erase hpS⟩
        · intro q hq
          have hq' := Finset.mem_erase.mp hq
          exact (Finset.mem_insert.mp (hST hq'.2)).resolve_left hq'.1
        · rw [Finset.card_erase_of_mem hpS, hcard, Nat.add_sub_cancel]
      · left
        refine ⟨fun q hq => (Finset.mem_insert.mp (hST hq)).resolve_left ?_, hcard⟩
        rintro rfl
        exact hpS hq
    · rintro (⟨hST, hcard⟩ | ⟨S', ⟨hS'T, hcard⟩, rfl⟩)
      · exact ⟨hST.trans (Finset.subset_insert p T), hcard⟩
      · have hpS' : p ∉ S' := fun h => hp (hS'T h)
        exact ⟨Finset.insert_subset_insert p hS'T, by rw [Finset.card_insert_of_notMem hpS', hcard]⟩
  have hdisj : Disjoint (T.powersetCard (j + 1)) ((T.powersetCard j).image (insert p)) := by
    rw [Finset.disjoint_left]
    intro S hS₁ hS₂
    rcases Finset.mem_image.mp hS₂ with ⟨S', _, rfl⟩
    exact hp ((Finset.mem_powersetCard.mp hS₁).1 (Finset.mem_insert_self p S'))
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun S' hS' => ?_
    have hpS' : p ∉ S' := fun h => hp ((Finset.mem_powersetCard.mp hS').1 h)
    rw [Finset.prod_insert hpS']
  · intro x hx y hy hxy
    have hpx : p ∉ x := fun h => hp ((Finset.mem_powersetCard.mp hx).1 h)
    have hpy : p ∉ y := fun h => hp ((Finset.mem_powersetCard.mp hy).1 h)
    have h1 := congrArg (fun s : Finset ℕ => s.erase p) hxy
    simpa [Finset.erase_insert hpx, Finset.erase_insert hpy] using h1

theorem gTrunc_insert (w : ℕ → ℝ) {p : ℕ} {T : Finset ℕ} (hp : p ∉ T) (m : ℕ) :
    gTrunc w (insert p T) m =
      (1 - w p) * gTrunc w T m + (-1 : ℝ) ^ m * w p * elemSym w T m := by
  induction m with
  | zero =>
    simp [gTrunc]
  | succ m ih =>
    rw [gTrunc_succ, ih, elemSym_insert w hp m, gTrunc_succ, pow_succ (-1 : ℝ) m]
    ring

theorem RTrunc_insert (w : ℕ → ℝ) {p : ℕ} {T : Finset ℕ} (hp : p ∉ T) (m : ℕ)
    (hw : ∀ q ∈ insert p T, w q < 1) :
    RTrunc w (insert p T) m =
      RTrunc w T m + (-1 : ℝ) ^ m * w p * elemSym w T m / ((1 - w p) * V2 w T) := by
  have h1p : 1 - w p ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hw p (Finset.mem_insert_self p T)))
  have hV2 : V2 w T ≠ 0 := V2_ne_zero fun q hq => hw q (Finset.mem_insert_of_mem hq)
  rw [RTrunc, gTrunc_insert w hp m, V2_insert hp, RTrunc]
  field_simp

private theorem RTrunc_mono_aux {w : ℕ → ℝ} {T' s : Finset ℕ} (hdisj : Disjoint T' s)
    (hw : ∀ p ∈ T' ∪ s, 0 ≤ w p ∧ w p < 1) (m : ℕ) :
    (Odd m → RTrunc w (T' ∪ s) m ≤ RTrunc w T' m) ∧
    (Even m → RTrunc w T' m ≤ RTrunc w (T' ∪ s) m) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert p s hp ih =>
    have hdisj' : Disjoint T' s := Finset.disjoint_of_subset_right (Finset.subset_insert p s) hdisj
    have hpT' : p ∉ T' := fun h => Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self p s)
    have hp_union : p ∉ T' ∪ s := by simp [hpT', hp]
    have hw' : ∀ q ∈ T' ∪ s, 0 ≤ w q ∧ w q < 1 := fun q hq =>
      hw q (by simp only [Finset.mem_union, Finset.mem_insert] at hq ⊢; tauto)
    have hwp : 0 ≤ w p ∧ w p < 1 := hw p (by simp)
    have hV2_pos : 0 < V2 w (T' ∪ s) := V2_pos fun q hq => (hw' q hq).2
    have helem : 0 ≤ elemSym w (T' ∪ s) m := elemSym_nonneg (fun q hq => (hw' q hq).1) m
    have hstep : RTrunc w (insert p (T' ∪ s)) m =
        RTrunc w (T' ∪ s) m +
          (-1 : ℝ) ^ m * w p * elemSym w (T' ∪ s) m / ((1 - w p) * V2 w (T' ∪ s)) :=
      RTrunc_insert w hp_union m fun q hq =>
        (hw q (by simpa [Finset.union_insert] using hq)).2
    have hterm_nonneg : 0 ≤ w p * elemSym w (T' ∪ s) m / ((1 - w p) * V2 w (T' ∪ s)) := by
      refine div_nonneg (mul_nonneg hwp.1 helem) (mul_nonneg (sub_nonneg.mpr hwp.2.le) hV2_pos.le)
    have ih' := ih hdisj' hw'
    rw [Finset.union_insert]
    constructor
    · intro hm
      have hle : RTrunc w (insert p (T' ∪ s)) m ≤ RTrunc w (T' ∪ s) m := by
        rw [hstep, hm.neg_one_pow, neg_one_mul, neg_mul, neg_div]
        linarith
      exact hle.trans (ih'.1 hm)
    · intro hm
      have hle : RTrunc w (T' ∪ s) m ≤ RTrunc w (insert p (T' ∪ s)) m := by
        rw [hstep, hm.neg_one_pow, one_mul]
        linarith
      exact (ih'.2 hm).trans hle

theorem RTrunc_mono_odd {w : ℕ → ℝ} {T' T : Finset ℕ} (hsub : T' ⊆ T) {m : ℕ}
    (hm : Odd m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    RTrunc w T m ≤ RTrunc w T' m := by
  have hunion : T' ∪ (T \ T') = T := Finset.union_sdiff_of_subset hsub
  have hdisj : Disjoint T' (T \ T') := disjoint_sdiff_self_right
  have hw' : ∀ p ∈ T' ∪ (T \ T'), 0 ≤ w p ∧ w p < 1 := by
    rw [hunion]
    exact hw
  simpa [hunion] using (RTrunc_mono_aux hdisj hw' m).1 hm

theorem RTrunc_anti_even {w : ℕ → ℝ} {T' T : Finset ℕ} (hsub : T' ⊆ T) {m : ℕ}
    (hm : Even m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    RTrunc w T' m ≤ RTrunc w T m := by
  have hunion : T' ∪ (T \ T') = T := Finset.union_sdiff_of_subset hsub
  have hdisj : Disjoint T' (T \ T') := disjoint_sdiff_self_right
  have hw' : ∀ p ∈ T' ∪ (T \ T'), 0 ≤ w p ∧ w p < 1 := by
    rw [hunion]
    exact hw
  simpa [hunion] using (RTrunc_mono_aux hdisj hw' m).2 hm

theorem one_le_RTrunc_of_even {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Even m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    1 ≤ RTrunc w T m := by
  simpa [RTrunc_empty] using RTrunc_anti_even (Finset.empty_subset T) hm hw

theorem RTrunc_le_one_of_odd {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Odd m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    RTrunc w T m ≤ 1 := by
  simpa [RTrunc_empty] using RTrunc_mono_odd (Finset.empty_subset T) hm hw

theorem V2_le_gTrunc_of_even {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Even m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    V2 w T ≤ gTrunc w T m := by
  have hV2 : 0 < V2 w T := V2_pos fun p hp => (hw p hp).2
  have hR : 1 ≤ gTrunc w T m / V2 w T := one_le_RTrunc_of_even hm hw
  simpa [one_mul] using (le_div_iff₀ hV2).mp hR

theorem gTrunc_le_V2_of_odd {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Odd m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    gTrunc w T m ≤ V2 w T := by
  have hV2 : 0 < V2 w T := V2_pos fun p hp => (hw p hp).2
  have hR : gTrunc w T m / V2 w T ≤ 1 := RTrunc_le_one_of_odd hm hw
  simpa [one_mul] using (div_le_iff₀ hV2).mp hR

private theorem finset_prod_le_one {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a s)
    have ha1 : f a ≤ 1 := hf1 a (Finset.mem_insert_self a s)
    have hs1 : ∏ i ∈ s, f i ≤ 1 :=
      ih (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
    have hs0 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
    nlinarith

private theorem finset_prod_le_prod {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a s)
    have hag : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
    have hsg : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hag hsg hs0 (ha0.trans hag)

theorem V2_anti {w : ℕ → ℝ} {T' T : Finset ℕ} (hsub : T' ⊆ T)
    (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    V2 w T ≤ V2 w T' := by
  have hprod : V2 w (T \ T') * V2 w T' = V2 w T := by
    simpa [V2] using Finset.prod_sdiff hsub
  have hV2' : 0 < V2 w T' := V2_pos fun p hp => (hw p (hsub hp)).2
  have hsdiff_le : V2 w (T \ T') ≤ 1 := by
    refine finset_prod_le_one (T \ T') (fun p hp => ?_) (fun p hp => ?_)
    · exact sub_nonneg.mpr (hw p (Finset.sdiff_subset hp)).2.le
    · exact sub_le_self 1 (hw p (Finset.sdiff_subset hp)).1
  rw [← hprod]
  exact mul_le_of_le_one_left hV2'.le hsdiff_le

theorem V2_ratio_mono {w : ℕ → ℝ} {A T' T : Finset ℕ} (_hAT : A ⊆ T) (hsub : T' ⊆ T)
    (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    V2 w (T' ∩ A) / V2 w T' ≤ V2 w (T ∩ A) / V2 w T := by
  have hsplit : ∀ S : Finset ℕ, S ⊆ T →
      V2 w (S ∩ A) / V2 w S = (V2 w (S \ A))⁻¹ := by
    intro S hST
    have hprod : V2 w (S ∩ A) * V2 w (S \ A) = V2 w S := by
      simpa [V2] using (Finset.prod_inter_mul_prod_sdiff S A (fun p => 1 - w p))
    have hpos_int : 0 < V2 w (S ∩ A) :=
      V2_pos fun p hp => (hw p (hST (Finset.mem_inter.mp hp).1)).2
    have hpos_diff : 0 < V2 w (S \ A) :=
      V2_pos fun p hp => (hw p (hST (Finset.sdiff_subset hp))).2
    rw [← hprod]
    field_simp
  rw [hsplit T' hsub, hsplit T Finset.Subset.rfl]
  have hdiff_sub : T' \ A ⊆ T \ A := Finset.sdiff_subset_sdiff hsub Finset.Subset.rfl
  have hdiff_pos : 0 < V2 w (T \ A) :=
    V2_pos fun p hp => (hw p (Finset.sdiff_subset hp)).2
  have hdiff_le : V2 w (T \ A) ≤ V2 w (T' \ A) :=
    V2_anti hdiff_sub fun p hp => hw p (Finset.sdiff_subset hp)
  exact inv_anti₀ hdiff_pos hdiff_le

end Monotonicity

section HybridBounds

private theorem prod_primes_dvd_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {n : ℕ} :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    have hq_prime : q.Prime := hS q (Finset.mem_insert_self q S)
    have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ S, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hp_prime : p.Prime := hS_prime p hp
      exact (Nat.coprime_primes hq_prime hp_prime).mpr (fun heq => hq (heq ▸ hp))
    rw [Finset.prod_insert hq]
    constructor
    · intro h
      have hq_dvd : q ∣ n := dvd_trans (dvd_mul_right q _) h
      have hS_dvd : (∏ p ∈ S, p) ∣ n := dvd_trans (dvd_mul_left _ q) h
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpS
      · exact hq_dvd
      · exact (ih hS_prime).mp hS_dvd p hpS
    · intro h
      exact hcop.mul_dvd_of_dvd_of_dvd (h q (Finset.mem_insert_self q S))
        ((ih hS_prime).mpr fun p hp => h p (Finset.mem_insert_of_mem hp))

private theorem prod_primes_mul_dvd_iff {S₁ S₂ : Finset ℕ}
    (hS₁ : ∀ p ∈ S₁, p.Prime) (hS₂ : ∀ p ∈ S₂, p.Prime) (hdisj : Disjoint S₁ S₂) {n : ℕ} :
    (∏ p ∈ S₁, p) * (∏ p ∈ S₂, p) ∣ n ↔ (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n) := by
  have hcop : Nat.Coprime (∏ p ∈ S₁, p) (∏ p ∈ S₂, p) := by
    refine Nat.Coprime.prod_left fun p hp₁ => Nat.Coprime.prod_right fun q hq₂ => ?_
    refine (Nat.coprime_primes (hS₁ p hp₁) (hS₂ q hq₂)).mpr ?_
    intro heq
    exact Finset.disjoint_left.mp hdisj hp₁ (heq ▸ hq₂)
  constructor
  · intro h
    exact ⟨(prod_primes_dvd_iff hS₁).mp (dvd_trans (dvd_mul_right _ _) h),
      (prod_primes_dvd_iff hS₂).mp (dvd_trans (dvd_mul_left _ _) h)⟩
  · rintro ⟨h₁, h₂⟩
    exact hcop.mul_dvd_of_dvd_of_dvd ((prod_primes_dvd_iff hS₁).mpr h₁)
      ((prod_primes_dvd_iff hS₂).mpr h₂)

private theorem prime_mem_of_dvd_prod_primes {p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime) (hdvd : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Nat.dvd_one] at hdvd
    exact absurd hdvd hp.ne_one
  | @insert q S hq ih =>
    rw [Finset.prod_insert hq] at hdvd
    rcases hp.dvd_mul.mp hdvd with hpq | hpS
    · have hq_prime : q.Prime := hS q (Finset.mem_insert_self q S)
      rcases (Nat.dvd_prime hq_prime).mp hpq with rfl | rfl
      · exact absurd rfl hp.ne_one
      · exact Finset.mem_insert_self p S
    · exact Finset.mem_insert_of_mem (ih (fun r hr => hS r (Finset.mem_insert_of_mem hr)) hpS)

private theorem injOn_prod_primes_mul {Q₁ P₂ : Finset ℕ}
    (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime) (hdisj : Disjoint Q₁ P₂) :
    Set.InjOn (fun S : Finset ℕ × Finset ℕ => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)
      (Q₁.powerset ×ˢ P₂.powerset : Finset (Finset ℕ × Finset ℕ)) := by
  intro S hS T hT hEq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset] at hS hT
  have hmem_of_dvd : ∀ {A₁ A₂ B₁ B₂ : Finset ℕ},
      A₁ ⊆ Q₁ → A₂ ⊆ P₂ → B₁ ⊆ Q₁ → B₂ ⊆ P₂ →
      (∏ p ∈ A₁, p) * ∏ p ∈ A₂, p = (∏ p ∈ B₁, p) * ∏ p ∈ B₂, p →
      A₁ ⊆ B₁ ∧ A₂ ⊆ B₂ := by
    intro A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hAB
    have hdvd : (∏ p ∈ A₁, p) * ∏ p ∈ A₂, p ∣ (∏ p ∈ B₁, p) * ∏ p ∈ B₂, p :=
      dvd_of_eq hAB
    have hdisjA : Disjoint A₁ A₂ := hdisj.mono hA₁ hA₂
    have hAB_all := (prod_primes_mul_dvd_iff (fun p hp => hQ₁ p (hA₁ hp))
      (fun p hp => hP₂ p (hA₂ hp)) hdisjA).mp hdvd
    constructor
    · intro p hpA₁
      have hp_prime : p.Prime := hQ₁ p (hA₁ hpA₁)
      have hpdvd : p ∣ (∏ q ∈ B₁, q) * ∏ q ∈ B₂, q := hAB_all.1 p hpA₁
      rcases hp_prime.dvd_mul.mp hpdvd with h₁ | h₂
      · exact prime_mem_of_dvd_prod_primes hp_prime (fun q hq => hQ₁ q (hB₁ hq)) h₁
      · have hpB₂ := prime_mem_of_dvd_prod_primes hp_prime (fun q hq => hP₂ q (hB₂ hq)) h₂
        exact absurd (hB₂ hpB₂) (Finset.disjoint_left.mp hdisj (hA₁ hpA₁))
    · intro p hpA₂
      have hp_prime : p.Prime := hP₂ p (hA₂ hpA₂)
      have hpdvd : p ∣ (∏ q ∈ B₁, q) * ∏ q ∈ B₂, q := hAB_all.2 p hpA₂
      rcases hp_prime.dvd_mul.mp hpdvd with h₁ | h₂
      · have hpB₁ := prime_mem_of_dvd_prod_primes hp_prime (fun q hq => hQ₁ q (hB₁ hq)) h₁
        exact absurd (hA₂ hpA₂) (Finset.disjoint_left.mp hdisj (hB₁ hpB₁))
      · exact prime_mem_of_dvd_prod_primes hp_prime (fun q hq => hP₂ q (hB₂ hq)) h₂
  have h1 := hmem_of_dvd hS.1 hS.2 hT.1 hT.2 hEq
  have h2 := hmem_of_dvd hT.1 hT.2 hS.1 hS.2 hEq.symm
  ext1
  · exact Finset.Subset.antisymm h1.1 h2.1
  · exact Finset.Subset.antisymm h1.2 h2.2

theorem sum_bonfDivisors_eq {Q₁ P₂ : Finset ℕ} {k : ℕ}
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (f : ℕ → ℝ) :
    ∑ d ∈ bonfDivisors Q₁ P₂ k, f d =
      ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        f ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
  have hinj : Set.InjOn (fun S : Finset ℕ × Finset ℕ => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)
      ((Q₁.powerset ×ˢ P₂.powerset.filter (fun S₂ => S₂.card ≤ k)) :
        Finset (Finset ℕ × Finset ℕ)) := by
    refine (injOn_prod_primes_mul hQ₁ hP₂ hdisj).mono ?_
    intro S hS
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.1⟩
  rw [bonfDivisors, Finset.sum_image hinj, Finset.sum_product]

theorem card_bonfDivisors {Q₁ P₂ : Finset ℕ} {k : ℕ}
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime) :
    (bonfDivisors Q₁ P₂ k).card =
      2 ^ Q₁.card * ∑ j ∈ Finset.range (k + 1), P₂.card.choose j := by
  have hinj : Set.InjOn (fun S : Finset ℕ × Finset ℕ => (∏ p ∈ S.1, p) * ∏ p ∈ S.2, p)
      ((Q₁.powerset ×ˢ P₂.powerset.filter (fun S₂ => S₂.card ≤ k)) :
        Finset (Finset ℕ × Finset ℕ)) := by
    refine (injOn_prod_primes_mul hQ₁ hP₂ hdisj).mono ?_
    intro S hS
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.1⟩
  rw [bonfDivisors, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_powerset]
  congr 1
  have hfib : (P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).card =
      ∑ j ∈ Finset.range (k + 1),
        ((P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).filter (fun S₂ => S₂.card = j)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun S₂ hS₂ => ?_
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp (Finset.mem_coe.mp hS₂)).2)
  rw [hfib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfilt : (P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).filter (fun S₂ => S₂.card = j) =
      P₂.powersetCard j := by
    ext S₂
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hS₂, _⟩, rfl⟩; exact ⟨hS₂, rfl⟩
    · rintro ⟨hS₂, rfl⟩; exact ⟨⟨hS₂, hjk⟩, rfl⟩
  rw [hfilt, Finset.card_powersetCard]

theorem bonferroni_hybrid_main_term (Q₁ P₂ : Finset ℕ) (g : ℕ → ℝ) (k : ℕ)
    (hg : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ P₂,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p) :
    (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
      (-1 : ℝ) ^ (S₁.card + S₂.card) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) =
      V2 g Q₁ * gTrunc g P₂ k := by
  have hcongr : ∀ S₁ ∈ Q₁.powerset,
      (∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        (-1 : ℝ) ^ (S₁.card + S₂.card) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) =
      ((-1 : ℝ) ^ S₁.card * ∏ p ∈ S₁, g p) *
        ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
          (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p := by
    intro S₁ hS₁
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    rw [hg S₁ (Finset.mem_powerset.mp hS₁) S₂
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1), pow_add]
    ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
  congr 1
  · have hV2 : V2 g Q₁ = ∏ p ∈ Q₁, (1 + -g p) := by
      refine Finset.prod_congr rfl fun p _ => by ring
    rw [hV2, Finset.prod_one_add]
    refine Finset.sum_congr rfl fun S₁ _ => ?_
    rw [Finset.prod_neg]
  · have hfib : ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p =
        ∑ j ∈ Finset.range (k + 1),
          ∑ S₂ ∈ (P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).filter (fun S₂ => S₂.card = j),
            (-1 : ℝ) ^ S₂.card * ∏ p ∈ S₂, g p := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S₂ hS₂
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS₂).2)
    rw [hfib, gTrunc]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hfilt : (P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).filter (fun S₂ => S₂.card = j) =
        P₂.powersetCard j := by
      ext S₂
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hS₂, _⟩, rfl⟩; exact ⟨hS₂, rfl⟩
      · rintro ⟨hS₂, rfl⟩; exact ⟨⟨hS₂, hjk⟩, rfl⟩
    rw [hfilt, elemSym, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    rw [(Finset.mem_powersetCard.mp hS₂).2]

theorem sum_bonfDivisors_density (Q₁ P₂ : Finset ℕ) (g : ℕ → ℝ) (k : ℕ)
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (hg : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ P₂,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p) :
    ∑ d ∈ bonfDivisors Q₁ P₂ k, g d =
      (∏ p ∈ Q₁, (1 + g p)) * ∑ j ∈ Finset.range (k + 1), elemSym g P₂ j := by
  rw [sum_bonfDivisors_eq hdisj hQ₁ hP₂ g]
  have hcongr : ∀ S₁ ∈ Q₁.powerset,
      (∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k), g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) =
      (∏ p ∈ S₁, g p) * ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k), ∏ p ∈ S₂, g p := by
    intro S₁ hS₁
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    exact hg S₁ (Finset.mem_powerset.mp hS₁) S₂
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1)
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul, Finset.prod_one_add]
  congr 1
  have hfib : ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k), ∏ p ∈ S₂, g p =
      ∑ j ∈ Finset.range (k + 1),
        ∑ S₂ ∈ (P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).filter (fun S₂ => S₂.card = j),
          ∏ p ∈ S₂, g p := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro S₂ hS₂
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS₂).2)
  rw [hfib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfilt : (P₂.powerset.filter (fun S₂ => S₂.card ≤ k)).filter (fun S₂ => S₂.card = j) =
      P₂.powersetCard j := by
    ext S₂
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hS₂, _⟩, rfl⟩; exact ⟨hS₂, rfl⟩
    · rintro ⟨hS₂, rfl⟩; exact ⟨⟨hS₂, hjk⟩, rfl⟩
  rw [hfilt]
  rfl

private theorem bonferroni_hybrid_real_identity (A Q₁ P₂ : Finset ℕ) (g : ℕ → ℝ) (k : ℕ)
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (hg : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ P₂,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p) :
    (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
      (-1 : ℝ) ^ (S₁.card + S₂.card) *
        ((A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n))).card : ℝ)) =
      (A.card : ℝ) * V2 g Q₁ * gTrunc g P₂ k +
        ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
          (-1 : ℝ) ^ (S₁.card + S₂.card) *
            (((A.filter (fun n => ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) ∣ n)).card : ℝ) -
              (A.card : ℝ) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) := by
  have hsplit : ∀ S₁ ∈ Q₁.powerset,
      (∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        (-1 : ℝ) ^ (S₁.card + S₂.card) *
          ((A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n))).card : ℝ)) =
      (∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        (-1 : ℝ) ^ (S₁.card + S₂.card) * ((A.card : ℝ) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p))) +
      (∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
        (-1 : ℝ) ^ (S₁.card + S₂.card) *
          (((A.filter (fun n => ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) ∣ n)).card : ℝ) -
            (A.card : ℝ) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p))) := by
    intro S₁ hS₁
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    have hS₁Q : S₁ ⊆ Q₁ := Finset.mem_powerset.mp hS₁
    have hS₂P : S₂ ⊆ P₂ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
    have hdvd_eq : A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n)) =
        A.filter (fun n => ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) ∣ n) := by
      ext n
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ =>
        (prod_primes_mul_dvd_iff (fun p hp => hQ₁ p (hS₁Q hp))
          (fun p hp => hP₂ p (hS₂P hp)) (hdisj.mono hS₁Q hS₂P)).symm
    rw [hdvd_eq]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  have hpull : (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
      (-1 : ℝ) ^ (S₁.card + S₂.card) * ((A.card : ℝ) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p))) =
      (A.card : ℝ) *
        ∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ k),
          (-1 : ℝ) ^ (S₁.card + S₂.card) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ _ => ?_
    ring
  rw [hpull, bonferroni_hybrid_main_term Q₁ P₂ g k hg, mul_assoc]

theorem bonferroni_hybrid_lower_bound (A Q₁ P₂ : Finset ℕ) (g : ℕ → ℝ) (m : ℕ)
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (hg : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ P₂,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p) :
    (A.card : ℝ) * V2 g Q₁ * gTrunc g P₂ (2 * m + 1) -
      ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m + 1),
        |((A.filter (fun n => d ∣ n)).card : ℝ) - (A.card : ℝ) * g d| ≤
      ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℝ) := by
  have hsum : (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m + 1),
      (-1 : ℝ) ^ (S₁.card + S₂.card) *
        ((A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n))).card : ℝ)) ≤
      ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℝ) := by
    exact_mod_cast (bonferroni_hybrid_sum A Q₁ P₂ m hdisj).1
  rw [bonferroni_hybrid_real_identity A Q₁ P₂ g (2 * m + 1) hdisj hQ₁ hP₂ hg] at hsum
  have hrem_abs :
      |∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m + 1),
        (-1 : ℝ) ^ (S₁.card + S₂.card) *
          (((A.filter (fun n => ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) ∣ n)).card : ℝ) -
            (A.card : ℝ) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p))| ≤
      ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m + 1),
        |((A.filter (fun n => d ∣ n)).card : ℝ) - (A.card : ℝ) * g d| := by
    rw [sum_bonfDivisors_eq hdisj hQ₁ hP₂]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S₁ _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S₂ _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hneg := neg_le_of_abs_le hrem_abs
  linarith

theorem bonferroni_hybrid_upper_bound (A Q₁ P₂ : Finset ℕ) (g : ℕ → ℝ) (m : ℕ)
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (hg : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ P₂,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p) :
    ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℝ) ≤
      (A.card : ℝ) * V2 g Q₁ * gTrunc g P₂ (2 * m) +
        ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m),
          |((A.filter (fun n => d ∣ n)).card : ℝ) - (A.card : ℝ) * g d| := by
  have hsum : ((A.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℝ) ≤
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m),
        (-1 : ℝ) ^ (S₁.card + S₂.card) *
          ((A.filter (fun n => (∀ p ∈ S₁, p ∣ n) ∧ (∀ p ∈ S₂, p ∣ n))).card : ℝ)) := by
    exact_mod_cast (bonferroni_hybrid_sum A Q₁ P₂ m hdisj).2
  rw [bonferroni_hybrid_real_identity A Q₁ P₂ g (2 * m) hdisj hQ₁ hP₂ hg] at hsum
  have hrem_abs :
      (∑ S₁ ∈ Q₁.powerset, ∑ S₂ ∈ P₂.powerset.filter (fun S₂ => S₂.card ≤ 2 * m),
        (-1 : ℝ) ^ (S₁.card + S₂.card) *
          (((A.filter (fun n => ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) ∣ n)).card : ℝ) -
            (A.card : ℝ) * g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p))) ≤
      ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m),
        |((A.filter (fun n => d ∣ n)).card : ℝ) - (A.card : ℝ) * g d| := by
    rw [sum_bonfDivisors_eq hdisj hQ₁ hP₂]
    refine (le_abs_self _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
    refine Finset.sum_le_sum fun S₁ _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S₂ _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  linarith

theorem sieveRem_shifted_eq (A Q₁ P₂ : Finset ℕ) (g : ℕ → ℝ) (k q d : ℕ)
    (hq_prime : q.Prime) (hqQ₁ : q ∉ Q₁) (hqP₂ : q ∉ P₂)
    (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (hd : d ∈ bonfDivisors Q₁ P₂ k) (hgqd : g (q * d) = g q * g d) :
    let Aq := A.filter (fun n => q ∣ n)
    let r : ℕ → ℝ := fun t => ((A.filter (fun n => t ∣ n)).card : ℝ) - (A.card : ℝ) * g t
    ((Aq.filter (fun n => d ∣ n)).card : ℝ) - (Aq.card : ℝ) * g d = r (q * d) - g d * r q := by
  dsimp only
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  have hS' := Finset.mem_product.mp hS
  have hS₁Q : S₁ ⊆ Q₁ := Finset.mem_powerset.mp hS'.1
  have hS₂P : S₂ ⊆ P₂ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS'.2).1
  have hcop : Nat.Coprime q ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hq_prime (hQ₁ p (hS₁Q hp))).mpr fun heq => hqQ₁ (heq ▸ hS₁Q hp)
    · refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hq_prime (hP₂ p (hS₂P hp))).mpr fun heq => hqP₂ (heq ▸ hS₂P hp)
  have hfilt : (A.filter (fun n => q ∣ n)).filter (fun n => ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) ∣ n) =
      A.filter (fun n => (q * ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p)) ∣ n) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hnA, hqn⟩, hdn⟩
      exact ⟨hnA, hcop.mul_dvd_of_dvd_of_dvd hqn hdn⟩
    · rintro ⟨hnA, hqdn⟩
      exact ⟨⟨hnA, dvd_trans (dvd_mul_right _ _) hqdn⟩, dvd_trans (dvd_mul_left _ _) hqdn⟩
  rw [hfilt, hgqd]
  ring

theorem bonferroni_hybrid_shifted_upper_bound (A Q₁ P₂ : Finset ℕ) (g : ℕ → ℝ) (m q : ℕ)
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (hq_prime : q.Prime) (hqQ₁ : q ∉ Q₁) (hqP₂ : q ∉ P₂)
    (hw₁ : ∀ p ∈ Q₁, g p < 1) (hw₂ : ∀ p ∈ P₂, 0 ≤ g p ∧ g p < 1)
    (hg : ∀ S₁ ⊆ Q₁, ∀ S₂ ⊆ P₂,
      g ((∏ p ∈ S₁, p) * ∏ p ∈ S₂, p) = (∏ p ∈ S₁, g p) * ∏ p ∈ S₂, g p)
    (hgq : ∀ d ∈ bonfDivisors Q₁ P₂ (2 * m), g (q * d) = g q * g d)
    (hg_nonneg : ∀ d ∈ bonfDivisors Q₁ P₂ (2 * m), 0 ≤ g d) :
    let Aq := A.filter (fun n => q ∣ n)
    let r : ℕ → ℝ := fun t => ((A.filter (fun n => t ∣ n)).card : ℝ) - (A.card : ℝ) * g t
    ((Aq.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℝ) -
        (A.card : ℝ) * g q * V2 g Q₁ * gTrunc g P₂ (2 * m) ≤
      ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), |r (q * d)| +
        |r q| * (∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), g d) +
        |r q| * V2 g Q₁ * gTrunc g P₂ (2 * m) := by
  dsimp only
  set Aq := A.filter (fun n => q ∣ n)
  set r : ℕ → ℝ := fun t => ((A.filter (fun n => t ∣ n)).card : ℝ) - (A.card : ℝ) * g t
  have hub := bonferroni_hybrid_upper_bound Aq Q₁ P₂ g m hdisj hQ₁ hP₂ hg
  have hrem : ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m),
      |((Aq.filter (fun n => d ∣ n)).card : ℝ) - (Aq.card : ℝ) * g d| ≤
      ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), |r (q * d)| +
        |r q| * ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), g d := by
    calc
      ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m),
          |((Aq.filter (fun n => d ∣ n)).card : ℝ) - (Aq.card : ℝ) * g d|
        = ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), |r (q * d) - g d * r q| := by
            refine Finset.sum_congr rfl fun d hd => ?_
            rw [sieveRem_shifted_eq A Q₁ P₂ g (2 * m) q d hq_prime hqQ₁ hqP₂ hQ₁ hP₂ hd (hgq d hd)]
      _ ≤ ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), (|r (q * d)| + |r q| * g d) := by
            refine Finset.sum_le_sum fun d hd => ?_
            calc
              |r (q * d) - g d * r q| ≤ |r (q * d)| + |g d * r q| := abs_sub _ _
              _ = |r (q * d)| + |r q| * g d := by
                    rw [abs_mul, abs_of_nonneg (hg_nonneg d hd), mul_comm (g d) |r q|]
      _ = ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), |r (q * d)| +
            |r q| * ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), g d := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hAq_eq : (Aq.card : ℝ) = (A.card : ℝ) * g q + r q := by
    simp only [Aq, r]
    ring
  have hV2_nonneg : 0 ≤ V2 g Q₁ := (V2_pos hw₁).le
  have hgTrunc_nonneg : 0 ≤ gTrunc g P₂ (2 * m) :=
    (V2_pos fun p hp => (hw₂ p hp).2).le.trans (V2_le_gTrunc_of_even (even_two_mul m) hw₂)
  have hmain_nonneg : 0 ≤ V2 g Q₁ * gTrunc g P₂ (2 * m) := mul_nonneg hV2_nonneg hgTrunc_nonneg
  have hrq_le : r q * V2 g Q₁ * gTrunc g P₂ (2 * m) ≤ |r q| * V2 g Q₁ * gTrunc g P₂ (2 * m) := by
    have h1 : r q * (V2 g Q₁ * gTrunc g P₂ (2 * m)) ≤ |r q| * (V2 g Q₁ * gTrunc g P₂ (2 * m)) :=
      mul_le_mul_of_nonneg_right (le_abs_self (r q)) hmain_nonneg
    linarith
  have hcomb : ((Aq.filter (fun n => (∀ p ∈ Q₁, ¬ p ∣ n) ∧ (∀ p ∈ P₂, ¬ p ∣ n))).card : ℝ) ≤
      (Aq.card : ℝ) * V2 g Q₁ * gTrunc g P₂ (2 * m) +
        (∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), |r (q * d)| +
          |r q| * ∑ d ∈ bonfDivisors Q₁ P₂ (2 * m), g d) :=
    hub.trans (add_le_add le_rfl hrem)
  have hprod_expand :
      ((A.card : ℝ) * g q + r q) * V2 g Q₁ * gTrunc g P₂ (2 * m) =
        (A.card : ℝ) * g q * V2 g Q₁ * gTrunc g P₂ (2 * m) + r q * V2 g Q₁ * gTrunc g P₂ (2 * m) := by
    ring
  rw [hAq_eq, hprod_expand] at hcomb
  linarith

end HybridBounds

section AnalyticTailBounds

private theorem add_pow_ge_leading {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    a ^ (k + 1) + (k + 1 : ℝ) * b * a ^ k ≤ (a + b) ^ (k + 1) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hab : 0 ≤ a + b := add_nonneg ha hb
    have hmul : (a + b) * (a ^ (k + 1) + (k + 1 : ℝ) * b * a ^ k) ≤ (a + b) ^ (k + 2) := by
      simpa [pow_succ'] using mul_le_mul_of_nonneg_left ih hab
    have hextra : 0 ≤ (k + 1 : ℝ) * b ^ 2 * a ^ k := by positivity
    have hpow : a ^ (k + 2) + ((k + 1 : ℕ) + 1 : ℝ) * b * a ^ (k + 1) ≤
        (a + b) * (a ^ (k + 1) + (k + 1 : ℝ) * b * a ^ k) := by
      have hid : (a + b) * (a ^ (k + 1) + (k + 1 : ℝ) * b * a ^ k) =
          a ^ (k + 2) + ((k + 1 : ℕ) + 1 : ℝ) * b * a ^ (k + 1) + (k + 1 : ℝ) * b ^ 2 * a ^ k := by
        push_cast
        ring
      linarith
    exact hpow.trans hmul

theorem elemSym_le_pow_div_factorial {w : ℕ → ℝ} {T : Finset ℕ}
    (hw : ∀ p ∈ T, 0 ≤ w p) (k : ℕ) :
    elemSym w T k ≤ (∑ p ∈ T, w p) ^ k / (Nat.factorial k : ℝ) := by
  have hfact_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  refine (le_div_iff₀ hfact_pos).mpr ?_
  rw [mul_comm]
  suffices h : ∀ T : Finset ℕ, (∀ p ∈ T, 0 ≤ w p) →
      ∀ k : ℕ, (Nat.factorial k : ℝ) * elemSym w T k ≤ (∑ p ∈ T, w p) ^ k from
    h T hw k
  intro T hT
  induction T using Finset.induction_on with
  | empty =>
    intro j
    cases j with
    | zero => simp
    | succ j =>
      rw [elemSym_eq_zero_of_lt (by simp), mul_zero]
      simp
  | @insert p T hp ih =>
    have hwp : 0 ≤ w p := hT p (Finset.mem_insert_self p T)
    have hT' : ∀ q ∈ T, 0 ≤ w q := fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have ih' := ih hT'
    intro j
    cases j with
    | zero => simp
    | succ j =>
      rw [elemSym_insert w hp j, Finset.sum_insert hp, Nat.factorial_succ, Nat.cast_mul,
        mul_add]
      have h1 : ((j + 1 : ℕ) : ℝ) * (Nat.factorial j : ℝ) * elemSym w T (j + 1) ≤
          (∑ q ∈ T, w q) ^ (j + 1) := by
        simpa [Nat.factorial_succ, Nat.cast_mul] using ih' (j + 1)
      have h2 : ((j + 1 : ℕ) : ℝ) * (Nat.factorial j : ℝ) * (w p * elemSym w T j) ≤
          ((j + 1 : ℕ) : ℝ) * w p * (∑ q ∈ T, w q) ^ j := by
        have hstep := mul_le_mul_of_nonneg_left (ih' j)
          (mul_nonneg (Nat.cast_nonneg (j + 1)) hwp)
        linarith
      have hsum_nonneg : 0 ≤ ∑ q ∈ T, w q := Finset.sum_nonneg hT'
      have hlead := add_pow_ge_leading hsum_nonneg hwp j
      have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [hcast] at h1 h2 ⊢
      rw [add_comm (w p)]
      linarith

theorem gTrunc_ge_V2_sub_next_of_odd {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Odd m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    V2 w T - elemSym w T (m + 1) ≤ gTrunc w T m := by
  have hm1 : Even (m + 1) := hm.add_one
  have hV2 : V2 w T ≤ gTrunc w T (m + 1) := V2_le_gTrunc_of_even hm1 hw
  rw [gTrunc_succ, hm1.neg_one_pow, one_mul] at hV2
  linarith

theorem gTrunc_le_V2_add_next_of_even {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Even m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    gTrunc w T m ≤ V2 w T + elemSym w T (m + 1) := by
  have hm1 : Odd (m + 1) := hm.add_odd odd_one
  have hV2 : gTrunc w T (m + 1) ≤ V2 w T := gTrunc_le_V2_of_odd hm1 hw
  rw [gTrunc_succ, hm1.neg_one_pow] at hV2
  linarith

theorem RTrunc_odd_analytic_lb {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Odd m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    1 - (∑ p ∈ T, w p) ^ (m + 1) / ((Nat.factorial (m + 1) : ℝ) * V2 w T) ≤ RTrunc w T m := by
  have hV2 : 0 < V2 w T := V2_pos fun p hp => (hw p hp).2
  have h1 : V2 w T - elemSym w T (m + 1) ≤ gTrunc w T m := gTrunc_ge_V2_sub_next_of_odd hm hw
  have h2 : elemSym w T (m + 1) ≤ (∑ p ∈ T, w p) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) :=
    elemSym_le_pow_div_factorial (fun p hp => (hw p hp).1) (m + 1)
  have h3 : (V2 w T - (∑ p ∈ T, w p) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) / V2 w T ≤
      gTrunc w T m / V2 w T := div_le_div_of_nonneg_right (by linarith) hV2.le
  have hV2_ne : V2 w T ≠ 0 := hV2.ne'
  have heq : (V2 w T - (∑ p ∈ T, w p) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) / V2 w T =
      1 - (∑ p ∈ T, w p) ^ (m + 1) / ((Nat.factorial (m + 1) : ℝ) * V2 w T) := by
    field_simp
  rwa [heq] at h3

theorem RTrunc_even_analytic_ub {w : ℕ → ℝ} {T : Finset ℕ} {m : ℕ}
    (hm : Even m) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p < 1) :
    RTrunc w T m ≤ 1 + (∑ p ∈ T, w p) ^ (m + 1) / ((Nat.factorial (m + 1) : ℝ) * V2 w T) := by
  have hV2 : 0 < V2 w T := V2_pos fun p hp => (hw p hp).2
  have h1 : gTrunc w T m ≤ V2 w T + elemSym w T (m + 1) := gTrunc_le_V2_add_next_of_even hm hw
  have h2 : elemSym w T (m + 1) ≤ (∑ p ∈ T, w p) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) :=
    elemSym_le_pow_div_factorial (fun p hp => (hw p hp).1) (m + 1)
  have h3 : gTrunc w T m / V2 w T ≤
      (V2 w T + (∑ p ∈ T, w p) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) / V2 w T :=
    div_le_div_of_nonneg_right (by linarith) hV2.le
  have hV2_ne : V2 w T ≠ 0 := hV2.ne'
  have heq : (V2 w T + (∑ p ∈ T, w p) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) / V2 w T =
      1 + (∑ p ∈ T, w p) ^ (m + 1) / ((Nat.factorial (m + 1) : ℝ) * V2 w T) := by
    field_simp
  rwa [heq] at h3

private theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / (2 * (1 - x)) := by
  let f : ℝ → ℝ := fun t => t + t ^ 2 / (2 * (1 - t)) + Real.log (1 - t)
  have hcont : ContinuousOn f (Set.Ico 0 1) := by
    refine (continuousOn_id.add ?_).add ?_
    · refine ContinuousOn.div (continuousOn_id.pow 2)
        (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)) ?_
      intro t ht
      exact mul_ne_zero two_ne_zero (sub_pos.mpr ht.2).ne'
    · refine ContinuousOn.log (continuousOn_const.sub continuousOn_id) ?_
      intro t ht
      exact ne_of_gt (sub_pos.mpr ht.2)
  have hderiv : ∀ t ∈ interior (Set.Ico (0 : ℝ) 1),
      HasDerivAt f (1 + (2 * t * (2 * (1 - t)) - t ^ 2 * (-2)) / (2 * (1 - t)) ^ 2 +
        (-1) / (1 - t)) t := by
    intro t ht
    rw [interior_Ico] at ht
    have h1t : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
    have h2t : 2 * (1 - t) ≠ 0 := mul_ne_zero two_ne_zero h1t
    have hd1 : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id' t
    have hd2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hd3 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_id' t).const_sub 1
    have hd4 : HasDerivAt (fun u : ℝ => 2 * (1 - u)) (-2) t := by
      simpa using hd3.const_mul 2
    have hd_quot : HasDerivAt (fun u : ℝ => u ^ 2 / (2 * (1 - u)))
        ((2 * t * (2 * (1 - t)) - t ^ 2 * (-2)) / (2 * (1 - t)) ^ 2) t :=
      hd2.div hd4 h2t
    have hd_log : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - t)) t :=
      hd3.log h1t
    exact (hd1.add hd_quot).add hd_log
  have hmono : MonotoneOn f (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1) hcont ?_ ?_
    · intro t ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht_oo : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ico] using ht
      have h1t : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht_oo.2)
      rw [(hderiv t (by simpa [interior_Ico] using ht_oo)).deriv]
      have hid : 1 + (2 * t * (2 * (1 - t)) - t ^ 2 * (-2)) / (2 * (1 - t)) ^ 2 + (-1) / (1 - t) =
          t ^ 2 / (2 * (1 - t) ^ 2) := by
        field_simp
        ring
      rw [hid]
      positivity
  have hf0 : f 0 = 0 := by simp [f]
  have h0x : f 0 ≤ f x := hmono ⟨le_rfl, zero_lt_one⟩ ⟨hx0, hx1⟩ hx0
  rw [hf0] at h0x
  dsimp only [f] at h0x
  linarith

theorem V2_ge_exp_neg_sum {w : ℕ → ℝ} {T : Finset ℕ} {w_max : ℝ}
    (hwmax : w_max < 1) (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ w_max) :
    Real.exp (-(∑ p ∈ T, w p + (1 / (2 * (1 - w_max))) * ∑ p ∈ T, (w p) ^ 2)) ≤ V2 w T := by
  have h1wmax : 0 < 1 - w_max := sub_pos.mpr hwmax
  have hsum_eq :
      -(∑ p ∈ T, w p + (1 / (2 * (1 - w_max))) * ∑ p ∈ T, (w p) ^ 2) =
      ∑ p ∈ T, -(w p + (w p) ^ 2 / (2 * (1 - w_max))) := by
    rw [neg_add, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hsum_eq, Real.exp_sum, V2]
  refine finset_prod_le_prod T (fun p _ => (Real.exp_pos _).le) fun p hp => ?_
  have hwp := hw p hp
  have hwp1 : w p < 1 := lt_of_le_of_lt hwp.2 hwmax
  have h1wp : 0 < 1 - w p := sub_pos.mpr hwp1
  have hlog : -Real.log (1 - w p) ≤ w p + (w p) ^ 2 / (2 * (1 - w_max)) := by
    refine (neg_log_one_sub_le hwp.1 hwp1).trans ?_
    gcongr
    linarith [hwp.2]
  have hexp : Real.exp (-(w p + (w p) ^ 2 / (2 * (1 - w_max)))) ≤ Real.exp (Real.log (1 - w p)) :=
    Real.exp_le_exp.mpr (by linarith)
  simpa [Real.exp_log h1wp] using hexp

theorem sum_choose_le_pow_div_factorial (N m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ) ≤
      ∑ j ∈ Finset.range (m + 1), (N : ℝ) ^ j / (Nat.factorial j : ℝ) := by
  refine Finset.sum_le_sum fun j _ => ?_
  have hfact_pos : (0 : ℝ) < (Nat.factorial j : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
  refine (le_div_iff₀ hfact_pos).mpr ?_
  have hnat : N.choose j * Nat.factorial j ≤ N ^ j := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow N j
  exact_mod_cast hnat

theorem sum_elemSym_le_exp {w : ℕ → ℝ} {T : Finset ℕ}
    (hw : ∀ p ∈ T, 0 ≤ w p) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), elemSym w T j ≤ Real.exp (∑ p ∈ T, w p) := by
  let N := max m T.card
  have h1 : ∑ j ∈ Finset.range (m + 1), elemSym w T j ≤
      ∑ j ∈ Finset.range (N + 1), elemSym w T j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => elemSym_nonneg hw j)
    exact Finset.range_mono (Nat.succ_le_succ (le_max_left m T.card))
  have h2 : ∑ j ∈ Finset.range (N + 1), elemSym w T j = ∏ p ∈ T, (1 + w p) :=
    (prod_one_add_eq_sum_elemSym w T N (le_max_right m T.card)).symm
  have h3 : ∏ p ∈ T, (1 + w p) ≤ ∏ p ∈ T, Real.exp (w p) := by
    refine finset_prod_le_prod T (fun p hp => by linarith [hw p hp]) fun p hp => ?_
    linarith [Real.add_one_le_exp (w p)]
  rw [← Real.exp_sum] at h3
  exact h1.trans (h2.le.trans h3)

end AnalyticTailBounds

end BuchstabSwitching
