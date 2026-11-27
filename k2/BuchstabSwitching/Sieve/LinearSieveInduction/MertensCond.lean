import BuchstabSwitching.Sieve.RosserIwaniecComb
import BuchstabSwitching.Sieve.MertensTwoVar
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# All-Levels Two-Variable Mertens Product Condition

Defines `AllLevelsMertensCondFrom` and `AllLevelsMertensCond`, proves monotonicity and
filtering inheritance (`filter_lt`, `filter_nat_lt`), and bridges from
`MertensTwoVar.two_var_mertens_cond_of_excursion` and `MertensTwoVar.eps_large_u_two_var_sound`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 1. All-Levels Two-Variable Mertens Product Condition -/

/-- All-levels two-variable Mertens product condition from lower threshold `u`:
for all `1 < w` with `u ≤ w ≤ z₁`, `V(w) ≤ K * (log z₁ / log w) * V(z₁)`. -/
def AllLevelsMertensCondFrom (g : ℕ → ℝ) (P : Finset ℕ) (u K : ℝ) : Prop :=
  ∀ ⦃w z₁ : ℝ⦄, 1 < w → u ≤ w → w ≤ z₁ →
    sieveV g (P.filter (fun p : ℕ => (p : ℝ) < w)) ≤
      K * (Real.log z₁ / Real.log w) * sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁))

/-- Unconditional all-levels two-variable Mertens product condition (`u = 1`). -/
def AllLevelsMertensCond (g : ℕ → ℝ) (P : Finset ℕ) (K : ℝ) : Prop :=
  ∀ ⦃w z₁ : ℝ⦄, 1 < w → w ≤ z₁ →
    sieveV g (P.filter (fun p : ℕ => (p : ℝ) < w)) ≤
      K * (Real.log z₁ / Real.log w) * sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁))

theorem AllLevelsMertensCond.to_from {g : ℕ → ℝ} {P : Finset ℕ} {K : ℝ}
    (h : AllLevelsMertensCond g P K) (u : ℝ) : AllLevelsMertensCondFrom g P u K :=
  fun _ _ hw _ hwz => h hw hwz

theorem allLevelsMertensCond_iff_from_one (g : ℕ → ℝ) (P : Finset ℕ) (K : ℝ) :
    AllLevelsMertensCond g P K ↔ AllLevelsMertensCondFrom g P 1 K :=
  ⟨fun h => h.to_from 1, fun h _ _ hw hwz => h hw hw.le hwz⟩

theorem AllLevelsMertensCondFrom.mono_u {g : ℕ → ℝ} {P : Finset ℕ} {u₁ u₂ K : ℝ}
    (hu : u₁ ≤ u₂) (h : AllLevelsMertensCondFrom g P u₁ K) :
    AllLevelsMertensCondFrom g P u₂ K :=
  fun _ _ hw huw hwz => h hw (hu.trans huw) hwz

theorem sieveV_nonneg {g : ℕ → ℝ} {P : Finset ℕ} (hg : ∀ p ∈ P, g p ≤ 1) :
    0 ≤ sieveV g P := by
  refine Finset.prod_nonneg fun p hp => ?_
  linarith [hg p hp]

theorem sieveV_pos {g : ℕ → ℝ} {P : Finset ℕ} (hg : ∀ p ∈ P, g p < 1) :
    0 < sieveV g P := by
  refine Finset.prod_pos fun p hp => ?_
  linarith [hg p hp]

theorem AllLevelsMertensCondFrom.mono_K {g : ℕ → ℝ} {P : Finset ℕ} {u K₁ K₂ : ℝ}
    (hg : ∀ p ∈ P, g p ≤ 1) (hK : K₁ ≤ K₂) (h : AllLevelsMertensCondFrom g P u K₁) :
    AllLevelsMertensCondFrom g P u K₂ := by
  intro w z₁ hw huw hwz
  have h1 := h hw huw hwz
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlogz : 0 < Real.log z₁ := Real.log_pos (lt_of_lt_of_le hw hwz)
  have hV : 0 ≤ sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁)) :=
    sieveV_nonneg fun p hp => hg p (Finset.filter_subset _ P hp)
  have hmul : 0 ≤ (Real.log z₁ / Real.log w) * sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁)) :=
    mul_nonneg (div_nonneg hlogz.le hlogw.le) hV
  have hKmul : K₁ * ((Real.log z₁ / Real.log w) * sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁))) ≤
      K₂ * ((Real.log z₁ / Real.log w) * sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁))) :=
    mul_le_mul_of_nonneg_right hK hmul
  linarith

/-- Filtering `P` below any real cutoff `z'` preserves `AllLevelsMertensCondFrom`. -/
theorem AllLevelsMertensCondFrom.filter_lt {g : ℕ → ℝ} {P : Finset ℕ} {u K : ℝ}
    (hK : 1 ≤ K) (hg : ∀ p ∈ P, g p ≤ 1) (h : AllLevelsMertensCondFrom g P u K) (z' : ℝ) :
    AllLevelsMertensCondFrom g (P.filter (fun p : ℕ => (p : ℝ) < z')) u K := by
  intro w z₁ hw huw hwz
  set P' : Finset ℕ := P.filter (fun p : ℕ => (p : ℝ) < z')
  have hfilt_le : ∀ x : ℝ, x ≤ z' →
      P'.filter (fun p : ℕ => (p : ℝ) < x) = P.filter (fun p : ℕ => (p : ℝ) < x) := by
    intro x hx
    ext p
    simp only [P', Finset.mem_filter]
    exact ⟨fun ⟨⟨hp, _⟩, hpx⟩ => ⟨hp, hpx⟩, fun ⟨hp, hpx⟩ => ⟨⟨hp, lt_of_lt_of_le hpx hx⟩, hpx⟩⟩
  have hfilt_ge : ∀ x : ℝ, z' ≤ x → P'.filter (fun p : ℕ => (p : ℝ) < x) = P' := by
    intro x hx
    ext p
    simp only [P', Finset.mem_filter]
    exact ⟨fun ⟨hmem, _⟩ => hmem, fun ⟨hp, hpz'⟩ => ⟨⟨hp, hpz'⟩, lt_of_lt_of_le hpz' hx⟩⟩
  rcases le_or_gt z₁ z' with hz₁ | hz₁
  · rw [hfilt_le w (hwz.trans hz₁), hfilt_le z₁ hz₁]
    exact h hw huw hwz
  · rcases lt_or_ge w z' with hw' | hw'
    · rw [hfilt_le w hw'.le, hfilt_ge z₁ hz₁.le]
      have hP'eq : P' = P.filter (fun p : ℕ => (p : ℝ) < z') := rfl
      have hsub := h hw huw hw'.le
      have hlogw : 0 < Real.log w := Real.log_pos hw
      have hlogz' : Real.log z' ≤ Real.log z₁ :=
        Real.log_le_log (lt_trans (by linarith) hw') hz₁.le
      have hV' : 0 ≤ sieveV g P' := sieveV_nonneg fun p hp => hg p (Finset.filter_subset _ P hp)
      have hK0 : 0 ≤ K := by linarith
      have hdiv : Real.log z' / Real.log w ≤ Real.log z₁ / Real.log w :=
        div_le_div_of_nonneg_right hlogz' hlogw.le
      calc sieveV g (P.filter (fun p : ℕ => (p : ℝ) < w))
          ≤ K * (Real.log z' / Real.log w) * sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z')) := hsub
        _ ≤ K * (Real.log z₁ / Real.log w) * sieveV g P' := by
            rw [← hP'eq]
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hK0) hV'
    · rw [hfilt_ge w hw', hfilt_ge z₁ (hw'.trans hwz)]
      have hlogw : 0 < Real.log w := Real.log_pos hw
      have hlog_le : Real.log w ≤ Real.log z₁ := Real.log_le_log (by linarith) hwz
      have hone_le_ratio : 1 ≤ Real.log z₁ / Real.log w := (one_le_div hlogw).mpr hlog_le
      have hone_le_mul : 1 ≤ K * (Real.log z₁ / Real.log w) := by nlinarith
      have hV' : 0 ≤ sieveV g P' := sieveV_nonneg fun p hp => hg p (Finset.filter_subset _ P hp)
      exact le_mul_of_one_le_left hV' hone_le_mul

theorem AllLevelsMertensCondFrom.filter_nat_lt {g : ℕ → ℝ} {P : Finset ℕ} {u K : ℝ}
    (hK : 1 ≤ K) (hg : ∀ p ∈ P, g p ≤ 1) (h : AllLevelsMertensCondFrom g P u K) (p₁ : ℕ) :
    AllLevelsMertensCondFrom g (P.filter (· < p₁)) u K := by
  have hfilt : P.filter (· < p₁) = P.filter (fun p : ℕ => (p : ℝ) < (p₁ : ℝ)) := by
    ext p; simp [Nat.cast_lt]
  rw [hfilt]
  exact h.filter_lt hK hg (p₁ : ℝ)

theorem sieveV_filter_lt_eq_prod_mul {g : ℕ → ℝ} {P : Finset ℕ}
    (hg : ∀ p ∈ P, g p < 1) {w z₁ : ℝ} (hwz : w ≤ z₁) :
    sieveV g (P.filter (fun p : ℕ => (p : ℝ) < w)) =
      (∏ p ∈ P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁), (1 - g p)⁻¹) *
        sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁)) := by
  let A : Finset ℕ := P.filter (fun p : ℕ => (p : ℝ) < w)
  let B : Finset ℕ := P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    have h1 : (p : ℝ) < w := (Finset.mem_filter.mp hpA).2
    have h2 : w ≤ (p : ℝ) := (Finset.mem_filter.mp hpB).2.1
    linarith
  have hunion : P.filter (fun p : ℕ => (p : ℝ) < z₁) = A ∪ B := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpz⟩
      rcases lt_or_ge (p : ℝ) w with hpw | hpw
      · exact Or.inl ⟨hp, hpw⟩
      · exact Or.inr ⟨hp, hpw, hpz⟩
    · rintro (⟨hp, hpw⟩ | ⟨hp, _, hpz⟩)
      · exact ⟨hp, lt_of_lt_of_le hpw hwz⟩
      · exact ⟨hp, hpz⟩
  have hprod_mul : (∏ p ∈ B, (1 - g p)⁻¹) * (∏ p ∈ B, (1 - g p)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hne : 1 - g p ≠ 0 := by linarith [hg p (Finset.filter_subset _ P hp)]
    exact inv_mul_cancel₀ hne
  change sieveV g A = (∏ p ∈ B, (1 - g p)⁻¹) * sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁))
  rw [hunion, sieveV, sieveV, Finset.prod_union hdisj]
  calc ∏ p ∈ A, (1 - g p)
      = 1 * ∏ p ∈ A, (1 - g p) := (one_mul _).symm
    _ = ((∏ p ∈ B, (1 - g p)⁻¹) * (∏ p ∈ B, (1 - g p))) * (∏ p ∈ A, (1 - g p)) := by rw [hprod_mul]
    _ = (∏ p ∈ B, (1 - g p)⁻¹) * ((∏ p ∈ A, (1 - g p)) * (∏ p ∈ B, (1 - g p))) := by ring

/-- Lifting a two-variable inverse-product bound on `P.filter (w ≤ p < z₁)` (for `max u₀ u ≤ w < z₁`)
to `AllLevelsMertensCondFrom g P u K`, automatically handling `w < u₀` when `∀ p ∈ P, u₀ ≤ p`. -/
theorem allLevelsMertensCondFrom_of_prod_bound {g : ℕ → ℝ} {P : Finset ℕ} {u₀ u K : ℝ}
    (hu₀ : 1 < u₀) (hK : 1 ≤ K) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hP_ge : ∀ p ∈ P, u₀ ≤ (p : ℝ))
    (hprod : ∀ ⦃w z₁ : ℝ⦄, max u₀ u ≤ w → w < z₁ →
      ∏ p ∈ P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁), (1 - g p)⁻¹ ≤
        K * (Real.log z₁ / Real.log w)) :
    AllLevelsMertensCondFrom g P u K := by
  intro w z₁ hw huw hwz
  rw [sieveV_filter_lt_eq_prod_mul (fun p hp => (hg p hp).2) hwz]
  have hVz_nonneg : 0 ≤ sieveV g (P.filter (fun p : ℕ => (p : ℝ) < z₁)) :=
    sieveV_nonneg fun p hp => (hg p (Finset.filter_subset _ P hp)).2.le
  refine mul_le_mul_of_nonneg_right ?_ hVz_nonneg
  rcases eq_or_lt_of_le hwz with rfl | hlt
  · have hemp : P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w) = ∅ := by
      ext p; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]; intro _ h1 h2; linarith
    have hlogw : Real.log w ≠ 0 := (Real.log_pos hw).ne'
    rw [hemp, Finset.prod_empty, div_self hlogw, mul_one]
    exact hK
  · rcases le_or_gt u₀ w with hu₀w | hwu₀
    · exact hprod (max_le hu₀w huw) hlt
    · rcases le_or_gt z₁ u₀ with hz₁u₀ | hu₀z₁
      · have hemp : P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁) = ∅ := by
          ext p
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hp _ hpz
          have := hP_ge p hp
          linarith
        have hlogw : 0 < Real.log w := Real.log_pos hw
        have hlogz : Real.log w ≤ Real.log z₁ := Real.log_le_log (by linarith) hwz
        have hratio : 1 ≤ Real.log z₁ / Real.log w := (one_le_div hlogw).mpr hlogz
        rw [hemp, Finset.prod_empty]
        nlinarith
      · have hfilt_eq : P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁) =
            P.filter (fun p : ℕ => u₀ ≤ (p : ℝ) ∧ (p : ℝ) < z₁) := by
          ext p
          simp only [Finset.mem_filter]
          exact ⟨fun ⟨hp, _, hpz⟩ => ⟨hp, hP_ge p hp, hpz⟩,
            fun ⟨hp, hpu, hpz⟩ => ⟨hp, hwu₀.le.trans hpu, hpz⟩⟩
        rw [hfilt_eq]
        have hmax : max u₀ u ≤ u₀ := max_le le_rfl (huw.trans hwu₀.le)
        have hbd := hprod hmax hu₀z₁
        have hlogw : 0 < Real.log w := Real.log_pos hw
        have hlogz : 0 < Real.log z₁ := Real.log_pos (lt_trans hu₀ hu₀z₁)
        have hlog_wu : Real.log w ≤ Real.log u₀ := Real.log_le_log (by linarith) hwu₀.le
        have hdiv : Real.log z₁ / Real.log u₀ ≤ Real.log z₁ / Real.log w :=
          div_le_div_of_nonneg_left hlogz.le hlogw hlog_wu
        have hK0 : 0 ≤ K := by linarith
        exact hbd.trans (mul_le_mul_of_nonneg_left hdiv hK0)

/-- Bridge from `MertensTwoVar.two_var_mertens_cond_of_excursion` to `AllLevelsMertensCond`
for `g p = 1 / (p - 1)` on any `P` of primes `≥ p_star` not dividing `N`. -/
theorem allLevelsMertensCond_of_excursion
    {p_star X_0 : ℕ} (hp_star : 3 ≤ p_star)
    (hP_ne : ((Finset.Icc p_star X_0).filter Nat.Prime).Nonempty)
    {M0 : ℝ} {E_lo E_hi : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi)
    (hE_lo_anti : AntitoneOn E_lo (Set.Ici (p_star : ℝ)))
    {D_max twin_tail s2_tail : ℝ}
    (h_excur : ∀ q ∈ (Finset.Icc p_star X_0).filter Nat.Prime,
      ∀ p ∈ (Finset.Icc p_star X_0).filter Nat.Prime, q ≤ p →
        mertensAfter M0 p - mertensBefore M0 q ≤ D_max)
    (h_tail : ∀ x : ℝ, (X_0 : ℝ) ≤ x →
      E_hi x - min (((Finset.Icc p_star X_0).filter Nat.Prime).inf' hP_ne (mertensBefore M0))
        (-E_lo (p_star : ℝ)) ≤ D_max)
    (h_twin : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p_star ≤ p) →
      ∏ p ∈ S, ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) ≤ twin_tail)
    (h_s2 : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p_star ≤ p) →
      ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ s2_tail)
    {N : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p_star ≤ p ∧ ¬ p ∣ N)
    (hK : 1 ≤ twin_tail * Real.exp (D_max + c_p (p_star : ℝ) * s2_tail)) :
    AllLevelsMertensCond (fun p : ℕ => 1 / ((p : ℝ) - 1)) P
      (twin_tail * Real.exp (D_max + c_p (p_star : ℝ) * s2_tail)) := by
  rw [allLevelsMertensCond_iff_from_one]
  refine allLevelsMertensCondFrom_of_prod_bound (u₀ := (p_star : ℝ))
    (by exact_mod_cast (by omega : 1 < p_star)) hK ?_ ?_ ?_
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p_star).trans (hP p hp).2.1
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one hp1.le
    have h2 : 1 / ((p : ℝ) - 1) < 1 := by rw [one_div_lt hp1 zero_lt_one]; linarith
    exact ⟨h1, h2⟩
  · intro p hp; exact_mod_cast (hP p hp).2.1
  · intro w z₁ hw hwz
    have hw_pstar : (p_star : ℝ) ≤ w := le_trans (le_max_left _ _) hw
    have hsub : P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁) ⊆
        (Finset.Ico (Nat.ceil w) (Nat.ceil z₁)).filter (fun p => p.Prime ∧ ¬ p ∣ N) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpw, hpz⟩
      have hpp := hP p hpP
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hpw, Nat.lt_ceil.mpr hpz⟩,
        hpp.1, hpp.2.2⟩
    have hprod_le :
        ∏ p ∈ P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁), (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        ∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z₁)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro p hp
        have hpw : w ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2.1
        have hp3 : (3 : ℝ) ≤ p := le_trans (by exact_mod_cast hp_star) (hw_pstar.trans hpw)
        have hp1 : 0 < (p : ℝ) - 1 := by linarith
        have hlt1 : 1 / ((p : ℝ) - 1) < 1 := by rw [one_div_lt hp1 zero_lt_one]; linarith
        exact (inv_pos.mpr (by linarith)).le
      · intro p hp _
        have hp_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
        have hpw : w ≤ (p : ℝ) := Nat.ceil_le.mp hp_ico.1
        have hp3 : (3 : ℝ) ≤ p := le_trans (by exact_mod_cast hp_star) (hw_pstar.trans hpw)
        have hp1 : 0 < (p : ℝ) - 1 := by linarith
        have hlt1 : 1 / ((p : ℝ) - 1) < 1 := by rw [one_div_lt hp1 zero_lt_one]; linarith
        have hnn : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one hp1.le
        exact (one_le_inv₀ (by linarith)).mpr (by linarith)
    exact hprod_le.trans (two_var_mertens_cond_of_excursion hp_star hP_ne hM hE_lo_anti
      h_excur h_tail h_twin h_s2 hw_pstar hwz N)

/-- Bridge from `MertensTwoVar.eps_large_u_two_var_sound` to `AllLevelsMertensCondFrom`
for `u ≥ Real.exp 10.1` and `g p = 1 / (p - 1)`. -/
theorem allLevelsMertensCondFrom_of_large_u
    {M0 : ℝ} {E_lo E_hi : ℝ → ℝ} (hM : MertensSumBounds M0 E_lo E_hi)
    {u E_lo_bd E_hi_bd : ℝ} (hu : Real.exp 10.1 ≤ u)
    (hE_lo : ∀ x, u ≤ x → E_lo x ≤ E_lo_bd)
    (hE_hi : ∀ x, u ≤ x → E_hi x ≤ E_hi_bd)
    (hK : 1 ≤ Real.exp (2.0002 / u + E_hi_bd + E_lo_bd))
    {N : ℕ} (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ u ≤ (p : ℝ) ∧ ¬ p ∣ N) :
    AllLevelsMertensCondFrom (fun p : ℕ => 1 / ((p : ℝ) - 1)) P u
      (Real.exp (2.0002 / u + E_hi_bd + E_lo_bd)) := by
  have hu_ge_1024 : (1024 : ℝ) ≤ u := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h10 : (1024 : ℝ) ≤ Real.exp 10 := by
      calc (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
        _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
        _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h101 : Real.exp 10 ≤ Real.exp 10.1 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  refine allLevelsMertensCondFrom_of_prod_bound (u₀ := u) (by linarith) hK ?_ ?_ ?_
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := le_trans (by linarith) (hP p hp).2.1
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    exact ⟨div_nonneg zero_le_one hp1.le, by rw [one_div_lt hp1 zero_lt_one]; linarith⟩
  · intro p hp; exact (hP p hp).2.1
  · intro w z₁ hw hwz
    have huw : u ≤ w := (le_max_left _ _).trans hw
    have hsub : P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁) ⊆
        (Finset.Ico (Nat.ceil w) (Nat.ceil z₁)).filter (fun p => p.Prime ∧ ¬ p ∣ N) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpw, hpz⟩
      have hpp := hP p hpP
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hpw, Nat.lt_ceil.mpr hpz⟩,
        hpp.1, hpp.2.2⟩
    have hprod_le :
        ∏ p ∈ P.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z₁), (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        ∏ p ∈ (Finset.Ico (Nat.ceil w) (Nat.ceil z₁)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
          (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro p hp
        have hpw : w ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2.1
        have hp3 : (3 : ℝ) ≤ p := le_trans (by linarith) (huw.trans hpw)
        have hp1 : 0 < (p : ℝ) - 1 := by linarith
        have hlt1 : 1 / ((p : ℝ) - 1) < 1 := by rw [one_div_lt hp1 zero_lt_one]; linarith
        exact (inv_pos.mpr (by linarith)).le
      · intro p hp _
        have hpw : w ≤ (p : ℝ) := Nat.ceil_le.mp (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
        have hp3 : (3 : ℝ) ≤ p := le_trans (by linarith) (huw.trans hpw)
        have hp1 : 0 < (p : ℝ) - 1 := by linarith
        have hlt1 : 1 / ((p : ℝ) - 1) < 1 := by rw [one_div_lt hp1 zero_lt_one]; linarith
        have hnn : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one hp1.le
        exact (one_le_inv₀ (by linarith)).mpr (by linarith)
    have hsound := (eps_large_u_two_var_sound hM hu huw hwz N).2
    have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
    have hlogz : 0 < Real.log z₁ := Real.log_pos (by linarith)
    have hratio : 0 ≤ Real.log z₁ / Real.log w := div_nonneg hlogz.le hlogw.le
    have hexp_le : Real.exp (2.0002 / u + E_hi z₁ + E_lo w) ≤
        Real.exp (2.0002 / u + E_hi_bd + E_lo_bd) :=
      Real.exp_le_exp.mpr (by linarith [hE_hi z₁ (huw.trans hwz.le), hE_lo w huw])
    exact hprod_le.trans (hsound.trans (mul_le_mul_of_nonneg_right hexp_le hratio))

end

end BuchstabSwitching
