import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.TwoPrimePartition
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import Mathlib.Tactic

/-!
# Selberg Asymptotic Bridge: Discrete Finite-Partition `j_full_lb_z3`

Defines `J_odd_lb_asym`, `J_odd_ub_asym`, `TwoPrimeDiscreteGrid`, and `j_full_lb_z3`,
and proves `j_full_lb_z3_ge_general` and `j_full_lb_z3_ge` for `1 ≤ ξ < z^3`.
-/

namespace BuchstabSwitching

/-! ## 4. Discrete Finite-Partition `j_full_lb_z3` (Regime 2c, `1 ≤ ξ < z^3`) -/

section DiscreteJFullLB

/-- Asymptotic lower envelope for `J_odd(X)` valid for `X ≥ 1`. -/
noncomputable def J_odd_lb_asym (X : ℝ) : ℝ :=
  max 0 (H_0 * ((1 / 2 : ℝ) * Real.log X + alpha0) - C_J * X ^ (-(1 / 4 : ℝ)))

/-- Asymptotic upper envelope for `J_odd(X)` valid for `X ≥ 1`. -/
noncomputable def J_odd_ub_asym (X : ℝ) : ℝ :=
  H_0 * ((1 / 2 : ℝ) * Real.log X + alpha0) + C_J * X ^ (-(1 / 4 : ℝ))

lemma J_odd_lb_asym_nonneg (X : ℝ) : 0 ≤ J_odd_lb_asym X :=
  le_max_left _ _

lemma J_odd_lb_asym_le {X : ℝ} (hX : 1 ≤ X) : J_odd_lb_asym X ≤ J_odd X :=
  max_le (J_odd_nonneg X) (asym_le_J_odd hX)

lemma le_J_odd_ub_asym {X : ℝ} (hX : 1 ≤ X) : J_odd X ≤ J_odd_ub_asym X :=
  J_odd_le_asym hX

lemma J_odd_ub_asym_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ J_odd_ub_asym X :=
  (J_odd_nonneg X).trans (le_J_odd_ub_asym hX)

/-- Disjoint 2-prime box grid in real prime coordinates `[a_i, a_{i+1}) × [b_{i,j}, b_{i,j+1})`
above `z_nat` and with `a_{i+1} * b_{i,j+1} ≤ xi`. -/
structure TwoPrimeDiscreteGrid (z_nat : ℕ) (xi : ℝ) where
  m₁ : ℕ
  a : Fin (m₁ + 1) → ℝ
  ha_ge : (z_nat : ℝ) ≤ a 0
  ha_mono : StrictMono a
  m₂ : Fin m₁ → ℕ
  b : (i : Fin m₁) → Fin (m₂ i + 1) → ℝ
  hb_ge : ∀ i : Fin m₁, a i.succ ≤ b i 0
  hb_mono : ∀ i : Fin m₁, StrictMono (b i)
  hb_le : ∀ i : Fin m₁, ∀ j : Fin (m₂ i), a i.succ * b i j.succ ≤ xi

/-- Explicit discrete finite-partition 2-prime inclusion-exclusion value matching
`selberg_weights.py:j_full_lb_z3` with strictly disjoint subintervals `[w_k, w_{k+1})`. -/
noncomputable def j_full_lb_z3 (E_lo E_hi J_lb J_ub : ℝ → ℝ) (z_nat : ℕ) (xi : ℝ)
    {k₁ : ℕ} (w : Fin (k₁ + 1) → ℝ) (G : TwoPrimeDiscreteGrid z_nat xi) : ℝ :=
  J_lb xi
    - (∑ k : Fin k₁,
        let w0 := w k.castSucc
        let w1p := if k.val + 1 = k₁ then w k.succ + 1 else w k.succ
        J_ub (xi / w0) *
          (max 0 (Real.log (Real.log w1p / Real.log w0) + E_hi w1p + E_lo w0) +
            2 / (w0 - 2)))
    + ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
        let a0 := G.a i.castSucc
        let a1 := G.a i.succ
        let b0 := G.b i j.castSucc
        let b1 := G.b i j.succ
        max 0 (Real.log (Real.log a1 / Real.log a0) - E_lo a1 - E_hi a0) *
          max 0 (Real.log (Real.log b1 / Real.log b0) - E_lo b1 - E_hi b0) *
          J_lb (xi / (a1 * b1))

/-- General soundness theorem for `j_full_lb_z3` with arbitrary valid `J_lb ≤ J_odd ≤ J_ub`
and `MertensSumBounds` when `(z_nat : ℝ) ≤ xi < (z_nat : ℝ) ^ 3`. -/
theorem j_full_lb_z3_ge_general
    {M0 : ℝ} {E_lo E_hi J_lb J_ub : ℝ → ℝ}
    (hM : MertensSumBounds M0 E_lo E_hi)
    (hJ_lb : ∀ X : ℝ, 1 ≤ X → 0 ≤ J_lb X ∧ J_lb X ≤ J_odd X)
    (hJ_ub : ∀ X : ℝ, 1 ≤ X → J_odd X ≤ J_ub X)
    {z_nat : ℕ} (hz3 : 3 ≤ z_nat) {xi : ℝ}
    (hzxi : (z_nat : ℝ) ≤ xi) (hxi3 : xi < (z_nat : ℝ) ^ 3)
    {k₁ : ℕ} (hk₁ : 1 ≤ k₁) (w : Fin (k₁ + 1) → ℝ)
    (hw0 : w 0 = (z_nat : ℝ)) (hw_end : w ⟨k₁, Nat.lt_succ_self k₁⟩ = xi)
    (hw_mono : StrictMono w)
    (G : TwoPrimeDiscreteGrid z_nat xi) :
    j_full_lb_z3 E_lo E_hi J_lb J_ub z_nat xi w G ≤ J_full z_nat xi := by
  have hxi1 : 1 ≤ xi := le_trans (by exact_mod_cast (by omega : 1 ≤ z_nat)) hzxi
  have hxi_lt_nat : Nat.floor xi < z_nat ^ 3 := by
    have h1 : (Nat.floor xi : ℝ) ≤ xi := Nat.floor_le (by linarith)
    exact_mod_cast (lt_of_le_of_lt h1 hxi3)
  have hie := J_full_two_prime_ie_ge z_nat (by linarith) hxi_lt_nat
  dsimp only at hie
  set xi_nat := Nat.floor xi
  set M := max z_nat (xi_nat + 1)
  set Q_z := (Finset.Ico z_nat M).filter (fun p => p.Prime ∧ 2 < p)
  have hz_le_fl : z_nat ≤ xi_nat := Nat.le_floor hzxi
  have hM_eq : M = xi_nat + 1 := max_eq_right (by omega)
  -- 0-prime lower bound
  have h0_le : J_lb xi ≤ J_odd xi := (hJ_lb xi hxi1).2
  -- 1-prime upper bound over disjoint intervals
  have h1_le : ∑ q ∈ Q_z, (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) ≤
      ∑ k : Fin k₁,
        let w0 := w k.castSucc
        let w1p := if k.val + 1 = k₁ then w k.succ + 1 else w k.succ
        J_ub (xi / w0) *
          (max 0 (Real.log (Real.log w1p / Real.log w0) + E_hi w1p + E_lo w0) +
            2 / (w0 - 2)) := by
    let pts : Fin (k₁ + 1) → ℕ := fun k =>
      if k.val = k₁ then xi_nat + 1 else Nat.ceil (w k)
    have hpts0 : pts 0 = z_nat := by
      have hk0 : (0 : ℕ) ≠ k₁ := by omega
      simp only [pts, Fin.val_zero, hk0, ↓reduceIte, hw0, Nat.ceil_natCast]
    have hptsend : pts ⟨k₁, Nat.lt_succ_self k₁⟩ = xi_nat + 1 := by
      simp [pts]
    have hpts_mono : ∀ k : Fin k₁, pts k.castSucc ≤ pts k.succ := by
      intro k
      have hk_ne : k.val ≠ k₁ := by omega
      by_cases hlast : k.val + 1 = k₁
      · simp only [pts, Fin.val_castSucc, Fin.val_succ, hk_ne, hlast, ↓reduceIte]
        have hw_le_xi : w k.castSucc ≤ xi := by
          rw [← hw_end]
          exact StrictMono.monotone hw_mono (Fin.le_last _)
        have hceil_le : Nat.ceil (w k.castSucc) ≤ Nat.ceil xi := Nat.ceil_mono hw_le_xi
        exact hceil_le.trans (Nat.ceil_le_floor_add_one xi)
      · simp only [pts, Fin.val_castSucc, Fin.val_succ, hk_ne, hlast, ↓reduceIte]
        exact Nat.ceil_mono (StrictMono.monotone hw_mono (Fin.castSucc_lt_succ).le)
    have hQz_sum : ∑ q ∈ Q_z, (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) =
        ∑ q ∈ Finset.Ico z_nat (xi_nat + 1),
          (if q.Prime then (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) else 0) := by
      rw [← hM_eq, Finset.sum_filter]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq_ge3 : 2 < q := lt_of_lt_of_le (by omega : 2 < z_nat) (Finset.mem_Ico.mp hq).1
      by_cases hpr : q.Prime
      · simp [hpr, hq_ge3]
      · simp [hpr]
    rw [hQz_sum, ← hpts0, ← hptsend, sum_Ico_partition pts hpts_mono]
    refine Finset.sum_le_sum fun k _ => ?_
    set w0 := w k.castSucc
    set w1 := w k.succ
    set w1p := if k.val + 1 = k₁ then w1 + 1 else w1
    have hw0_ge : (z_nat : ℝ) ≤ w0 := by
      rw [← hw0]; exact StrictMono.monotone hw_mono (Fin.zero_le _)
    have hw0_gt2 : 2 < w0 := lt_of_lt_of_le (by exact_mod_cast (by omega : 2 < z_nat)) hw0_ge
    have hw0_lt_w1 : w0 < w1 := hw_mono Fin.castSucc_lt_succ
    have hw1_le_xi : w1 ≤ xi := by
      rw [← hw_end]; exact StrictMono.monotone hw_mono (Fin.le_last _)
    have hw0_lt_xi : w0 < xi := lt_of_lt_of_le hw0_lt_w1 hw1_le_xi
    have hxi_w0_ge1 : 1 ≤ xi / w0 := (one_le_div (by linarith)).mpr hw0_lt_xi.le
    have hk_ne : k.val ≠ k₁ := by omega
    have hpts_k : pts k.castSucc = Nat.ceil w0 := by
      simp only [pts, Fin.val_castSucc, hk_ne, ↓reduceIte, w0]
    rw [hpts_k]
    have hterm_le : ∑ q ∈ Finset.Ico (Nat.ceil w0) (pts k.succ),
        (if q.Prime then (1 / ((q : ℝ) - 2)) * J_odd (xi / (q : ℝ)) else 0) ≤
        J_odd (xi / w0) *
          ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
            (1 / ((q : ℝ) - 2)) := by
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_ge : Nat.ceil w0 ≤ q := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
      have hw0_le_q : w0 ≤ (q : ℝ) := (Nat.le_ceil w0).trans (by exact_mod_cast hq_ge)
      have hq_gt2 : 2 < (q : ℝ) := lt_of_lt_of_le hw0_gt2 hw0_le_q
      have hdiv_le : xi / (q : ℝ) ≤ xi / w0 :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) hw0_le_q
      have hJ_le := J_odd_mono hdiv_le
      have h1q_nn : 0 ≤ (1 : ℝ) / ((q : ℝ) - 2) := one_div_nonneg.mpr (by linarith)
      rw [mul_comm (J_odd (xi / w0))]
      exact mul_le_mul_of_nonneg_left hJ_le h1q_nn
    have hmert_le : ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
        (1 / ((q : ℝ) - 2)) ≤
        max 0 (Real.log (Real.log w1p / Real.log w0) + E_hi w1p + E_lo w0) +
          2 / (w0 - 2) := by
      by_cases hlast : k.val + 1 = k₁
      · have hpts_k1 : pts k.succ = xi_nat + 1 := by
          simp only [pts, Fin.val_succ, hlast, ↓reduceIte]
        have hw1_eq_xi : w1 = xi := by
          have hk_last : k.succ = ⟨k₁, Nat.lt_succ_self k₁⟩ := Fin.ext (by simp [hlast])
          dsimp only [w1]
          rw [hk_last, hw_end]
        have hw1p_eq : w1p = xi + 1 := by simp [w1p, hlast, hw1_eq_xi]
        rw [hpts_k1, hw1p_eq]
        have hsub_ico : (Finset.Ico (Nat.ceil w0) (xi_nat + 1)).filter Nat.Prime ⊆
            (Finset.Ico (Nat.ceil w0) (Nat.ceil (xi + 1))).filter Nat.Prime := by
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_Ico] at hq ⊢
          have hfl_le : xi_nat + 1 ≤ Nat.ceil (xi + 1) := by
            have h1 : (xi_nat : ℝ) + 1 ≤ xi + 1 := by
              linarith [Nat.floor_le (by linarith : 0 ≤ xi)]
            exact_mod_cast h1.trans (Nat.le_ceil _)
          exact ⟨⟨hq.1.1, lt_of_lt_of_le hq.1.2 hfl_le⟩, hq.2⟩
        have hsum_sub : ∑ q ∈ (Finset.Ico (Nat.ceil w0) (xi_nat + 1)).filter Nat.Prime,
              (1 : ℝ) / ((q : ℝ) - 2) ≤
            ∑ q ∈ (Finset.Ico (Nat.ceil w0) (Nat.ceil (xi + 1))).filter Nat.Prime,
              (1 : ℝ) / ((q : ℝ) - 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_ico fun q hq _ => by
            have hq_ge := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
            have : 2 < (q : ℝ) := lt_of_lt_of_le hw0_gt2 ((Nat.le_ceil w0).trans (by exact_mod_cast hq_ge))
            have : 0 < (q : ℝ) - 2 := by linarith
            positivity
        have hm := sum_prime_inv_sub_two_Ico_le hM hw0_gt2 (by linarith : w0 < xi + 1)
        linarith [le_max_right (0 : ℝ) (Real.log (Real.log (xi + 1) / Real.log w0) + E_hi (xi + 1) + E_lo w0)]
      · have hpts_k1 : pts k.succ = Nat.ceil w1 := by
          simp only [pts, Fin.val_succ, hlast, ↓reduceIte, w1]
        have hw1p_eq : w1p = w1 := by simp [w1p, hlast]
        rw [hpts_k1, hw1p_eq]
        have hm := sum_prime_inv_sub_two_Ico_le hM hw0_gt2 hw0_lt_w1
        linarith [le_max_right (0 : ℝ) (Real.log (Real.log w1 / Real.log w0) + E_hi w1 + E_lo w0)]
    have hJub_le := hJ_ub (xi / w0) hxi_w0_ge1
    have hsum_nn : 0 ≤ ∑ q ∈ (Finset.Ico (Nat.ceil w0) (pts k.succ)).filter Nat.Prime,
        (1 : ℝ) / ((q : ℝ) - 2) := by
      refine Finset.sum_nonneg fun q hq => ?_
      have hq_ge := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
      have : 2 < (q : ℝ) := lt_of_lt_of_le hw0_gt2 ((Nat.le_ceil w0).trans (by exact_mod_cast hq_ge))
      positivity
    have hmert_nn : 0 ≤ max 0 (Real.log (Real.log w1p / Real.log w0) + E_hi w1p + E_lo w0) +
        2 / (w0 - 2) := by
      have : 0 < w0 - 2 := by linarith
      have : 0 ≤ max 0 (Real.log (Real.log w1p / Real.log w0) + E_hi w1p + E_lo w0) := le_max_left _ _
      positivity
    have hJnn : 0 ≤ J_odd (xi / w0) := J_odd_nonneg _
    exact hterm_le.trans (mul_le_mul hJub_le hmert_le hsum_nn (hJnn.trans hJub_le))
  -- 2-prime lower bound over disjoint boxes
  have h2_le :
      ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
        max 0 (Real.log (Real.log (G.a i.succ) / Real.log (G.a i.castSucc)) -
          E_lo (G.a i.succ) - E_hi (G.a i.castSucc)) *
        max 0 (Real.log (Real.log (G.b i j.succ) / Real.log (G.b i j.castSucc)) -
          E_lo (G.b i j.succ) - E_hi (G.b i j.castSucc)) *
        J_lb (xi / (G.a i.succ * G.b i j.succ)) ≤
      ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
        (1 / (((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2))) * J_odd (xi / ((q₁ * q₂ : ℕ) : ℝ)) := by
    let B : (Σ i : Fin G.m₁, Fin (G.m₂ i)) → Finset (ℕ × ℕ) := fun p =>
      (Finset.Ico (Nat.ceil (G.a p.1.castSucc)) (Nat.ceil (G.a p.1.succ))).filter Nat.Prime ×ˢ
      (Finset.Ico (Nat.ceil (G.b p.1 p.2.castSucc)) (Nat.ceil (G.b p.1 p.2.succ))).filter Nat.Prime
    let F2 : ℕ × ℕ → ℝ := fun q =>
      (1 / (((q.1 : ℝ) - 2) * ((q.2 : ℝ) - 2))) * J_odd (xi / ((q.1 * q.2 : ℕ) : ℝ))
    have hB_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Σ i : Fin G.m₁, Fin (G.m₂ i))) B := by
      rintro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      rintro ⟨q₁, q₂⟩ h1 h2
      simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_Ico] at h1 h2
      rcases lt_trichotomy i₁ i₂ with hi | rfl | hi
      · have hle : G.a i₁.succ ≤ G.a i₂.castSucc := StrictMono.monotone G.ha_mono (by
          change i₁.val + 1 ≤ i₂.val; exact Fin.lt_def.mp hi)
        have h1_lt : (q₁ : ℝ) < G.a i₁.succ := Nat.lt_ceil.mp h1.1.1.2
        have h2_ge : G.a i₂.castSucc ≤ (q₁ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h2.1.1.1)
        linarith
      · have hjne : j₁ ≠ j₂ := fun h => hne (by subst h; rfl)
        rcases lt_or_gt_of_ne hjne with hj | hj
        · have hle : G.b i₁ j₁.succ ≤ G.b i₁ j₂.castSucc := StrictMono.monotone (G.hb_mono i₁) (by
            change j₁.val + 1 ≤ j₂.val; exact Fin.lt_def.mp hj)
          have h1_lt : (q₂ : ℝ) < G.b i₁ j₁.succ := Nat.lt_ceil.mp h1.2.1.2
          have h2_ge : G.b i₁ j₂.castSucc ≤ (q₂ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h2.2.1.1)
          linarith
        · have hle : G.b i₁ j₂.succ ≤ G.b i₁ j₁.castSucc := StrictMono.monotone (G.hb_mono i₁) (by
            change j₂.val + 1 ≤ j₁.val; exact Fin.lt_def.mp hj)
          have h2_lt : (q₂ : ℝ) < G.b i₁ j₂.succ := Nat.lt_ceil.mp h2.2.1.2
          have h1_ge : G.b i₁ j₁.castSucc ≤ (q₂ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1.2.1.1)
          linarith
      · have hle : G.a i₂.succ ≤ G.a i₁.castSucc := StrictMono.monotone G.ha_mono (by
          change i₂.val + 1 ≤ i₁.val; exact Fin.lt_def.mp hi)
        have h2_lt : (q₁ : ℝ) < G.a i₂.succ := Nat.lt_ceil.mp h2.1.1.2
        have h1_ge : G.a i₁.castSucc ≤ (q₁ : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1.1.1.1)
        linarith
    let S_full : Finset (ℕ × ℕ) := Q_z.sigma (fun q₁ => Q_z.filter (q₁ < ·)) |>.map
      ⟨fun p => (p.1, p.2), fun p₁ p₂ h => by
        rcases p₁ with ⟨a₁, b₁⟩; rcases p₂ with ⟨a₂, b₂⟩
        simp only [Prod.mk.injEq] at h; simp [h.1, h.2]⟩
    have hB_sub : ∀ p ∈ (Finset.univ : Finset (Σ i : Fin G.m₁, Fin (G.m₂ i))), B p ⊆ S_full := by
      rintro ⟨i, j⟩ _ ⟨q₁, q₂⟩ hq
      simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_Ico] at hq
      rcases hq with ⟨⟨hq₁_ico, hq₁_pr⟩, ⟨hq₂_ico, hq₂_pr⟩⟩
      have ha0_ge : (z_nat : ℝ) ≤ G.a i.castSucc :=
        G.ha_ge.trans (StrictMono.monotone G.ha_mono (Fin.zero_le _))
      have ha_lt : G.a i.castSucc < G.a i.succ := G.ha_mono Fin.castSucc_lt_succ
      have hb0_ge : G.a i.succ ≤ G.b i j.castSucc :=
        (G.hb_ge i).trans (StrictMono.monotone (G.hb_mono i) (Fin.zero_le _))
      have hb_lt : G.b i j.castSucc < G.b i j.succ := (G.hb_mono i) Fin.castSucc_lt_succ
      have hq₁_ge_z : z_nat ≤ q₁ := by
        have h1 : (z_nat : ℝ) ≤ (q₁ : ℝ) :=
          ha0_ge.trans ((Nat.le_ceil _).trans (by exact_mod_cast hq₁_ico.1))
        exact_mod_cast h1
      have hq₁_lt_a1 : (q₁ : ℝ) < G.a i.succ := Nat.lt_ceil.mp hq₁_ico.2
      have hb0_le_q₂ : G.b i j.castSucc ≤ (q₂ : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hq₂_ico.1)
      have hq₂_lt_b1 : (q₂ : ℝ) < G.b i j.succ := Nat.lt_ceil.mp hq₂_ico.2
      have hq₁_lt_q₂ : q₁ < q₂ := by exact_mod_cast lt_of_lt_of_le hq₁_lt_a1 (hb0_ge.trans hb0_le_q₂)
      have hq₂_ge_z : z_nat ≤ q₂ := hq₁_ge_z.trans hq₁_lt_q₂.le
      have ha1_gt1 : 1 < G.a i.succ := by
        have : (3 : ℝ) ≤ (z_nat : ℝ) := by exact_mod_cast hz3
        linarith
      have hb1_gt1 : 1 < G.b i j.succ := by linarith
      have hprod_ij := G.hb_le i j
      have hq₁_lt_xi : (q₁ : ℝ) < xi := by
        have : G.a i.succ ≤ G.a i.succ * G.b i j.succ :=
          le_mul_of_one_le_right (by linarith) hb1_gt1.le
        linarith
      have hq₂_lt_xi : (q₂ : ℝ) < xi := by
        have : G.b i j.succ ≤ G.a i.succ * G.b i j.succ :=
          le_mul_of_one_le_left (by linarith) ha1_gt1.le
        linarith
      have hq₁_lt_M : q₁ < M := lt_of_le_of_lt (Nat.le_floor hq₁_lt_xi.le)
        (lt_of_lt_of_le (Nat.lt_succ_self xi_nat) (le_max_right _ _))
      have hq₂_lt_M : q₂ < M := lt_of_le_of_lt (Nat.le_floor hq₂_lt_xi.le)
        (lt_of_lt_of_le (Nat.lt_succ_self xi_nat) (le_max_right _ _))
      have hq₁Q : q₁ ∈ Q_z := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hq₁_ge_z, hq₁_lt_M⟩, hq₁_pr, by omega⟩
      have hq₂Q : q₂ ∈ Q_z := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hq₂_ge_z, hq₂_lt_M⟩, hq₂_pr, by omega⟩
      simp only [S_full, Finset.mem_map, Finset.mem_sigma, Finset.mem_filter]
      exact ⟨⟨q₁, q₂⟩, ⟨hq₁Q, hq₂Q, hq₁_lt_q₂⟩, rfl⟩
    have hF2_nn : ∀ q ∈ S_full, 0 ≤ F2 q := by
      rintro q hq
      simp only [S_full, Finset.mem_map, Finset.mem_sigma, Finset.mem_filter] at hq
      rcases hq with ⟨⟨q₁, q₂⟩, ⟨ha, hb, _⟩, rfl⟩
      have ha_gt2 : 2 < q₁ := (Finset.mem_filter.mp ha).2.2
      have hb_gt2 : 2 < q₂ := (Finset.mem_filter.mp hb).2.2
      have h1 : (0 : ℝ) < (q₁ : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast ha_gt2
        linarith
      have h2 : (0 : ℝ) < (q₂ : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (q₂ : ℝ) := by exact_mod_cast hb_gt2
        linarith
      have hden_pos : 0 < ((q₁ : ℝ) - 2) * ((q₂ : ℝ) - 2) := mul_pos h1 h2
      exact mul_nonneg (one_div_nonneg.mpr hden_pos.le) (J_odd_nonneg _)
    have hS_full_eq : ∑ q ∈ S_full, F2 q =
        ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·), F2 (q₁, q₂) := by
      simp only [S_full, Finset.sum_map, Finset.sum_sigma]
      rfl
    have hbox_le : ∀ p : Σ i : Fin G.m₁, Fin (G.m₂ i),
        max 0 (Real.log (Real.log (G.a p.1.succ) / Real.log (G.a p.1.castSucc)) -
          E_lo (G.a p.1.succ) - E_hi (G.a p.1.castSucc)) *
        max 0 (Real.log (Real.log (G.b p.1 p.2.succ) / Real.log (G.b p.1 p.2.castSucc)) -
          E_lo (G.b p.1 p.2.succ) - E_hi (G.b p.1 p.2.castSucc)) *
        J_lb (xi / (G.a p.1.succ * G.b p.1 p.2.succ)) ≤
        ∑ q ∈ B p, F2 q := by
      rintro ⟨i, j⟩
      have ha0_gt2 : 2 < G.a i.castSucc := by
        have h3 : (3 : ℝ) ≤ (z_nat : ℝ) := by exact_mod_cast hz3
        linarith [G.ha_ge, StrictMono.monotone G.ha_mono (Fin.zero_le i.castSucc)]
      have ha_lt := G.ha_mono (Fin.castSucc_lt_succ (i := i))
      have hab := (G.hb_ge i).trans (StrictMono.monotone (G.hb_mono i) (Fin.zero_le j.castSucc))
      have hb_lt := (G.hb_mono i) (Fin.castSucc_lt_succ (i := j))
      have hprod := G.hb_le i j
      have hdiv_ge1 : 1 ≤ xi / (G.a i.succ * G.b i j.succ) := by
        have : 0 < G.a i.succ * G.b i j.succ := mul_pos (by linarith) (by linarith)
        exact (one_le_div this).mpr hprod
      have hJlb := hJ_lb (xi / (G.a i.succ * G.b i j.succ)) hdiv_ge1
      have hbox := two_prime_box_ge hM ha0_gt2 ha_lt hab hb_lt hprod
      have hs1_nn : 0 ≤ max 0 (Real.log (Real.log (G.a i.succ) / Real.log (G.a i.castSucc)) -
          E_lo (G.a i.succ) - E_hi (G.a i.castSucc)) := le_max_left _ _
      have hs2_nn : 0 ≤ max 0 (Real.log (Real.log (G.b i j.succ) / Real.log (G.b i j.castSucc)) -
          E_lo (G.b i j.succ) - E_hi (G.b i j.castSucc)) := le_max_left _ _
      have hstep :
          max 0 (Real.log (Real.log (G.a i.succ) / Real.log (G.a i.castSucc)) -
            E_lo (G.a i.succ) - E_hi (G.a i.castSucc)) *
          max 0 (Real.log (Real.log (G.b i j.succ) / Real.log (G.b i j.castSucc)) -
            E_lo (G.b i j.succ) - E_hi (G.b i j.castSucc)) *
          J_lb (xi / (G.a i.succ * G.b i j.succ)) ≤
          max 0 (Real.log (Real.log (G.a i.succ) / Real.log (G.a i.castSucc)) -
            E_lo (G.a i.succ) - E_hi (G.a i.castSucc)) *
          max 0 (Real.log (Real.log (G.b i j.succ) / Real.log (G.b i j.castSucc)) -
            E_lo (G.b i j.succ) - E_hi (G.b i j.castSucc)) *
          J_odd (xi / (G.a i.succ * G.b i j.succ)) :=
        mul_le_mul_of_nonneg_left hJlb.2 (mul_nonneg hs1_nn hs2_nn)
      have hB_eq : ∑ q ∈ B ⟨i, j⟩, F2 q =
          ∑ q₁ ∈ (Finset.Ico (Nat.ceil (G.a i.castSucc)) (Nat.ceil (G.a i.succ))).filter Nat.Prime,
          ∑ q₂ ∈ (Finset.Ico (Nat.ceil (G.b i j.castSucc)) (Nat.ceil (G.b i j.succ))).filter Nat.Prime,
            F2 (q₁, q₂) := by
        simp only [B, Finset.sum_product]
      rw [hB_eq]
      exact hstep.trans hbox
    have hdisj_sum := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.biUnion_subset.mpr hB_sub) (fun q hq _ => hF2_nn q hq)
    rw [Finset.sum_biUnion (fun x hx y hy hxy => hB_disj hx hy hxy)] at hdisj_sum
    calc ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
          max 0 (Real.log (Real.log (G.a i.succ) / Real.log (G.a i.castSucc)) -
            E_lo (G.a i.succ) - E_hi (G.a i.castSucc)) *
          max 0 (Real.log (Real.log (G.b i j.succ) / Real.log (G.b i j.castSucc)) -
            E_lo (G.b i j.succ) - E_hi (G.b i j.castSucc)) *
          J_lb (xi / (G.a i.succ * G.b i j.succ))
        = ∑ p : Σ i : Fin G.m₁, Fin (G.m₂ i),
            max 0 (Real.log (Real.log (G.a p.1.succ) / Real.log (G.a p.1.castSucc)) -
              E_lo (G.a p.1.succ) - E_hi (G.a p.1.castSucc)) *
            max 0 (Real.log (Real.log (G.b p.1 p.2.succ) / Real.log (G.b p.1 p.2.castSucc)) -
              E_lo (G.b p.1 p.2.succ) - E_hi (G.b p.1 p.2.castSucc)) *
            J_lb (xi / (G.a p.1.succ * G.b p.1 p.2.succ)) := by rw [Fintype.sum_sigma]
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Σ i : Fin G.m₁, Fin (G.m₂ i))), ∑ q ∈ B p, F2 q :=
          Finset.sum_le_sum fun p _ => hbox_le p
      _ ≤ ∑ q ∈ S_full, F2 q := hdisj_sum
      _ = ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·), F2 (q₁, q₂) := hS_full_eq
  unfold j_full_lb_z3
  dsimp only
  linarith

/-- Soundness of `j_full_lb_z3` specialized to `External.MertensPrimeSumPremise` and
`J_odd_asymptotic_enclosure` (`J_odd_lb_asym`, `J_odd_ub_asym`). -/
theorem j_full_lb_z3_ge
    {M0 : ℝ} (hM : External.MertensPrimeSumPremise M0)
    {z_nat : ℕ} (hz3 : 3 ≤ z_nat) {xi : ℝ}
    (hzxi : (z_nat : ℝ) ≤ xi) (hxi3 : xi < (z_nat : ℝ) ^ 3)
    {k₁ : ℕ} (hk₁ : 1 ≤ k₁) (w : Fin (k₁ + 1) → ℝ)
    (hw0 : w 0 = (z_nat : ℝ)) (hw_end : w ⟨k₁, Nat.lt_succ_self k₁⟩ = xi)
    (hw_mono : StrictMono w)
    (G : TwoPrimeDiscreteGrid z_nat xi) :
    j_full_lb_z3 External.jsMertensLoErr External.jsMertensHiErr
        J_odd_lb_asym J_odd_ub_asym z_nat xi w G ≤
      J_full z_nat xi :=
  j_full_lb_z3_ge_general hM.mertensSumBounds
    (fun _ hX => ⟨J_odd_lb_asym_nonneg _, J_odd_lb_asym_le hX⟩)
    (fun _ hX => le_J_odd_ub_asym hX)
    hz3 hzxi hxi3 hk₁ w hw0 hw_end hw_mono G

end DiscreteJFullLB

end BuchstabSwitching
