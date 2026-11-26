import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstH0
import Mathlib.Tactic

/-!
# Certified Unconditional Upper Bound on `H_quarter` and `C_J`

Provides kernel-verified unconditional upper bounds (`H_quarter_le_cert`, `C_J_le_cert`)
via `M₀ = 400` truncation (`RayCertInstH0.oddPrimes400Data`) and odd-integer telescoping.
-/

namespace BuchstabSwitching

noncomputable section

section RayCertCJ

private def prodHqIv (xs : List (ℕ × ℕ × ℕ)) (hi : ℕ) : ℕ :=
  xs.foldl (fun acc ⟨p, r4, r2⟩ =>
    let den := 1000 * p * (p - 2)
    let num := den + 2 * r4 + r2
    hstarCeilDiv (acc * num) den) hi

private lemma prodHqIv_append (xs₁ xs₂ : List (ℕ × ℕ × ℕ)) (hi : ℕ) :
    prodHqIv (xs₁ ++ xs₂) hi = prodHqIv xs₂ (prodHqIv xs₁ hi) := by
  simp [prodHqIv, List.foldl_append]

private lemma prodHq_c0 : prodHqIv oddPrimes400DataC0 scaleS = 5060109186177 := by decide
private lemma prodHq_c1 : prodHqIv oddPrimes400DataC1 5060109186177 = 5191015527871 := by decide
private lemma prodHq_c2 : prodHqIv oddPrimes400DataC2 5191015527871 = 5236661307771 := by decide
private lemma prodHq_c3 : prodHqIv oddPrimes400DataC3 5236661307771 = 5257275723915 := by decide

private lemma prodHqIv_sound (xs : List (ℕ × ℕ × ℕ))
    (hxs : ∀ x ∈ xs, 3 ≤ x.1 ∧ x.1 * 1000 ^ 4 ≤ x.2.1 ^ 4 ∧ x.1 * 1000 ^ 2 ≤ x.2.2 ^ 2) :
    ∀ hi : ℕ,
      ((hi : ℝ) / (scaleS : ℝ)) *
          (xs.map (fun x =>
            1 + (2 * (x.1 : ℝ) ^ (1 / 4 : ℝ) + (x.1 : ℝ) ^ (1 / 2 : ℝ)) /
              ((x.1 : ℝ) * ((x.1 : ℝ) - 2)))).prod ≤
        ((prodHqIv xs hi : ℕ) : ℝ) / (scaleS : ℝ) := by
  induction xs with
  | nil => intro hi; simp [prodHqIv]
  | cons x tl ih =>
    intro hi
    rcases x with ⟨p, r4, r2⟩
    have hx := hxs (p, r4, r2) List.mem_cons_self
    have htl : ∀ y ∈ tl, 3 ≤ y.1 ∧ y.1 * 1000 ^ 4 ≤ y.2.1 ^ 4 ∧ y.1 * 1000 ^ 2 ≤ y.2.2 ^ 2 :=
      fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    set den : ℕ := 1000 * p * (p - 2)
    set num : ℕ := den + 2 * r4 + r2
    have hden_pos : 0 < den := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hx.1
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have hr4_bd : (p : ℝ) ^ (1 / 4 : ℝ) ≤ (r4 : ℝ) / 1000 := by
      have hpow : (p : ℝ) ≤ ((r4 : ℝ) / 1000) ^ 4 := by
        rw [div_pow, le_div_iff₀ (by norm_num)]
        exact_mod_cast hx.2.1
      have h1 := Real.rpow_le_rpow hp_pos.le hpow (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h1
      simpa using h1
    have hr2_bd : (p : ℝ) ^ (1 / 2 : ℝ) ≤ (r2 : ℝ) / 1000 := by
      have hpow : (p : ℝ) ≤ ((r2 : ℝ) / 1000) ^ 2 := by
        rw [div_pow, le_div_iff₀ (by norm_num)]
        exact_mod_cast hx.2.2
      have h1 := Real.rpow_le_rpow hp_pos.le hpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h1
      simpa using h1
    have hfac_le : 1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
        ((p : ℝ) * ((p : ℝ) - 2)) ≤ (num : ℝ) / (den : ℝ) := by
      have hden_real : (den : ℝ) = 1000 * (p : ℝ) * ((p : ℝ) - 2) := by
        dsimp only [den]; rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
      have hnum_real : (num : ℝ) = 1000 * (p : ℝ) * ((p : ℝ) - 2) + 2 * (r4 : ℝ) + (r2 : ℝ) := by
        dsimp only [num]; push_cast; rw [hden_real]
      have htop : 2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ) ≤
          (2 * (r4 : ℝ) + (r2 : ℝ)) / 1000 := by linarith
      have hdiv1 : (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
          ((2 * (r4 : ℝ) + (r2 : ℝ)) / 1000) / ((p : ℝ) * ((p : ℝ) - 2)) :=
        div_le_div_of_nonneg_right htop (mul_pos hp_pos hp2_pos).le
      rw [hnum_real, hden_real]
      have hid : 1 + ((2 * (r4 : ℝ) + (r2 : ℝ)) / 1000) / ((p : ℝ) * ((p : ℝ) - 2)) =
          (1000 * (p : ℝ) * ((p : ℝ) - 2) + 2 * (r4 : ℝ) + (r2 : ℝ)) /
            (1000 * (p : ℝ) * ((p : ℝ) - 2)) := by field_simp; ring
      linarith
    have hS : (0 : ℝ) < (scaleS : ℝ) := scaleS_pos
    have hstep : ((hi : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ)) ≤
        ((hstarCeilDiv (hi * num) den : ℕ) : ℝ) / (scaleS : ℝ) := by
      have h1 : (hi : ℝ) * (num : ℝ) / (den : ℝ) ≤
          ((hstarCeilDiv (hi * num) den : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by exact_mod_cast hden_pos)]
        have h2 : hi * num ≤ hstarCeilDiv (hi * num) den * den := by
          by_cases hz : hi * num = 0
          · rw [hz]; simp
          · unfold hstarCeilDiv
            have h1' := Nat.div_add_mod (hi * num + den - 1) den
            have h2' := Nat.mod_lt (hi * num + den - 1) hden_pos
            have hcomm : den * ((hi * num + den - 1) / den) = (hi * num + den - 1) / den * den :=
              Nat.mul_comm _ _
            omega
        exact_mod_cast h2
      calc ((hi : ℝ) / (scaleS : ℝ)) * ((num : ℝ) / (den : ℝ))
          = ((hi : ℝ) * (num : ℝ) / (den : ℝ)) / (scaleS : ℝ) := by ring
        _ ≤ ((hstarCeilDiv (hi * num) den : ℕ) : ℝ) / (scaleS : ℝ) :=
            div_le_div_of_nonneg_right h1 hS.le
    have hprod_nn : 0 ≤ (tl.map (fun y =>
        1 + (2 * (y.1 : ℝ) ^ (1 / 4 : ℝ) + (y.1 : ℝ) ^ (1 / 2 : ℝ)) /
          ((y.1 : ℝ) * ((y.1 : ℝ) - 2)))).prod := by
      refine List.prod_nonneg ?_
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro y hy
      have hy3 : (3 : ℝ) ≤ (y.1 : ℝ) := by exact_mod_cast (htl y hy).1
      have : (0 : ℝ) < (y.1 : ℝ) - 2 := by linarith
      positivity
    have hrec := ih htl (hstarCeilDiv (hi * num) den)
    dsimp only [prodHqIv] at hrec ⊢
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    have hfac_mul : ((hi : ℝ) / (scaleS : ℝ)) *
        (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
          ((p : ℝ) * ((p : ℝ) - 2))) ≤
        ((hstarCeilDiv (hi * num) den : ℕ) : ℝ) / (scaleS : ℝ) :=
      (mul_le_mul_of_nonneg_left hfac_le (div_nonneg (Nat.cast_nonneg _) hS.le)).trans hstep
    calc ((hi : ℝ) / (scaleS : ℝ)) *
          ((1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
            ((p : ℝ) * ((p : ℝ) - 2))) *
            (tl.map (fun y =>
              1 + (2 * (y.1 : ℝ) ^ (1 / 4 : ℝ) + (y.1 : ℝ) ^ (1 / 2 : ℝ)) /
                ((y.1 : ℝ) * ((y.1 : ℝ) - 2)))).prod)
        = (((hi : ℝ) / (scaleS : ℝ)) *
            (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
              ((p : ℝ) * ((p : ℝ) - 2)))) *
            (tl.map (fun y =>
              1 + (2 * (y.1 : ℝ) ^ (1 / 4 : ℝ) + (y.1 : ℝ) ^ (1 / 2 : ℝ)) /
                ((y.1 : ℝ) * ((y.1 : ℝ) - 2)))).prod := by ring
      _ ≤ (((hstarCeilDiv (hi * num) den : ℕ) : ℝ) / (scaleS : ℝ)) *
            (tl.map (fun y =>
              1 + (2 * (y.1 : ℝ) ^ (1 / 4 : ℝ) + (y.1 : ℝ) ^ (1 / 2 : ℝ)) /
                ((y.1 : ℝ) * ((y.1 : ℝ) - 2)))).prod :=
          mul_le_mul_of_nonneg_right hfac_mul hprod_nn
      _ ≤ ((prodHqIv tl (hstarCeilDiv (hi * num) den) : ℕ) : ℝ) / (scaleS : ℝ) := hrec

private lemma inv_rpow_three_halves_le_sqrt_sub {n : ℕ} (hn : 3 ≤ n) :
    ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤
      1 / Real.sqrt ((n : ℝ) - 2) - 1 / Real.sqrt (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : 0 < (n : ℝ) - 2 := by linarith
  have h2 : 0 < (n : ℝ) := by linarith
  have hs1 : 0 < Real.sqrt ((n : ℝ) - 2) := Real.sqrt_pos.mpr h1
  have hs2 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr h2
  have hs1_le : Real.sqrt ((n : ℝ) - 2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have hdiff_id : (1 / Real.sqrt ((n : ℝ) - 2) - 1 / Real.sqrt (n : ℝ)) *
      (Real.sqrt ((n : ℝ) - 2) * Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 2))) =
      2 := by
    have hsq1 : Real.sqrt ((n : ℝ) - 2) ^ 2 = (n : ℝ) - 2 := Real.sq_sqrt h1.le
    have hsq2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt h2.le
    field_simp [hs1.ne', hs2.ne']
    nlinarith [hsq1, hsq2]
  have hden_pos : 0 < Real.sqrt ((n : ℝ) - 2) * Real.sqrt (n : ℝ) *
      (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 2)) := by positivity
  have hden_le : Real.sqrt ((n : ℝ) - 2) * Real.sqrt (n : ℝ) *
      (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 2)) ≤ 2 * (n : ℝ) * Real.sqrt (n : ℝ) := by
    have hp1 : Real.sqrt ((n : ℝ) - 2) * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right hs1_le hs2.le
    have hp2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt h2.le
    have hp3 : Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 2) ≤ 2 * Real.sqrt (n : ℝ) := by linarith
    calc Real.sqrt ((n : ℝ) - 2) * Real.sqrt (n : ℝ) *
            (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 2))
        ≤ (n : ℝ) * (2 * Real.sqrt (n : ℝ)) :=
          mul_le_mul (hp1.trans_eq hp2) hp3 (by positivity) h2.le
      _ = 2 * (n : ℝ) * Real.sqrt (n : ℝ) := by ring
  have hrpow_id : ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ = 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' h2.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
    norm_num [one_div]
  rw [hrpow_id]
  have hleft : 1 / Real.sqrt ((n : ℝ) - 2) - 1 / Real.sqrt (n : ℝ) =
      2 / (Real.sqrt ((n : ℝ) - 2) * Real.sqrt (n : ℝ) *
        (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 2))) := (eq_div_iff hden_pos.ne').mpr hdiff_id
  rw [hleft]
  calc 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) = 2 / (2 * (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    _ ≤ 2 / (Real.sqrt ((n : ℝ) - 2) * Real.sqrt (n : ℝ) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) - 2))) :=
        div_le_div_of_nonneg_left (by norm_num) hden_pos hden_le

theorem H_quarter_le_cert :
    H_quarter ≤ (5671279098075 : ℝ) / (scaleS : ℝ) := by
  have htend := summable_abs_h_J_mul_rpow.hasSum.tendsto_sum_nat
  refine le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨400, fun M hM => ?_⟩)
  set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
  have hP : ∀ p ∈ P, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
  let S_range : Finset ℕ :=
    (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2)
  have hsub : S_range ⊆ B_cubefree P := by
    intro b hb
    simp only [S_range, Finset.mem_filter, Finset.mem_range, B_cubefree, Finset.mem_Icc] at hb ⊢
    rcases hb with ⟨hbM, hb_odd, hb_fac⟩
    have hb0 : b ≠ 0 := by intro h0; subst h0; exact absurd hb_odd (by decide)
    have hb_pf : b.primeFactors ⊆ P := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd := Nat.dvd_of_mem_primeFactors hp
      have hp_ne2 : p ≠ 2 := by
        intro h2; subst h2
        exact Nat.not_even_iff_odd.mpr hb_odd (even_iff_two_dvd.mpr hp_dvd)
      have hp_le := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hp_dvd
      have hp_ge2 := hp_prime.two_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, by omega⟩
    have hb_le : b ≤ ∏ p ∈ P, p ^ 2 := by
      have h_eq := (prod_primeFactors_pow_factorization hb0).symm
      calc b = ∏ p ∈ b.primeFactors, p ^ b.factorization p := h_eq
        _ ≤ ∏ p ∈ b.primeFactors, p ^ 2 :=
            Finset.prod_le_prod fun p hp =>
              Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (hb_fac p hp)
        _ ≤ ∏ p ∈ P, p ^ 2 :=
            Finset.prod_le_prod_of_subset_of_one_le hb_pf fun p hp _ =>
              Nat.one_le_pow 2 p (hP p hp).1.pos
    exact ⟨⟨Nat.pos_of_ne_zero hb0, hb_le⟩, hb_odd, hb_pf, hb_fac⟩
  have hsum_eq : ∑ b ∈ Finset.range M, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) =
      ∑ b ∈ S_range, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hcond : Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2
    · exact (ite_eq_left hcond).symm
    · have hh0 : h_J b = 0 := by unfold h_J; exact ite_eq_right hcond
      rw [ite_eq_right hcond, hh0, abs_zero, zero_mul]
  have hprod_bound : ∑ b ∈ Finset.range M, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      ∏ p ∈ P, (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
        ((p : ℝ) * ((p : ℝ) - 2))) := by
    calc ∑ b ∈ Finset.range M, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)
        = ∑ b ∈ S_range, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) := hsum_eq
      _ ≤ ∑ b ∈ B_cubefree P, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∏ p ∈ P, (1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
            ((p : ℝ) * ((p : ℝ) - 2))) := sum_B_cubefree_abs_rpow P hP
  set P_400 : Finset ℕ := (Finset.range 400).filter (fun p => p.Prime ∧ 2 < p)
  set P_tail : Finset ℕ := (Finset.Ico 400 M).filter (fun p => p.Prime ∧ 2 < p)
  have hdisj : Disjoint P_400 P_tail := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
    have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hp2).1
    omega
  have hunion : P = P_400 ∪ P_tail := by
    ext p
    simp only [P, P_400, P_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hpM, hpr, hp2⟩
      by_cases hp400 : p < 400
      · exact Or.inl ⟨hp400, hpr, hp2⟩
      · exact Or.inr ⟨⟨Nat.le_of_not_lt hp400, hpM⟩, hpr, hp2⟩
    · rintro (⟨hp400, hpr, hp2⟩ | ⟨⟨_, hpM⟩, hpr, hp2⟩)
      · exact ⟨lt_of_lt_of_le hp400 hM, hpr, hp2⟩
      · exact ⟨hpM, hpr, hp2⟩
  let g_hq : ℕ → ℝ := fun p =>
    1 + (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2))
  have hP400_bd : ∏ p ∈ P_400, g_hq p ≤ (5257275723915 : ℝ) / (scaleS : ℝ) := by
    have hprod_eq : ∏ p ∈ P_400, g_hq p = (oddPrimes400Data.map (fun x => g_hq x.1)).prod := by
      have h1 : P_400 = oddPrimes400.toFinset := oddPrimes400_eq
      rw [h1, List.prod_toFinset _ oddPrimes400_nodup, oddPrimes400, List.map_map]
      rfl
    have hsnd := prodHqIv_sound oddPrimes400Data (fun x hx => by
      have hxp := oddPrimes400Data_props x hx
      exact ⟨hxp.1, hxp.2.2.2.1, hxp.2.2.2.2⟩) scaleS
    have hcheck : prodHqIv oddPrimes400Data scaleS = 5257275723915 := by
      simp only [oddPrimes400Data, prodHqIv_append]
      rw [prodHq_c0, prodHq_c1, prodHq_c2, prodHq_c3]
    rw [hcheck] at hsnd
    have hdiv : ((scaleS : ℝ) / (scaleS : ℝ)) = 1 := div_self scaleS_pos.ne'
    rw [hdiv, one_mul] at hsnd
    rw [hprod_eq]
    exact hsnd
  have htail_bd : ∏ p ∈ P_tail, g_hq p ≤ (1000 / 927 : ℝ) := by
    have hprod_le : ∏ p ∈ P_tail, g_hq p ≤
        ∏ p ∈ P_tail, Real.exp ((2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) /
          ((p : ℝ) * ((p : ℝ) - 2))) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p _ => ?_)
      · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        dsimp [g_hq]; positivity
      · dsimp [g_hq]; rw [add_comm]; exact Real.add_one_le_exp _
    rw [← Real.exp_sum] at hprod_le
    have hsum_tail : ∑ p ∈ P_tail,
        (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
        (73 / 1000 : ℝ) := by
      have hpt : ∀ p ∈ P_tail,
          (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
            (129400 / 88953 : ℝ) * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        intro p hp
        have hp400 : (400 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have hp_r4 : (447 / 100 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := by
          have hpow : ((447 / 100 : ℝ) ^ (4 : ℕ)) ≤ (p : ℝ) := by norm_num; linarith
          have h1 := Real.rpow_le_rpow (by positivity) hpow (by norm_num : (0 : ℝ) ≤ 1 / 4)
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h1
          simpa using h1
        have hsqrt_id : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) = (p : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hp_pos]; norm_num
        have hnum_le : 2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ) ≤
            (647 / 447 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by
          have h1 : (447 / 100 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← hsqrt_id]; exact mul_le_mul_of_nonneg_right hp_r4 (by positivity)
          linarith
        have hden_ge : (199 / 200 : ℝ) * (p : ℝ) ^ 2 ≤ (p : ℝ) * ((p : ℝ) - 2) := by
          have hlin : (199 / 200 : ℝ) * (p : ℝ) ≤ (p : ℝ) - 2 := by linarith
          calc (199 / 200 : ℝ) * (p : ℝ) ^ 2
              = (p : ℝ) * ((199 / 200 : ℝ) * (p : ℝ)) := by ring
            _ ≤ (p : ℝ) * ((p : ℝ) - 2) := mul_le_mul_of_nonneg_left hlin hp_pos.le
        have hrpow_id : (p : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) ^ 2 = ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
          rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_sub hp_pos, ← Real.rpow_neg hp_pos.le]
          congr 1; norm_num
        calc (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2))
            ≤ ((647 / 447 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2)) :=
              div_le_div_of_nonneg_right hnum_le (mul_pos hp_pos (by linarith : 0 < (p : ℝ) - 2)).le
          _ ≤ ((647 / 447 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ)) / ((199 / 200 : ℝ) * (p : ℝ) ^ 2) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
          _ = (129400 / 88953 : ℝ) * ((p : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) ^ 2) := by ring
          _ = (129400 / 88953 : ℝ) * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by rw [hrpow_id]
      have hsub_img : P_tail ⊆ (Finset.Ico 200 M).image (fun j => 2 * j + 1) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpIco, hpr, hp2⟩
        rw [Finset.mem_Ico] at hpIco
        have hp_odd : Odd p := hpr.odd_of_ne_two (by omega)
        rcases hp_odd with ⟨j, rfl⟩
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
      have hsum1 : ∑ p ∈ P_tail,
          (2 * (p : ℝ) ^ (1 / 4 : ℝ) + (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
          (129400 / 88953 : ℝ) * ∑ p ∈ P_tail, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hpt
      have hsum2 : ∑ p ∈ P_tail, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤
          ∑ j ∈ Finset.Ico 200 M,
            (1 / Real.sqrt ((2 * j + 1 : ℝ) - 2) - 1 / Real.sqrt ((2 * j + 1 : ℝ))) := by
        calc ∑ p ∈ P_tail, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹
            ≤ ∑ p ∈ ((Finset.Ico 200 M).image (fun j => 2 * j + 1) : Finset ℕ),
                ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_img (fun _ _ _ => by positivity)
          _ = ∑ j ∈ Finset.Ico 200 M, (((2 * j + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
              Finset.sum_image (fun a _ b _ h => by omega)
          _ ≤ ∑ j ∈ Finset.Ico 200 M,
                (1 / Real.sqrt ((2 * j + 1 : ℝ) - 2) - 1 / Real.sqrt ((2 * j + 1 : ℝ))) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj200 : 200 ≤ j := (Finset.mem_Ico.mp hj).1
              simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
                inv_rpow_three_halves_le_sqrt_sub (n := 2 * j + 1) (by omega)
      have h200M : 200 ≤ M := by omega
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h200M
      have htel : ∀ k : ℕ, ∑ j ∈ Finset.Ico 200 (200 + k),
          (1 / Real.sqrt ((2 * (j : ℝ) + 1) - 2) - 1 / Real.sqrt (2 * (j : ℝ) + 1)) =
          1 / Real.sqrt 399 - 1 / Real.sqrt (2 * ((200 + k : ℕ) : ℝ) - 1) := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
          rw [show 200 + (k + 1) = (200 + k) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
          push_cast
          have heq1 : 2 * ((200 + k : ℝ)) + 1 - 2 = 2 * ((200 + k : ℝ)) - 1 := by ring
          have heq2 : 2 * ((200 + k : ℝ)) + 1 = 2 * ((200 + k + 1 : ℝ)) - 1 := by ring
          rw [heq1, heq2]; ring
      have hsqrt399 : (1997 / 100 : ℝ) ≤ Real.sqrt 399 := by
        rw [Real.le_sqrt' (by norm_num)]; norm_num
      have htail_le : ∑ j ∈ Finset.Ico 200 (200 + d),
          (1 / Real.sqrt ((2 * (j : ℝ) + 1) - 2) - 1 / Real.sqrt (2 * (j : ℝ) + 1)) ≤
          (100 / 1997 : ℝ) := by
        rw [htel d]
        have hpos : 0 ≤ 1 / Real.sqrt (2 * ((200 + d : ℕ) : ℝ) - 1) := by positivity
        have h1 : 1 / Real.sqrt 399 ≤ 1 / (1997 / 100 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) hsqrt399
        linarith
      have hnum : (129400 / 88953 : ℝ) * (100 / 1997 : ℝ) ≤ (73 / 1000 : ℝ) := by norm_num
      exact hsum1.trans ((mul_le_mul_of_nonneg_left (hsum2.trans htail_le) (by norm_num)).trans hnum)
    have hexp_le : Real.exp (73 / 1000 : ℝ) ≤ (1000 / 927 : ℝ) := by
      have h2 : (927 / 1000 : ℝ) ≤ Real.exp (-(73 / 1000 : ℝ)) := by
        have := Real.add_one_le_exp (-(73 / 1000 : ℝ))
        linarith
      rw [Real.exp_neg] at h2
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 927 / 1000) h2
    exact hprod_le.trans ((Real.exp_le_exp.mpr hsum_tail).trans hexp_le)
  calc ∑ b ∈ Finset.range M, |h_J b| * (b : ℝ) ^ (1 / 4 : ℝ)
      ≤ ∏ p ∈ P, g_hq p := hprod_bound
    _ = (∏ p ∈ P_400, g_hq p) * ∏ p ∈ P_tail, g_hq p := by rw [hunion, Finset.prod_union hdisj]
    _ ≤ ((5257275723915 : ℝ) / (scaleS : ℝ)) * (1000 / 927 : ℝ) :=
        mul_le_mul hP400_bd htail_bd (Finset.prod_nonneg fun p hp => by
          have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
          have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
          dsimp [g_hq]; positivity) (by unfold scaleS; positivity)
    _ ≤ (5671279098075 : ℝ) / (scaleS : ℝ) := by unfold scaleS; norm_num

theorem C_J_le_cert :
    C_J ≤ (8030531202875 : ℝ) / (scaleS : ℝ) := by
  unfold C_J
  have hcf : C_F0 = (78 / 100 : ℝ) := rfl
  have ha0 : alpha0 ≤ (636 / 1000 : ℝ) := alpha0_le_636_div_1000
  have h1 : alpha0 + C_F0 ≤ (1416 / 1000 : ℝ) := by rw [hcf]; linarith
  have h2 : H_quarter ≤ (5671279098075 : ℝ) / (scaleS : ℝ) := H_quarter_le_cert
  have hmul : (alpha0 + C_F0) * H_quarter ≤
      (1416 / 1000 : ℝ) * ((5671279098075 : ℝ) / (scaleS : ℝ)) :=
    mul_le_mul h1 h2 H_quarter_nonneg (by norm_num)
  have hnum : (1416 / 1000 : ℝ) * ((5671279098075 : ℝ) / (scaleS : ℝ)) ≤
      (8030531202875 : ℝ) / (scaleS : ℝ) := by unfold scaleS; norm_num
  exact hmul.trans hnum

end RayCertCJ

end

end BuchstabSwitching
