import BuchstabSwitchingK2.Sieve.SelbergL1Cancellation
import Mathlib.Tactic

/-!
# Local Exclusion & SOS Inequality for Selberg `Λ²` Sieve (`B`-Set Cell Sieving)

Proves the algebraic local-exclusion bounds used to eliminate small-prime cofactor
leakage when applying Selberg's `Λ²` upper sieve on `B_N` cells `(a, b, c)`:
1. `sos_local_exclusion_real`: pointwise 1-prime SOS inequality
   `u ^ 2 ≤ ((q - 1) / (q - 2)) * ((u + v) ^ 2 + (q - 2) * v ^ 2)` for `2 < q`;
2. `selbergJ_le_prod_mul_selbergJ_sdiff`: general subset comparison
   `selbergJ g P xi ≤ (∏ p ∈ S, (1 + g p / (1 - g p))) * selbergJ g (P \ S) xi`
   for any `S ⊆ P`;
3. `selbergJ_odd_le_prod_mul_selbergJ_sdiff` and `inv_selbergJ_odd_sdiff_le`:
   odd-prime specialization `g p = 1 / (p - 1)` giving
   `1 / selbergJ g (P \ S) xi ≤ (∏ p ∈ S, (p - 1) / (p - 2)) / selbergJ g P xi`.
-/

namespace BuchstabSwitchingK2

/-- Elementary 1-prime SOS inequality for real `q > 2`: dropping the constraint on a single
prime multiplies the minimum of the diagonalized Selberg quadratic form by `(q - 1) / (q - 2)`. -/
theorem sos_local_exclusion_real {q u v : ℝ} (hq : 2 < q) :
    u ^ 2 ≤ ((q - 1) / (q - 2)) * ((u + v) ^ 2 + (q - 2) * v ^ 2) := by
  have hq2 : 0 < q - 2 := by linarith
  have hid :
      ((q - 1) / (q - 2)) * ((u + v) ^ 2 + (q - 2) * v ^ 2) - u ^ 2 =
        (u + (q - 1) * v) ^ 2 / (q - 2) := by
    field_simp [hq2.ne']
    ring
  have hnn : 0 ≤ (u + (q - 1) * v) ^ 2 / (q - 2) := div_nonneg (sq_nonneg _) hq2.le
  linarith

/-- General subset exclusion comparison for `selbergJ`: removing a finite prime set `S ⊆ P`
reduces `selbergJ g P xi` by at most the Euler factor `∏ p ∈ S, (1 + g p / (1 - g p))`. -/
theorem selbergJ_le_prod_mul_selbergJ_sdiff
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hSP : S ⊆ P)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) (xi : ℕ) :
    selbergJ g P xi ≤
      (∏ p ∈ S, (1 + g p / (1 - g p))) * selbergJ g (P \ S) xi := by
  let h : ℕ → ℝ := fun p => g p / (1 - g p)
  have hh_nn : ∀ p ∈ P, 0 ≤ h p := by
    intro p hp
    rcases hg p hp with ⟨hg0, hg1⟩
    exact div_nonneg hg0.le (sub_pos.mpr hg1).le
  set f : ℕ → Finset ℕ × ℕ := fun d => (d.primeFactors ∩ S, ∏ p ∈ d.primeFactors \ S, p)
  have hf_mem : ∀ d ∈ D_xi P xi, f d ∈ S.powerset ×ˢ D_xi (P \ S) xi := by
    intro d hd
    have hd_sq := squarefree_of_mem_D_xi hP hd
    have hd_sub := primeFactors_subset_of_mem_D_xi hP hd
    have hd_le : d ≤ xi := ((mem_D_xi_iff P xi d).mp hd).2
    have hfst : d.primeFactors ∩ S ∈ S.powerset :=
      Finset.mem_powerset.mpr Finset.inter_subset_right
    have hsnd : (∏ p ∈ d.primeFactors \ S, p) ∈ D_xi (P \ S) xi := by
      refine (mem_D_xi_iff (P \ S) xi _).mpr ⟨⟨d.primeFactors \ S, ?_, rfl⟩, ?_⟩
      · exact Finset.sdiff_subset_sdiff hd_sub (Finset.Subset.refl S)
      · have hsplit :
            (∏ p ∈ d.primeFactors ∩ S, p) * (∏ p ∈ d.primeFactors \ S, p) = d := by
          rw [Finset.prod_inter_mul_prod_sdiff, Nat.prod_primeFactors_of_squarefree hd_sq]
        have hpos1 : 0 < ∏ p ∈ d.primeFactors ∩ S, p := by
          refine Finset.prod_pos fun p hp => ?_
          exact (hP p (hd_sub (Finset.mem_inter.mp hp).1)).pos
        calc
          ∏ p ∈ d.primeFactors \ S, p
              ≤ (∏ p ∈ d.primeFactors ∩ S, p) * (∏ p ∈ d.primeFactors \ S, p) :=
                Nat.le_mul_of_pos_left _ hpos1
          _ = d := hsplit
          _ ≤ xi := hd_le
    exact Finset.mem_product.mpr ⟨hfst, hsnd⟩
  have hf_inj : Set.InjOn f (D_xi P xi) := by
    intro d₁ hd₁ d₂ hd₂ hEq
    have h₁ : Squarefree d₁ := squarefree_of_mem_D_xi hP hd₁
    have h₂ : Squarefree d₂ := squarefree_of_mem_D_xi hP hd₂
    have hfst : d₁.primeFactors ∩ S = d₂.primeFactors ∩ S := congrArg Prod.fst hEq
    have hsnd :
        (∏ p ∈ d₁.primeFactors \ S, p) = ∏ p ∈ d₂.primeFactors \ S, p :=
      congrArg Prod.snd hEq
    calc
      d₁ = (∏ p ∈ d₁.primeFactors ∩ S, p) * (∏ p ∈ d₁.primeFactors \ S, p) := by
        rw [Finset.prod_inter_mul_prod_sdiff, Nat.prod_primeFactors_of_squarefree h₁]
      _ = (∏ p ∈ d₂.primeFactors ∩ S, p) * (∏ p ∈ d₂.primeFactors \ S, p) := by
        rw [hfst, hsnd]
      _ = d₂ := by
        rw [Finset.prod_inter_mul_prod_sdiff, Nat.prod_primeFactors_of_squarefree h₂]
  have hf_val : ∀ d ∈ D_xi P xi,
      selbergH g d = (∏ p ∈ (f d).1, h p) * selbergH g (f d).2 := by
    intro d hd
    have hd_sub := primeFactors_subset_of_mem_D_xi hP hd
    have hT_pr : ∀ p ∈ d.primeFactors \ S, p.Prime := fun p hp =>
      hP p (hd_sub (Finset.mem_sdiff.mp hp).1)
    have hpf_snd : (f d).2.primeFactors = d.primeFactors \ S := Nat.primeFactors_prod hT_pr
    dsimp only [f, selbergH]
    rw [hpf_snd, Finset.prod_inter_mul_prod_sdiff]
  have hsum_map :
      selbergJ g P xi ≤
        ∑ x ∈ S.powerset ×ˢ D_xi (P \ S) xi, (∏ p ∈ x.1, h p) * selbergH g x.2 := by
    unfold selbergJ
    calc
      ∑ d ∈ D_xi P xi, selbergH g d
          = ∑ d ∈ D_xi P xi, (∏ p ∈ (f d).1, h p) * selbergH g (f d).2 :=
            Finset.sum_congr rfl hf_val
      _ = ∑ x ∈ (D_xi P xi).image f, (∏ p ∈ x.1, h p) * selbergH g x.2 := by
            symm
            exact Finset.sum_image (fun d₁ hd₁ d₂ hd₂ hEq => hf_inj hd₁ hd₂ hEq)
      _ ≤ ∑ x ∈ S.powerset ×ˢ D_xi (P \ S) xi, (∏ p ∈ x.1, h p) * selbergH g x.2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hf_mem) ?_
            rintro ⟨T, d'⟩ hx _
            simp only [Finset.mem_product, Finset.mem_powerset] at hx
            have hT_nn : 0 ≤ ∏ p ∈ T, h p :=
              Finset.prod_nonneg fun p hp => hh_nn p (hSP (hx.1 hp))
            have hd'_nn : 0 ≤ selbergH g d' :=
              selbergH_nonneg hg ((primeFactors_subset_of_mem_D_xi
                (fun p hp => hP p (Finset.mem_sdiff.mp hp).1) hx.2).trans Finset.sdiff_subset)
            exact mul_nonneg hT_nn hd'_nn
  have hprod_split :
      (∑ x ∈ S.powerset ×ˢ D_xi (P \ S) xi, (∏ p ∈ x.1, h p) * selbergH g x.2) =
        (∑ T ∈ S.powerset, ∏ p ∈ T, h p) * selbergJ g (P \ S) xi := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    dsimp only
    rw [← Finset.mul_sum]
    rfl
  have hpow_prod :
      (∑ T ∈ S.powerset, ∏ p ∈ T, h p) = ∏ p ∈ S, (1 + h p) := by
    have hterm : ∀ T ∈ S.powerset,
        (∏ p ∈ T, h p) = (∏ p ∈ T, h p) * (∏ _p ∈ S \ T, (1 : ℝ)) := by
      intro T _
      simp
    rw [Finset.sum_congr rfl hterm, ← Finset.prod_add h (fun _ => (1 : ℝ)) S]
    exact Finset.prod_congr rfl fun p _ => add_comm (h p) 1
  rw [hprod_split, hpow_prod] at hsum_map
  exact hsum_map

/-- Odd-prime specialization (`g p = 1 / (p - 1)`) of `selbergJ_le_prod_mul_selbergJ_sdiff`. -/
theorem selbergJ_odd_le_prod_mul_selbergJ_sdiff
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) (hSP : S ⊆ P) (xi : ℕ) :
    let g : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
    selbergJ g P xi ≤
      (∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2))) * selbergJ g (P \ S) xi := by
  intro g
  have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hg : ∀ p ∈ P, 0 < g p ∧ g p < 1 := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).2
    refine ⟨div_pos zero_lt_one (by linarith), ?_⟩
    dsimp only [g]
    rw [div_lt_one (by linarith)]
    linarith
  have hmain := selbergJ_le_prod_mul_selbergJ_sdiff hP' hSP hg xi
  have hprod :
      (∏ p ∈ S, (1 + g p / (1 - g p))) =
        ∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p (hSP hp)).2
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    dsimp only [g]
    have hsub : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
      field_simp [hp1]
      ring
    rw [hsub]
    field_simp [hp1, hp2]
    ring
  rwa [hprod] at hmain

/-- Reciprocal Selberg main-term upper bound after excluding prime subset `S ⊆ P`. -/
theorem inv_selbergJ_odd_sdiff_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) (hSP : S ⊆ P)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    let g : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1)
    1 / selbergJ g (P \ S) xi ≤
      (∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2))) / selbergJ g P xi := by
  intro g
  have hP' : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hPs' : ∀ p ∈ P \ S, p.Prime := fun p hp => hP' p (Finset.mem_sdiff.mp hp).1
  have hg : ∀ p ∈ P, 0 < g p ∧ g p < 1 := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).2
    refine ⟨div_pos zero_lt_one (by linarith), ?_⟩
    dsimp only [g]
    rw [div_lt_one (by linarith)]
    linarith
  have hgs : ∀ p ∈ P \ S, 0 < g p ∧ g p < 1 := fun p hp => hg p (Finset.mem_sdiff.mp hp).1
  have hJ : 0 < selbergJ g P xi := selbergJ_pos hP' hg hxi
  have hJs : 0 < selbergJ g (P \ S) xi := selbergJ_pos hPs' hgs hxi
  have hmul := selbergJ_odd_le_prod_mul_selbergJ_sdiff hP hSP xi
  rw [div_le_div_iff₀ hJs hJ, one_mul]
  exact hmul

end BuchstabSwitchingK2
