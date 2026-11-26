import BuchstabSwitching.Sieve.SelbergDiagonalization
import BuchstabSwitching.Sieve.OddSquarefreeBounds
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import Mathlib.Tactic

/-!
# Selberg Asymptotic Bridge: `J_full`, `J_N`, Prime-Omission Coupling, and `J_odd` Helpers

Defines `selbergG`, `J_full`, and `J_N`, proves the prime-omission monotonicity coupling
`VN_mul_JN_ge_Vfull_mul_Jfull`, relates `selbergJ` to `OddSquarefreeBounds.J_odd`, proves
`H_0_pos`, and extracts `V_full(⌈x⌉)` lower bounds from `EulerProductVPremise` and
`EulerProductVGRHPremise`.
-/

namespace BuchstabSwitching

/-! ## 1. `J_full`, `J_N`, Prime-Omission Coupling, and `J_odd` Identification -/

section JFullAndCoupling

/-- Shifted-prime Selberg weight `g(p) = 1 / (p - 1)` for `p > 2`. -/
noncomputable def selbergG (p : ℕ) : ℝ :=
  1 / ((p : ℝ) - 1)

/-- Full odd-prime Selberg normalizer `J_full(z, ξ)` over odd primes `p < z`. -/
noncomputable def J_full (z : ℕ) (xi : ℝ) : ℝ :=
  selbergJ (fun p => 1 / ((p : ℝ) - 1))
    ((Finset.range z).filter (fun p => p.Prime ∧ 2 < p)) (Nat.floor xi)

/-- `N`-coprime odd-prime Selberg normalizer `J_N(z, ξ)` over odd primes `p < z`, `p ∤ N`. -/
noncomputable def J_N (N z : ℕ) (xi : ℝ) : ℝ :=
  selbergJ (fun p => 1 / ((p : ℝ) - 1))
    ((Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) (Nat.floor xi)

lemma selbergG_bounds {p : ℕ} (hp : 2 < p) :
    0 < selbergG p ∧ selbergG p < 1 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : 0 < (p : ℝ) - 1 := by linarith
  unfold selbergG
  refine ⟨one_div_pos.mpr hden, ?_⟩
  rw [one_div_lt hden zero_lt_one]
  linarith

lemma selbergH_selbergG {d : ℕ} (hd : ∀ p ∈ d.primeFactors, 2 < p) :
    selbergH (fun p => 1 / ((p : ℝ) - 1)) d =
      ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) := by
  unfold selbergH
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hd p hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hsub : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
    field_simp
    ring
  rw [hsub, div_div_div_cancel_right₀ h1]

private lemma filter_prime_gt_two_eq_not_dvd_two (z : ℕ) :
    (Finset.range z).filter (fun p => p.Prime ∧ 2 < p) =
      (Finset.range z).filter (fun p => p.Prime ∧ ¬ p ∣ 2) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpz, hp, hp2⟩
    refine ⟨hpz, hp, fun hdvd => ?_⟩
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · rintro ⟨hpz, hp, hndvd⟩
    refine ⟨hpz, hp, ?_⟩
    have h2 : 2 ≤ p := hp.two_le
    have hne : p ≠ 2 := fun h => hndvd (by subst h; exact dvd_refl 2)
    omega

private lemma filter_prime_gt_two_not_dvd_eq_of_even {N : ℕ} (hN : Even N) (z : ℕ) :
    (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N) =
      (Finset.range z).filter (fun p => p.Prime ∧ ¬ p ∣ N) := by
  have h2N : 2 ∣ N := even_iff_two_dvd.mp hN
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpz, hp, _, hndvd⟩
    exact ⟨hpz, hp, hndvd⟩
  · rintro ⟨hpz, hp, hndvd⟩
    refine ⟨hpz, hp, ?_, hndvd⟩
    have h2 : 2 ≤ p := hp.two_le
    have hne : p ≠ 2 := fun h => hndvd (h ▸ h2N)
    omega

lemma eulerProd_selbergG_eq_VN_two (z : ℕ) :
    eulerProd (fun p => 1 / ((p : ℝ) - 1))
        ((Finset.range z).filter (fun p => p.Prime ∧ 2 < p)) =
      External.VN 2 z := by
  unfold eulerProd External.VN
  rw [filter_prime_gt_two_eq_not_dvd_two z]

lemma eulerProd_selbergG_eq_VN_of_even {N : ℕ} (hN : Even N) (z : ℕ) :
    eulerProd (fun p => 1 / ((p : ℝ) - 1))
        ((Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) =
      External.VN N z := by
  unfold eulerProd External.VN
  rw [filter_prime_gt_two_not_dvd_eq_of_even hN z]

/-- Prime-omission monotonicity coupling: for every even `N`, `z : ℕ`, and `xi : ℝ`,
`External.VN N z * J_N N z xi ≥ External.VN 2 z * J_full z xi`. -/
theorem VN_mul_JN_ge_Vfull_mul_Jfull {N : ℕ} (hN : Even N) (z : ℕ) (xi : ℝ) :
    External.VN N z * J_N N z xi ≥ External.VN 2 z * J_full z xi := by
  let P : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p)
  let P' : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)
  have hsub : P' ⊆ P := by
    intro p hp
    simp only [P, P', Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hg : ∀ p ∈ P, 0 < (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p ∧
      (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p < 1 := fun p hp =>
    selbergG_bounds (Finset.mem_filter.mp hp).2.2
  have hmono := eulerProd_mul_selbergJ_omission_mono P' P (fun p => 1 / ((p : ℝ) - 1))
    (Nat.floor xi) hsub hP hg
  rw [eulerProd_selbergG_eq_VN_two z, eulerProd_selbergG_eq_VN_of_even hN z] at hmono
  exact hmono

/-- Monotonicity of `External.VN 2 z * J_full z xi` as `z` increases. -/
theorem VN_two_mul_J_full_antitone_z {z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) (xi : ℝ) :
    External.VN 2 z₂ * J_full z₂ xi ≤ External.VN 2 z₁ * J_full z₁ xi := by
  let P₁ : Finset ℕ := (Finset.range z₁).filter (fun p => p.Prime ∧ 2 < p)
  let P₂ : Finset ℕ := (Finset.range z₂).filter (fun p => p.Prime ∧ 2 < p)
  have hsub : P₁ ⊆ P₂ := by
    intro p hp
    simp only [P₁, P₂, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hz, hp.2⟩
  have hP₂ : ∀ p ∈ P₂, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hg₂ : ∀ p ∈ P₂, 0 < (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p ∧
      (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p < 1 := fun p hp =>
    selbergG_bounds (Finset.mem_filter.mp hp).2.2
  have hmono := eulerProd_mul_selbergJ_omission_mono P₁ P₂ (fun p => 1 / ((p : ℝ) - 1))
    (Nat.floor xi) hsub hP₂ hg₂
  rw [eulerProd_selbergG_eq_VN_two z₂, eulerProd_selbergG_eq_VN_two z₁] at hmono
  exact hmono

/-- Specialization of `VN_two_mul_J_full_antitone_z` from `Nat.ceil z` to `Nat.floor z`. -/
theorem VN_two_mul_J_full_ceil_le_floor (z xi : ℝ) :
    External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) xi ≤
      External.VN 2 (Nat.floor z) * J_full (Nat.floor z) xi :=
  VN_two_mul_J_full_antitone_z (Nat.floor_le_ceil z) xi

lemma J_full_nonneg (z : ℕ) (xi : ℝ) : 0 ≤ J_full z xi := by
  unfold J_full
  refine selbergJ_nonneg ?_ ?_ (Nat.floor xi)
  · intro p hp; exact (Finset.mem_filter.mp hp).2.1
  · intro p hp; exact selbergG_bounds (Finset.mem_filter.mp hp).2.2

lemma J_N_nonneg (N z : ℕ) (xi : ℝ) : 0 ≤ J_N N z xi := by
  unfold J_N
  refine selbergJ_nonneg ?_ ?_ (Nat.floor xi)
  · intro p hp; exact (Finset.mem_filter.mp hp).2.1
  · intro p hp; exact selbergG_bounds (Finset.mem_filter.mp hp).2.2.1

lemma J_full_mono_xi (z : ℕ) {xi₁ xi₂ : ℝ} (h : xi₁ ≤ xi₂) :
    J_full z xi₁ ≤ J_full z xi₂ := by
  unfold J_full selbergJ
  let P := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hg : ∀ p ∈ P, 0 < (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p ∧
      (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p < 1 := fun p hp =>
    selbergG_bounds (Finset.mem_filter.mp hp).2.2
  exact Finset.sum_le_sum_of_subset_of_nonneg (D_xi_mono_xi P (Nat.floor_mono h)) fun d hd _ =>
    selbergH_nonneg hg (primeFactors_subset_of_mem_D_xi hP hd)

/-- For any `M > Nat.floor X`, `selbergJ` over odd primes `< M` equals `OddSquarefreeBounds.J_odd X`. -/
theorem selbergJ_range_eq_J_odd {M : ℕ} {X : ℝ} (hXM : Nat.floor X < M) :
    selbergJ (fun p => 1 / ((p : ℝ) - 1))
        ((Finset.range M).filter (fun p => p.Prime ∧ 2 < p)) (Nat.floor X) =
      J_odd X := by
  let P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  by_cases hfl : Nat.floor X = 0
  · rw [hfl, selbergJ_zero hP]
    unfold J_odd
    simp [hfl]
  · have hD : D_xi P (Nat.floor X) =
        (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d) := by
      ext d
      rw [mem_D_xi_iff_squarefree hP]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hd_sq, hd_sub, hd_le⟩
        have hd_pos : 1 ≤ d := hd_sq.ne_zero.bot_lt
        have hd_odd : Odd d := by
          rw [Nat.odd_iff]
          by_contra hne
          have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
          have h2pf : 2 ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2d, hd_sq.ne_zero⟩
          have h2P := (Finset.mem_filter.mp (hd_sub h2pf)).2.2
          omega
        exact ⟨⟨hd_pos, hd_le⟩, hd_odd, hd_sq⟩
      · rintro ⟨⟨_, hd_le⟩, hd_odd, hd_sq⟩
        refine ⟨hd_sq, fun p hp => ?_, hd_le⟩
        have hp_pr := Nat.prime_of_mem_primeFactors hp
        have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        have hp_le : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd_sq.ne_zero) hp_dvd
        have hp_ne2 : p ≠ 2 := by
          rintro rfl
          exact Nat.not_even_iff_odd.mpr hd_odd (even_iff_two_dvd.mpr hp_dvd)
        have hp_gt2 : 2 < p := lt_of_le_of_ne hp_pr.two_le hp_ne2.symm
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt (hp_le.trans hd_le) hXM),
          hp_pr, hp_gt2⟩
    unfold selbergJ J_odd
    rw [hD]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_odd : Odd d := (Finset.mem_filter.mp hd).2.1
    have hd_sq : Squarefree d := (Finset.mem_filter.mp hd).2.2
    refine selbergH_selbergG fun p hp => ?_
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    have hp_ne2 : p ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hd_odd (even_iff_two_dvd.mpr hp_dvd)
    exact lt_of_le_of_ne hp_pr.two_le hp_ne2.symm

/-- When `Nat.floor xi < z`, `J_full z xi = J_odd xi`. -/
theorem J_full_eq_J_odd_of_lt {z : ℕ} {xi : ℝ} (h : Nat.floor xi < z) :
    J_full z xi = J_odd xi :=
  selbergJ_range_eq_J_odd h

/-- For all `z : ℕ` and `xi : ℝ`, `J_full z xi ≤ J_odd xi`. -/
theorem J_full_le_J_odd (z : ℕ) (xi : ℝ) : J_full z xi ≤ J_odd xi := by
  let P : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hg : ∀ p ∈ P, 0 < (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p ∧
      (fun p => (1 : ℝ) / ((p : ℝ) - 1)) p < 1 := fun p hp =>
    selbergG_bounds (Finset.mem_filter.mp hp).2.2
  have hsub : D_xi P (Nat.floor xi) ⊆
      (Finset.Icc 1 (Nat.floor xi)).filter (fun d => Odd d ∧ Squarefree d) := by
    intro d hd
    rcases (mem_D_xi_iff_squarefree hP).mp hd with ⟨hd_sq, hd_sub, hd_le⟩
    have hd_pos : 1 ≤ d := hd_sq.ne_zero.bot_lt
    have hd_odd : Odd d := by
      rw [Nat.odd_iff]
      by_contra hne
      have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
      have h2pf : 2 ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2d, hd_sq.ne_zero⟩
      have h2P := (Finset.mem_filter.mp (hd_sub h2pf)).2.2
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hd_le⟩, hd_odd, hd_sq⟩
  unfold J_full selbergJ J_odd
  calc ∑ d ∈ D_xi P (Nat.floor xi), selbergH (fun p => 1 / ((p : ℝ) - 1)) d
      = ∑ d ∈ D_xi P (Nat.floor xi), ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd_sub := primeFactors_subset_of_mem_D_xi hP hd
        exact selbergH_selbergG fun p hp => (Finset.mem_filter.mp (hd_sub hp)).2.2
    _ ≤ ∑ d ∈ (Finset.Icc 1 (Nat.floor xi)).filter (fun d => Odd d ∧ Squarefree d),
          ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ => ?_
        have hd_odd : Odd d := (Finset.mem_filter.mp hd).2.1
        have hd_sq : Squarefree d := (Finset.mem_filter.mp hd).2.2
        refine Finset.prod_nonneg fun p hp => ?_
        have hp_pr := Nat.prime_of_mem_primeFactors hp
        have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        have hp_ne2 : p ≠ 2 := by
          rintro rfl
          exact Nat.not_even_iff_odd.mpr hd_odd (even_iff_two_dvd.mpr hp_dvd)
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast lt_of_le_of_ne hp_pr.two_le hp_ne2.symm
        have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        positivity

end JFullAndCoupling

/-! ## 2. `J_odd` Properties, `H_0 > 0`, and Euler-Product Bridges -/

section JOddAndEulerHelpers

lemma J_odd_nonneg (X : ℝ) : 0 ≤ J_odd X := by
  unfold J_odd
  refine Finset.sum_nonneg fun d hd => Finset.prod_nonneg fun p hp => ?_
  have hd_odd : Odd d := (Finset.mem_filter.mp hd).2.1
  have hp_pr := Nat.prime_of_mem_primeFactors hp
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  have hp_ne2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hd_odd (even_iff_two_dvd.mpr hp_dvd)
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast lt_of_le_of_ne hp_pr.two_le hp_ne2.symm
  have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

lemma J_odd_mono {X₁ X₂ : ℝ} (h : X₁ ≤ X₂) : J_odd X₁ ≤ J_odd X₂ := by
  unfold J_odd
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    exact ⟨⟨hd.1.1, hd.1.2.trans (Nat.floor_mono h)⟩, hd.2⟩
  · intro d hd _
    refine Finset.prod_nonneg fun p hp => ?_
    have hd_odd : Odd d := (Finset.mem_filter.mp hd).2.1
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    have hp_ne2 : p ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hd_odd (even_iff_two_dvd.mpr hp_dvd)
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast lt_of_le_of_ne hp_pr.two_le hp_ne2.symm
    have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity

lemma J_odd_eq_zero_of_lt_one {X : ℝ} (hX : X < 1) : J_odd X = 0 := by
  unfold J_odd
  have hfl : Nat.floor X = 0 := Nat.floor_eq_zero.mpr hX
  simp [hfl]

lemma one_le_J_odd {X : ℝ} (hX : 1 ≤ X) : 1 ≤ J_odd X := by
  unfold J_odd
  have h1 : 1 ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, Nat.le_floor hX⟩, odd_one, squarefree_one⟩
  have hle : (∏ p ∈ (1 : ℕ).primeFactors, (1 / ((p : ℝ) - 2))) ≤
      ∑ d ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d),
        ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) := by
    refine Finset.single_le_sum (f := fun d : ℕ => ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)))
      (fun d hd => ?_) h1
    refine Finset.prod_nonneg fun p hp => ?_
    have hd_odd : Odd d := (Finset.mem_filter.mp hd).2.1
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    have hp_ne2 : p ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hd_odd (even_iff_two_dvd.mpr hp_dvd)
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast lt_of_le_of_ne hp_pr.two_le hp_ne2.symm
    have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity
  simpa using hle

lemma C_J_nonneg : 0 ≤ C_J := by
  unfold C_J
  exact mul_nonneg (by linarith [alpha0_pos, C_F0_pos]) H_quarter_nonneg

/-- Strict positivity `0 < H_0` proved directly from `J_odd_asymptotic_enclosure`. -/
theorem H_0_pos : 0 < H_0 := by
  set X : ℝ := max 1 ((2 * C_J + 2) ^ 4)
  have hX1 : 1 ≤ X := le_max_left _ _
  have hX_pow : (2 * C_J + 2) ^ 4 ≤ X := le_max_right _ _
  have hCJ_nn : 0 ≤ C_J := C_J_nonneg
  have hbase_pos : 0 < 2 * C_J + 2 := by linarith
  have hX_rpow : 2 * C_J + 2 ≤ X ^ (1 / 4 : ℝ) := by
    calc 2 * C_J + 2 = ((2 * C_J + 2) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_pos.le]
          norm_num
      _ ≤ X ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hX_pow (by norm_num)
  have herr_lt : C_J * X ^ (-(1 / 4 : ℝ)) < 1 / 2 := by
    rw [Real.rpow_neg (by linarith)]
    calc C_J * (X ^ (1 / 4 : ℝ))⁻¹ = C_J / X ^ (1 / 4 : ℝ) := by ring
      _ ≤ C_J / (2 * C_J + 2) := div_le_div_of_nonneg_left hCJ_nn hbase_pos hX_rpow
      _ < 1 / 2 := by
        rw [div_lt_div_iff₀ hbase_pos (by norm_num)]
        linarith
  have henc := (abs_le.mp (J_odd_asymptotic_enclosure X hX1)).2
  have hJ1 : 1 ≤ J_odd X := one_le_J_odd hX1
  have hmain_pos : 0 < H_0 * ((1 / 2 : ℝ) * Real.log X + alpha0) := by linarith
  have hlog_pos : 0 < (1 / 2 : ℝ) * Real.log X + alpha0 := by
    have := Real.log_nonneg hX1
    linarith [alpha0_pos]
  exact pos_of_mul_pos_left hmain_pos hlog_pos.le

lemma J_odd_le_asym {X : ℝ} (hX : 1 ≤ X) :
    J_odd X ≤ H_0 * ((1 / 2 : ℝ) * Real.log X + alpha0) + C_J * X ^ (-(1 / 4 : ℝ)) := by
  have henc := (abs_le.mp (J_odd_asymptotic_enclosure X hX)).2
  linarith

lemma asym_le_J_odd {X : ℝ} (hX : 1 ≤ X) :
    H_0 * ((1 / 2 : ℝ) * Real.log X + alpha0) - C_J * X ^ (-(1 / 4 : ℝ)) ≤ J_odd X := by
  have henc := (abs_le.mp (J_odd_asymptotic_enclosure X hX)).1
  linarith

lemma floor_div_natCast_eq_floor_div {xi : ℝ} (hxi : 0 ≤ xi) {q : ℕ} (hq : 1 ≤ q) :
    Nat.floor xi / q = Nat.floor (xi / (q : ℝ)) := by
  symm
  rw [Nat.floor_eq_iff (div_nonneg hxi (by positivity))]
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  constructor
  · rw [le_div_iff₀ hq_pos]
    have h1 : ((Nat.floor xi / q : ℕ) : ℝ) * (q : ℝ) ≤ (Nat.floor xi : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (Nat.floor xi) q
    exact h1.trans (Nat.floor_le hxi)
  · rw [div_lt_iff₀ hq_pos]
    have h1 : xi < (Nat.floor xi : ℝ) + 1 := Nat.lt_floor_add_one xi
    have h2 : Nat.floor xi + 1 ≤ (Nat.floor xi / q + 1) * q := by
      have := Nat.lt_mul_div_succ (Nat.floor xi) (by omega : 0 < q)
      nlinarith
    have h3 : (Nat.floor xi : ℝ) + 1 ≤ (((Nat.floor xi / q : ℕ) : ℝ) + 1) * (q : ℝ) := by
      exact_mod_cast h2
    linarith

/-- `External.VN 4 z = External.VN 2 z` since `4` and `2` have the exact same prime divisors. -/
theorem VN_four_eq_VN_two (z : ℕ) : External.VN 4 z = External.VN 2 z := by
  unfold External.VN
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpz, hp, hndvd⟩
    refine ⟨hpz, hp, fun hp2 => hndvd (hp2.trans (by norm_num : 2 ∣ 4))⟩
  · rintro ⟨hpz, hp, hndvd⟩
    refine ⟨hpz, hp, fun hp4 => hndvd ?_⟩
    have h2sq : 4 = 2 ^ 2 := by norm_num
    rw [h2sq] at hp4
    exact hp.dvd_of_dvd_pow hp4

/-- `External.UN_ratio U_c 4 = U_c` since `4` has no prime factors `> 2`. -/
theorem UN_ratio_four (U_c : ℝ) : External.UN_ratio U_c 4 = U_c := by
  unfold External.UN_ratio
  have hemp : (4 : ℕ).primeFactors.filter (2 < ·) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hp, hp4, _⟩, hp2⟩
    have h2sq : 4 = 2 ^ 2 := by norm_num
    rw [h2sq] at hp4
    have hle := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hp4)
    omega
  rw [hemp, Finset.prod_empty, mul_one]

/-- From `External.EulerProductVPremise`, extract the `V_full(⌈x⌉)` lower bound via `N = 4`. -/
theorem VN_two_ceil_ge_of_EulerProductVPremise {U_c eNegGamma : ℝ}
    (hV : External.EulerProductVPremise U_c eNegGamma) {x : ℝ} (hx : 285 ≤ x) :
    (1 - External.deltaV_bjs 4 x) * (eNegGamma * U_c) / Real.log x ≤
      External.VN 2 (Nat.ceil x) := by
  have h4 := (hV 4 (by decide) (by norm_num) x hx).1
  rwa [VN_four_eq_VN_two, UN_ratio_four] at h4

/-- From `External.EulerProductVGRHPremise`, extract the `V_full(⌈x⌉)` lower bound via `N = 4`. -/
theorem VN_two_ceil_ge_of_EulerProductVGRHPremise {U_c eNegGamma : ℝ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hV : External.EulerProductVGRHPremise U_c eNegGamma) {x : ℝ} (hx : 8 ≤ x) :
    (1 - External.deltaV_bs 4 x) * (eNegGamma * U_c) / Real.log x ≤
      External.VN 2 (Nat.ceil x) := by
  have h4 := (hV hGRH 4 (by decide) (by norm_num) x hx).1
  rwa [VN_four_eq_VN_two, UN_ratio_four] at h4

end JOddAndEulerHelpers

end BuchstabSwitching
