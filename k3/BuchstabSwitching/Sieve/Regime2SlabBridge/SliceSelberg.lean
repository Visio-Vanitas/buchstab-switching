import BuchstabSwitching.Sieve.Regime2SlabBridge.Decomposition
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBonf
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBuchstab
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.SelbergDiagonalization
import BuchstabSwitching.Sieve.OddSquarefreeBounds
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ### 3b. Adaptive Selberg Upper-Sieve Options for Each Slice `S(A_{N,q}, z)` -/

section SliceUpperOptions

/-- Odd squarefree `3^{ω(L)} / φ(L)` bound:
`∑_{1 ≤ L ≤ X, Odd L, Sqf L} 3^{ω(L)} / φ(L) ≤ (∑_{1 ≤ a ≤ X, Odd a, Sqf a} 1 / φ(a))^3 ≤ (H_tilde * f₀(X))^3`. -/
theorem odd_squarefree_three_pow_omega_div_totient_le (X : ℝ) (hX : 1 ≤ X) :
    ∑ L ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun L => Odd L ∧ Squarefree L),
        (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) ≤
      (H_tilde * ((1 / 2 : ℝ) * Real.log X + alpha0 + C_F0 / X)) ^ 3 := by
  set M : ℕ := Nat.floor X
  set Dset := (Finset.Icc 1 M).filter (fun L => Odd L ∧ Squarefree L)
  let T_dom := Dset.sigma fun L => L.divisors.sigma fun a => (L / a).divisors
  let T_cod := Dset ×ˢ Dset ×ˢ Dset
  let φ_map : (Σ L : ℕ, Σ a : ℕ, ℕ) → ℕ × ℕ × ℕ :=
    fun x => (x.2.1, x.2.2, x.1 / (x.2.1 * x.2.2))
  have hexp :
      ∑ L ∈ Dset, (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) =
        ∑ x ∈ T_dom, (1 : ℝ) / (Nat.totient x.1 : ℝ) := by
    have hL : ∀ L ∈ Dset,
        (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) =
          ∑ a ∈ L.divisors, ∑ b ∈ (L / a).divisors, (1 : ℝ) / (Nat.totient L : ℝ) := by
      intro L hL
      have hL_sqf : Squarefree L := (Finset.mem_filter.mp hL).2.2
      rw [three_pow_primeFactors_card_eq_sum_divisors hL_sqf, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hL]
    simp only [T_dom, Finset.sum_sigma]
  have hmaps : ∀ x ∈ T_dom, φ_map x ∈ T_cod := by
    rintro ⟨L, ⟨a, b⟩⟩ hx
    simp only [T_dom, Finset.mem_sigma, Dset, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_divisors] at hx
    rcases hx with ⟨⟨⟨hL1, hLM⟩, hL_odd, hL_sqf⟩, ⟨haL, hL0⟩, ⟨hbLa, hLa0⟩⟩
    have ha_pos : 0 < a := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL0 haL)
    have hb_pos : 0 < b := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hLa0 hbLa)
    have hab_dvd : a * b ∣ L := by
      rcases haL with ⟨q, hq⟩
      have hq_eq : L / a = q := by rw [hq, Nat.mul_div_cancel_left q ha_pos]
      rw [hq_eq] at hbLa
      rcases hbLa with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    let c := L / (a * b)
    have habc : a * b * c = L := Nat.mul_div_cancel' hab_dvd
    have hc_pos : 1 ≤ c := Nat.div_pos (Nat.le_of_dvd hL1 hab_dvd) (Nat.mul_pos ha_pos hb_pos)
    have ha_le : a ≤ M := (Nat.le_of_dvd hL1 haL).trans hLM
    have hb_le : b ≤ M :=
      (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hL1 haL) ha_pos) hbLa).trans
        ((Nat.div_le_self L a).trans hLM)
    have hc_le : c ≤ M := (Nat.div_le_self L (a * b)).trans hLM
    have ha_odd : Odd a := hL_odd.of_dvd_nat haL
    have hb_odd : Odd b := hL_odd.of_dvd_nat (hbLa.trans (Nat.div_dvd_of_dvd haL))
    have hc_odd : Odd c := hL_odd.of_dvd_nat (Nat.div_dvd_of_dvd hab_dvd)
    have ha_sqf : Squarefree a := hL_sqf.squarefree_of_dvd haL
    have hb_sqf : Squarefree b := hL_sqf.squarefree_of_dvd (hbLa.trans (Nat.div_dvd_of_dvd haL))
    have hc_sqf : Squarefree c := hL_sqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hab_dvd)
    simp only [T_cod, Finset.mem_product, Dset, Finset.mem_filter, Finset.mem_Icc, φ_map]
    exact ⟨⟨⟨ha_pos, ha_le⟩, ha_odd, ha_sqf⟩,
      ⟨⟨hb_pos, hb_le⟩, hb_odd, hb_sqf⟩, ⟨⟨hc_pos, hc_le⟩, hc_odd, hc_sqf⟩⟩
  have hinj : Set.InjOn φ_map (T_dom : Set (Σ L : ℕ, Σ a : ℕ, ℕ)) := by
    rintro ⟨L₁, ⟨a₁, b₁⟩⟩ hx₁ ⟨L₂, ⟨a₂, b₂⟩⟩ hx₂ heq
    simp only [Finset.mem_coe, T_dom, Finset.mem_sigma, Dset, Finset.mem_filter,
      Finset.mem_Icc, Nat.mem_divisors] at hx₁ hx₂
    rcases hx₁ with ⟨⟨_, _, _⟩, ⟨ha₁L₁, hL₁0⟩, ⟨hb₁La₁, hLa₁0⟩⟩
    rcases hx₂ with ⟨⟨_, _, _⟩, ⟨ha₂L₂, hL₂0⟩, ⟨hb₂La₂, hLa₂0⟩⟩
    have ha₁_pos : 0 < a₁ := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL₁0 ha₁L₁)
    have ha₂_pos : 0 < a₂ := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL₂0 ha₂L₂)
    have hab₁ : a₁ * b₁ ∣ L₁ := by
      rcases ha₁L₁ with ⟨q, hq⟩
      have hq_eq : L₁ / a₁ = q := by rw [hq, Nat.mul_div_cancel_left q ha₁_pos]
      rw [hq_eq] at hb₁La₁
      rcases hb₁La₁ with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    have hab₂ : a₂ * b₂ ∣ L₂ := by
      rcases ha₂L₂ with ⟨q, hq⟩
      have hq_eq : L₂ / a₂ = q := by rw [hq, Nat.mul_div_cancel_left q ha₂_pos]
      rw [hq_eq] at hb₂La₂
      rcases hb₂La₂ with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    simp only [φ_map, Prod.mk.injEq] at heq
    rcases heq with ⟨ha_eq, hb_eq, hc_eq⟩
    have hL_eq : L₁ = L₂ := by
      calc L₁ = (a₁ * b₁) * (L₁ / (a₁ * b₁)) := (Nat.mul_div_cancel' hab₁).symm
        _ = (a₂ * b₂) * (L₂ / (a₂ * b₂)) := by rw [hc_eq, ha_eq, hb_eq]
        _ = L₂ := Nat.mul_div_cancel' hab₂
    subst hL_eq ha_eq hb_eq
    rfl
  have hval : ∀ x ∈ T_dom,
      (1 : ℝ) / (Nat.totient x.1 : ℝ) =
        (1 / (Nat.totient (φ_map x).1 : ℝ)) *
          ((1 / (Nat.totient (φ_map x).2.1 : ℝ)) * (1 / (Nat.totient (φ_map x).2.2 : ℝ))) := by
    rintro ⟨L, ⟨a, b⟩⟩ hx
    simp only [T_dom, Finset.mem_sigma, Dset, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_divisors] at hx
    rcases hx with ⟨⟨_, _, hL_sqf⟩, ⟨haL, hL0⟩, ⟨hbLa, hLa0⟩⟩
    have ha_pos : 0 < a := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hL0 haL)
    have hab_dvd : a * b ∣ L := by
      rcases haL with ⟨q, hq⟩
      have hq_eq : L / a = q := by rw [hq, Nat.mul_div_cancel_left q ha_pos]
      rw [hq_eq] at hbLa
      rcases hbLa with ⟨c, hc⟩
      exact ⟨c, by rw [hq, hc]; ring⟩
    let c := L / (a * b)
    have habc : a * b * c = L := Nat.mul_div_cancel' hab_dvd
    have hsqf_abc : Squarefree (a * b * c) := habc ▸ hL_sqf
    have hcop_ab_c : Nat.Coprime (a * b) c := Nat.coprime_of_squarefree_mul hsqf_abc
    have hcop_a_b : Nat.Coprime a b :=
      Nat.coprime_of_squarefree_mul (hsqf_abc.squarefree_of_dvd (dvd_mul_right _ _))
    have htot : Nat.totient L = Nat.totient a * Nat.totient b * Nat.totient c := by
      rw [← habc, Nat.totient_mul hcop_ab_c, Nat.totient_mul hcop_a_b]
    simp only [φ_map]
    rw [htot]
    push_cast
    ring
  have hsum_le_cod :
      ∑ x ∈ T_dom, (1 : ℝ) / (Nat.totient x.1 : ℝ) ≤
        ∑ y ∈ T_cod, (1 / (Nat.totient y.1 : ℝ)) *
          ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) := by
    calc ∑ x ∈ T_dom, (1 : ℝ) / (Nat.totient x.1 : ℝ)
        = ∑ x ∈ T_dom, (1 / (Nat.totient (φ_map x).1 : ℝ)) *
            ((1 / (Nat.totient (φ_map x).2.1 : ℝ)) * (1 / (Nat.totient (φ_map x).2.2 : ℝ))) :=
          Finset.sum_congr rfl hval
      _ = ∑ y ∈ T_dom.image φ_map, (1 / (Nat.totient y.1 : ℝ)) *
            ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) := by
          rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
      _ ≤ ∑ y ∈ T_cod, (1 / (Nat.totient y.1 : ℝ)) *
            ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          exact hmaps x hx
  have hcod_eq :
      ∑ y ∈ T_cod, (1 / (Nat.totient y.1 : ℝ)) *
          ((1 / (Nat.totient y.2.1 : ℝ)) * (1 / (Nat.totient y.2.2 : ℝ))) =
        (∑ a ∈ Dset, (1 : ℝ) / (Nat.totient a : ℝ)) ^ 3 := by
    rw [show T_cod = Dset ×ˢ (Dset ×ˢ Dset) from rfl, Finset.sum_product]
    simp_rw [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hbase := odd_squarefree_inv_totient_le X hX
  have hbase_nn : 0 ≤ ∑ a ∈ Dset, (1 : ℝ) / (Nat.totient a : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hpow : (∑ a ∈ Dset, (1 : ℝ) / (Nat.totient a : ℝ)) ^ 3 ≤
      (H_tilde * ((1 / 2 : ℝ) * Real.log X + alpha0 + C_F0 / X)) ^ 3 :=
    pow_le_pow_left₀ hbase_nn hbase 3
  linarith

/-- Per-`q` pre-sieve-free adaptive Selberg `Λ²` upper bound on `S(A_{N,q}, z)` via
`SelbergDiagonalization.selberg_optimal_upper_bound`, `VN_mul_JN_ge_Vfull_mul_Jfull`,
`odd_squarefree_three_pow_omega_le`, and `odd_squarefree_three_pow_omega_div_totient_le`. -/
theorem slice_selberg_upper {li2 X_lo : ℝ} {N z y q : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hq : q ∈ midPrimes N z y) {xi_q : ℝ} (hxi1 : 1 ≤ xi_q)
    (hqxi_sqrt : (q : ℝ) * xi_q ^ 2 ≤ Real.sqrt X_lo) :
    sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
          (1 / (External.VN 2 z * J_full z xi_q)) +
        ((1 / 16 : ℝ) * xi_q ^ 2 * (2 * Real.log xi_q + 6) ^ 2 +
          (1 + (H_tilde * ((1 / 2 : ℝ) * Real.log (xi_q ^ 2) + alpha0 + C_F0 / (xi_q ^ 2))) ^ 3)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
  have hq' := Finset.mem_filter.mp hq
  have hq_pr : q.Prime := hq'.2.1
  have hqN : ¬ q ∣ N := hq'.2.2
  have hq_ne2 : q ≠ 2 := fun h => hqN (h ▸ even_iff_two_dvd.mp hN)
  have hq3 : 3 ≤ q := lt_of_le_of_ne hq_pr.two_le hq_ne2.symm
  have hq_cop : Nat.Coprime q N := hq_pr.coprime_iff_not_dvd.mpr hqN
  let P_z := shiftedPrimesBelow N z
  have hP_z_pr : ∀ p ∈ P_z, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hP_z_prop : ∀ p ∈ P_z, p.Prime ∧ 2 < p ∧ ¬ p ∣ N := fun p hp => by
    have hfull := fullOddPrimesBelow_mem_iff.mp (shiftedPrimesBelow_subset_full hN hp)
    exact ⟨hfull.2.1, hfull.2.2, (Finset.mem_filter.mp hp).2.2⟩
  have hsel_g : ∀ p ∈ P_z, 0 < selbergG p ∧ selbergG p < 1 := fun p hp => by
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP_z_prop p hp).2.1
    unfold selbergG
    exact ⟨div_pos zero_lt_one (by linarith), by rw [one_div_lt (by linarith) zero_lt_one]; linarith⟩
  have hxi_nat : 1 ≤ Nat.floor xi_q := Nat.le_floor hxi1
  have hsel := selberg_optimal_upper_bound ((shiftedSet N).filter (q ∣ ·)) P_z
    (fun _ => (1 : ℝ)) selbergG (Nat.floor xi_q) hP_z_pr hsel_g (fun _ _ => zero_le_one) hxi_nat
  have hJ_eq : selbergJ selbergG P_z (Nat.floor xi_q) = J_N N z xi_q := by
    unfold J_N selbergJ
    have hset : P_z = (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N) := by
      rw [show P_z = shiftedPrimesBelow N z from rfl, shiftedPrimesBelow_eq_filter_full hN]
      ext p
      simp only [fullOddPrimesBelow, Finset.mem_filter, Finset.mem_range]
      tauto
    rw [← hset]
    rfl
  have hJ_ge1 : 1 ≤ J_N N z xi_q := by
    rw [← hJ_eq]
    exact selbergJ_pos hP_z_pr hsel_g hxi_nat
  have hJfull_ge1 : 1 ≤ J_full z xi_q := by
    let P_full := fullOddPrimesBelow z
    have hP_full_pr : ∀ p ∈ P_full, p.Prime := fun p hp => (fullOddPrimesBelow_mem_iff.mp hp).2.1
    have hsel_full : ∀ p ∈ P_full, 0 < selbergG p ∧ selbergG p < 1 := fun p hp => by
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (fullOddPrimesBelow_mem_iff.mp hp).2.2
      unfold selbergG
      exact ⟨div_pos zero_lt_one (by linarith), by rw [one_div_lt (by linarith) zero_lt_one]; linarith⟩
    exact selbergJ_pos hP_full_pr hsel_full hxi_nat
  have hV2_pos : 0 < External.VN 2 z := External.VN_pos_of_even z (by decide)
  have hVN_pos : 0 < External.VN N z := External.VN_pos_of_even z hN
  have hVNJN_ge := VN_mul_JN_ge_Vfull_mul_Jfull hN z xi_q
  have hmass_eq :
      sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) =
        ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) +
          sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q := by
    change sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) q = _
    rw [sieveDivMass_eq_main_add_rem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q,
      sieveMass_shiftedSet, gTot_prime hq_pr]
    ring
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hcard_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    exact lt_trans (div_pos hN_pos hlog_pos) (shiftedSet_card_gt_div_log hGRH hCls hN_real)
  have hxi2_ge1 : 1 ≤ xi_q ^ 2 := by nlinarith
  have hrq_le : |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| ≤
      epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    have hq_sqrt : (q : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h1 : (q : ℝ) ≤ (q : ℝ) * xi_q ^ 2 := le_mul_of_one_le_right (Nat.cast_nonneg q) hxi2_ge1
      exact (h1.trans hqxi_sqrt).trans (Real.sqrt_le_sqrt hX_N)
    exact (div_le_iff₀ hcard_pos).mp
      (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hq3 hq_sqrt hq_cop)
  have hmain_div :
      sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) / selbergJ selbergG P_z (Nat.floor xi_q) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
            (1 / (External.VN 2 z * J_full z xi_q)) +
          1 * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    rw [hJ_eq, hmass_eq, add_div]
    have h1 :
        ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) / J_N N z xi_q ≤
          ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
            (1 / (External.VN 2 z * J_full z xi_q)) := by
      have hinv : 1 / J_N N z xi_q ≤ External.VN N z / (External.VN 2 z * J_full z xi_q) := by
        have hpos_den : 0 < External.VN 2 z * J_full z xi_q := mul_pos hV2_pos (by linarith)
        rw [div_le_div_iff₀ (by linarith : 0 < J_N N z xi_q) hpos_den]
        linarith
      have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
        have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
        linarith
      have hcoeff_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) := by positivity
      calc ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) / J_N N z xi_q
          = ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) * (1 / J_N N z xi_q) := by ring
        _ ≤ ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) *
              (External.VN N z / (External.VN 2 z * J_full z xi_q)) :=
            mul_le_mul_of_nonneg_left hinv hcoeff_nn
        _ = ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
              (1 / (External.VN 2 z * J_full z xi_q)) := by ring
    have h2 : sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / J_N N z xi_q ≤
        1 * epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
      have hdiv1 : sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / J_N N z xi_q ≤
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| / 1 :=
        div_le_div₀ (abs_nonneg _) (le_abs_self _) zero_lt_one hJ_ge1
      linarith
    linarith
  -- Remainder sum over `D_xi P_z ((Nat.floor xi_q)^2)`
  let Dset := (Finset.Icc 1 (Nat.floor (xi_q ^ 2))).filter (fun L => Odd L ∧ Squarefree L)
  have hD_sub : D_xi P_z ((Nat.floor xi_q) ^ 2) ⊆ Dset := by
    intro L hL
    rcases (mem_D_xi_iff_squarefree hP_z_pr).mp hL with ⟨hL_sqf, hL_pf, hL_le⟩
    have hL_pos : 1 ≤ L := hL_sqf.ne_zero.bot_lt
    have hL_odd : Odd L := by
      refine Nat.prod_primeFactors_of_squarefree hL_sqf ▸ ?_
      exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp =>
        (hP_z_prop p (hL_pf hp)).1.odd_of_ne_two (by have := (hP_z_prop p (hL_pf hp)).2.1; omega)
    have hL_le_fl : L ≤ Nat.floor (xi_q ^ 2) := by
      have hfl_le : ((Nat.floor xi_q : ℝ) ^ 2) ≤ xi_q ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) 2
      have hcast : (L : ℝ) ≤ (Nat.floor xi_q : ℝ) ^ 2 := by exact_mod_cast hL_le
      exact Nat.le_floor (hcast.trans hfl_le)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hL_pos, hL_le_fl⟩, hL_odd, hL_sqf⟩
  have hrem_sum :
      ∑ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2),
          (3 : ℝ) ^ L.primeFactors.card *
            |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (gProd selbergG) L| ≤
        ((1 / 16 : ℝ) * xi_q ^ 2 * (2 * Real.log xi_q + 6) ^ 2 +
          (H_tilde * ((1 / 2 : ℝ) * Real.log (xi_q ^ 2) + alpha0 + C_F0 / (xi_q ^ 2))) ^ 3) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    have hterm_le : ∀ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2),
        (3 : ℝ) ^ L.primeFactors.card *
            |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (gProd selbergG) L| ≤
          (3 : ℝ) ^ L.primeFactors.card * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) +
            ((3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ)) *
              (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
      intro L hL
      have hL_sqf := squarefree_of_mem_D_xi hP_z_pr hL
      have hL_pf := primeFactors_subset_of_mem_D_xi hP_z_pr hL
      have hL_pos : 1 ≤ L := hL_sqf.ne_zero.bot_lt
      have hg_eq : gProd selbergG L = gTot L := gTot_eq_gProd_selbergG_of_squarefree hL_sqf
      have hrem_congr :
          sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (gProd selbergG) L =
            sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTot L := by
        unfold sieveRem
        rw [hg_eq]
      have hcop_qL : Nat.Coprime q L := by
        rw [← Nat.prod_primeFactors_of_squarefree hL_sqf]
        refine coprime_prod_primes_left hq_pr ?_ fun p hp => hP_z_pr p (hL_pf hp)
        intro hq_pf
        have hq_lt := Finset.mem_range.mp (Finset.mem_filter.mp (hL_pf hq_pf)).1
        have hqz := (Finset.mem_Ico.mp hq'.1).1
        omega
      have hcop_LN : Nat.Coprime L N := by
        rw [← Nat.prod_primeFactors_of_squarefree hL_sqf]
        refine Nat.Coprime.prod_left fun p hp => ?_
        exact (hP_z_prop p (hL_pf hp)).1.coprime_iff_not_dvd.mpr (hP_z_prop p (hL_pf hp)).2.2
      have hqL_cop : Nat.Coprime (q * L) N := hq_cop.mul_left hcop_LN
      have hqL3 : 3 ≤ q * L := by nlinarith
      have hL_le_xi2 : (L : ℝ) ≤ xi_q ^ 2 := by
        have hL_le := ((mem_D_xi_iff P_z ((Nat.floor xi_q) ^ 2) L).mp hL).2
        have hfl_le : ((Nat.floor xi_q : ℝ) ^ 2) ≤ xi_q ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) 2
        exact (by exact_mod_cast hL_le : (L : ℝ) ≤ (Nat.floor xi_q : ℝ) ^ 2).trans hfl_le
      have hqL_sqrt : ((q * L : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have h1 : ((q * L : ℕ) : ℝ) = (q : ℝ) * (L : ℝ) := by push_cast; ring
        have h2 : (q : ℝ) * (L : ℝ) ≤ (q : ℝ) * xi_q ^ 2 :=
          mul_le_mul_of_nonneg_left hL_le_xi2 (Nat.cast_nonneg q)
        exact (h1.trans_le (h2.trans hqxi_sqrt)).trans (Real.sqrt_le_sqrt hX_N)
      have hrqL_le : |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * L)| ≤
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) :=
        (div_le_iff₀ hcard_pos).mp
          (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hqL3 hqL_sqrt hqL_cop)
      rw [hrem_congr, shifted_rem_aq_eq_gTot N q L hcop_qL]
      have habs :
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * L) -
              sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / (Nat.totient L : ℝ)| ≤
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) +
              (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) / (Nat.totient L : ℝ) := by
        calc |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * L) -
                sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / (Nat.totient L : ℝ)|
            ≤ |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * L)| +
                |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| / (Nat.totient L : ℝ) := by
              calc _ ≤ |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * L)| +
                      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / (Nat.totient L : ℝ)| :=
                    abs_sub _ _
                _ = _ := by
                      have hden : |(Nat.totient L : ℝ)| = (Nat.totient L : ℝ) :=
                        abs_of_nonneg (Nat.cast_nonneg _)
                      rw [abs_div, hden]
          _ ≤ _ := add_le_add hrqL_le (div_le_div_of_nonneg_right hrq_le (Nat.cast_nonneg _))
      have h3_nn : (0 : ℝ) ≤ (3 : ℝ) ^ L.primeFactors.card := by positivity
      calc (3 : ℝ) ^ L.primeFactors.card *
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * L) -
              sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / (Nat.totient L : ℝ)|
          ≤ (3 : ℝ) ^ L.primeFactors.card *
              (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) +
                (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) / (Nat.totient L : ℝ)) :=
            mul_le_mul_of_nonneg_left habs h3_nn
        _ = (3 : ℝ) ^ L.primeFactors.card * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) +
              ((3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ)) *
                (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by ring
    have hsum1 : ∑ L ∈ Dset, (3 : ℝ) ^ L.primeFactors.card ≤
        (1 / 16 : ℝ) * xi_q ^ 2 * (2 * Real.log xi_q + 6) ^ 2 := by
      have h := odd_squarefree_three_pow_omega_le (xi_q ^ 2) hxi2_ge1
      have hlog : Real.log (xi_q ^ 2) = 2 * Real.log xi_q := by
        rw [Real.log_pow]; push_cast; ring
      rwa [hlog] at h
    have hsum2 : ∑ L ∈ Dset, (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) ≤
        (H_tilde * ((1 / 2 : ℝ) * Real.log (xi_q ^ 2) + alpha0 + C_F0 / (xi_q ^ 2))) ^ 3 :=
      odd_squarefree_three_pow_omega_div_totient_le (xi_q ^ 2) hxi2_ge1
    have hsub1 : ∑ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2), (3 : ℝ) ^ L.primeFactors.card ≤
        ∑ L ∈ Dset, (3 : ℝ) ^ L.primeFactors.card :=
      Finset.sum_le_sum_of_subset_of_nonneg hD_sub (fun _ _ _ => by positivity)
    have hsub2 : ∑ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2),
          (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) ≤
        ∑ L ∈ Dset, (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hD_sub (fun _ _ _ => by positivity)
    calc ∑ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2),
            (3 : ℝ) ^ L.primeFactors.card *
              |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (gProd selbergG) L|
        ≤ ∑ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2),
            ((3 : ℝ) ^ L.primeFactors.card * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) +
              ((3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ)) *
                (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ))) :=
          Finset.sum_le_sum hterm_le
      _ = ((∑ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2), (3 : ℝ) ^ L.primeFactors.card) +
            (∑ L ∈ D_xi P_z ((Nat.floor xi_q) ^ 2),
              (3 : ℝ) ^ L.primeFactors.card / (Nat.totient L : ℝ))) *
            (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
      _ ≤ ((1 / 16 : ℝ) * xi_q ^ 2 * (2 * Real.log xi_q + 6) ^ 2 +
            (H_tilde * ((1 / 2 : ℝ) * Real.log (xi_q ^ 2) + alpha0 + C_F0 / (xi_q ^ 2))) ^ 3) *
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
          have hadd := add_le_add (hsub1.trans hsum1) (hsub2.trans hsum2)
          have hmul := mul_le_mul_of_nonneg_right hadd (mul_nonneg hepd_nn hcard_pos.le)
          linarith
  linarith

/-- Summed pre-sieve-free Selberg `Λ²` upper bound over a slice `[q0, q1)` (`2c` form normalized by
`|A_N| * External.VN N z`), matching `regime_slabs.py:498-512`. -/
theorem slice_selberg_sum_upper {li2 X_lo : ℝ} {N z y q0 q1 : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    {xi_q h_q : ℝ} (hxi1 : 1 ≤ xi_q) (hh_nn : 0 ≤ h_q)
    (hqxi_hq : ∀ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1), (q : ℝ) * xi_q ^ 2 ≤ h_q)
    (hh_sqrt : h_q ≤ Real.sqrt X_lo)
    {sq_ub cnt_ub jf_lb v_full_lb : ℝ}
    (hsq : ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub)
    (hcnt : (((midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)).card : ℝ) ≤ cnt_ub)
    (hjf_pos : 0 < jf_lb) (hjf_le : jf_lb ≤ J_full z xi_q)
    (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ External.VN 2 z) :
    let s3c := min (cnt_ub * xi_q ^ 2) (sq_ub * h_q)
    let es1 := (1 / 16 : ℝ) * s3c * (2 * Real.log xi_q + 6) ^ 2 * epdNormFn X_lo li2 X_lo
    let f0 := (1 / 2 : ℝ) * Real.log (xi_q ^ 2) + alpha0 + C_F0 / (xi_q ^ 2)
    let es := (es1 + cnt_ub * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo) / v_full_lb
    ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      (sq_ub / (v_full_lb * jf_lb) + es) *
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
  dsimp only
  set S := (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)
  set s3c := min (cnt_ub * xi_q ^ 2) (sq_ub * h_q)
  set es1 := (1 / 16 : ℝ) * s3c * (2 * Real.log xi_q + 6) ^ 2 * epdNormFn X_lo li2 X_lo
  set f0 := (1 / 2 : ℝ) * Real.log (xi_q ^ 2) + alpha0 + C_F0 / (xi_q ^ 2)
  set es := (es1 + cnt_ub * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo) / v_full_lb
  have hV_ge : v_full_lb ≤ External.VN N z := hv_le.trans (VN_two_le_VN hN z)
  have hVN_pos : 0 < External.VN N z := hv_pos.trans_le hV_ge
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hsum_le : ∑ q ∈ S,
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ∑ q ∈ S,
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
            (1 / (External.VN 2 z * J_full z xi_q)) +
          ((1 / 16 : ℝ) * xi_q ^ 2 * (2 * Real.log xi_q + 6) ^ 2 +
            (1 + (H_tilde * f0) ^ 3)) * epdNormFn X_lo li2 X_lo *
              ((shiftedCoprimePrimes N).card : ℝ)) := by
    refine Finset.sum_le_sum fun q hq => ?_
    exact slice_selberg_upper hGRH hCls hX_lo hX_N hN (Finset.mem_filter.mp hq).1 hxi1
      ((hqxi_hq q hq).trans hh_sqrt)
  rw [Finset.sum_add_distrib] at hsum_le
  have hmain_sum :
      ∑ q ∈ S, ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
          (1 / (External.VN 2 z * J_full z xi_q)) ≤
        (sq_ub / (v_full_lb * jf_lb)) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    have heq :
        ∑ q ∈ S, ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
            (1 / (External.VN 2 z * J_full z xi_q)) =
          ((∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1)) / (External.VN 2 z * J_full z xi_q)) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      simp only [Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by ring
    rw [heq]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hcard_nn hVN_pos.le)
    have hsq_nn : 0 ≤ sq_ub := by
      refine le_trans (Finset.sum_nonneg fun q hq => ?_) hsq
      have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
      have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
      positivity
    exact div_le_div₀ hsq_nn hsq (mul_pos hv_pos hjf_pos) (mul_le_mul hv_le hjf_le hjf_pos.le
      (External.VN_nonneg 2 z))
  have hs3c_le : (S.card : ℝ) * xi_q ^ 2 ≤ s3c := by
    refine le_min ?_ ?_
    · exact mul_le_mul_of_nonneg_right hcnt (sq_nonneg xi_q)
    · have h1 : ∀ q ∈ S, xi_q ^ 2 ≤ h_q * ((1 : ℝ) / ((q : ℝ) - 1)) := by
        intro q hq
        have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pr.pos
        have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
        have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
        have hxi_q : xi_q ^ 2 ≤ h_q / (q : ℝ) := (le_div_iff₀ hq_pos).mpr (by linarith [hqxi_hq q hq])
        have hq_div : h_q / (q : ℝ) ≤ h_q / ((q : ℝ) - 1) :=
          div_le_div_of_nonneg_left hh_nn hq1_pos (by linarith)
        have h_eq : h_q / ((q : ℝ) - 1) = h_q * ((1 : ℝ) / ((q : ℝ) - 1)) := by ring
        linarith
      calc (S.card : ℝ) * xi_q ^ 2
          = ∑ _q ∈ S, xi_q ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ q ∈ S, h_q * ((1 : ℝ) / ((q : ℝ) - 1)) := Finset.sum_le_sum h1
        _ = h_q * ∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1) := by rw [← Finset.mul_sum]
        _ ≤ h_q * sq_ub := mul_le_mul_of_nonneg_left hsq hh_nn
        _ = sq_ub * h_q := by ring
  have hf0_nn : 0 ≤ f0 := by
    have hlog_nn : 0 ≤ Real.log (xi_q ^ 2) := Real.log_nonneg (by nlinarith)
    have ha0 := alpha0_pos
    have hcf := C_F0_pos
    have hxi2_pos : 0 < xi_q ^ 2 := by nlinarith
    dsimp only [f0]
    positivity
  have herr_sum :
      ∑ q ∈ S, ((1 / 16 : ℝ) * xi_q ^ 2 * (2 * Real.log xi_q + 6) ^ 2 +
          (1 + (H_tilde * f0) ^ 3)) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ) ≤
        es * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hexpand :
        (S.card : ℝ) * (((1 / 16 : ℝ) * xi_q ^ 2 * (2 * Real.log xi_q + 6) ^ 2 +
            (1 + (H_tilde * f0) ^ 3)) * epdNormFn X_lo li2 X_lo *
            ((shiftedCoprimePrimes N).card : ℝ)) =
          ((1 / 16 : ℝ) * ((S.card : ℝ) * xi_q ^ 2) * (2 * Real.log xi_q + 6) ^ 2 *
              epdNormFn X_lo li2 X_lo +
            (S.card : ℝ) * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo) *
            ((shiftedCoprimePrimes N).card : ℝ) := by ring
    rw [hexpand]
    have hleft_le :
        (1 / 16 : ℝ) * ((S.card : ℝ) * xi_q ^ 2) * (2 * Real.log xi_q + 6) ^ 2 *
            epdNormFn X_lo li2 X_lo +
          (S.card : ℝ) * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo ≤
        es1 + cnt_ub * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo := by
      have ha : (1 / 16 : ℝ) * ((S.card : ℝ) * xi_q ^ 2) * (2 * Real.log xi_q + 6) ^ 2 *
            epdNormFn X_lo li2 X_lo ≤ es1 := by
        dsimp only [es1]
        have hsq_nn : 0 ≤ (2 * Real.log xi_q + 6) ^ 2 := sq_nonneg _
        have h1 : (1 / 16 : ℝ) * ((S.card : ℝ) * xi_q ^ 2) ≤ (1 / 16 : ℝ) * s3c :=
          mul_le_mul_of_nonneg_left hs3c_le (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hsq_nn) hepd_nn
      have hH_nn : 0 ≤ 1 + (H_tilde * f0) ^ 3 := by
        have := H_tilde_nonneg
        positivity
      have hb : (S.card : ℝ) * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo ≤
          cnt_ub * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcnt hH_nn) hepd_nn
      linarith
    have hleft_nn : 0 ≤ es1 + cnt_ub * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo := by
      have hs3c_nn : 0 ≤ s3c := (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg xi_q)).trans hs3c_le
      have hcnt_nn : 0 ≤ cnt_ub := (Nat.cast_nonneg _).trans hcnt
      have hH_nn : 0 ≤ 1 + (H_tilde * f0) ^ 3 := by
        have := H_tilde_nonneg
        positivity
      have hes1_nn : 0 ≤ es1 := by dsimp only [es1]; positivity
      positivity
    have hdiv_ge1 : 1 ≤ External.VN N z / v_full_lb := (one_le_div hv_pos).mpr hV_ge
    calc ((1 / 16 : ℝ) * ((S.card : ℝ) * xi_q ^ 2) * (2 * Real.log xi_q + 6) ^ 2 *
            epdNormFn X_lo li2 X_lo +
          (S.card : ℝ) * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo) *
          ((shiftedCoprimePrimes N).card : ℝ)
        ≤ (es1 + cnt_ub * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo) *
            ((shiftedCoprimePrimes N).card : ℝ) :=
          mul_le_mul_of_nonneg_right hleft_le hcard_nn
      _ ≤ (es1 + cnt_ub * (1 + (H_tilde * f0) ^ 3) * epdNormFn X_lo li2 X_lo) *
            ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / v_full_lb) :=
          le_mul_of_one_le_right (mul_nonneg hleft_nn hcard_nn) hdiv_ge1
      _ = es * (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
          dsimp only [es]
          field_simp [hv_pos.ne']
  linarith

end SliceUpperOptions

end

end BuchstabSwitching
