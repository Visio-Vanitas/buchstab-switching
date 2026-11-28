import BuchstabSwitching.External.EulerProductV.MertensCancel
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstH0

/-!
# Divisor Adjustment, `H_0` Tail Bound, and Assembly of `EulerProductVPremise`

Combines:
1. Exact Euler-product factorization of `VN N (Nat.ceil x)` into `UN_ratio`, the large-prime
   divisor factor `R₁(N, z)`, the twin-prime tail ratio `R₂(z) = H_0 / H0Partial z`, and
   `eulerR3 x`;
2. Divisor-count bound `1 - f₁(N, x) ≤ R₁(N, z) ≤ 1` via `2^{ω(N)} ≤ N`;
3. Asymptotic convergence `H0Partial M → H_0` and telescoping tail bound `1 ≤ R₂(z) ≤ 1 + f₂(x)`;
4. Three-factor `deltaV_bjs` assembly proving `eulerProductVPremise_of_eulerR3`.
-/

namespace BuchstabSwitching.External

private lemma H_0_pos' : 0 < BuchstabSwitching.H_0 :=
  lt_of_lt_of_le (div_pos (by norm_num) BuchstabSwitching.scaleS_pos)
    BuchstabSwitching.H_0_bounds_cert.1

private lemma H0Partial_pos (z : ℕ) : 0 < BuchstabSwitching.H0Partial z := by
  unfold BuchstabSwitching.H0Partial
  refine Finset.prod_pos fun p hp => ?_
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

private lemma summable_abs_h_J' : Summable (fun b : ℕ => |BuchstabSwitching.h_J b|) := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun b => ?_)
    BuchstabSwitching.summable_abs_h_J_mul_rpow
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [BuchstabSwitching.h_J_zero]
  · have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb0
    have hr : (1 : ℝ) ≤ (b : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hb1 (by norm_num)
    calc |BuchstabSwitching.h_J b| = |BuchstabSwitching.h_J b| * 1 := (mul_one _).symm
      _ ≤ |BuchstabSwitching.h_J b| * (b : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hr (abs_nonneg _)

private lemma tendsto_H0Partial' :
    Filter.Tendsto BuchstabSwitching.H0Partial Filter.atTop (nhds BuchstabSwitching.H_0) := by
  have hbound : ∀ M : ℕ,
      |BuchstabSwitching.H0Partial M - ∑ b ∈ Finset.range M, BuchstabSwitching.h_J b| ≤
        (∑' b : ℕ, |BuchstabSwitching.h_J b|) -
          ∑ b ∈ Finset.range M, |BuchstabSwitching.h_J b| := by
    intro M
    set P : Finset ℕ := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
    have hP : ∀ p ∈ P, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
    have hB_eq : BuchstabSwitching.H0Partial M =
        ∑ b ∈ BuchstabSwitching.B_cubefree P, BuchstabSwitching.h_J b := by
      unfold BuchstabSwitching.H0Partial
      exact (BuchstabSwitching.sum_B_cubefree_h_J P hP).symm
    let S_range : Finset ℕ :=
      (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2)
    have hsub_range : S_range ⊆ BuchstabSwitching.B_cubefree P := by
      intro b hb
      simp only [S_range, Finset.mem_filter, Finset.mem_range, BuchstabSwitching.B_cubefree,
        Finset.mem_Icc] at hb ⊢
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
        calc b = ∏ p ∈ b.primeFactors, p ^ b.factorization p :=
              (BuchstabSwitching.prod_primeFactors_pow_factorization hb0).symm
          _ ≤ ∏ p ∈ b.primeFactors, p ^ 2 :=
              Finset.prod_le_prod fun p hp =>
                Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (hb_fac p hp)
          _ ≤ ∏ p ∈ P, p ^ 2 :=
              Finset.prod_le_prod_of_subset_of_one_le hb_pf fun p hp _ =>
                Nat.one_le_pow 2 p (hP p hp).1.pos
      exact ⟨⟨Nat.pos_of_ne_zero hb0, hb_le⟩, hb_odd, hb_pf, hb_fac⟩
    have hrange_eq : ∑ b ∈ Finset.range M, BuchstabSwitching.h_J b =
        ∑ b ∈ S_range, BuchstabSwitching.h_J b := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hcond : Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2
      · exact (ite_eq_left hcond).symm
      · have hh0 : BuchstabSwitching.h_J b = 0 := by
          unfold BuchstabSwitching.h_J; exact ite_eq_right hcond
        rw [ite_eq_right hcond, hh0]
    have hsplit : BuchstabSwitching.H0Partial M =
        (∑ b ∈ Finset.range M, BuchstabSwitching.h_J b) +
          ∑ b ∈ BuchstabSwitching.B_cubefree P \ S_range, BuchstabSwitching.h_J b := by
      rw [hB_eq, hrange_eq, ← Finset.sum_sdiff hsub_range, add_comm]
    have hdisj : Disjoint (Finset.range M) (BuchstabSwitching.B_cubefree P \ S_range) := by
      rw [Finset.disjoint_left]
      intro b hbM hbs
      rw [Finset.mem_sdiff] at hbs
      apply hbs.2
      have hcond := (Finset.mem_filter.mp hbs.1).2
      exact Finset.mem_filter.mpr ⟨hbM, hcond.1, hcond.2.2⟩
    calc |BuchstabSwitching.H0Partial M - ∑ b ∈ Finset.range M, BuchstabSwitching.h_J b|
        = |∑ b ∈ BuchstabSwitching.B_cubefree P \ S_range, BuchstabSwitching.h_J b| := by
          rw [hsplit, add_sub_cancel_left]
      _ ≤ ∑ b ∈ BuchstabSwitching.B_cubefree P \ S_range, |BuchstabSwitching.h_J b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑' b : ℕ, |BuchstabSwitching.h_J b|) -
            ∑ b ∈ Finset.range M, |BuchstabSwitching.h_J b| := by
          have hsum_union : (∑ b ∈ Finset.range M, |BuchstabSwitching.h_J b|) +
              (∑ b ∈ BuchstabSwitching.B_cubefree P \ S_range, |BuchstabSwitching.h_J b|) ≤
              ∑' b : ℕ, |BuchstabSwitching.h_J b| := by
            rw [← Finset.sum_union hdisj]
            exact summable_abs_h_J'.sum_le_tsum _ (fun _ _ => abs_nonneg _)
          linarith
  have hdiff : Filter.Tendsto
      (fun M : ℕ => BuchstabSwitching.H0Partial M - ∑ b ∈ Finset.range M, BuchstabSwitching.h_J b)
      Filter.atTop (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero
      (f := fun M : ℕ => ‖BuchstabSwitching.H0Partial M -
        ∑ b ∈ Finset.range M, BuchstabSwitching.h_J b‖)
      (g := fun M : ℕ => (∑' b : ℕ, |BuchstabSwitching.h_J b|) -
        ∑ b ∈ Finset.range M, |BuchstabSwitching.h_J b|)
      (fun _ => norm_nonneg _)
      (fun M => by simpa [Real.norm_eq_abs] using hbound M) ?_
    have h0 : (∑' b : ℕ, |BuchstabSwitching.h_J b|) -
        (∑' b : ℕ, |BuchstabSwitching.h_J b|) = 0 := sub_self _
    rw [← h0]
    exact tendsto_const_nhds.sub summable_abs_h_J'.hasSum.tendsto_sum_nat
  have hsum : Filter.Tendsto (fun M : ℕ => ∑ b ∈ Finset.range M, BuchstabSwitching.h_J b)
      Filter.atTop (nhds BuchstabSwitching.H_0) :=
    BuchstabSwitching.summable_h_J.hasSum.tendsto_sum_nat
  simpa [sub_add_cancel, zero_add] using hdiff.add hsum

private noncomputable def eulerR1 (N z : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (fun p => 2 < p ∧ z ≤ p), (1 - 1 / ((p : ℝ) - 1))

private noncomputable def eulerR2 (z : ℕ) : ℝ :=
  BuchstabSwitching.H_0 / BuchstabSwitching.H0Partial z

private lemma VN_even_eq_odd_filter {N : ℕ} (hN : Even N) (z : ℕ) :
    VN N z = ∏ p ∈ ((Finset.range z).filter (fun p => p.Prime ∧ 2 < p)).filter (fun p => ¬ p ∣ N),
      (1 - 1 / ((p : ℝ) - 1)) := by
  have h2N : 2 ∣ N := even_iff_two_dvd.mp hN
  unfold VN
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpz, hp, hnd⟩
    have hne2 : p ≠ 2 := fun h => hnd (h ▸ h2N)
    exact ⟨⟨hpz, hp, lt_of_le_of_ne hp.two_le hne2.symm⟩, hnd⟩
  · rintro ⟨⟨hpz, hp, _⟩, hnd⟩
    exact ⟨hpz, hp, hnd⟩

private lemma VN_two_eq_odd_filter (z : ℕ) :
    VN 2 z = ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ 2 < p),
      (1 - 1 / ((p : ℝ) - 1)) := by
  rw [VN_even_eq_odd_filter (by decide : Even 2) z]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h, _⟩; exact h
  · rintro ⟨hpz, hp, hp2⟩
    refine ⟨⟨hpz, hp, hp2⟩, fun hdvd => ?_⟩
    have := Nat.le_of_dvd (by omega) hdvd
    omega

private lemma VN_factorization {N : ℕ} (hN : Even N) (hN0 : N ≠ 0)
    {x : ℝ} (hx : 285 ≤ x) :
    let U_c := 2 * (1 / BuchstabSwitching.H_0)
    let eNegGamma := Real.exp (-Real.eulerMascheroniConstant)
    let z := Nat.ceil x
    VN N z = (eulerR1 N z * eulerR2 z * eulerR3 x) *
      ((eNegGamma * UN_ratio U_c N) / Real.log x) := by
  intro U_c eNegGamma z
  have hz_ge : x ≤ (z : ℝ) := Nat.le_ceil x
  have hz3 : 3 ≤ z := by
    have hz285 : 285 ≤ z := by exact_mod_cast hx.trans hz_ge
    omega
  have hH0_pos : 0 < BuchstabSwitching.H_0 := H_0_pos'
  have hUc_pos : 0 < U_c := by dsimp only [U_c]; positivity
  have hHz_pos : 0 < BuchstabSwitching.H0Partial z := H0Partial_pos z
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have heg_pos : 0 < eNegGamma := Real.exp_pos _
  set P_odd : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p)
  set Q : Finset ℕ := N.primeFactors.filter (2 < ·)
  have hPdvd_eq : P_odd.filter (fun p => p ∣ N) = Q.filter (· < z) := by
    ext p
    simp only [P_odd, Q, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpz, hp, hp2⟩, hdvd⟩
      exact ⟨⟨⟨hp, hdvd, hN0⟩, hp2⟩, hpz⟩
    · rintro ⟨⟨⟨hp, hdvd, _⟩, hp2⟩, hpz⟩
      exact ⟨⟨hpz, hp, hp2⟩, hdvd⟩
  have hQge_eq : Q.filter (fun p => ¬ p < z) =
      N.primeFactors.filter (fun p => 2 < p ∧ z ≤ p) := by
    ext p
    simp only [Q, Finset.mem_filter, not_lt, and_assoc]
  have hinv_pair : ∀ p : ℕ, 2 < p →
      (((p : ℝ) - 1) / ((p : ℝ) - 2)) * (1 - 1 / ((p : ℝ) - 1)) = 1 := by
    intro p hp2
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp [h1, h2]
    ring
  have hsplit_V : (∏ p ∈ Q.filter (· < z), (1 - 1 / ((p : ℝ) - 1))) * VN N z = VN 2 z := by
    rw [VN_even_eq_odd_filter hN z, VN_two_eq_odd_filter z, ← hPdvd_eq]
    exact Finset.prod_filter_mul_prod_filter_not P_odd (fun p => p ∣ N) _
  have hsplit_Q : (∏ p ∈ Q.filter (· < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
      (∏ p ∈ Q.filter (fun p => ¬ p < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))) =
      ∏ p ∈ Q, (((p : ℝ) - 1) / ((p : ℝ) - 2)) :=
    Finset.prod_filter_mul_prod_filter_not Q (· < z) _
  have hcancel_ge : (∏ p ∈ Q.filter (fun p => ¬ p < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
      eulerR1 N z = 1 := by
    unfold eulerR1
    rw [← hQge_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    exact hinv_pair p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hcancel_lt : (∏ p ∈ Q.filter (· < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
      (∏ p ∈ Q.filter (· < z), (1 - 1 / ((p : ℝ) - 1))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    exact hinv_pair p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hVN_step1 : VN N z = UN_ratio U_c N * eulerR1 N z * (VN 2 z / U_c) := by
    unfold UN_ratio
    change VN N z = (U_c * ∏ p ∈ Q, (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
      eulerR1 N z * (VN 2 z / U_c)
    rw [← hsplit_Q, ← hsplit_V]
    have hUc_ne : U_c ≠ 0 := hUc_pos.ne'
    calc VN N z = 1 * VN N z * 1 := by ring
      _ = ((∏ p ∈ Q.filter (· < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
            (∏ p ∈ Q.filter (· < z), (1 - 1 / ((p : ℝ) - 1)))) * VN N z *
          ((∏ p ∈ Q.filter (fun p => ¬ p < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
            eulerR1 N z) := by rw [hcancel_lt, hcancel_ge]
      _ = (U_c * ((∏ p ∈ Q.filter (· < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
            (∏ p ∈ Q.filter (fun p => ¬ p < z), (((p : ℝ) - 1) / ((p : ℝ) - 2))))) *
          eulerR1 N z *
          (((∏ p ∈ Q.filter (· < z), (1 - 1 / ((p : ℝ) - 1))) * VN N z) / U_c) := by
            field_simp [hUc_ne]
  have hH_mul_V2 : BuchstabSwitching.H0Partial z * VN 2 z =
      ∏ p ∈ P_odd, (1 - 1 / (p : ℝ)) := by
    unfold BuchstabSwitching.H0Partial
    rw [VN_two_eq_odd_filter z]
    change (∏ p ∈ P_odd, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) *
      (∏ p ∈ P_odd, (1 - 1 / ((p : ℝ) - 1))) = ∏ p ∈ P_odd, (1 - 1 / (p : ℝ))
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
    have h0 : (p : ℝ) ≠ 0 := by linarith
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp [h0, h1, h2]
    ring
  set P_all : Finset ℕ := (Finset.range z).filter Nat.Prime
  have h2_mem : 2 ∈ P_all :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have herase : P_all.erase 2 = P_odd := by
    ext p
    simp only [P_all, P_odd, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hne2, hpz, hp⟩
      exact ⟨hpz, hp, lt_of_le_of_ne hp.two_le hne2.symm⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨by omega, hpz, hp⟩
  have hp_all_eq : (1 / 2 : ℝ) * ∏ p ∈ P_odd, (1 - 1 / (p : ℝ)) =
      ∏ p ∈ P_all, (1 - 1 / (p : ℝ)) := by
    have hmul := Finset.mul_prod_erase P_all (fun p : ℕ => 1 - 1 / (p : ℝ)) h2_mem
    rw [herase, show (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num] at hmul
    exact hmul
  have hV2_div_Uc : VN 2 z / U_c = eulerR2 z * ∏ p ∈ P_all, (1 - 1 / (p : ℝ)) := by
    unfold eulerR2
    dsimp only [U_c]
    have hHz_ne : BuchstabSwitching.H0Partial z ≠ 0 := hHz_pos.ne'
    have hH0_ne : BuchstabSwitching.H_0 ≠ 0 := hH0_pos.ne'
    have hV2_eq : VN 2 z =
        (2 / BuchstabSwitching.H0Partial z) * ∏ p ∈ P_all, (1 - 1 / (p : ℝ)) := by
      rw [← hp_all_eq, ← hH_mul_V2]
      field_simp [hHz_ne]
    rw [hV2_eq]
    field_simp [hHz_ne, hH0_ne]
  have hP_all_r3 : ∏ p ∈ P_all, (1 - 1 / (p : ℝ)) =
      (eNegGamma / Real.log x) * eulerR3 x := by
    unfold eulerR3
    change ∏ p ∈ P_all, (1 - 1 / (p : ℝ)) =
      (eNegGamma / Real.log x) * ((Real.log x / eNegGamma) * ∏ p ∈ P_all, (1 - 1 / (p : ℝ)))
    field_simp [hlogx_pos.ne', heg_pos.ne']
  rw [hVN_step1, hV2_div_Uc, hP_all_r3]
  ring

private lemma one_sub_sum_le_prod {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i t hit ih =>
    have hi := ha i (Finset.mem_insert_self i t)
    have ht : ∀ j ∈ t, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hit, Finset.prod_insert hit]
    have hsum_nn : 0 ≤ ∑ j ∈ t, a j := Finset.sum_nonneg fun j hj => (ht j hj).1
    have hmul : (1 - a i) * (1 - ∑ j ∈ t, a j) ≤ (1 - a i) * ∏ j ∈ t, (1 - a j) :=
      mul_le_mul_of_nonneg_left (ih ht) (by linarith)
    have hexp : 1 - (a i + ∑ j ∈ t, a j) ≤ (1 - a i) * (1 - ∑ j ∈ t, a j) := by
      nlinarith [mul_nonneg hi.1 hsum_nn]
    exact hexp.trans hmul

private lemma exp_one_lt_three' : Real.exp 1 < 3 := by
  have hbd := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by omega : 0 < 4)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hbd
  linarith [le_of_abs_le hbd]

private lemma eulerR1_bounds {N : ℕ} (hN3 : 3 ≤ N) {x : ℝ} (hx : 285 ≤ x) :
    let f1 := (1.45 : ℝ) * (Real.log N / (x - 1)) *
      (1 + 10 * Real.log (Real.log N) / Real.log N)
    0 ≤ eulerR1 N (Nat.ceil x) ∧ eulerR1 N (Nat.ceil x) ≤ 1 ∧
      0 ≤ f1 ∧ 1 - f1 ≤ eulerR1 N (Nat.ceil x) := by
  intro f1
  set z : ℕ := Nat.ceil x
  set S : Finset ℕ := N.primeFactors.filter (fun p => 2 < p ∧ z ≤ p)
  have hS_a : ∀ p ∈ S, 0 ≤ 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) ≤ 1 := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    exact ⟨div_nonneg zero_le_one hden.le, (div_le_one hden).mpr (by linarith)⟩
  have hR1_nn : 0 ≤ eulerR1 N z :=
    Finset.prod_nonneg fun p hp => by linarith [(hS_a p hp).2]
  have hR1_le1 : eulerR1 N z ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => by linarith [(hS_a p hp).2])
      (fun p hp => by linarith [(hS_a p hp).1])
  have h1_sub : 1 - eulerR1 N z ≤ (N.primeFactors.card : ℝ) / (x - 1) := by
    have hprod := one_sub_sum_le_prod S (fun p => 1 / ((p : ℝ) - 1)) hS_a
    have hsum_le : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤ (S.card : ℝ) / (x - 1) := by
      have hpt : ∀ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / (x - 1) := by
        intro p hp
        have hpz : z ≤ p := (Finset.mem_filter.mp hp).2.2
        have hxz : x ≤ (p : ℝ) := (Nat.le_ceil x).trans (by exact_mod_cast hpz)
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      calc ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1)
          ≤ ∑ _p ∈ S, (1 : ℝ) / (x - 1) := Finset.sum_le_sum hpt
        _ = (S.card : ℝ) / (x - 1) := by simp [div_eq_mul_inv]
    have hcard : (S.card : ℝ) ≤ (N.primeFactors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hdiv_card : (S.card : ℝ) / (x - 1) ≤ (N.primeFactors.card : ℝ) / (x - 1) :=
      div_le_div_of_nonneg_right hcard (by linarith)
    change 1 - ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1)) ≤ _
    linarith
  have hcard_log : (N.primeFactors.card : ℝ) ≤ (1.45 : ℝ) * Real.log N := by
    have hpow_le : 2 ^ N.primeFactors.card ≤ N := by
      calc 2 ^ N.primeFactors.card = ∏ _p ∈ N.primeFactors, 2 := by simp
        _ ≤ ∏ p ∈ N.primeFactors, p :=
            Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
        _ ≤ N := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
    have hpow_r : ((2 : ℝ) ^ N.primeFactors.card) ≤ (N : ℝ) := by exact_mod_cast hpow_le
    have hlog_le : (N.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (by positivity) hpow_r
      rwa [Real.log_pow] at h
    have hln2 : (1 : ℝ) ≤ (1.45 : ℝ) * Real.log 2 := by linarith [Real.log_two_gt_d9]
    calc (N.primeFactors.card : ℝ)
        ≤ (N.primeFactors.card : ℝ) * ((1.45 : ℝ) * Real.log 2) :=
          le_mul_of_one_le_right (Nat.cast_nonneg _) hln2
      _ = (1.45 : ℝ) * ((N.primeFactors.card : ℝ) * Real.log 2) := by ring
      _ ≤ (1.45 : ℝ) * Real.log (N : ℝ) := mul_le_mul_of_nonneg_left hlog_le (by norm_num)
  have hN_r : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN_gt1 : 1 < Real.log (N : ℝ) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (N : ℝ) := Real.log_lt_log (Real.exp_pos 1) (exp_one_lt_three'.trans_le hN_r)
  have hllog_pos : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hlogN_gt1
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hmult_ge1 : 1 ≤ 1 + 10 * Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) := by
    have : 0 ≤ 10 * Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) := by positivity
    linarith
  have hx1_pos : 0 < x - 1 := by linarith
  have hbase_nn : 0 ≤ (1.45 : ℝ) * (Real.log N / (x - 1)) :=
    mul_nonneg (by norm_num) (div_nonneg hlogN_pos.le hx1_pos.le)
  have hbase_le : (N.primeFactors.card : ℝ) / (x - 1) ≤ (1.45 : ℝ) * (Real.log N / (x - 1)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hcard_log hx1_pos.le
  have hf1_ge : (1.45 : ℝ) * (Real.log N / (x - 1)) ≤ f1 :=
    le_mul_of_one_le_right hbase_nn hmult_ge1
  have hf1_nn : 0 ≤ f1 := le_trans hbase_nn hf1_ge
  exact ⟨hR1_nn, hR1_le1, hf1_nn, by linarith⟩

private lemma eulerR2_bounds {x : ℝ} (hx : 285 ≤ x) :
    1 ≤ eulerR2 (Nat.ceil x) ∧ eulerR2 (Nat.ceil x) ≤ 1 + (1.002 : ℝ) / (x - 3) := by
  set z : ℕ := Nat.ceil x
  have hxz : x ≤ (z : ℝ) := Nat.le_ceil x
  have hz285 : 285 ≤ z := by exact_mod_cast hx.trans hxz
  have hHz_pos : 0 < BuchstabSwitching.H0Partial z := H0Partial_pos z
  constructor
  · have hmono : ∀ M : ℕ, z ≤ M →
        BuchstabSwitching.H0Partial z ≤ BuchstabSwitching.H0Partial M := by
      intro M hM
      unfold BuchstabSwitching.H0Partial
      refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨lt_of_lt_of_le hp.1 hM, hp.2⟩
      · intro p hp
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        positivity
      · intro p hp _
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        linarith [show 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 2)) by positivity]
    have hle : BuchstabSwitching.H0Partial z ≤ BuchstabSwitching.H_0 :=
      le_of_tendsto_of_tendsto (f := fun _ => BuchstabSwitching.H0Partial z)
        (g := BuchstabSwitching.H0Partial) tendsto_const_nhds tendsto_H0Partial'
        (Filter.eventually_atTop.mpr ⟨z, hmono⟩)
    unfold eulerR2
    exact (one_le_div hHz_pos).mpr hle
  · have htail_M : ∀ M : ℕ, z ≤ M →
        BuchstabSwitching.H0Partial M ≤
          BuchstabSwitching.H0Partial z * Real.exp (1 / (x - 2)) := by
      intro M hM
      set P_z : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p)
      set P_tail : Finset ℕ := (Finset.Ico z M).filter (fun p => p.Prime ∧ 2 < p)
      have hdisj : Disjoint P_z P_tail := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
        have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hp2).1
        omega
      have hunion : (Finset.range M).filter (fun p => p.Prime ∧ 2 < p) = P_z ∪ P_tail := by
        ext p
        simp only [P_z, P_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
          Finset.mem_Ico]
        constructor
        · rintro ⟨hpM, hpr, hp2⟩
          by_cases hpz : p < z
          · exact Or.inl ⟨hpz, hpr, hp2⟩
          · exact Or.inr ⟨⟨Nat.le_of_not_lt hpz, hpM⟩, hpr, hp2⟩
        · rintro (⟨hpz, hpr, hp2⟩ | ⟨⟨_, hpM⟩, hpr, hp2⟩)
          · exact ⟨lt_of_lt_of_le hpz hM, hpr, hp2⟩
          · exact ⟨hpM, hpr, hp2⟩
      have hsplit : BuchstabSwitching.H0Partial M =
          BuchstabSwitching.H0Partial z *
            ∏ p ∈ P_tail, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
        unfold BuchstabSwitching.H0Partial
        rw [hunion, Finset.prod_union hdisj]
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left ?_ hHz_pos.le
      have hprod_exp : ∏ p ∈ P_tail, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤
          ∏ p ∈ P_tail, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
        refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun _ _ => ?_)
        · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
          have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
          positivity
        · rw [add_comm]; exact Real.add_one_le_exp _
      rw [← Real.exp_sum] at hprod_exp
      refine hprod_exp.trans (Real.exp_le_exp.mpr ?_)
      have hsum_ico : ∑ p ∈ P_tail, 1 / ((p : ℝ) * ((p : ℝ) - 2)) ≤
          ∑ n ∈ Finset.Ico z M, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) := by
        calc ∑ p ∈ P_tail, 1 / ((p : ℝ) * ((p : ℝ) - 2))
            ≤ ∑ n ∈ Finset.Ico z M, 1 / ((n : ℝ) * ((n : ℝ) - 2)) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n hn _ => ?_
              have hnz : (3 : ℝ) ≤ (n : ℝ) := by
                exact_mod_cast (by omega : 3 ≤ z).trans (Finset.mem_Ico.mp hn).1
              have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
              positivity
          _ ≤ ∑ n ∈ Finset.Ico z M, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hnz : (3 : ℝ) ≤ (n : ℝ) := by
                exact_mod_cast (by omega : 3 ≤ z).trans (Finset.mem_Ico.mp hn).1
              have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
              have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
              have hdiff : 1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1) =
                  1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
                field_simp [hn1.ne', hn2.ne']; ring
              rw [hdiff]
              exact one_div_le_one_div_of_le (mul_pos hn1 hn2) (by nlinarith)
      have htele_aux : ∀ k : ℕ,
          ∑ n ∈ Finset.Ico z (z + k), (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) =
            1 / ((z : ℝ) - 2) - 1 / (((z + k : ℕ) : ℝ) - 2) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [show z + (k + 1) = (z + k) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
          push_cast; ring
      have htele : ∑ n ∈ Finset.Ico z M, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) =
          1 / ((z : ℝ) - 2) - 1 / ((M : ℝ) - 2) := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hM
        rw [hd, htele_aux d]
      rw [htele] at hsum_ico
      have hM_nn : (0 : ℝ) ≤ 1 / ((M : ℝ) - 2) := by
        have hM3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 3 ≤ M)
        exact div_nonneg zero_le_one (by linarith)
      have hzx : 1 / ((z : ℝ) - 2) ≤ 1 / (x - 2) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
    have hH0_le : BuchstabSwitching.H_0 ≤
        BuchstabSwitching.H0Partial z * Real.exp (1 / (x - 2)) :=
      le_of_tendsto_of_tendsto (f := BuchstabSwitching.H0Partial)
        (g := fun _ => BuchstabSwitching.H0Partial z * Real.exp (1 / (x - 2)))
        tendsto_H0Partial' tendsto_const_nhds (Filter.eventually_atTop.mpr ⟨z, htail_M⟩)
    have hR2_exp : eulerR2 z ≤ Real.exp (1 / (x - 2)) := by
      unfold eulerR2
      rw [div_le_iff₀ hHz_pos, mul_comm]
      exact hH0_le
    have hexp_le : Real.exp (1 / (x - 2)) ≤ 1 + (1.002 : ℝ) / (x - 3) := by
      have hx2_pos : 0 < x - 2 := by linarith
      have hx3_pos : 0 < x - 3 := by linarith
      have hneg : 1 - 1 / (x - 2) ≤ Real.exp (-(1 / (x - 2))) := by
        linarith [Real.add_one_le_exp (-(1 / (x - 2)))]
      have hsub_eq : 1 - 1 / (x - 2) = (x - 3) / (x - 2) := by
        field_simp [hx2_pos.ne']; ring
      rw [hsub_eq, Real.exp_neg, ← one_div] at hneg
      have hinv := one_div_le_one_div_of_le (div_pos hx3_pos hx2_pos) hneg
      rw [one_div_one_div, one_div_div] at hinv
      have h1 : (x - 2) / (x - 3) = 1 + 1 / (x - 3) := by
        field_simp [hx3_pos.ne']; ring
      have h2 : 1 / (x - 3) ≤ (1.002 : ℝ) / (x - 3) :=
        div_le_div_of_nonneg_right (by norm_num) hx3_pos.le
      linarith
    exact hR2_exp.trans hexp_le

/-- Unconditional assembly of `EulerProductVPremise` from two-sided bounds on `eulerR3`. -/
theorem eulerProductVPremise_of_eulerR3
    (hR3 : ∀ x : ℝ, 285 ≤ x →
      1 - 1 / (2 * (Real.log x) ^ 2) ≤ eulerR3 x ∧
        eulerR3 x ≤ 1 + 1 / (2 * (Real.log x) ^ 2)) :
    EulerProductVPremise (2 * (1 / BuchstabSwitching.H_0))
      (Real.exp (-Real.eulerMascheroniConstant)) := by
  intro N hN hN3 x hx
  set U_c : ℝ := 2 * (1 / BuchstabSwitching.H_0)
  set eNegGamma : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  set z : ℕ := Nat.ceil x
  have hN0 : N ≠ 0 := by omega
  have hfac := VN_factorization hN hN0 hx
  have hR1 := eulerR1_bounds hN3 hx
  have hR2 := eulerR2_bounds hx
  have hR3x := hR3 x hx
  set f1 : ℝ := (1.45 : ℝ) * (Real.log N / (x - 1)) *
    (1 + 10 * Real.log (Real.log N) / Real.log N)
  set f2 : ℝ := (1.002 : ℝ) / (x - 3)
  set f3 : ℝ := (1 : ℝ) / (2 * (Real.log x) ^ 2)
  have hx3_pos : 0 < x - 3 := by linarith
  have hf2_pos : 0 < f2 := div_pos (by norm_num) hx3_pos
  have hf2_lt1 : f2 < 1 := by
    dsimp only [f2]
    rw [div_lt_one hx3_pos]
    linarith
  have hlogx_gt1 : 1 < Real.log x := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log x := Real.log_lt_log (Real.exp_pos 1) (exp_one_lt_three'.trans_le (by linarith))
  have hf3_pos : 0 < f3 := by dsimp only [f3]; positivity
  have hf3_lt1 : f3 < 1 := by
    dsimp only [f3]
    rw [div_lt_one (by positivity)]
    nlinarith
  have hR3_nn : 0 ≤ eulerR3 x := le_trans (by linarith) hR3x.1
  have hprod_hi : eulerR1 N z * eulerR2 z * eulerR3 x ≤ 1 + deltaV_bjs N x := by
    have h12 : eulerR1 N z * eulerR2 z ≤ (1 + f1) * (1 + f2) :=
      mul_le_mul (hR1.2.1.trans (by linarith [hR1.2.2.1])) hR2.2 (by linarith [hR2.1])
        (by linarith [hR1.2.2.1])
    have h123 : eulerR1 N z * eulerR2 z * eulerR3 x ≤ (1 + f1) * (1 + f2) * (1 + f3) :=
      mul_le_mul h12 hR3x.2 hR3_nn (mul_nonneg (by linarith [hR1.2.2.1]) (by linarith))
    have hd_hi : (1 + f1) * (1 + f2) * (1 + f3) - 1 ≤ deltaV_bjs N x := by
      unfold deltaV_bjs
      exact le_max_right _ _
    linarith
  have hprod_lo : 1 - deltaV_bjs N x ≤ eulerR1 N z * eulerR2 z * eulerR3 x := by
    have hd_lo : 1 - deltaV_bjs N x ≤ (1 - f1) * (1 - f2) * (1 - f3) := by
      have hmax : 1 - (1 - f1) * (1 - f2) * (1 - f3) ≤ deltaV_bjs N x := by
        unfold deltaV_bjs
        exact le_max_left _ _
      linarith
    have hprod_nn : 0 ≤ eulerR1 N z * eulerR2 z * eulerR3 x :=
      mul_nonneg (mul_nonneg hR1.1 (by linarith [hR2.1])) hR3_nn
    by_cases hf1_le1 : f1 ≤ 1
    · have h12 : (1 - f1) * (1 - f2) ≤ eulerR1 N z * eulerR2 z :=
        mul_le_mul hR1.2.2.2 (by linarith [hR2.1]) (by linarith) hR1.1
      have h123 : (1 - f1) * (1 - f2) * (1 - f3) ≤ eulerR1 N z * eulerR2 z * eulerR3 x :=
        mul_le_mul h12 hR3x.1 (by linarith) (mul_nonneg hR1.1 (by linarith [hR2.1]))
      exact hd_lo.trans h123
    · have hneg12 : (1 - f1) * (1 - f2) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by linarith)
      have hneg123 : (1 - f1) * (1 - f2) * (1 - f3) < 0 :=
        mul_neg_of_neg_of_pos hneg12 (by linarith)
      linarith
  have hH0_pos : 0 < BuchstabSwitching.H_0 := H_0_pos'
  have hUc_pos : 0 < U_c := by dsimp only [U_c]; positivity
  have hUN_pos : 0 < UN_ratio U_c N := lt_of_lt_of_le hUc_pos (UN_ratio_ge_Uc hUc_pos)
  have hM_nn : 0 ≤ (eNegGamma * UN_ratio U_c N) / Real.log x :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le hUN_pos.le) (by linarith)
  have hassoc1 : (1 - deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x =
      (1 - deltaV_bjs N x) * ((eNegGamma * UN_ratio U_c N) / Real.log x) :=
    mul_div_assoc _ _ _
  have hassoc2 : (1 + deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x =
      (1 + deltaV_bjs N x) * ((eNegGamma * UN_ratio U_c N) / Real.log x) :=
    mul_div_assoc _ _ _
  change (1 - deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x ≤ VN N z ∧
    VN N z ≤ (1 + deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x
  rw [hfac, hassoc1, hassoc2]
  exact ⟨mul_le_mul_of_nonneg_right hprod_lo hM_nn, mul_le_mul_of_nonneg_right hprod_hi hM_nn⟩

end BuchstabSwitching.External
