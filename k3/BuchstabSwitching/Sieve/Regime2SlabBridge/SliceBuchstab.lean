import BuchstabSwitching.Sieve.Regime2SlabBridge.Decomposition
import BuchstabSwitching.Sieve.Regime2SlabBridge.SliceBonf
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Sieve.OddSquarefreeBounds
import BuchstabSwitching.Sieve.LinearSieveInduction
import BuchstabSwitching.Sieve.ShiftedPrimeRemainder
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ### 3a. Finite-Terminating Buchstab Upper-Sieve Options for Each Slice `S(A_{N,q}, z)` -/

section SliceUpperOptions

private lemma oddHarmonicSum_mono {X₁ X₂ : ℝ} (h : X₁ ≤ X₂) :
    oddHarmonicSum X₁ ≤ oddHarmonicSum X₂ := by
  unfold oddHarmonicSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono h)⟩, hn.2⟩

private lemma odd_sqf_inv_totient_le_of_le {X X_ub : ℝ} (hX : 1 ≤ X_ub) (hXX : X ≤ X_ub) :
    ∑ d ∈ (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d),
        (1 : ℝ) / (Nat.totient d : ℝ) ≤
      H_tilde * ((1 / 2 : ℝ) * Real.log X_ub + alpha0 + C_F0 / X_ub) := by
  have h1 := odd_squarefree_inv_totient_le_mul_oddHarmonicSum X
  have h2 := oddHarmonicSum_mono hXX
  have h3 := (abs_le.mp (oddHarmonicSum_sub_asym_abs_le X_ub hX)).2
  have h4 : oddHarmonicSum X ≤ (1 / 2 : ℝ) * Real.log X_ub + alpha0 + C_F0 / X_ub := by linarith
  exact h1.trans (mul_le_mul_of_nonneg_left h4 H_tilde_nonneg)

/-- Per-`q` finite-terminating Buchstab upper bound on `S(A_{N,q}, z)` via
`LinearSieveInduction.finite_buchstab_upper_bound`, explicitly including BOTH `|r(q)|` terms
(fixing Finding §0.3) and allowing an arbitrary `X_rem ≥ Q_prod * D_q` for `inv_phi_ub`. -/
theorem slice_finite_buchstab_upper {li2 X_lo : ℝ} {N z y q p_star : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ z) (hq : q ∈ midPrimes N z y)
    {D_q Q_prod X_rem : ℝ} (hDz : (z : ℝ) ≤ D_q)
    (hQ_prod : (∏ p ∈ (shiftedPrimesBelow N z).filter (· < p_star), (p : ℝ)) ≤ Q_prod)
    (hqQD_sqrt : (q : ℝ) * (Q_prod * D_q) ≤ Real.sqrt X_lo)
    (hX_rem1 : 1 ≤ X_rem) (hQD_rem : Q_prod * D_q ≤ X_rem)
    (K_odd : ℕ)
    (hTerm : ∀ k, K_odd ≤ k →
      T_sum gTot (2 * k + 1) D_q ((shiftedPrimesBelow N z).filter (p_star ≤ ·)) = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.range K_odd, 1 ≤ K_seq (2 * k + 1))
    (hu_seq : ∀ k ∈ Finset.range K_odd,
      1 ≤ u_seq (2 * k + 1) ∧ u_seq (2 * k + 1) ≤ u_bjs (2 * k + 1) D_q (z : ℝ))
    (hCond : ∀ k ∈ Finset.range K_odd,
      AllLevelsMertensCondFrom gTot ((shiftedPrimesBelow N z).filter (p_star ≤ ·))
        (u_seq (2 * k + 1)) (K_seq (2 * k + 1)))
    (hF_bridge : 1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D_q / Real.log (z : ℝ)) ≤
      buchstabF cBuchstab (Real.log D_q / Real.log (z : ℝ))) :
    let s_q := Real.log D_q / Real.log (z : ℝ)
    let E_odd := ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) s_q
    let rem_b_q := min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
      ((1 / 2 : ℝ) * (Q_prod * D_q) + 1)
    let inv_phi_ub := H_tilde * ((1 / 2 : ℝ) * Real.log X_rem + alpha0 + C_F0 / X_rem)
    sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
          (buchstabF cBuchstab s_q + E_odd) +
        (rem_b_q + inv_phi_ub + External.VN N z * (buchstabF cBuchstab s_q + E_odd)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
  dsimp only
  have hq' := Finset.mem_filter.mp hq
  have hq_pr : q.Prime := hq'.2.1
  have hqN : ¬ q ∣ N := hq'.2.2
  have hq_ne2 : q ≠ 2 := fun h => hqN (h ▸ even_iff_two_dvd.mp hN)
  have hq3 : 3 ≤ q := lt_of_le_of_ne hq_pr.two_le hq_ne2.symm
  have hq_cop : Nat.Coprime q N := hq_pr.coprime_iff_not_dvd.mpr hqN
  let P_z := shiftedPrimesBelow N z
  let Q : Finset ℕ := P_z.filter (· < p_star)
  let P' : Finset ℕ := P_z.filter (p_star ≤ ·)
  have hdisj : Disjoint Q P' := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    omega
  have hunion : Q ∪ P' = P_z := by
    ext p
    simp only [Q, P', Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases lt_or_ge p p_star with hlt | hge
      · exact Or.inl ⟨hp, hlt⟩
      · exact Or.inr ⟨hp, hge⟩
  have hP_z_prop : ∀ p ∈ P_z, p.Prime ∧ 2 < p ∧ ¬ p ∣ N ∧ p < z := by
    intro p hp
    have hp_full : p ∈ fullOddPrimesBelow z := shiftedPrimesBelow_subset_full hN hp
    have hpf := fullOddPrimesBelow_mem_iff.mp hp_full
    have hpN := (Finset.mem_filter.mp hp).2.2
    exact ⟨hpf.2.1, hpf.2.2, hpN, hpf.1⟩
  have hQ_pr : ∀ p ∈ Q, p.Prime := fun p hp => (hP_z_prop p (Finset.mem_filter.mp hp).1).1
  have hP'_pr : ∀ p ∈ P', p.Prime := fun p hp => (hP_z_prop p (Finset.mem_filter.mp hp).1).1
  have hQ_V : 0 ≤ sieveV gTot Q :=
    sieveV_nonneg fun p hp => (gTot_prime_bounds (hQ_pr p hp)
      (hP_z_prop p (Finset.mem_filter.mp hp).1).2.1).2.le
  have hP'bd : ∀ p ∈ P', 2 ≤ p ∧ (p : ℝ) < (z : ℝ) := fun p hp => by
    have hprop := hP_z_prop p (Finset.mem_filter.mp hp).1
    exact ⟨hprop.1.two_le, by exact_mod_cast hprop.2.2.2⟩
  have hg_P' : ∀ p ∈ P', 0 ≤ gTot p ∧ gTot p ≤ 1 := fun p hp => by
    have hb := gTot_prime_bounds (hP_z_prop p (Finset.mem_filter.mp hp).1).1
      (hP_z_prop p (Finset.mem_filter.mp hp).1).2.1
    exact ⟨hb.1, hb.2.le⟩
  have hdvd : ∀ n ∈ (shiftedSet N).filter (q ∣ ·), ∀ S ⊆ Q, ∀ T ⊆ P',
      (∀ p ∈ S ∪ T, p ∣ n) ↔ (∏ p ∈ S ∪ T, p) ∣ n := by
    intro n _ S hS T hT
    refine forall_dvd_iff_prod_dvd_of_prime (fun p hp => ?_) n
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hQ_pr p (hS hp)
    · exact hP'_pr p (hT hp)
  have hmul : ∀ S ⊆ Q, ∀ T ⊆ P',
      gTot (∏ p ∈ S ∪ T, p) = (∏ r ∈ S, gTot r) * ∏ p ∈ T, gTot p :=
    fun S hS T hT => gTot_prod_union_disjoint_primes (hdisj.mono hS hT)
      (fun p hp => hQ_pr p (hS hp)) (fun p hp => hP'_pr p (hT hp))
  have hz_gt1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hup := finite_buchstab_upper_bound hdisj (fun _ => (1 : ℝ)) gTot hz_gt1 hDz
    (fun _ _ => zero_le_one) hQ_V hP'bd hg_P' hdvd hmul K_odd hTerm K_seq u_seq
    hK_seq hu_seq hCond hF_bridge
  rw [hunion] at hup
  have hV_eq : sieveV gTot P_z = External.VN N z := sieveV_gTot_shiftedPrimesBelow_eq_VN N z
  have hmass_eq :
      sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) =
        ((shiftedCoprimePrimes N).card : ℝ) * (1 / ((q : ℝ) - 1)) +
          sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q := by
    change sieveDivMass (shiftedSet N) (fun _ => (1 : ℝ)) q = _
    rw [sieveDivMass_eq_main_add_rem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q,
      sieveMass_shiftedSet, gTot_prime hq_pr]
    ring
  set s_q := Real.log D_q / Real.log (z : ℝ)
  set E_odd := ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) s_q
  have hs_pos : 0 < s_q := by
    have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt1
    have hlogD : 0 < Real.log D_q := Real.log_pos (lt_of_lt_of_le hz_gt1 hDz)
    exact div_pos hlogD hlogz
  have hF_pos : 0 < buchstabF cBuchstab s_q := buchstabF_pos cBuchstab_pos hs_pos
  have hE_nn : 0 ≤ E_odd := Finset.sum_nonneg fun k hk =>
    E_bjs_nonneg (hK_seq k hk) (2 * k + 1) s_q
  have hFE_nn : 0 ≤ buchstabF cBuchstab s_q + E_odd := add_nonneg hF_pos.le hE_nn
  have hN_real : 4 * (10 : ℝ) ^ 18 ≤ (N : ℝ) := hX_lo.trans hX_N
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hcard_pos : 0 < ((shiftedCoprimePrimes N).card : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    exact lt_trans (div_pos hN_pos hlog_pos) (shiftedSet_card_gt_div_log hGRH hCls hN_real)
  have hQ_prod_ge1 : 1 ≤ ∏ p ∈ Q, (p : ℝ) := by
    refine Finset.one_le_prod₀ fun p hp => ?_
    exact_mod_cast (hQ_pr p hp).one_lt.le
  have hQD_ge1 : 1 ≤ Q_prod * D_q := by
    have hD2 : (2 : ℝ) ≤ D_q := le_trans (by exact_mod_cast hz2) hDz
    have hQ1 : 1 ≤ Q_prod := hQ_prod_ge1.trans hQ_prod
    nlinarith
  have hrq_le : |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| ≤
      epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    have hq_sqrt : (q : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h1 : (q : ℝ) ≤ (q : ℝ) * (Q_prod * D_q) :=
        le_mul_of_one_le_right (Nat.cast_nonneg q) hQD_ge1
      exact (h1.trans hqQD_sqrt).trans (Real.sqrt_le_sqrt hX_N)
    exact (div_le_iff₀ hcard_pos).mp
      (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hq3 hq_sqrt hq_cop)
  have hriRem_le :
      riRemPlus ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTot Q P' D_q ≤
        (min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
            ((1 / 2 : ℝ) * (Q_prod * D_q) + 1) +
          H_tilde * ((1 / 2 : ℝ) * Real.log X_rem + alpha0 + C_F0 / X_rem)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    have hD_gt1 : 1 < D_q := lt_of_lt_of_le hz_gt1 hDz
    have hprime_QP' : ∀ p ∈ Q ∪ P', p.Prime := fun p hp => by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hQ_pr p hp
      · exact hP'_pr p hp
    let Dset := (Finset.Icc 1 (Nat.floor (Q_prod * D_q))).filter (fun d => Odd d ∧ Squarefree d)
    let f : Finset ℕ × Finset ℕ → ℕ := fun x => ∏ p ∈ x.1 ∪ x.2, p
    have hf_maps : ∀ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q), f x ∈ Dset := by
      rintro ⟨S, T⟩ hx
      rcases Finset.mem_product.mp hx with ⟨hS, hT⟩
      have hmod := riRemPlus_modulus_bounds hdisj hprime_QP' hD_gt1 hS hT
      have hS_sub := Finset.mem_powerset.mp hS
      have hT_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hd_pos : 1 ≤ f (S, T) :=
        Finset.prod_pos fun p hp => (hprime_QP' p (Finset.union_subset_union hS_sub hT_sub hp)).pos
      have hd_odd : Odd (f (S, T)) := by
        refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp => ?_
        have hp_pz : p ∈ P_z := hunion ▸ (Finset.union_subset_union hS_sub hT_sub hp)
        exact (hP_z_prop p hp_pz).1.odd_of_ne_two (by have := (hP_z_prop p hp_pz).2.1; omega)
      have hd_lt : (f (S, T) : ℝ) < Q_prod * D_q := by
        have h1 : (f (S, T) : ℝ) < (∏ p ∈ Q, (p : ℝ)) * D_q := hmod.2.2
        have h2 : (∏ p ∈ Q, (p : ℝ)) * D_q ≤ Q_prod * D_q :=
          mul_le_mul_of_nonneg_right hQ_prod (by linarith)
        exact h1.trans_le h2
      have hd_le_fl : f (S, T) ≤ Nat.floor (Q_prod * D_q) := Nat.le_floor hd_lt.le
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hd_le_fl⟩, hd_odd, hmod.1⟩
    have hf_inj : Set.InjOn f ↑(Q.powerset ×ˢ P'.powerset.filter (DPlus D_q)) := by
      refine (prod_primes_injOn_disjoint hdisj hQ_pr hP'_pr).mono ?_
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset, Finset.mem_filter,
        Set.mem_prod] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    have hsplit_term : ∀ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
        |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTot (f x)| ≤
          |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f x)| +
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| * (1 / (Nat.totient (f x) : ℝ)) := by
      rintro ⟨S, T⟩ hx
      rcases Finset.mem_product.mp hx with ⟨hS, hT⟩
      have hS_sub := Finset.mem_powerset.mp hS
      have hT_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hqz : z ≤ q := (Finset.mem_Ico.mp hq'.1).1
      have hcop_q : Nat.Coprime q (f (S, T)) := by
        refine coprime_prod_primes_left hq_pr ?_ ?_
        · intro hmem
          have hmem_pz : q ∈ P_z := hunion ▸ (Finset.union_subset_union hS_sub hT_sub hmem)
          have hq_lt := (hP_z_prop q hmem_pz).2.2.2
          omega
        · intro p hp
          exact hprime_QP' p (Finset.union_subset_union hS_sub hT_sub hp)
      rw [shifted_rem_aq_eq_gTot N q (f (S, T)) hcop_q]
      calc |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f (S, T)) -
              sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / (Nat.totient (f (S, T)) : ℝ)|
          ≤ |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f (S, T))| +
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q / (Nat.totient (f (S, T)) : ℝ)| :=
            abs_sub _ _
        _ = |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f (S, T))| +
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| * (1 / (Nat.totient (f (S, T)) : ℝ)) := by
            have hden : |(Nat.totient (f (S, T)) : ℝ)| = (Nat.totient (f (S, T)) : ℝ) :=
              abs_of_nonneg (Nat.cast_nonneg _)
            rw [abs_div, hden]
            ring
    have hrqd_le : ∀ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f x)| ≤
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
      rintro ⟨S, T⟩ hx
      rcases Finset.mem_product.mp hx with ⟨hS, hT⟩
      have hS_sub := Finset.mem_powerset.mp hS
      have hT_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hd_pos : 1 ≤ f (S, T) :=
        Finset.prod_pos fun p hp => (hprime_QP' p (Finset.union_subset_union hS_sub hT_sub hp)).pos
      have hqd3 : 3 ≤ q * f (S, T) := by nlinarith
      have hcop_N : Nat.Coprime (f (S, T)) N := by
        refine Nat.Coprime.prod_left fun p hp => ?_
        have hp_pz : p ∈ P_z := hunion ▸ (Finset.union_subset_union hS_sub hT_sub hp)
        have hprop := hP_z_prop p hp_pz
        exact hprop.1.coprime_iff_not_dvd.mpr hprop.2.2.1
      have hqd_cop : Nat.Coprime (q * f (S, T)) N := hq_cop.mul_left hcop_N
      have hmod := riRemPlus_modulus_bounds hdisj hprime_QP' hD_gt1 hS hT
      have hd_lt : (f (S, T) : ℝ) < Q_prod * D_q := by
        have h1 : (f (S, T) : ℝ) < (∏ p ∈ Q, (p : ℝ)) * D_q := hmod.2.2
        have h2 : (∏ p ∈ Q, (p : ℝ)) * D_q ≤ Q_prod * D_q :=
          mul_le_mul_of_nonneg_right hQ_prod (by linarith)
        exact h1.trans_le h2
      have hqd_sqrt : ((q * f (S, T) : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have h1 : ((q * f (S, T) : ℕ) : ℝ) = (q : ℝ) * (f (S, T) : ℝ) := by push_cast; ring
        have h2 : (q : ℝ) * (f (S, T) : ℝ) ≤ (q : ℝ) * (Q_prod * D_q) :=
          mul_le_mul_of_nonneg_left hd_lt.le (Nat.cast_nonneg q)
        exact (h1.trans_le (h2.trans hqQD_sqrt)).trans (Real.sqrt_le_sqrt hX_N)
      exact (div_le_iff₀ hcard_pos).mp
        (abs_shifted_rem_div_card_le_epdNorm hGRH hCls hX_lo hX_N hqd3 hqd_sqrt hqd_cop)
    have hriRem_sum :
        riRemPlus ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTot Q P' D_q ≤
          (Dset.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) +
            |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
              ∑ d ∈ Dset, (1 : ℝ) / (Nat.totient d : ℝ) := by
      unfold riRemPlus
      rw [← Finset.sum_product']
      calc ∑ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
              |sieveRem ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) gTot (f x)|
          ≤ ∑ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
              (|sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f x)| +
                |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
                  (1 / (Nat.totient (f x) : ℝ))) :=
            Finset.sum_le_sum hsplit_term
        _ = (∑ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
                |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f x)|) +
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
                ∑ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
                  (1 / (Nat.totient (f x) : ℝ)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ (Dset.card : ℝ) * (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) +
              |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q| *
                ∑ d ∈ Dset, (1 : ℝ) / (Nat.totient d : ℝ) := by
            refine add_le_add ?_ ?_
            · have hsum1 :
                  ∑ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
                      |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f x)| ≤
                    ((Q.powerset ×ˢ P'.powerset.filter (DPlus D_q)).card : ℝ) *
                      (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
                calc ∑ x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
                        |sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot (q * f x)|
                    ≤ ∑ _x ∈ Q.powerset ×ˢ P'.powerset.filter (DPlus D_q),
                        (epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) :=
                      Finset.sum_le_sum hrqd_le
                  _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
              have hcard_le : (Q.powerset ×ˢ P'.powerset.filter (DPlus D_q)).card ≤ Dset.card :=
                Finset.card_le_card_of_injOn f hf_maps hf_inj
              exact hsum1.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_le)
                (mul_nonneg hepd_nn hcard_pos.le))
            · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              rw [← Finset.sum_image (f := fun d : ℕ => (1 : ℝ) / (Nat.totient d : ℝ))
                (fun x hx y hy h => hf_inj hx hy h)]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
              intro d hd
              rcases Finset.mem_image.mp hd with ⟨x, hx, rfl⟩
              exact hf_maps x hx
    have hDset_sf : (Dset.card : ℝ) ≤
        4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q) :=
      odd_squarefree_count_le (Q_prod * D_q) hQD_ge1
    have hDset_odd : (Dset.card : ℝ) ≤ (1 / 2 : ℝ) * (Q_prod * D_q) + 1 := by
      have hsub_odd : Dset ⊆ (Finset.Icc 1 (Nat.floor (Q_prod * D_q))).filter Odd := by
        intro d hd
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2.1⟩
      have hcard_odd : Dset.card ≤ (Nat.floor (Q_prod * D_q) + 1) / 2 := by
        calc Dset.card
            ≤ ((Finset.Icc 1 (Nat.floor (Q_prod * D_q))).filter Odd).card :=
              Finset.card_le_card hsub_odd
          _ = (Nat.floor (Q_prod * D_q) + 1) / 2 := card_Icc_filter_odd _
      have h2_le : ((Dset.card : ℝ)) ≤ (((Nat.floor (Q_prod * D_q) + 1) / 2 : ℕ) : ℝ) := by
        exact_mod_cast hcard_odd
      have hdiv_le : (((Nat.floor (Q_prod * D_q) + 1) / 2 : ℕ) : ℝ) ≤
          ((Nat.floor (Q_prod * D_q) : ℝ) + 1) / 2 := by
        have hnat : 2 * ((Nat.floor (Q_prod * D_q) + 1) / 2) ≤ Nat.floor (Q_prod * D_q) + 1 :=
          Nat.mul_div_le _ 2
        have hreal : (2 : ℝ) * (((Nat.floor (Q_prod * D_q) + 1) / 2 : ℕ) : ℝ) ≤
            (Nat.floor (Q_prod * D_q) : ℝ) + 1 := by
          exact_mod_cast hnat
        linarith
      have hfl_le : (Nat.floor (Q_prod * D_q) : ℝ) ≤ Q_prod * D_q := Nat.floor_le (by linarith)
      linarith
    have hDset_min : (Dset.card : ℝ) ≤
        min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
          ((1 / 2 : ℝ) * (Q_prod * D_q) + 1) := le_min hDset_sf hDset_odd
    have hinv_phi : ∑ d ∈ Dset, (1 : ℝ) / (Nat.totient d : ℝ) ≤
        H_tilde * ((1 / 2 : ℝ) * Real.log X_rem + alpha0 + C_F0 / X_rem) :=
      odd_sqf_inv_totient_le_of_le hX_rem1 hQD_rem
    have hinv_phi_nn : 0 ≤ ∑ d ∈ Dset, (1 : ℝ) / (Nat.totient d : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hterm1 := mul_le_mul_of_nonneg_right hDset_min (mul_nonneg hepd_nn hcard_pos.le)
    have hterm2 := mul_le_mul hrq_le hinv_phi hinv_phi_nn (mul_nonneg hepd_nn hcard_pos.le)
    linarith
  have hmain_split :
      sieveV gTot P_z * sieveMass ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) *
          (buchstabF cBuchstab s_q + E_odd) ≤
        ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
            (buchstabF cBuchstab s_q + E_odd) +
          External.VN N z * (buchstabF cBuchstab s_q + E_odd) *
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) := by
    rw [hV_eq, hmass_eq]
    have hV_nn : 0 ≤ External.VN N z := External.VN_nonneg N z
    have hr_le : sieveRem (shiftedSet N) (fun _ => (1 : ℝ)) gTot q ≤
        epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) :=
      (le_abs_self _).trans hrq_le
    have hmul_le := mul_le_mul_of_nonneg_left hr_le (mul_nonneg hV_nn hFE_nn)
    linarith
  linarith

/-- Summed finite-terminating Buchstab upper bound over a slice `[q0, q1)` (`2c` form normalized by
`|A_N| * External.VN N z`), with BOTH `|r(q)|` terms explicitly included (fixing Finding §0.3). -/
theorem slice_finite_buchstab_sum_upper {li2 X_lo : ℝ} {N z y q0 q1 p_star : ℕ}
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : ClassicalPrimePremises li2)
    (hX_lo : 4 * (10 : ℝ) ^ 18 ≤ X_lo) (hX_N : X_lo ≤ (N : ℝ)) (hN : Even N)
    (hz2 : 2 ≤ z)
    {D_q Q_prod H_2 : ℝ} (hDz : (z : ℝ) ≤ D_q)
    (hQ_prod : (∏ p ∈ (shiftedPrimesBelow N z).filter (· < p_star), (p : ℝ)) ≤ Q_prod)
    (hH2_nn : 0 ≤ H_2)
    (hQD_H2 : ∀ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (q : ℝ) * (Q_prod * D_q) ≤ H_2)
    (hH2_sqrt : H_2 ≤ Real.sqrt X_lo)
    {X_rem : ℝ} (hX_rem1 : 1 ≤ X_rem) (hQD_rem : Q_prod * D_q ≤ X_rem)
    (K_odd : ℕ)
    (hTerm : ∀ k, K_odd ≤ k →
      T_sum gTot (2 * k + 1) D_q ((shiftedPrimesBelow N z).filter (p_star ≤ ·)) = 0)
    (K_seq : ℕ → ℝ) (u_seq : ℕ → ℝ)
    (hK_seq : ∀ k ∈ Finset.range K_odd, 1 ≤ K_seq (2 * k + 1))
    (hu_seq : ∀ k ∈ Finset.range K_odd,
      1 ≤ u_seq (2 * k + 1) ∧ u_seq (2 * k + 1) ≤ u_bjs (2 * k + 1) D_q (z : ℝ))
    (hCond : ∀ k ∈ Finset.range K_odd,
      AllLevelsMertensCondFrom gTot ((shiftedPrimesBelow N z).filter (p_star ≤ ·))
        (u_seq (2 * k + 1)) (K_seq (2 * k + 1)))
    (hF_bridge : 1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) (Real.log D_q / Real.log (z : ℝ)) ≤
      buchstabF cBuchstab (Real.log D_q / Real.log (z : ℝ)))
    {sq_ub cnt_ub q_lo v_full_lb : ℝ}
    (hq_lo_pos : 0 < q_lo)
    (hq_lo_le : ∀ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1), q_lo ≤ (q : ℝ))
    (hsq : ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
      (1 : ℝ) / ((q : ℝ) - 1) ≤ sq_ub)
    (hcnt : (((midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)).card : ℝ) ≤ cnt_ub)
    (hv_pos : 0 < v_full_lb) (hv_le : v_full_lb ≤ External.VN 2 z) :
    let s_q := Real.log D_q / Real.log (z : ℝ)
    let E_odd := ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) s_q
    let rem_b := min (4 / Real.pi ^ 2 * sq_ub * H_2 + cnt_ub * Real.sqrt (H_2 / q_lo))
      ((1 / 2 : ℝ) * sq_ub * H_2 + cnt_ub)
    let inv_phi_ub := H_tilde * ((1 / 2 : ℝ) * Real.log X_rem + alpha0 + C_F0 / X_rem)
    let err_sl :=
      (rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo / v_full_lb +
        cnt_ub * (buchstabF cBuchstab s_q + E_odd) * epdNormFn X_lo li2 X_lo
    ∑ q ∈ (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1),
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      (sq_ub * (buchstabF cBuchstab s_q + E_odd) + err_sl) *
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
  dsimp only
  set S := (midPrimes N z y).filter (fun q => q0 ≤ q ∧ q < q1)
  set s_q := Real.log D_q / Real.log (z : ℝ)
  set E_odd := ∑ k ∈ Finset.range K_odd, E_bjs (K_seq (2 * k + 1)) (2 * k + 1) s_q
  set rem_b := min (4 / Real.pi ^ 2 * sq_ub * H_2 + cnt_ub * Real.sqrt (H_2 / q_lo))
    ((1 / 2 : ℝ) * sq_ub * H_2 + cnt_ub)
  set inv_phi_ub := H_tilde * ((1 / 2 : ℝ) * Real.log X_rem + alpha0 + C_F0 / X_rem)
  have hQ_prod_ge1 : 1 ≤ Q_prod := by
    refine le_trans ?_ hQ_prod
    refine Finset.one_le_prod₀ fun p hp => ?_
    exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.one_lt.le
  have hQD_ge1 : 1 ≤ Q_prod * D_q := by
    have hD2 : (2 : ℝ) ≤ D_q := le_trans (by exact_mod_cast hz2) hDz
    nlinarith
  have hV_ge : v_full_lb ≤ External.VN N z := hv_le.trans (VN_two_le_VN hN z)
  have hVN_pos : 0 < External.VN N z := hv_pos.trans_le hV_ge
  have hcard_nn : 0 ≤ ((shiftedCoprimePrimes N).card : ℝ) := Nat.cast_nonneg _
  have hepd_nn := epdNormFn_nonneg_of_premises hGRH hCls hX_lo hX_N
  have hsum_le : ∑ q ∈ S,
        sieveCount ((shiftedSet N).filter (q ∣ ·)) (fun _ => (1 : ℝ)) (shiftedPrimesBelow N z) ≤
      ∑ q ∈ S,
        (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
            (buchstabF cBuchstab s_q + E_odd) +
          (min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
              ((1 / 2 : ℝ) * (Q_prod * D_q) + 1) +
            inv_phi_ub + External.VN N z * (buchstabF cBuchstab s_q + E_odd)) *
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ)) := by
    refine Finset.sum_le_sum fun q hq => ?_
    exact slice_finite_buchstab_upper hGRH hCls hX_lo hX_N hN hz2 (Finset.mem_filter.mp hq).1
      hDz hQ_prod ((hQD_H2 q hq).trans hH2_sqrt) hX_rem1 hQD_rem K_odd hTerm K_seq u_seq
      hK_seq hu_seq hCond hF_bridge
  rw [Finset.sum_add_distrib] at hsum_le
  have hs_pos : 0 < s_q := by
    have hz_gt1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
    exact div_pos (Real.log_pos (lt_of_lt_of_le hz_gt1 hDz)) (Real.log_pos hz_gt1)
  have hFE_nn : 0 ≤ buchstabF cBuchstab s_q + E_odd :=
    add_nonneg (buchstabF_pos cBuchstab_pos hs_pos).le
      (Finset.sum_nonneg fun k hk => E_bjs_nonneg (hK_seq k hk) (2 * k + 1) s_q)
  have hmain_sum :
      ∑ q ∈ S, ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
          (buchstabF cBuchstab s_q + E_odd) ≤
        sq_ub * (buchstabF cBuchstab s_q + E_odd) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    have heq :
        ∑ q ∈ S, ((shiftedCoprimePrimes N).card : ℝ) * External.VN N z * (1 / ((q : ℝ) - 1)) *
            (buchstabF cBuchstab s_q + E_odd) =
          (∑ q ∈ S, (1 : ℝ) / ((q : ℝ) - 1)) * (buchstabF cBuchstab s_q + E_odd) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hFE_nn)
      (mul_nonneg hcard_nn hVN_pos.le)
  have hsq_q_inv : ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ≤ sq_ub := by
    refine le_trans (Finset.sum_le_sum fun q hq => ?_) hsq
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hrem_b_sf :
      ∑ q ∈ S, (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q)) ≤
        4 / Real.pi ^ 2 * sq_ub * H_2 + cnt_ub * Real.sqrt (H_2 / q_lo) := by
    have h1 : ∀ q ∈ S,
        4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q) ≤
          4 / Real.pi ^ 2 * H_2 * (1 / (q : ℝ)) + Real.sqrt (H_2 / q_lo) := by
      intro q hq
      have hq_pos : (0 : ℝ) < (q : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos
      have hQD_le : Q_prod * D_q ≤ H_2 / (q : ℝ) :=
        (le_div_iff₀ hq_pos).mpr (by linarith [hQD_H2 q hq])
      have hQD_lo : H_2 / (q : ℝ) ≤ H_2 / q_lo :=
        div_le_div_of_nonneg_left hH2_nn hq_lo_pos (hq_lo_le q hq)
      have hsqrt_le : Real.sqrt (Q_prod * D_q) ≤ Real.sqrt (H_2 / q_lo) :=
        Real.sqrt_le_sqrt (hQD_le.trans hQD_lo)
      have hterm1 : 4 / Real.pi ^ 2 * (Q_prod * D_q) ≤ 4 / Real.pi ^ 2 * H_2 * (1 / (q : ℝ)) := by
        have : 0 ≤ 4 / Real.pi ^ 2 := by positivity
        calc 4 / Real.pi ^ 2 * (Q_prod * D_q)
            ≤ 4 / Real.pi ^ 2 * (H_2 / (q : ℝ)) := mul_le_mul_of_nonneg_left hQD_le this
          _ = 4 / Real.pi ^ 2 * H_2 * (1 / (q : ℝ)) := by ring
      linarith
    calc ∑ q ∈ S, (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
        ≤ ∑ q ∈ S, (4 / Real.pi ^ 2 * H_2 * (1 / (q : ℝ)) + Real.sqrt (H_2 / q_lo)) :=
          Finset.sum_le_sum h1
      _ = 4 / Real.pi ^ 2 * H_2 * (∑ q ∈ S, (1 : ℝ) / (q : ℝ)) +
            (S.card : ℝ) * Real.sqrt (H_2 / q_lo) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 / Real.pi ^ 2 * H_2 * sq_ub + cnt_ub * Real.sqrt (H_2 / q_lo) := by
          have h1a := mul_le_mul_of_nonneg_left hsq_q_inv (by positivity : 0 ≤ 4 / Real.pi ^ 2 * H_2)
          have h2a := mul_le_mul_of_nonneg_right hcnt (Real.sqrt_nonneg (H_2 / q_lo))
          linarith
      _ = 4 / Real.pi ^ 2 * sq_ub * H_2 + cnt_ub * Real.sqrt (H_2 / q_lo) := by ring
  have hrem_b_odd :
      ∑ q ∈ S, ((1 / 2 : ℝ) * (Q_prod * D_q) + 1) ≤
        (1 / 2 : ℝ) * sq_ub * H_2 + cnt_ub := by
    have h1 : ∀ q ∈ S,
        (1 / 2 : ℝ) * (Q_prod * D_q) + 1 ≤ (1 / 2 : ℝ) * H_2 * (1 / (q : ℝ)) + 1 := by
      intro q hq
      have hq_pos : (0 : ℝ) < (q : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos
      have hQD_le : Q_prod * D_q ≤ H_2 / (q : ℝ) :=
        (le_div_iff₀ hq_pos).mpr (by linarith [hQD_H2 q hq])
      rw [div_eq_mul_one_div] at hQD_le
      have : (1 / 2 : ℝ) * (Q_prod * D_q) ≤ (1 / 2 : ℝ) * H_2 * (1 / (q : ℝ)) := by linarith
      linarith
    calc ∑ q ∈ S, ((1 / 2 : ℝ) * (Q_prod * D_q) + 1)
        ≤ ∑ q ∈ S, ((1 / 2 : ℝ) * H_2 * (1 / (q : ℝ)) + 1) := Finset.sum_le_sum h1
      _ = (1 / 2 : ℝ) * H_2 * (∑ q ∈ S, (1 : ℝ) / (q : ℝ)) + (S.card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (1 / 2 : ℝ) * H_2 * sq_ub + cnt_ub := by
          have h1a := mul_le_mul_of_nonneg_left hsq_q_inv (by positivity : 0 ≤ (1 / 2 : ℝ) * H_2)
          linarith
      _ = (1 / 2 : ℝ) * sq_ub * H_2 + cnt_ub := by ring
  have hrem_b_min :
      ∑ q ∈ S, min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
          ((1 / 2 : ℝ) * (Q_prod * D_q) + 1) ≤ rem_b := by
    refine le_min ?_ ?_
    · exact (Finset.sum_le_sum fun q _ => min_le_left _ _).trans hrem_b_sf
    · exact (Finset.sum_le_sum fun q _ => min_le_right _ _).trans hrem_b_odd
  have hrem_b_nn : 0 ≤ rem_b :=
    (Finset.sum_nonneg fun _ _ => le_min (by positivity) (by positivity)).trans hrem_b_min
  have hinv_phi_nn : 0 ≤ inv_phi_ub := by
    have h1 := odd_sqf_inv_totient_le_of_le hX_rem1 hQD_rem
    have h2 : 0 ≤ ∑ d ∈ (Finset.Icc 1 (Nat.floor (Q_prod * D_q))).filter (fun d => Odd d ∧ Squarefree d),
        (1 : ℝ) / (Nat.totient d : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    exact h2.trans h1
  have herr_sum :
      ∑ q ∈ S, (min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
            ((1 / 2 : ℝ) * (Q_prod * D_q) + 1) +
          inv_phi_ub + External.VN N z * (buchstabF cBuchstab s_q + E_odd)) *
          epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) ≤
        ((rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo / v_full_lb +
          cnt_ub * (buchstabF cBuchstab s_q + E_odd) * epdNormFn X_lo li2 X_lo) *
          (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
    have hpull :
        ∑ q ∈ S, (min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
              ((1 / 2 : ℝ) * (Q_prod * D_q) + 1) +
            inv_phi_ub + External.VN N z * (buchstabF cBuchstab s_q + E_odd)) *
            epdNormFn X_lo li2 X_lo * ((shiftedCoprimePrimes N).card : ℝ) =
          ((∑ q ∈ S, min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
              ((1 / 2 : ℝ) * (Q_prod * D_q) + 1)) +
            (S.card : ℝ) * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
              ((shiftedCoprimePrimes N).card : ℝ) +
            (S.card : ℝ) * (buchstabF cBuchstab s_q + E_odd) * epdNormFn X_lo li2 X_lo *
              (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      have hc1 : ∑ _q ∈ S, inv_phi_ub = (S.card : ℝ) * inv_phi_ub := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hc2 : ∑ _q ∈ S, External.VN N z * (buchstabF cBuchstab s_q + E_odd) =
          (S.card : ℝ) * (External.VN N z * (buchstabF cBuchstab s_q + E_odd)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_add_distrib, hc1, hc2]
      ring
    have hp1 :
        ((∑ q ∈ S, min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
              ((1 / 2 : ℝ) * (Q_prod * D_q) + 1)) +
            (S.card : ℝ) * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
              ((shiftedCoprimePrimes N).card : ℝ) ≤
          ((rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo / v_full_lb) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      have ha : (∑ q ∈ S, min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
            ((1 / 2 : ℝ) * (Q_prod * D_q) + 1)) + (S.card : ℝ) * inv_phi_ub ≤
          rem_b + cnt_ub * inv_phi_ub := by
        have hcnt_phi := mul_le_mul_of_nonneg_right hcnt hinv_phi_nn
        linarith
      have hb : ((∑ q ∈ S, min (4 / Real.pi ^ 2 * (Q_prod * D_q) + Real.sqrt (Q_prod * D_q))
              ((1 / 2 : ℝ) * (Q_prod * D_q) + 1)) +
            (S.card : ℝ) * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
              ((shiftedCoprimePrimes N).card : ℝ) ≤
          (rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
            ((shiftedCoprimePrimes N).card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hepd_nn) hcard_nn
      have hdiv_ge1 : 1 ≤ External.VN N z / v_full_lb := (one_le_div hv_pos).mpr hV_ge
      have hcnt_nn : 0 ≤ cnt_ub := (Nat.cast_nonneg _).trans hcnt
      have hc_nn : 0 ≤ (rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
          ((shiftedCoprimePrimes N).card : ℝ) := by positivity
      have hc : (rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
            ((shiftedCoprimePrimes N).card : ℝ) ≤
          ((rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo / v_full_lb) *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
        calc (rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
              ((shiftedCoprimePrimes N).card : ℝ)
            ≤ (rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo *
                ((shiftedCoprimePrimes N).card : ℝ) * (External.VN N z / v_full_lb) :=
              le_mul_of_one_le_right hc_nn hdiv_ge1
          _ = ((rem_b + cnt_ub * inv_phi_ub) * epdNormFn X_lo li2 X_lo / v_full_lb) *
                (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by ring
      exact hb.trans hc
    have hp2 :
        (S.card : ℝ) * (buchstabF cBuchstab s_q + E_odd) * epdNormFn X_lo li2 X_lo *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) ≤
          cnt_ub * (buchstabF cBuchstab s_q + E_odd) * epdNormFn X_lo li2 X_lo *
            (((shiftedCoprimePrimes N).card : ℝ) * External.VN N z) := by
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hcard_nn hVN_pos.le)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcnt hFE_nn) hepd_nn
    rw [hpull]
    linarith
  linarith

end SliceUpperOptions

end

end BuchstabSwitching
