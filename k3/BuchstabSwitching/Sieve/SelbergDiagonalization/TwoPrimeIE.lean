import BuchstabSwitching.Sieve.SelbergDiagonalization.Weights
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Two-Prime Inclusion-Exclusion Identity for `ξ < z³`

Proves the exact 0-, 1-, and 2-prime decomposition `selbergJ_two_prime_inclusion_exclusion`
and its companion lower bound `selbergJ_lt_two_prime_inclusion_exclusion_le`.
-/

namespace BuchstabSwitching

/-! ### Two-Prime Inclusion-Exclusion Identity for `ξ < z³` -/

/-- Exact 0-, 1-, and 2-prime decomposition of `selbergJ g P xi` when `xi < z ^ 3`. -/
theorem selbergJ_two_prime_inclusion_exclusion (P : Finset ℕ) (g : ℕ → ℝ) (z xi : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hxi : xi < z ^ 3) :
    let P_lt := P.filter (· < z)
    let Q_z := P.filter (z ≤ ·)
    selbergJ g P xi =
      selbergJ g P_lt xi +
        ∑ q ∈ Q_z, selbergH g q * selbergJ g P_lt (xi / q) +
        ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
          selbergH g q₁ * selbergH g q₂ * selbergJ g P_lt (xi / (q₁ * q₂)) := by
  dsimp only
  set P_lt := P.filter (· < z)
  set Q_z := P.filter (z ≤ ·)
  have hP_lt_pr : ∀ p ∈ P_lt, p.Prime := fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hQ_pr : ∀ p ∈ Q_z, p.Prime := fun p hp => hP p (Finset.mem_filter.mp hp).1
  by_cases hxi0 : xi = 0
  · subst hxi0
    simp [selbergJ_zero hP, selbergJ_zero hP_lt_pr]
  have hdisj : Disjoint P_lt Q_z := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    omega
  have hunion : P_lt ∪ Q_z = P := by
    ext p
    simp only [P_lt, Q_z, Finset.mem_union, Finset.mem_filter]
    by_cases hp : p ∈ P <;> simp [hp]; omega
  have hz_gt1 : 1 < z := by
    by_contra hle
    have hz01 : z = 0 ∨ z = 1 := by omega
    rcases hz01 with rfl | rfl
    · simp at hxi
    · simp at hxi
      omega
  let D0 := (D_xi P xi).filter (fun d => (d.primeFactors ∩ Q_z).card = 0)
  let D1 := (D_xi P xi).filter (fun d => (d.primeFactors ∩ Q_z).card = 1)
  let D2 := (D_xi P xi).filter (fun d => (d.primeFactors ∩ Q_z).card = 2)
  have hcard_lt3 : ∀ d ∈ D_xi P xi, (d.primeFactors ∩ Q_z).card < 3 := by
    intro d hd
    by_contra hge
    have h3 : 3 ≤ (d.primeFactors ∩ Q_z).card := by omega
    have hle_d : z ^ (d.primeFactors ∩ Q_z).card ≤ d := by
      calc z ^ (d.primeFactors ∩ Q_z).card
          = ∏ _p ∈ d.primeFactors ∩ Q_z, z := by simp [Finset.prod_const]
        _ ≤ ∏ p ∈ d.primeFactors ∩ Q_z, p := by
            refine Finset.prod_le_prod fun p hp => ?_
            exact (Finset.mem_filter.mp (Finset.mem_inter.mp hp).2).2
        _ ≤ ∏ p ∈ d.primeFactors, p := by
            refine Nat.le_of_dvd (Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos) ?_
            exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_left
        _ = d := Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_D_xi hP hd)
    have hd_le : d ≤ xi := ((mem_D_xi_iff P xi d).mp hd).2
    have hpow : z ^ 3 ≤ z ^ (d.primeFactors ∩ Q_z).card :=
      Nat.pow_le_pow_right (by omega) h3
    omega
  have hpart : D_xi P xi = D0 ∪ D1 ∪ D2 := by
    ext d
    simp only [D0, D1, D2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hd
      have hlt := hcard_lt3 d hd
      interval_cases h : (d.primeFactors ∩ Q_z).card
      · exact Or.inl (Or.inl ⟨hd, rfl⟩)
      · exact Or.inl (Or.inr ⟨hd, rfl⟩)
      · exact Or.inr ⟨hd, rfl⟩
    · rintro ((⟨hd, _⟩ | ⟨hd, _⟩) | ⟨hd, _⟩) <;> exact hd
  have hdisj01 : Disjoint D0 D1 := by
    rw [Finset.disjoint_left]
    intro d h0 h1
    have c0 := (Finset.mem_filter.mp h0).2
    have c1 := (Finset.mem_filter.mp h1).2
    omega
  have hdisj012 : Disjoint (D0 ∪ D1) D2 := by
    rw [Finset.disjoint_left]
    intro d h01 h2
    have c2 := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h01 with h0 | h1
    · have c0 := (Finset.mem_filter.mp h0).2; omega
    · have c1 := (Finset.mem_filter.mp h1).2; omega
  have hJ_split : selbergJ g P xi =
      (∑ d ∈ D0, selbergH g d) + (∑ d ∈ D1, selbergH g d) + (∑ d ∈ D2, selbergH g d) := by
    unfold selbergJ
    rw [hpart, Finset.sum_union hdisj012, Finset.sum_union hdisj01]
  have hD0_eq : D0 = D_xi P_lt xi := by
    ext d
    simp only [D0, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hc⟩
      rcases (mem_D_xi_iff_squarefree hP).mp hd with ⟨hd_sq, hd_sub, hd_le⟩
      refine (mem_D_xi_iff_squarefree hP_lt_pr).mpr ⟨hd_sq, ?_, hd_le⟩
      intro p hp
      have hpP := hd_sub hp
      have hp_notQ : p ∉ Q_z := by
        intro hpQ
        have hne : (d.primeFactors ∩ Q_z).Nonempty := ⟨p, Finset.mem_inter.mpr ⟨hp, hpQ⟩⟩
        have hpos := Finset.card_pos.mpr hne
        omega
      rw [← hunion, Finset.mem_union] at hpP
      exact hpP.resolve_right hp_notQ
    · intro hd
      rcases (mem_D_xi_iff_squarefree hP_lt_pr).mp hd with ⟨hd_sq, hd_sub, hd_le⟩
      have hdP : d ∈ D_xi P xi := D_xi_mono_P (Finset.filter_subset _ P) xi hd
      refine ⟨hdP, Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun p hp => ?_)⟩
      rcases Finset.mem_inter.mp hp with ⟨hpd, hpQ⟩
      exact Finset.disjoint_left.mp hdisj (hd_sub hpd) hpQ
  have hS0 : ∑ d ∈ D0, selbergH g d = selbergJ g P_lt xi := by
    rw [hD0_eq]; rfl
  have hS1 : ∑ d ∈ D1, selbergH g d = ∑ q ∈ Q_z, selbergH g q * selbergJ g P_lt (xi / q) := by
    have hsum_sigma : ∑ q ∈ Q_z, selbergH g q * selbergJ g P_lt (xi / q) =
        ∑ p ∈ Q_z.sigma (fun q => D_xi P_lt (xi / q)), selbergH g (p.1 * p.2) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun q hq => ?_
      unfold selbergJ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₀ hd₀ => ?_
      have hq_pr := hQ_pr q hq
      have hd₀_ne := ne_zero_of_mem_D_xi hP_lt_pr hd₀
      have hd₀_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hd₀
      have hcop : Nat.Coprime q d₀ := by
        rw [Nat.Prime.coprime_iff_not_dvd hq_pr]
        intro hqd₀
        have hqpf : q ∈ d₀.primeFactors := Nat.mem_primeFactors.mpr ⟨hq_pr, hqd₀, hd₀_ne⟩
        exact Finset.disjoint_left.mp hdisj (hd₀_sub hqpf) hq
      rw [selbergH_mul_of_coprime g hcop hq_pr.ne_zero hd₀_ne]
    rw [hsum_sigma]
    symm
    refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
    · rintro ⟨q, d₀⟩ hp
      simp only [Finset.mem_sigma] at hp
      rcases hp with ⟨hq, hd₀⟩
      have hq_pr := hQ_pr q hq
      have hq_mem : q ∈ D_xi P xi := by
        have hq_le : q ≤ xi := by
          have hd₀_pos := pos_of_mem_D_xi hP_lt_pr hd₀
          have hd₀_le : d₀ ≤ xi / q := ((mem_D_xi_iff P_lt (xi / q) d₀).mp hd₀).2
          have : 1 ≤ xi / q := hd₀_pos.trans_le hd₀_le
          exact (Nat.le_div_iff_mul_le hq_pr.pos).mp this |>.trans' (by omega)
        exact (mem_D_xi_iff P xi q).mpr ⟨⟨{q}, Finset.singleton_subset_iff.mpr
          (Finset.mem_filter.mp hq).1, by simp⟩, hq_le⟩
      have hd₀_mem : d₀ ∈ D_xi P xi :=
        D_xi_mono_P (Finset.filter_subset _ P) xi (D_xi_mono_xi P_lt (Nat.div_le_self xi q) hd₀)
      have hd₀_ne := ne_zero_of_mem_D_xi hP_lt_pr hd₀
      have hd₀_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hd₀
      have hcop : Nat.Coprime q d₀ := by
        rw [Nat.Prime.coprime_iff_not_dvd hq_pr]
        intro hqd₀
        exact Finset.disjoint_left.mp hdisj
          (hd₀_sub (Nat.mem_primeFactors.mpr ⟨hq_pr, hqd₀, hd₀_ne⟩)) hq
      have hle : q * d₀ ≤ xi := by
        have hd₀_le : d₀ ≤ xi / q := ((mem_D_xi_iff P_lt (xi / q) d₀).mp hd₀).2
        exact (Nat.mul_le_mul_left q hd₀_le).trans (Nat.mul_div_le xi q)
      have hmem : q * d₀ ∈ D_xi P xi := mul_mem_D_xi hP hq_mem hd₀_mem hcop hle
      have hinter : (q * d₀).primeFactors ∩ Q_z = {q} := by
        rw [Nat.primeFactors_mul hq_pr.ne_zero hd₀_ne, hq_pr.primeFactors]
        ext r
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hr, hrQ⟩
          · rfl
          · exact absurd hrQ (Finset.disjoint_left.mp hdisj (hd₀_sub hr))
        · rintro rfl
          exact ⟨Or.inl rfl, hq⟩
      exact Finset.mem_filter.mpr ⟨hmem, by rw [hinter, Finset.card_singleton]⟩
    · rintro ⟨q₁, d₁⟩ hp₁ ⟨q₂, d₂⟩ hp₂ heq
      simp only [Finset.mem_sigma] at hp₁ hp₂
      have hq₁_pr := hQ_pr q₁ hp₁.1
      have hq₂_pr := hQ_pr q₂ hp₂.1
      have hd₁_ne := ne_zero_of_mem_D_xi hP_lt_pr hp₁.2
      have hd₂_ne := ne_zero_of_mem_D_xi hP_lt_pr hp₂.2
      have hd₁_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hp₁.2
      have hd₂_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hp₂.2
      have hpf := congrArg (fun n => n.primeFactors ∩ Q_z) heq
      dsimp only at hpf heq
      have hi1 : (q₁ * d₁).primeFactors ∩ Q_z = {q₁} := by
        rw [Nat.primeFactors_mul hq₁_pr.ne_zero hd₁_ne, hq₁_pr.primeFactors]
        ext r
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hr, _⟩
          · rfl
          · exact absurd hr (fun h => Finset.disjoint_left.mp hdisj (hd₁_sub h) ‹r ∈ Q_z›)
        · rintro rfl; exact ⟨Or.inl rfl, hp₁.1⟩
      have hi2 : (q₂ * d₂).primeFactors ∩ Q_z = {q₂} := by
        rw [Nat.primeFactors_mul hq₂_pr.ne_zero hd₂_ne, hq₂_pr.primeFactors]
        ext r
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hr, _⟩
          · rfl
          · exact absurd hr (fun h => Finset.disjoint_left.mp hdisj (hd₂_sub h) ‹r ∈ Q_z›)
        · rintro rfl; exact ⟨Or.inl rfl, hp₂.1⟩
      rw [hi1, hi2] at hpf
      have hq_eq : q₁ = q₂ := Finset.singleton_injective hpf
      subst hq_eq
      have hd_eq : d₁ = d₂ := Nat.mul_left_cancel hq₁_pr.pos heq
      subst hd_eq
      rfl
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdD, hcard⟩
      obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hcard
      have hq_mem : q ∈ d.primeFactors ∩ Q_z := hq_eq ▸ Finset.mem_singleton_self q
      rcases Finset.mem_inter.mp hq_mem with ⟨hq_pf, hqQ⟩
      have hq_pr := hQ_pr q hqQ
      have hqd : q ∣ d := Nat.dvd_of_mem_primeFactors hq_pf
      let d₀ := d / q
      have hd_eq : q * d₀ = d := Nat.mul_div_cancel' hqd
      have hd₀D_full : d₀ ∈ D_xi P xi := mem_D_xi_of_dvd hP hdD ⟨q, by rw [mul_comm, hd_eq]⟩
      have hd_le : d ≤ xi := ((mem_D_xi_iff P xi d).mp hdD).2
      have hd₀_le : d₀ ≤ xi / q := (Nat.le_div_iff_mul_le hq_pr.pos).mpr (by rw [mul_comm, hd_eq]; exact hd_le)
      have hd₀_sq := squarefree_of_mem_D_xi hP hd₀D_full
      have hd₀_sub_P := primeFactors_subset_of_mem_D_xi hP hd₀D_full
      have hd₀_ne := ne_zero_of_mem_D_xi hP hd₀D_full
      have hcop : Nat.Coprime q d₀ := by
        have hsq : Squarefree (q * d₀) := by rw [hd_eq]; exact squarefree_of_mem_D_xi hP hdD
        exact Nat.coprime_of_squarefree_mul hsq
      have hd₀_sub : d₀.primeFactors ⊆ P_lt := by
        intro r hr
        have hrP := hd₀_sub_P hr
        have hrd : r ∈ d.primeFactors := by
          rw [← hd_eq, Nat.primeFactors_mul hq_pr.ne_zero hd₀_ne]
          exact Finset.mem_union_right _ hr
        have hr_ne_q : r ≠ q := by
          rintro rfl
          exact (Nat.Prime.coprime_iff_not_dvd hq_pr).mp hcop (Nat.dvd_of_mem_primeFactors hr)
        have hr_notQ : r ∉ Q_z := by
          intro hrQ
          have hmem : r ∈ d.primeFactors ∩ Q_z := Finset.mem_inter.mpr ⟨hrd, hrQ⟩
          rw [hq_eq, Finset.mem_singleton] at hmem
          exact hr_ne_q hmem
        rw [← hunion, Finset.mem_union] at hrP
        exact hrP.resolve_right hr_notQ
      have hd₀_mem : d₀ ∈ D_xi P_lt (xi / q) :=
        (mem_D_xi_iff_squarefree hP_lt_pr).mpr ⟨hd₀_sq, hd₀_sub, hd₀_le⟩
      exact ⟨⟨q, d₀⟩, Finset.mem_sigma.mpr ⟨hqQ, hd₀_mem⟩, hd_eq⟩
    · intro p _; rfl
  have hS2 : ∑ d ∈ D2, selbergH g d =
      ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
        selbergH g q₁ * selbergH g q₂ * selbergJ g P_lt (xi / (q₁ * q₂)) := by
    let T2 : Finset (Σ q₁ : ℕ, Σ q₂ : ℕ, ℕ) :=
      Q_z.sigma (fun q₁ => (Q_z.filter (q₁ < ·)).sigma (fun q₂ => D_xi P_lt (xi / (q₁ * q₂))))
    have hsum_T2 : ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
          selbergH g q₁ * selbergH g q₂ * selbergJ g P_lt (xi / (q₁ * q₂)) =
        ∑ p ∈ T2, selbergH g (p.1 * p.2.1 * p.2.2) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun q₁ hq₁ => ?_
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun q₂ hq₂ => ?_
      have hq₁_pr := hQ_pr q₁ hq₁
      have hq₂Q := (Finset.mem_filter.mp hq₂).1
      have hq₂_pr := hQ_pr q₂ hq₂Q
      have hlt : q₁ < q₂ := (Finset.mem_filter.mp hq₂).2
      have hcop₁₂ : Nat.Coprime q₁ q₂ :=
        ((hq₂_pr.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hq₁_pr.pos hlt)).symm
      unfold selbergJ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₀ hd₀ => ?_
      have hd₀_ne := ne_zero_of_mem_D_xi hP_lt_pr hd₀
      have hd₀_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hd₀
      have hcop₁ : Nat.Coprime q₁ d₀ := (hq₁_pr.coprime_iff_not_dvd).mpr fun h =>
        Finset.disjoint_left.mp hdisj (hd₀_sub (Nat.mem_primeFactors.mpr ⟨hq₁_pr, h, hd₀_ne⟩)) hq₁
      have hcop₂ : Nat.Coprime q₂ d₀ := (hq₂_pr.coprime_iff_not_dvd).mpr fun h =>
        Finset.disjoint_left.mp hdisj (hd₀_sub (Nat.mem_primeFactors.mpr ⟨hq₂_pr, h, hd₀_ne⟩)) hq₂Q
      have hcop12_d : Nat.Coprime (q₁ * q₂) d₀ := hcop₁.mul_left hcop₂
      rw [selbergH_mul_of_coprime g hcop12_d (Nat.mul_pos hq₁_pr.pos hq₂_pr.pos).ne' hd₀_ne,
        selbergH_mul_of_coprime g hcop₁₂ hq₁_pr.ne_zero hq₂_pr.ne_zero]
    rw [hsum_T2]
    symm
    refine Finset.sum_bij (fun p _ => p.1 * p.2.1 * p.2.2) ?_ ?_ ?_ ?_
    · rintro ⟨q₁, q₂, d₀⟩ hp
      simp only [T2, Finset.mem_sigma, Finset.mem_filter] at hp
      rcases hp with ⟨hq₁, ⟨hq₂Q, hlt⟩, hd₀⟩
      have hq₁_pr := hQ_pr q₁ hq₁
      have hq₂_pr := hQ_pr q₂ hq₂Q
      have hd₀_ne := ne_zero_of_mem_D_xi hP_lt_pr hd₀
      have hd₀_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hd₀
      have hcop₁₂ : Nat.Coprime q₁ q₂ :=
        ((hq₂_pr.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hq₁_pr.pos hlt)).symm
      have hcop₁ : Nat.Coprime q₁ d₀ := (hq₁_pr.coprime_iff_not_dvd).mpr fun h =>
        Finset.disjoint_left.mp hdisj (hd₀_sub (Nat.mem_primeFactors.mpr ⟨hq₁_pr, h, hd₀_ne⟩)) hq₁
      have hcop₂ : Nat.Coprime q₂ d₀ := (hq₂_pr.coprime_iff_not_dvd).mpr fun h =>
        Finset.disjoint_left.mp hdisj (hd₀_sub (Nat.mem_primeFactors.mpr ⟨hq₂_pr, h, hd₀_ne⟩)) hq₂Q
      have hcop12_d : Nat.Coprime (q₁ * q₂) d₀ := hcop₁.mul_left hcop₂
      have hd₀_le : d₀ ≤ xi / (q₁ * q₂) := ((mem_D_xi_iff P_lt (xi / (q₁ * q₂)) d₀).mp hd₀).2
      have hmul_le : q₁ * q₂ * d₀ ≤ xi :=
        (Nat.mul_le_mul_left (q₁ * q₂) hd₀_le).trans (Nat.mul_div_le xi (q₁ * q₂))
      have hd₀_pos := pos_of_mem_D_xi hP_lt_pr hd₀
      have hq₁_mem : q₁ ∈ D_xi P xi := (mem_D_xi_iff P xi q₁).mpr ⟨⟨{q₁},
        Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hq₁).1, by simp⟩,
        by calc q₁ ≤ q₁ * q₂ := Nat.le_mul_of_pos_right q₁ hq₂_pr.pos
          _ ≤ q₁ * q₂ * d₀ := Nat.le_mul_of_pos_right _ hd₀_pos
          _ ≤ xi := hmul_le⟩
      have hq₂_mem : q₂ ∈ D_xi P xi := (mem_D_xi_iff P xi q₂).mpr ⟨⟨{q₂},
        Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hq₂Q).1, by simp⟩,
        by calc q₂ ≤ q₁ * q₂ := Nat.le_mul_of_pos_left q₂ hq₁_pr.pos
          _ ≤ q₁ * q₂ * d₀ := Nat.le_mul_of_pos_right _ hd₀_pos
          _ ≤ xi := hmul_le⟩
      have hq₁₂_mem : q₁ * q₂ ∈ D_xi P xi :=
        mul_mem_D_xi hP hq₁_mem hq₂_mem hcop₁₂
          ((Nat.le_mul_of_pos_right (q₁ * q₂) hd₀_pos).trans hmul_le)
      have hd₀_mem : d₀ ∈ D_xi P xi :=
        D_xi_mono_P (Finset.filter_subset _ P) xi (D_xi_mono_xi P_lt (Nat.div_le_self xi (q₁ * q₂)) hd₀)
      have hmem : q₁ * q₂ * d₀ ∈ D_xi P xi := mul_mem_D_xi hP hq₁₂_mem hd₀_mem hcop12_d hmul_le
      have hinter : (q₁ * q₂ * d₀).primeFactors ∩ Q_z = {q₁, q₂} := by
        rw [Nat.primeFactors_mul (Nat.mul_pos hq₁_pr.pos hq₂_pr.pos).ne' hd₀_ne,
          Nat.primeFactors_mul hq₁_pr.ne_zero hq₂_pr.ne_zero, hq₁_pr.primeFactors, hq₂_pr.primeFactors]
        ext r
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl) | hr, hrQ⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hrQ (Finset.disjoint_left.mp hdisj (hd₀_sub hr))
        · rintro (rfl | rfl)
          · exact ⟨Or.inl (Or.inl rfl), hq₁⟩
          · exact ⟨Or.inl (Or.inr rfl), hq₂Q⟩
      refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
      rw [hinter, Finset.card_pair hlt.ne]
    · rintro ⟨q₁, q₂, d₀⟩ hp₁ ⟨q₃, q₄, d₁⟩ hp₂ heq
      simp only [T2, Finset.mem_sigma, Finset.mem_filter] at hp₁ hp₂
      rcases hp₁ with ⟨hq₁, ⟨hq₂Q, hlt₁₂⟩, hd₀⟩
      rcases hp₂ with ⟨hq₃, ⟨hq₄Q, hlt₃₄⟩, hd₁⟩
      have hq₁_pr := hQ_pr q₁ hq₁
      have hq₂_pr := hQ_pr q₂ hq₂Q
      have hq₃_pr := hQ_pr q₃ hq₃
      have hq₄_pr := hQ_pr q₄ hq₄Q
      have hd₀_ne := ne_zero_of_mem_D_xi hP_lt_pr hd₀
      have hd₁_ne := ne_zero_of_mem_D_xi hP_lt_pr hd₁
      have hd₀_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hd₀
      have hd₁_sub := primeFactors_subset_of_mem_D_xi hP_lt_pr hd₁
      dsimp only at heq
      have hi1 : (q₁ * q₂ * d₀).primeFactors ∩ Q_z = {q₁, q₂} := by
        rw [Nat.primeFactors_mul (Nat.mul_pos hq₁_pr.pos hq₂_pr.pos).ne' hd₀_ne,
          Nat.primeFactors_mul hq₁_pr.ne_zero hq₂_pr.ne_zero, hq₁_pr.primeFactors, hq₂_pr.primeFactors]
        ext r
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl) | hr, hrQ⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hrQ (Finset.disjoint_left.mp hdisj (hd₀_sub hr))
        · rintro (rfl | rfl)
          · exact ⟨Or.inl (Or.inl rfl), hq₁⟩
          · exact ⟨Or.inl (Or.inr rfl), hq₂Q⟩
      have hi2 : (q₃ * q₄ * d₁).primeFactors ∩ Q_z = {q₃, q₄} := by
        rw [Nat.primeFactors_mul (Nat.mul_pos hq₃_pr.pos hq₄_pr.pos).ne' hd₁_ne,
          Nat.primeFactors_mul hq₃_pr.ne_zero hq₄_pr.ne_zero, hq₃_pr.primeFactors, hq₄_pr.primeFactors]
        ext r
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨(rfl | rfl) | hr, hrQ⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hrQ (Finset.disjoint_left.mp hdisj (hd₁_sub hr))
        · rintro (rfl | rfl)
          · exact ⟨Or.inl (Or.inl rfl), hq₃⟩
          · exact ⟨Or.inl (Or.inr rfl), hq₄Q⟩
      have hset : ({q₁, q₂} : Finset ℕ) = {q₃, q₄} := by
        rw [← hi1, ← hi2, heq]
      have hq₁_mem : q₁ ∈ ({q₃, q₄} : Finset ℕ) := hset ▸ Finset.mem_insert_self q₁ {q₂}
      have hq₂_mem : q₂ ∈ ({q₃, q₄} : Finset ℕ) := hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q₂)
      have hq₃_mem : q₃ ∈ ({q₁, q₂} : Finset ℕ) := hset.symm ▸ Finset.mem_insert_self q₃ {q₄}
      have hq₄_mem : q₄ ∈ ({q₁, q₂} : Finset ℕ) := hset.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q₄)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq₁_mem hq₂_mem hq₃_mem hq₄_mem
      have hq₁₃ : q₁ = q₃ := by omega
      have hq₂₄ : q₂ = q₄ := by omega
      subst hq₁₃; subst hq₂₄
      have hd_eq : d₀ = d₁ := Nat.mul_left_cancel (Nat.mul_pos hq₁_pr.pos hq₂_pr.pos) heq
      subst hd_eq
      rfl
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdD, hcard⟩
      obtain ⟨a, b, hab_ne, hab_eq⟩ := Finset.card_eq_two.mp hcard
      let q₁ := min a b
      let q₂ := max a b
      have hlt : q₁ < q₂ := by
        rcases lt_or_gt_of_ne hab_ne with h | h
        · simp [q₁, q₂, min_eq_left h.le, max_eq_right h.le, h]
        · simp [q₁, q₂, min_eq_right h.le, max_eq_left h.le, h]
      have hpair_eq : d.primeFactors ∩ Q_z = {q₁, q₂} := by
        rw [hab_eq]
        rcases le_total a b with h | h
        · simp [q₁, q₂, min_eq_left h, max_eq_right h]
        · simp [q₁, q₂, min_eq_right h, max_eq_left h, Finset.pair_comm]
      have hq₁_mem : q₁ ∈ d.primeFactors ∩ Q_z := hpair_eq ▸ Finset.mem_insert_self q₁ {q₂}
      have hq₂_mem : q₂ ∈ d.primeFactors ∩ Q_z := hpair_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q₂)
      rcases Finset.mem_inter.mp hq₁_mem with ⟨hq₁_pf, hq₁Q⟩
      rcases Finset.mem_inter.mp hq₂_mem with ⟨hq₂_pf, hq₂Q⟩
      have hq₁_pr := hQ_pr q₁ hq₁Q
      have hq₂_pr := hQ_pr q₂ hq₂Q
      have hq₁₂_dvd : q₁ * q₂ ∣ d := by
        have hcop : Nat.Coprime q₁ q₂ :=
          ((hq₂_pr.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hq₁_pr.pos hlt)).symm
        exact hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hq₁_pf)
          (Nat.dvd_of_mem_primeFactors hq₂_pf)
      let d₀ := d / (q₁ * q₂)
      have hd_eq : q₁ * q₂ * d₀ = d := Nat.mul_div_cancel' hq₁₂_dvd
      have hd₀D_full : d₀ ∈ D_xi P xi := mem_D_xi_of_dvd hP hdD ⟨q₁ * q₂, by rw [mul_comm, hd_eq]⟩
      have hd_le : d ≤ xi := ((mem_D_xi_iff P xi d).mp hdD).2
      have hd₀_le : d₀ ≤ xi / (q₁ * q₂) :=
        (Nat.le_div_iff_mul_le (Nat.mul_pos hq₁_pr.pos hq₂_pr.pos)).mpr
          (by rw [mul_comm, hd_eq]; exact hd_le)
      have hd₀_sq := squarefree_of_mem_D_xi hP hd₀D_full
      have hd₀_sub_P := primeFactors_subset_of_mem_D_xi hP hd₀D_full
      have hd₀_ne := ne_zero_of_mem_D_xi hP hd₀D_full
      have hcop : Nat.Coprime (q₁ * q₂) d₀ := by
        have hsq : Squarefree (q₁ * q₂ * d₀) := by rw [hd_eq]; exact squarefree_of_mem_D_xi hP hdD
        exact Nat.coprime_of_squarefree_mul hsq
      have hd₀_sub : d₀.primeFactors ⊆ P_lt := by
        intro r hr
        have hrP := hd₀_sub_P hr
        have hrd : r ∈ d.primeFactors := by
          rw [← hd_eq, Nat.primeFactors_mul (Nat.mul_pos hq₁_pr.pos hq₂_pr.pos).ne' hd₀_ne]
          exact Finset.mem_union_right _ hr
        have hr_not_q₁₂ : r ≠ q₁ ∧ r ≠ q₂ := by
          have hr_dvd : r ∣ d₀ := Nat.dvd_of_mem_primeFactors hr
          constructor
          · rintro rfl
            exact (Nat.Prime.coprime_iff_not_dvd hq₁_pr).mp
              (hcop.coprime_dvd_left (dvd_mul_right q₁ q₂)) hr_dvd
          · rintro rfl
            exact (Nat.Prime.coprime_iff_not_dvd hq₂_pr).mp
              (hcop.coprime_dvd_left (dvd_mul_left q₂ q₁)) hr_dvd
        have hr_notQ : r ∉ Q_z := by
          intro hrQ
          have hmem : r ∈ d.primeFactors ∩ Q_z := Finset.mem_inter.mpr ⟨hrd, hrQ⟩
          rw [hpair_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl <;> simp at hr_not_q₁₂
        rw [← hunion, Finset.mem_union] at hrP
        exact hrP.resolve_right hr_notQ
      have hd₀_mem : d₀ ∈ D_xi P_lt (xi / (q₁ * q₂)) :=
        (mem_D_xi_iff_squarefree hP_lt_pr).mpr ⟨hd₀_sq, hd₀_sub, hd₀_le⟩
      refine ⟨⟨q₁, q₂, d₀⟩, ?_, hd_eq⟩
      simp only [T2, Finset.mem_sigma, Finset.mem_filter]
      exact ⟨hq₁Q, ⟨hq₂Q, hlt⟩, hd₀_mem⟩
    · intro p _; rfl
  rw [hJ_split, hS0, hS1, hS2]

/-- Companion 2-prime inclusion-exclusion lower bound on `selbergJ g (P.filter (· < z)) xi`
when `xi < z ^ 3`. -/
theorem selbergJ_lt_two_prime_inclusion_exclusion_le
    (P : Finset ℕ) (g : ℕ → ℝ) (z xi : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) (hxi : xi < z ^ 3) :
    let P_lt := P.filter (· < z)
    let Q_z := P.filter (z ≤ ·)
    selbergJ g P xi -
      ∑ q ∈ Q_z, selbergH g q * selbergJ g P (xi / q) +
      ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
        selbergH g q₁ * selbergH g q₂ * selbergJ g P (xi / (q₁ * q₂)) ≤
      selbergJ g P_lt xi := by
  dsimp only
  set P_lt := P.filter (· < z)
  set Q_z := P.filter (z ≤ ·)
  have hP_lt_pr : ∀ p ∈ P_lt, p.Prime := fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hg_lt : ∀ p ∈ P_lt, 0 < g p ∧ g p < 1 := fun p hp => hg p (Finset.mem_filter.mp hp).1
  have hQ_pr : ∀ p ∈ Q_z, p.Prime := fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hmain := selbergJ_two_prime_inclusion_exclusion P g z xi hP hxi
  dsimp only at hmain
  have h1 : ∀ q ∈ Q_z, selbergJ g P (xi / q) =
      selbergJ g P_lt (xi / q) + ∑ r ∈ Q_z, selbergH g r * selbergJ g P_lt ((xi / q) / r) := by
    intro q hq
    have hq_z : z ≤ q := (Finset.mem_filter.mp hq).2
    have hxq_lt : xi / q < z ^ 3 := lt_of_le_of_lt (Nat.div_le_self xi q) hxi
    have hxq := selbergJ_two_prime_inclusion_exclusion P g z (xi / q) hP hxq_lt
    dsimp only at hxq
    have hzero : ∑ r₁ ∈ Q_z, ∑ r₂ ∈ Q_z.filter (r₁ < ·),
        selbergH g r₁ * selbergH g r₂ * selbergJ g P_lt ((xi / q) / (r₁ * r₂)) = 0 := by
      refine Finset.sum_eq_zero fun r₁ hr₁ => Finset.sum_eq_zero fun r₂ hr₂ => ?_
      have hr₁_z : z ≤ r₁ := (Finset.mem_filter.mp hr₁).2
      have hr₂_z : z ≤ r₂ := (Finset.mem_filter.mp (Finset.mem_filter.mp hr₂).1).2
      have hprod_ge : z ^ 3 ≤ q * (r₁ * r₂) := by
        calc z ^ 3 = z * (z * z) := by ring
          _ ≤ q * (r₁ * r₂) := Nat.mul_le_mul hq_z (Nat.mul_le_mul hr₁_z hr₂_z)
      have hdiv0 : (xi / q) / (r₁ * r₂) = 0 := by
        rw [Nat.div_div_eq_div_mul]
        exact Nat.div_eq_of_lt (lt_of_lt_of_le hxi hprod_ge)
      rw [hdiv0, selbergJ_zero hP_lt_pr, mul_zero]
    rw [hxq, hzero, add_zero]
  have h1_sum :
      ∑ q ∈ Q_z, selbergH g q * selbergJ g P (xi / q) =
        (∑ q ∈ Q_z, selbergH g q * selbergJ g P_lt (xi / q)) +
        ∑ q ∈ Q_z, ∑ r ∈ Q_z, selbergH g q * selbergH g r * selbergJ g P_lt (xi / (q * r)) := by
    trans ∑ q ∈ Q_z, (selbergH g q * selbergJ g P_lt (xi / q) +
        ∑ r ∈ Q_z, selbergH g q * selbergH g r * selbergJ g P_lt (xi / (q * r)))
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [h1 q hq, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Nat.div_div_eq_div_mul]
      ring
    · rw [Finset.sum_add_distrib]
  have h2_pairs :
      2 * ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
          selbergH g q₁ * selbergH g q₂ * selbergJ g P_lt (xi / (q₁ * q₂)) ≤
        ∑ q ∈ Q_z, ∑ r ∈ Q_z, selbergH g q * selbergH g r * selbergJ g P_lt (xi / (q * r)) := by
    let F : ℕ → ℕ → ℝ := fun q r => selbergH g q * selbergH g r * selbergJ g P_lt (xi / (q * r))
    have hF_symm : ∀ q r, F q r = F r q := fun q r => by
      simp only [F, mul_comm q r]
      ring
    have hF_nonneg : ∀ q ∈ Q_z, ∀ r ∈ Q_z, 0 ≤ F q r := fun q hq r hr => by
      have hq_sub : q.primeFactors ⊆ P := by
        rw [(hQ_pr q hq).primeFactors]
        exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hq).1
      have hr_sub : r.primeFactors ⊆ P := by
        rw [(hQ_pr r hr).primeFactors]
        exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hr).1
      exact mul_nonneg (mul_nonneg (selbergH_nonneg hg hq_sub) (selbergH_nonneg hg hr_sub))
        (selbergJ_nonneg hP_lt_pr hg_lt _)
    have hsplit : ∑ q ∈ Q_z, ∑ r ∈ Q_z, F q r =
        (∑ q ∈ Q_z, ∑ r ∈ Q_z.filter (q < ·), F q r) +
        (∑ q ∈ Q_z, ∑ r ∈ Q_z.filter (· < q), F q r) +
        ∑ q ∈ Q_z, F q q := by
      have hrow : ∀ q ∈ Q_z, ∑ r ∈ Q_z, F q r =
          (∑ r ∈ Q_z.filter (q < ·), F q r) + (∑ r ∈ Q_z.filter (· < q), F q r) + F q q := by
        intro q hq
        have hlt_le : Q_z.filter (q < ·) ∪ Q_z.filter (· < q) ∪ {q} = Q_z := by
          ext r
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ((⟨hr, _⟩ | ⟨hr, _⟩) | rfl) <;> assumption
          · intro hr
            rcases lt_trichotomy q r with h | rfl | h
            · exact Or.inl (Or.inl ⟨hr, h⟩)
            · exact Or.inr rfl
            · exact Or.inl (Or.inr ⟨hr, h⟩)
        have hd1 : Disjoint (Q_z.filter (q < ·)) (Q_z.filter (· < q)) := by
          rw [Finset.disjoint_left]
          intro r h1 h2
          have := (Finset.mem_filter.mp h1).2
          have := (Finset.mem_filter.mp h2).2
          omega
        have hd2 : Disjoint (Q_z.filter (q < ·) ∪ Q_z.filter (· < q)) {q} := by
          rw [Finset.disjoint_left]
          intro r h12 h3
          rw [Finset.mem_singleton] at h3
          subst h3
          rcases Finset.mem_union.mp h12 with h1 | h2
          · exact lt_irrefl _ (Finset.mem_filter.mp h1).2
          · exact lt_irrefl _ (Finset.mem_filter.mp h2).2
        conv_lhs => rw [← hlt_le]
        rw [Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_singleton]
      rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hsym_sum : ∑ q ∈ Q_z, ∑ r ∈ Q_z.filter (· < q), F q r =
        ∑ q ∈ Q_z, ∑ r ∈ Q_z.filter (q < ·), F q r := by
      have hs1 : ∑ q ∈ Q_z, ∑ r ∈ Q_z.filter (· < q), F q r =
          ∑ p ∈ Q_z.sigma (fun q => Q_z.filter (· < q)), F p.1 p.2 := by
        rw [Finset.sum_sigma]
      have hs2 : ∑ q ∈ Q_z, ∑ r ∈ Q_z.filter (q < ·), F q r =
          ∑ p ∈ Q_z.sigma (fun q => Q_z.filter (q < ·)), F p.1 p.2 := by
        rw [Finset.sum_sigma]
      have hbij : ∑ p ∈ Q_z.sigma (fun q => Q_z.filter (· < q)), F p.1 p.2 =
          ∑ p ∈ Q_z.sigma (fun q => Q_z.filter (q < ·)), F p.1 p.2 := by
        refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
        · rintro ⟨q, r⟩ hp
          simp only [Finset.mem_sigma, Finset.mem_filter] at hp ⊢
          exact ⟨hp.2.1, hp.1, hp.2.2⟩
        · rintro ⟨q₁, r₁⟩ _ ⟨q₂, r₂⟩ _ h
          simp only [Sigma.mk.inj_iff] at h
          rcases h with ⟨rfl, hr⟩
          have : q₁ = q₂ := by simpa using hr
          subst this; rfl
        · rintro ⟨r, q⟩ hp
          simp only [Finset.mem_sigma, Finset.mem_filter] at hp
          exact ⟨⟨q, r⟩, Finset.mem_sigma.mpr ⟨hp.2.1, Finset.mem_filter.mpr ⟨hp.1, hp.2.2⟩⟩, rfl⟩
        · rintro ⟨q, r⟩ _
          exact hF_symm q r
      rw [hs1, hs2, hbij]
    have hdiag_nn : 0 ≤ ∑ q ∈ Q_z, F q q :=
      Finset.sum_nonneg fun q hq => hF_nonneg q hq q hq
    rw [hsplit, hsym_sum]
    linarith
  have h2_eq :
      ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
          selbergH g q₁ * selbergH g q₂ * selbergJ g P (xi / (q₁ * q₂)) =
        ∑ q₁ ∈ Q_z, ∑ q₂ ∈ Q_z.filter (q₁ < ·),
          selbergH g q₁ * selbergH g q₂ * selbergJ g P_lt (xi / (q₁ * q₂)) := by
    refine Finset.sum_congr rfl fun q₁ hq₁ => Finset.sum_congr rfl fun q₂ hq₂ => ?_
    have hq₁_z : z ≤ q₁ := (Finset.mem_filter.mp hq₁).2
    have hq₂_z : z ≤ q₂ := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
    have hdiv_lt : xi / (q₁ * q₂) < z := by
      have hz_pos : 0 < z := by
        by_contra h0
        have hz0 : z = 0 := by omega
        subst hz0; simp at hxi
      have hq₁₂_ge : z ^ 2 ≤ q₁ * q₂ := by
        calc z ^ 2 = z * z := by ring
          _ ≤ q₁ * q₂ := Nat.mul_le_mul hq₁_z hq₂_z
      have hmul : (xi / (q₁ * q₂)) * z ^ 2 < z * z ^ 2 := by
        calc (xi / (q₁ * q₂)) * z ^ 2 ≤ (xi / (q₁ * q₂)) * (q₁ * q₂) :=
              Nat.mul_le_mul_left _ hq₁₂_ge
          _ ≤ xi := Nat.div_mul_le_self xi (q₁ * q₂)
          _ < z ^ 3 := hxi
          _ = z * z ^ 2 := by ring
      exact Nat.lt_of_mul_lt_mul_right hmul
    have hD_eq : D_xi P (xi / (q₁ * q₂)) = D_xi P_lt (xi / (q₁ * q₂)) := by
      ext d
      constructor
      · intro hd
        rcases (mem_D_xi_iff_squarefree hP).mp hd with ⟨hd_sq, hd_sub, hd_le⟩
        refine (mem_D_xi_iff_squarefree hP_lt_pr).mpr ⟨hd_sq, ?_, hd_le⟩
        intro p hp
        have hp_le : p ≤ d := Nat.le_of_mem_primeFactors hp
        exact Finset.mem_filter.mpr ⟨hd_sub hp, hp_le.trans_lt (hd_le.trans_lt hdiv_lt)⟩
      · exact fun hd => D_xi_mono_P (Finset.filter_subset _ P) _ hd
    have hJ_eq : selbergJ g P (xi / (q₁ * q₂)) = selbergJ g P_lt (xi / (q₁ * q₂)) := by
      unfold selbergJ; rw [hD_eq]
    rw [hJ_eq]
  rw [hmain, h1_sum, h2_eq]
  linarith

end BuchstabSwitching
