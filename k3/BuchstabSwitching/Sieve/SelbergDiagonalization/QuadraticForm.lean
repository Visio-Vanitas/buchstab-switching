import BuchstabSwitching.Sieve.SelbergDiagonalization.Weights
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Selberg Diagonalization Identity

Proves Selberg's diagonalization identity `selberg_quad_form_eq_inv_J`, showing that the
quadratic form evaluated at the optimal weights `selbergLam` equals `1 / selbergJ g P xi`.
-/

namespace BuchstabSwitching

/-! ### Selberg Diagonalization Identity -/

lemma inv_gProd_eq_sum_inv_selbergH {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {u : ℕ} (hu_sq : Squarefree u) (hu_sub : u.primeFactors ⊆ P) :
    1 / gProd g u = ∑ r ∈ u.divisors, 1 / selbergH g r := by
  have h1 : ∀ p ∈ u.primeFactors, 1 / g p = 1 + (1 - g p) / g p := by
    intro p hp
    have hgp : g p ≠ 0 := (hg p (hu_sub hp)).1.ne'
    field_simp [hgp]
    ring
  have hprod : 1 / gProd g u = ∏ p ∈ u.primeFactors, (1 + (1 - g p) / g p) := by
    unfold gProd
    rw [one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    simpa [one_div] using h1 p hp
  rw [hprod, Finset.prod_one_add]
  refine Finset.sum_bij (fun S _ => ∏ p ∈ S, p) ?_ ?_ ?_ ?_
  · intro S hS
    have hS_sub : S ⊆ u.primeFactors := Finset.mem_powerset.mp hS
    refine Nat.mem_divisors.mpr ⟨?_, hu_sq.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hu_sq]
    exact Finset.prod_dvd_prod_of_subset S u.primeFactors _ hS_sub
  · intro S₁ hS₁ S₂ hS₂ heq
    have hS₁_pr : ∀ p ∈ S₁, p.Prime := fun p hp => hP p (hu_sub (Finset.mem_powerset.mp hS₁ hp))
    have hS₂_pr : ∀ p ∈ S₂, p.Prime := fun p hp => hP p (hu_sub (Finset.mem_powerset.mp hS₂ hp))
    have hpf := congrArg Nat.primeFactors heq
    rwa [Nat.primeFactors_prod hS₁_pr, Nat.primeFactors_prod hS₂_pr] at hpf
  · intro r hr
    rcases Nat.mem_divisors.mp hr with ⟨hru, _⟩
    have hr_sq : Squarefree r := hu_sq.squarefree_of_dvd hru
    have hr_sub : r.primeFactors ⊆ u.primeFactors := Nat.primeFactors_mono hru hu_sq.ne_zero
    exact ⟨r.primeFactors, Finset.mem_powerset.mpr hr_sub, Nat.prod_primeFactors_of_squarefree hr_sq⟩
  · intro S hS
    have hS_sub : S ⊆ P := (Finset.mem_powerset.mp hS).trans hu_sub
    have hS_pr : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS_sub hp)
    unfold selbergH
    rw [Nat.primeFactors_prod hS_pr, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [inv_div]

lemma sum_moebius_divisors (q : ℕ) :
    ∑ m ∈ q.divisors, (ArithmeticFunction.moebius m : ℝ) = if q = 1 then 1 else 0 := by
  by_cases hq : q = 0
  · subst hq; simp
  · have hzeta : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) q =
        (1 : ArithmeticFunction ℤ) q := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.mul_apply] at hzeta
    simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hzeta
    have hsum : ∑ x ∈ Nat.divisorsAntidiagonal q,
        ArithmeticFunction.moebius x.1 * (if x.2 = 0 then (0 : ℤ) else 1) =
        ∑ m ∈ q.divisors, ArithmeticFunction.moebius m := by
      rw [Nat.sum_divisorsAntidiagonal (f := fun x y =>
        ArithmeticFunction.moebius x * (if y = 0 then (0 : ℤ) else 1))]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hdiv_ne : q / m ≠ 0 := by
        rcases Nat.mem_divisors.mp hm with ⟨hm_dvd, _⟩
        intro h0
        have : q = m * (q / m) := (Nat.mul_div_cancel' hm_dvd).symm
        rw [h0, mul_zero] at this
        exact hq this
      simp [hdiv_ne]
    rw [hsum] at hzeta
    have h1 : (1 : ArithmeticFunction ℤ) q = if q = 1 then 1 else 0 := by
      simp [ArithmeticFunction.one_apply]
    rw [h1] at hzeta
    have hcast : ((∑ m ∈ q.divisors, ArithmeticFunction.moebius m : ℤ) : ℝ) =
        ((if q = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) := congrArg (Int.cast : ℤ → ℝ) hzeta
    push_cast at hcast
    exact hcast

lemma selberg_diag_y {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    {xi r : ℕ} (hr : r ∈ D_xi P xi) :
    ∑ d ∈ (D_xi P xi).filter (r ∣ ·), selbergLam g P xi d * gProd g d =
      (ArithmeticFunction.moebius r : ℝ) * selbergH g r / selbergJ g P xi := by
  set D := D_xi P xi
  set J := selbergJ g P xi
  have hr_pos := pos_of_mem_D_xi hP hr
  have hxi : 1 ≤ xi := hr_pos.trans_le ((mem_D_xi_iff P xi r).mp hr).2
  have hJ : 0 < J := lt_of_lt_of_le zero_lt_one (selbergJ_pos hP hg hxi)
  have hstep1 : ∀ d ∈ D.filter (r ∣ ·),
      selbergLam g P xi d * gProd g d =
        ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d),
          ((ArithmeticFunction.moebius d : ℝ) * selbergH g (d * k)) / J := by
    intro d hd
    have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
    have hd_sub := primeFactors_subset_of_mem_D_xi hP hdD
    have hd_ne : d ≠ 0 := ne_zero_of_mem_D_xi hP hdD
    have hV_ne : (∏ p ∈ d.primeFactors, (1 - g p)) ≠ 0 :=
      (Finset.prod_pos fun p hp => sub_pos.mpr (hg p (hd_sub hp)).2).ne'
    have hhg : gProd g d / (∏ p ∈ d.primeFactors, (1 - g p)) = selbergH g d := by
      unfold gProd selbergH
      rw [← Finset.prod_div_distrib]
    have hdD' : d ∈ D_xi P xi := hdD
    unfold selbergLam
    simp only [hdD', ↓reduceIte]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkD : k ∈ D_xi P (xi / d) := (Finset.mem_filter.mp hk).1
    have hkd : Nat.Coprime k d := (Finset.mem_filter.mp hk).2
    have hk_ne : k ≠ 0 := ne_zero_of_mem_D_xi hP hkD
    rw [selbergH_mul_of_coprime g hkd.symm hd_ne hk_ne]
    calc ((ArithmeticFunction.moebius d : ℝ) / ((∏ p ∈ d.primeFactors, (1 - g p)) * J)) *
          selbergH g k * gProd g d
        = ((ArithmeticFunction.moebius d : ℝ) * (gProd g d / (∏ p ∈ d.primeFactors, (1 - g p))) *
            selbergH g k) / J := by ring
      _ = ((ArithmeticFunction.moebius d : ℝ) * (selbergH g d * selbergH g k)) / J := by
          rw [hhg]; ring
  rw [Finset.sum_congr rfl hstep1]
  let A : Finset (Σ d : ℕ, ℕ) :=
    (D.filter (r ∣ ·)).sigma (fun d => (D_xi P (xi / d)).filter (Nat.Coprime · d))
  let B : Finset (Σ n : ℕ, ℕ) :=
    (D.filter (r ∣ ·)).sigma (fun n => (n / r).divisors)
  have hsigma1 : ∑ d ∈ D.filter (r ∣ ·), ∑ k ∈ (D_xi P (xi / d)).filter (Nat.Coprime · d),
        ((ArithmeticFunction.moebius d : ℝ) * selbergH g (d * k)) / J =
      ∑ p ∈ A, ((ArithmeticFunction.moebius p.1 : ℝ) * selbergH g (p.1 * p.2)) / J := by
    rw [Finset.sum_sigma]
  have hsigma2 : ∑ p ∈ A, ((ArithmeticFunction.moebius p.1 : ℝ) * selbergH g (p.1 * p.2)) / J =
      ∑ q ∈ B, ((ArithmeticFunction.moebius (r * q.2) : ℝ) * selbergH g q.1) / J := by
    refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1 / r⟩) ?_ ?_ ?_ ?_
    · rintro ⟨d, k⟩ hp
      simp only [A, Finset.mem_sigma, Finset.mem_filter] at hp
      rcases hp with ⟨⟨hdD, hrd⟩, hkD, hkd⟩
      have hd_pos := pos_of_mem_D_xi hP hdD
      have hk_mem : k ∈ D := D_xi_mono_xi P (Nat.div_le_self xi d) hkD
      have hk_le : k ≤ xi / d := ((mem_D_xi_iff P (xi / d) k).mp hkD).2
      have hdk_le : d * k ≤ xi := (Nat.mul_le_mul_left d hk_le).trans (Nat.mul_div_le xi d)
      have hdk_mem : d * k ∈ D := mul_mem_D_xi hP hdD hk_mem hkd.symm hdk_le
      have hrdk : r ∣ d * k := hrd.trans (dvd_mul_right d k)
      have hm_eq : r * (d / r) = d := Nat.mul_div_cancel' hrd
      have hn_eq : d * k = r * ((d / r) * k) := by rw [← mul_assoc, hm_eq]
      have hdiv_eq : (d * k) / r = (d / r) * k := by
        rw [hn_eq, Nat.mul_div_right _ hr_pos]
      have hdk_ne : d * k ≠ 0 := ne_zero_of_mem_D_xi hP hdk_mem
      have hnr_ne : (d * k) / r ≠ 0 := by
        rcases hrd with ⟨m, rfl⟩
        have hm0 : m ≠ 0 := by rintro rfl; exact hd_pos.ne' (mul_zero r)
        rw [hdiv_eq]
        have : (r * m) / r = m := Nat.mul_div_right m hr_pos
        rw [this]
        exact mul_ne_zero hm0 (ne_zero_of_mem_D_xi hP hkD)
      simp only [B, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hdk_mem, hrdk⟩, ⟨⟨k, hdiv_eq⟩, hnr_ne⟩⟩
    · rintro ⟨d₁, k₁⟩ hp₁ ⟨d₂, k₂⟩ hp₂ heq
      simp only [A, Finset.mem_sigma, Finset.mem_filter] at hp₁ hp₂
      have hrd₁ : r ∣ d₁ := hp₁.1.2
      have hrd₂ : r ∣ d₂ := hp₂.1.2
      have hd₁_pos := pos_of_mem_D_xi hP hp₁.1.1
      have hfst : d₁ * k₁ = d₂ * k₂ := congrArg Sigma.fst heq
      have hsnd : d₁ / r = d₂ / r := by
        have h := congrArg Sigma.snd heq
        simpa using h
      have hd_eq : d₁ = d₂ := by
        calc d₁ = r * (d₁ / r) := (Nat.mul_div_cancel' hrd₁).symm
          _ = r * (d₂ / r) := by rw [hsnd]
          _ = d₂ := Nat.mul_div_cancel' hrd₂
      subst hd_eq
      have hk_eq : k₁ = k₂ := Nat.mul_left_cancel hd₁_pos hfst
      simp [hk_eq]
    · rintro ⟨n, m⟩ hq
      simp only [B, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hq
      rcases hq with ⟨⟨hnD, hrn⟩, ⟨hm_dvd, _⟩⟩
      let d := r * m
      let k := (n / r) / m
      have hdk : d * k = n := by
        calc (r * m) * ((n / r) / m) = r * (m * ((n / r) / m)) := mul_assoc _ _ _
          _ = r * (n / r) := by rw [Nat.mul_div_cancel' hm_dvd]
          _ = n := Nat.mul_div_cancel' hrn
      have hdD : d ∈ D := mem_D_xi_of_dvd hP hnD ⟨k, hdk.symm⟩
      have hd_pos := pos_of_mem_D_xi hP hdD
      have hkD_full : k ∈ D := mem_D_xi_of_dvd hP hnD ⟨d, by rw [mul_comm, hdk]⟩
      have hn_le : n ≤ xi := ((mem_D_xi_iff P xi n).mp hnD).2
      have hk_le : k ≤ xi / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm, hdk]; exact hn_le)
      have hkD : k ∈ D_xi P (xi / d) := by
        rcases (mem_D_xi_iff P xi k).mp hkD_full with ⟨hS, _⟩
        exact (mem_D_xi_iff P (xi / d) k).mpr ⟨hS, hk_le⟩
      have hn_sq := squarefree_of_mem_D_xi hP hnD
      have hdk_sq : Squarefree (d * k) := by rw [hdk]; exact hn_sq
      have hkd : Nat.Coprime k d := (Nat.coprime_of_squarefree_mul hdk_sq).symm
      refine ⟨⟨d, k⟩, ?_, ?_⟩
      · simp only [A, Finset.mem_sigma, Finset.mem_filter]
        exact ⟨⟨hdD, dvd_mul_right r m⟩, ⟨hkD, hkd⟩⟩
      · have hd_div : d / r = m := Nat.mul_div_right m hr_pos
        simp [hdk, hd_div]
    · rintro ⟨d, k⟩ hp
      simp only [A, Finset.mem_sigma, Finset.mem_filter] at hp
      have hrd : r ∣ d := hp.1.2
      rw [Nat.mul_div_cancel' hrd]
  rw [hsigma1, hsigma2]
  have hsigma3 : ∑ q ∈ B, ((ArithmeticFunction.moebius (r * q.2) : ℝ) * selbergH g q.1) / J =
      ∑ n ∈ D.filter (r ∣ ·),
        ((ArithmeticFunction.moebius r : ℝ) * selbergH g n / J) *
          ∑ m ∈ (n / r).divisors, (ArithmeticFunction.moebius m : ℝ) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnD : n ∈ D := (Finset.mem_filter.mp hn).1
    have hrn : r ∣ n := (Finset.mem_filter.mp hn).2
    have hn_sq := squarefree_of_mem_D_xi hP hnD
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_dvd : m ∣ n / r := (Nat.mem_divisors.mp hm).1
    have hrm_dvd : r * m ∣ n := by
      rcases hm_dvd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      calc n = r * (n / r) := (Nat.mul_div_cancel' hrn).symm
        _ = r * (m * k) := by rw [hk]
        _ = r * m * k := (mul_assoc _ _ _).symm
    have hrm_sq : Squarefree (r * m) := hn_sq.squarefree_of_dvd hrm_dvd
    have hrm_cop : Nat.Coprime r m := Nat.coprime_of_squarefree_mul hrm_sq
    have hmu_mul : ArithmeticFunction.moebius (r * m) =
        ArithmeticFunction.moebius r * ArithmeticFunction.moebius m :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hrm_cop
    rw [hmu_mul]
    push_cast
    ring
  rw [hsigma3]
  have hcollapse : ∀ n ∈ D.filter (r ∣ ·),
      ((ArithmeticFunction.moebius r : ℝ) * selbergH g n / J) *
        ∑ m ∈ (n / r).divisors, (ArithmeticFunction.moebius m : ℝ) =
      if n = r then (ArithmeticFunction.moebius r : ℝ) * selbergH g r / J else 0 := by
    intro n hn
    have hrn : r ∣ n := (Finset.mem_filter.mp hn).2
    rw [sum_moebius_divisors]
    have hdiv1 : n / r = 1 ↔ n = r := by
      constructor
      · intro h
        calc n = r * (n / r) := (Nat.mul_div_cancel' hrn).symm
          _ = r * 1 := by rw [h]
          _ = r := mul_one r
      · rintro rfl
        exact Nat.div_self hr_pos
    by_cases hnr : n = r
    · simp [hnr, Nat.div_self hr_pos]
    · have hnr' : n / r ≠ 1 := fun h => hnr (hdiv1.mp h)
      simp [hnr, hnr']
  rw [Finset.sum_congr rfl hcollapse, Finset.sum_ite_eq']
  have hrmem : r ∈ D.filter (r ∣ ·) := Finset.mem_filter.mpr ⟨hr, dvd_refl r⟩
  simp [hrmem]

/-- Selberg's diagonalization identity: the quadratic form at optimal weights equals `1 / J(P, ξ)`. -/
theorem selberg_quad_form_eq_inv_J {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) {xi : ℕ} (hxi : 1 ≤ xi) :
    ∑ d₁ ∈ D_xi P xi, ∑ d₂ ∈ D_xi P xi,
        selbergLam g P xi d₁ * selbergLam g P xi d₂ * gProd g (Nat.lcm d₁ d₂) =
      1 / selbergJ g P xi := by
  set D := D_xi P xi
  set lam := selbergLam g P xi
  set J := selbergJ g P xi
  have hJ : 0 < J := lt_of_lt_of_le zero_lt_one (selbergJ_pos hP hg hxi)
  have hexp : ∀ d₁ ∈ D, ∀ d₂ ∈ D,
      lam d₁ * lam d₂ * gProd g (Nat.lcm d₁ d₂) =
        ∑ r ∈ D, if r ∣ d₁ ∧ r ∣ d₂ then
          (1 / selbergH g r) * (lam d₁ * gProd g d₁) * (lam d₂ * gProd g d₂)
        else 0 := by
    intro d₁ hd₁ d₂ hd₂
    have hd₁_pos := pos_of_mem_D_xi hP hd₁
    have hd₂_pos := pos_of_mem_D_xi hP hd₂
    have hd₁_sq := squarefree_of_mem_D_xi hP hd₁
    have hd₁_sub := primeFactors_subset_of_mem_D_xi hP hd₁
    set u := Nat.gcd d₁ d₂
    have hu_dvd₁ : u ∣ d₁ := Nat.gcd_dvd_left d₁ d₂
    have hu_sq : Squarefree u := hd₁_sq.squarefree_of_dvd hu_dvd₁
    have hu_sub : u.primeFactors ⊆ P :=
      (Nat.primeFactors_mono hu_dvd₁ hd₁_pos.ne').trans hd₁_sub
    have hu_pos : 0 < gProd g u := gProd_pos hg hu_sub
    have hlcm_eq : gProd g (Nat.lcm d₁ d₂) =
        gProd g d₁ * gProd g d₂ * (1 / gProd g u) := by
      have h := gProd_lcm_mul_gcd g hd₁_pos.ne' hd₂_pos.ne'
      field_simp [hu_pos.ne']
      linarith
    rw [hlcm_eq, inv_gProd_eq_sum_inv_selbergH hP hg hu_sq hu_sub]
    have hdiv_sub : u.divisors ⊆ D := by
      intro r hr
      exact mem_D_xi_of_dvd hP hd₁ ((Nat.mem_divisors.mp hr).1.trans hu_dvd₁)
    have hsum_u : ∑ r ∈ u.divisors, (1 / selbergH g r) =
        ∑ r ∈ D, if r ∣ d₁ ∧ r ∣ d₂ then 1 / selbergH g r else 0 := by
      rw [← Finset.sum_subset hdiv_sub]
      · refine Finset.sum_congr rfl fun r hr => ?_
        have hru : r ∣ u := (Nat.mem_divisors.mp hr).1
        have hrd : r ∣ d₁ ∧ r ∣ d₂ := Nat.dvd_gcd_iff.mp hru
        simp [hrd]
      · intro r _ hrn
        have hru : ¬ r ∣ u := fun h => hrn (Nat.mem_divisors.mpr ⟨h, hu_sq.ne_zero⟩)
        have hrd : ¬ (r ∣ d₁ ∧ r ∣ d₂) := fun h => hru (Nat.dvd_gcd h.1 h.2)
        simp [hrd]
    rw [hsum_u, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hrd : r ∣ d₁ ∧ r ∣ d₂
    · simp [hrd]; ring
    · simp [hrd]
  have hswap : ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * gProd g (Nat.lcm d₁ d₂) =
      ∑ r ∈ D, (1 / selbergH g r) *
        (∑ d₁ ∈ D.filter (r ∣ ·), lam d₁ * gProd g d₁) *
        (∑ d₂ ∈ D.filter (r ∣ ·), lam d₂ * gProd g d₂) := by
    calc ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * gProd g (Nat.lcm d₁ d₂)
        = ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ r ∈ D,
            if r ∣ d₁ ∧ r ∣ d₂ then
              (1 / selbergH g r) * (lam d₁ * gProd g d₁) * (lam d₂ * gProd g d₂)
            else 0 := by
          refine Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl fun d₂ hd₂ => ?_
          exact hexp d₁ hd₁ d₂ hd₂
      _ = ∑ d₁ ∈ D, ∑ r ∈ D, ∑ d₂ ∈ D,
            if r ∣ d₁ ∧ r ∣ d₂ then
              (1 / selbergH g r) * (lam d₁ * gProd g d₁) * (lam d₂ * gProd g d₂)
            else 0 := by
          refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm
      _ = ∑ r ∈ D, ∑ d₁ ∈ D, ∑ d₂ ∈ D,
            if r ∣ d₁ ∧ r ∣ d₂ then
              (1 / selbergH g r) * (lam d₁ * gProd g d₁) * (lam d₂ * gProd g d₂)
            else 0 := Finset.sum_comm
      _ = ∑ r ∈ D, (1 / selbergH g r) *
            (∑ d₁ ∈ D.filter (r ∣ ·), lam d₁ * gProd g d₁) *
            (∑ d₂ ∈ D.filter (r ∣ ·), lam d₂ * gProd g d₂) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [mul_assoc]
          simp only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          refine Finset.sum_congr rfl fun d₂ _ => ?_
          by_cases hr₁ : r ∣ d₁ <;> by_cases hr₂ : r ∣ d₂ <;>
            simp [hr₁, hr₂, mul_assoc, mul_comm, mul_left_comm]
  rw [hswap]
  have hdiag : ∀ r ∈ D,
      (1 / selbergH g r) *
        (∑ d₁ ∈ D.filter (r ∣ ·), lam d₁ * gProd g d₁) *
        (∑ d₂ ∈ D.filter (r ∣ ·), lam d₂ * gProd g d₂) =
      selbergH g r / J ^ 2 := by
    intro r hr
    rw [selberg_diag_y hP hg hr]
    have hr_sq := squarefree_of_mem_D_xi hP hr
    have hr_sub := primeFactors_subset_of_mem_D_xi hP hr
    have hH_pos := selbergH_pos hg hr_sub
    have hmu_sq : (ArithmeticFunction.moebius r : ℝ) ^ 2 = 1 := by
      have hm := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr_sq
      exact_mod_cast hm
    calc (1 / selbergH g r) *
          ((ArithmeticFunction.moebius r : ℝ) * selbergH g r / J) *
          ((ArithmeticFunction.moebius r : ℝ) * selbergH g r / J)
        = (ArithmeticFunction.moebius r : ℝ) ^ 2 * (selbergH g r / selbergH g r) *
            (selbergH g r / J ^ 2) := by ring
      _ = 1 * 1 * (selbergH g r / J ^ 2) := by rw [hmu_sq, div_self hH_pos.ne']
      _ = selbergH g r / J ^ 2 := by ring
  rw [Finset.sum_congr rfl hdiag, ← Finset.sum_div]
  change J / J ^ 2 = 1 / J
  field_simp [hJ.ne']

end BuchstabSwitching
