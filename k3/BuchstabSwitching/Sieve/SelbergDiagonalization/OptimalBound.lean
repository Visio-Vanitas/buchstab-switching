import BuchstabSwitching.Sieve.SelbergDiagonalization.Weights
import BuchstabSwitching.Sieve.SelbergDiagonalization.QuadraticForm
import BuchstabSwitching.Sieve.AbstractSieve
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Optimal Selberg Upper Bound and Prime-Omission Monotonicity

Proves the `3^ω(L)` lcm-pair counting identity `card_lcm_pairs_eq_three_pow`, the optimal
Selberg upper bound `selberg_optimal_upper_bound`, and prime-omission monotonicity
`eulerProd_mul_selbergJ_omission_mono`.
-/

namespace BuchstabSwitching

/-! ### LCM Pair Counting and Optimal Selberg Upper Bound -/

private lemma card_union_eq_powerset_pairs (S : Finset ℕ) :
    ((S.powerset ×ˢ S.powerset).filter (fun p => p.1 ∪ p.2 = S)).card = 3 ^ S.card := by
  induction S using Finset.induction_on with
  | empty => decide
  | @insert a s ha ih =>
    let P := (s.powerset ×ˢ s.powerset).filter (fun p => p.1 ∪ p.2 = s)
    let f₁ : Finset ℕ × Finset ℕ → Finset ℕ × Finset ℕ := fun p => (insert a p.1, insert a p.2)
    let f₂ : Finset ℕ × Finset ℕ → Finset ℕ × Finset ℕ := fun p => (insert a p.1, p.2)
    let f₃ : Finset ℕ × Finset ℕ → Finset ℕ × Finset ℕ := fun p => (p.1, insert a p.2)
    have hset : ((insert a s).powerset ×ˢ (insert a s).powerset).filter
          (fun p => p.1 ∪ p.2 = insert a s) =
        P.image f₁ ∪ P.image f₂ ∪ P.image f₃ := by
      ext ⟨A, B⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_union, Finset.mem_image, P, f₁, f₂, f₃]
      constructor
      · rintro ⟨⟨hA, hB⟩, hAB⟩
        have ha_mem : a ∈ A ∪ B := by rw [hAB]; exact Finset.mem_insert_self a s
        have ha_or : a ∈ A ∨ a ∈ B := Finset.mem_union.mp ha_mem
        have hA_erase : A.erase a ⊆ s := fun x hx =>
          Finset.mem_of_mem_insert_of_ne (hA (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
        have hB_erase : B.erase a ⊆ s := fun x hx =>
          Finset.mem_of_mem_insert_of_ne (hB (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
        have herase_union : A.erase a ∪ B.erase a = s := by
          ext x
          simp only [Finset.mem_union, Finset.mem_erase]
          constructor
          · rintro (⟨hx, hxA⟩ | ⟨hx, hxB⟩)
            · exact Finset.mem_of_mem_insert_of_ne (hA hxA) hx
            · exact Finset.mem_of_mem_insert_of_ne (hB hxB) hx
          · intro hxs
            have hxne : x ≠ a := fun h => ha (h ▸ hxs)
            have hxAB : x ∈ A ∪ B := hAB ▸ Finset.mem_insert_of_mem hxs
            rcases Finset.mem_union.mp hxAB with hxA | hxB
            · exact Or.inl ⟨hxne, hxA⟩
            · exact Or.inr ⟨hxne, hxB⟩
        by_cases haA : a ∈ A <;> by_cases haB : a ∈ B
        · exact Or.inl (Or.inl ⟨(A.erase a, B.erase a),
            ⟨⟨hA_erase, hB_erase⟩, herase_union⟩,
            Prod.ext (Finset.insert_erase haA) (Finset.insert_erase haB)⟩)
        · have hB' : B ⊆ s := fun x hx =>
            Finset.mem_of_mem_insert_of_ne (hB hx) (fun h => haB (h ▸ hx))
          have hB_eq : B.erase a = B := Finset.erase_eq_of_notMem haB
          exact Or.inl (Or.inr ⟨(A.erase a, B),
            ⟨⟨hA_erase, hB'⟩, by rwa [hB_eq] at herase_union⟩,
            Prod.ext (Finset.insert_erase haA) rfl⟩)
        · have hA' : A ⊆ s := fun x hx =>
            Finset.mem_of_mem_insert_of_ne (hA hx) (fun h => haA (h ▸ hx))
          have hA_eq : A.erase a = A := Finset.erase_eq_of_notMem haA
          exact Or.inr ⟨(A, B.erase a),
            ⟨⟨hA', hB_erase⟩, by rwa [hA_eq] at herase_union⟩,
            Prod.ext rfl (Finset.insert_erase haB)⟩
        · exact absurd ha_or (by simp [haA, haB])
      · rintro ((⟨⟨A', B'⟩, ⟨⟨hA', hB'⟩, hAB'⟩, heq⟩ | ⟨⟨A', B'⟩, ⟨⟨hA', hB'⟩, hAB'⟩, heq⟩) |
          ⟨⟨A', B'⟩, ⟨⟨hA', hB'⟩, hAB'⟩, heq⟩)
        · rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
          exact ⟨⟨Finset.insert_subset_insert a hA', Finset.insert_subset_insert a hB'⟩,
            by rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hAB']⟩
        · rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
          exact ⟨⟨Finset.insert_subset_insert a hA',
              hB'.trans (Finset.subset_insert a s)⟩,
            by rw [Finset.insert_union, hAB']⟩
        · rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
          exact ⟨⟨hA'.trans (Finset.subset_insert a s),
              Finset.insert_subset_insert a hB'⟩,
            by rw [Finset.union_insert, hAB']⟩
    have hf₁_inj : Set.InjOn f₁ P := by
      rintro ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ heq
      rcases Finset.mem_filter.mp h₁ with ⟨h₁p, _⟩
      rcases Finset.mem_filter.mp h₂ with ⟨h₂p, _⟩
      rcases Finset.mem_product.mp h₁p with ⟨hA₁p, hB₁p⟩
      rcases Finset.mem_product.mp h₂p with ⟨hA₂p, hB₂p⟩
      have haA₁ : a ∉ A₁ := fun h => ha (Finset.mem_powerset.mp hA₁p h)
      have haB₁ : a ∉ B₁ := fun h => ha (Finset.mem_powerset.mp hB₁p h)
      have haA₂ : a ∉ A₂ := fun h => ha (Finset.mem_powerset.mp hA₂p h)
      have haB₂ : a ∉ B₂ := fun h => ha (Finset.mem_powerset.mp hB₂p h)
      rcases Prod.ext_iff.mp heq with ⟨hA, hB⟩
      dsimp only [f₁] at hA hB
      have hA' : A₁ = A₂ := by
        have := congrArg (fun t => Finset.erase t a) hA
        simpa [Finset.erase_insert haA₁, Finset.erase_insert haA₂] using this
      have hB' : B₁ = B₂ := by
        have := congrArg (fun t => Finset.erase t a) hB
        simpa [Finset.erase_insert haB₁, Finset.erase_insert haB₂] using this
      exact Prod.ext hA' hB'
    have hf₂_inj : Set.InjOn f₂ P := by
      rintro ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ heq
      rcases Finset.mem_filter.mp h₁ with ⟨h₁p, _⟩
      rcases Finset.mem_filter.mp h₂ with ⟨h₂p, _⟩
      rcases Finset.mem_product.mp h₁p with ⟨hA₁p, _⟩
      rcases Finset.mem_product.mp h₂p with ⟨hA₂p, _⟩
      have haA₁ : a ∉ A₁ := fun h => ha (Finset.mem_powerset.mp hA₁p h)
      have haA₂ : a ∉ A₂ := fun h => ha (Finset.mem_powerset.mp hA₂p h)
      rcases Prod.ext_iff.mp heq with ⟨hA, hB⟩
      dsimp only [f₂] at hA hB
      have hA' : A₁ = A₂ := by
        have := congrArg (fun t => Finset.erase t a) hA
        simpa [Finset.erase_insert haA₁, Finset.erase_insert haA₂] using this
      exact Prod.ext hA' hB
    have hf₃_inj : Set.InjOn f₃ P := by
      rintro ⟨A₁, B₁⟩ h₁ ⟨A₂, B₂⟩ h₂ heq
      rcases Finset.mem_filter.mp h₁ with ⟨h₁p, _⟩
      rcases Finset.mem_filter.mp h₂ with ⟨h₂p, _⟩
      rcases Finset.mem_product.mp h₁p with ⟨_, hB₁p⟩
      rcases Finset.mem_product.mp h₂p with ⟨_, hB₂p⟩
      have haB₁ : a ∉ B₁ := fun h => ha (Finset.mem_powerset.mp hB₁p h)
      have haB₂ : a ∉ B₂ := fun h => ha (Finset.mem_powerset.mp hB₂p h)
      rcases Prod.ext_iff.mp heq with ⟨hA, hB⟩
      dsimp only [f₃] at hA hB
      have hB' : B₁ = B₂ := by
        have := congrArg (fun t => Finset.erase t a) hB
        simpa [Finset.erase_insert haB₁, Finset.erase_insert haB₂] using this
      exact Prod.ext hA hB'
    have hdisj₁₂ : Disjoint (P.image f₁) (P.image f₂) := by
      rw [Finset.disjoint_left]
      intro ⟨A, B⟩ h1 h2
      rcases Finset.mem_image.mp h1 with ⟨⟨A₁, B₁⟩, _, h1eq⟩
      rcases Finset.mem_image.mp h2 with ⟨⟨A₂, B₂⟩, h2p, h2eq⟩
      rcases Finset.mem_filter.mp h2p with ⟨h2prod, _⟩
      rcases Finset.mem_product.mp h2prod with ⟨_, hB₂p⟩
      have haB₁ : a ∈ B := by
        have h : insert a B₁ = B := (Prod.ext_iff.mp h1eq).2
        rw [← h]; exact Finset.mem_insert_self a B₁
      have haB₂ : a ∉ B := by
        have h : B₂ = B := (Prod.ext_iff.mp h2eq).2
        rw [← h]; exact fun hm => ha (Finset.mem_powerset.mp hB₂p hm)
      exact haB₂ haB₁
    have hdisj₁₃ : Disjoint (P.image f₁) (P.image f₃) := by
      rw [Finset.disjoint_left]
      intro ⟨A, B⟩ h1 h3
      rcases Finset.mem_image.mp h1 with ⟨⟨A₁, B₁⟩, _, h1eq⟩
      rcases Finset.mem_image.mp h3 with ⟨⟨A₂, B₂⟩, h3p, h3eq⟩
      rcases Finset.mem_filter.mp h3p with ⟨h3prod, _⟩
      rcases Finset.mem_product.mp h3prod with ⟨hA₂p, _⟩
      have haA₁ : a ∈ A := by
        have h : insert a A₁ = A := (Prod.ext_iff.mp h1eq).1
        rw [← h]; exact Finset.mem_insert_self a A₁
      have haA₃ : a ∉ A := by
        have h : A₂ = A := (Prod.ext_iff.mp h3eq).1
        rw [← h]; exact fun hm => ha (Finset.mem_powerset.mp hA₂p hm)
      exact haA₃ haA₁
    have hdisj₂₃ : Disjoint (P.image f₂) (P.image f₃) := by
      rw [Finset.disjoint_left]
      intro ⟨A, B⟩ h2 h3
      rcases Finset.mem_image.mp h2 with ⟨⟨A₁, B₁⟩, _, h2eq⟩
      rcases Finset.mem_image.mp h3 with ⟨⟨A₂, B₂⟩, h3p, h3eq⟩
      rcases Finset.mem_filter.mp h3p with ⟨h3prod, _⟩
      rcases Finset.mem_product.mp h3prod with ⟨hA₂p, _⟩
      have haA₂ : a ∈ A := by
        have h : insert a A₁ = A := (Prod.ext_iff.mp h2eq).1
        rw [← h]; exact Finset.mem_insert_self a A₁
      have haA₃ : a ∉ A := by
        have h : A₂ = A := (Prod.ext_iff.mp h3eq).1
        rw [← h]; exact fun hm => ha (Finset.mem_powerset.mp hA₂p hm)
      exact haA₃ haA₂
    rw [hset, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj₁₃, hdisj₂₃⟩),
      Finset.card_union_of_disjoint hdisj₁₂,
      Finset.card_image_of_injOn hf₁_inj,
      Finset.card_image_of_injOn hf₂_inj,
      Finset.card_image_of_injOn hf₃_inj,
      ih, Finset.card_insert_of_notMem ha, pow_succ]
    ring

/-- Number of divisor pairs `(d₁, d₂)` with `lcm d₁ d₂ = L` for squarefree `L` is `3 ^ ω(L)`. -/
theorem card_lcm_pairs_eq_three_pow {L : ℕ} (hL : Squarefree L) :
    ((L.divisors ×ˢ L.divisors).filter (fun p => Nat.lcm p.1 p.2 = L)).card =
      3 ^ L.primeFactors.card := by
  rw [← card_union_eq_powerset_pairs L.primeFactors]
  refine Finset.card_bij (fun p _ => (p.1.primeFactors, p.2.primeFactors)) ?_ ?_ ?_
  · rintro ⟨d₁, d₂⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors, Finset.mem_powerset] at hp ⊢
    rcases hp with ⟨⟨⟨hd₁, _⟩, ⟨hd₂, _⟩⟩, hlcm⟩
    have hd₁_ne : d₁ ≠ 0 := ne_zero_of_dvd_ne_zero hL.ne_zero hd₁
    have hd₂_ne : d₂ ≠ 0 := ne_zero_of_dvd_ne_zero hL.ne_zero hd₂
    refine ⟨⟨Nat.primeFactors_mono hd₁ hL.ne_zero, Nat.primeFactors_mono hd₂ hL.ne_zero⟩, ?_⟩
    rw [← primeFactors_lcm hd₁_ne hd₂_ne, hlcm]
  · rintro ⟨d₁, d₂⟩ hp₁ ⟨d₃, d₄⟩ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hp₁ hp₂
    have hd₁_sq : Squarefree d₁ := hL.squarefree_of_dvd hp₁.1.1.1
    have hd₂_sq : Squarefree d₂ := hL.squarefree_of_dvd hp₁.1.2.1
    have hd₃_sq : Squarefree d₃ := hL.squarefree_of_dvd hp₂.1.1.1
    have hd₄_sq : Squarefree d₄ := hL.squarefree_of_dvd hp₂.1.2.1
    rcases Prod.ext_iff.mp heq with ⟨h13, h24⟩
    dsimp only at h13 h24
    have hd₁₃ : d₁ = d₃ := by
      rw [← Nat.prod_primeFactors_of_squarefree hd₁_sq,
        ← Nat.prod_primeFactors_of_squarefree hd₃_sq, h13]
    have hd₂₄ : d₂ = d₄ := by
      rw [← Nat.prod_primeFactors_of_squarefree hd₂_sq,
        ← Nat.prod_primeFactors_of_squarefree hd₄_sq, h24]
    exact Prod.ext hd₁₃ hd₂₄
  · rintro ⟨A, B⟩ hAB
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hAB
    rcases hAB with ⟨⟨hA, hB⟩, hU⟩
    let d₁ := ∏ p ∈ A, p
    let d₂ := ∏ p ∈ B, p
    have hA_pr : ∀ p ∈ A, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hA hp)
    have hB_pr : ∀ p ∈ B, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hB hp)
    have hd₁_ne : d₁ ≠ 0 := (Finset.prod_pos fun p hp => (hA_pr p hp).pos).ne'
    have hd₂_ne : d₂ ≠ 0 := (Finset.prod_pos fun p hp => (hB_pr p hp).pos).ne'
    have hd₁_dvd : d₁ ∣ L := by
      rw [← Nat.prod_primeFactors_of_squarefree hL]
      exact Finset.prod_dvd_prod_of_subset A L.primeFactors _ hA
    have hd₂_dvd : d₂ ∣ L := by
      rw [← Nat.prod_primeFactors_of_squarefree hL]
      exact Finset.prod_dvd_prod_of_subset B L.primeFactors _ hB
    have hlcm_sq : Squarefree (Nat.lcm d₁ d₂) := by
      have hsub : Nat.lcm d₁ d₂ ∣ L := Nat.lcm_dvd hd₁_dvd hd₂_dvd
      exact hL.squarefree_of_dvd hsub
    have hlcm_eq : Nat.lcm d₁ d₂ = L := by
      rw [← Nat.prod_primeFactors_of_squarefree hlcm_sq,
        ← Nat.prod_primeFactors_of_squarefree hL,
        primeFactors_lcm hd₁_ne hd₂_ne,
        Nat.primeFactors_prod hA_pr, Nat.primeFactors_prod hB_pr, hU]
    refine ⟨(d₁, d₂), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
      exact ⟨⟨⟨hd₁_dvd, hL.ne_zero⟩, ⟨hd₂_dvd, hL.ne_zero⟩⟩, hlcm_eq⟩
    · exact Prod.ext (Nat.primeFactors_prod hA_pr) (Nat.primeFactors_prod hB_pr)

/-- Optimal Selberg `Λ²` upper bound with `3^ω(L)` remainder weight over `D_xi P (ξ²)`. -/
theorem selberg_optimal_upper_bound (I P : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℝ) (xi : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1)
    (ha : ∀ n ∈ I, 0 ≤ a n) (hxi : 1 ≤ xi) :
    sieveCount I a P ≤
      sieveMass I a / selbergJ g P xi +
        ∑ L ∈ D_xi P (xi ^ 2), (3 : ℝ) ^ L.primeFactors.card * |sieveRem I a (gProd g) L| := by
  set D := D_xi P xi
  set lam := selbergLam g P xi
  have h1D : 1 ∈ D := one_mem_D_xi P hxi
  have hlam1 : lam 1 = 1 := selbergLam_one hP hg hxi
  have hsub_unsieved :
      I.filter (fun n => ∀ p ∈ P, ¬ p ∣ n) ⊆ I.filter (fun n => ∀ d ∈ D, d ∣ n → d = 1) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hncop⟩
    refine Finset.mem_filter.mpr ⟨hnI, fun d hdD hdn => ?_⟩
    rcases (mem_D_xi_iff P xi d).mp hdD with ⟨⟨S, hSP, rfl⟩, _⟩
    by_cases hS : S = ∅
    · subst hS; simp
    · obtain ⟨p, hpS⟩ := Finset.ne_empty_iff_nonempty.mp hS
      have hpd : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem _ hpS
      exact absurd (hpd.trans hdn) (hncop p (hSP hpS))
  have hcount_le : sieveCount I a P ≤
      ∑ n ∈ I.filter (fun n => ∀ d ∈ D, d ∣ n → d = 1), a n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub_unsieved
      (fun n hn _ => ha n (Finset.mem_filter.mp hn).1)
  have hsieve := selberg_lambda_sq_upper_sieve_real I D lam a h1D hlam1 ha
  have hsplit : ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
        ∑ n ∈ I.filter (fun n => Nat.lcm d₁ d₂ ∣ n), a n =
      (∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * gProd g (Nat.lcm d₁ d₂)) * sieveMass I a +
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂) := by
    have hterm : ∀ d₁ d₂ : ℕ,
        lam d₁ * lam d₂ * ∑ n ∈ I.filter (fun n => Nat.lcm d₁ d₂ ∣ n), a n =
          lam d₁ * lam d₂ * gProd g (Nat.lcm d₁ d₂) * sieveMass I a +
            lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂) := by
      intro d₁ d₂
      unfold sieveRem sieveDivMass
      ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hmain : (∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * gProd g (Nat.lcm d₁ d₂)) * sieveMass I a =
      sieveMass I a / selbergJ g P xi := by
    rw [selberg_quad_form_eq_inv_J hP hg hxi]
    ring
  have hrem_abs :
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂) ≤
        ∑ L ∈ D_xi P (xi ^ 2), (3 : ℝ) ^ L.primeFactors.card * |sieveRem I a (gProd g) L| := by
    calc ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂)
        ≤ |∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂)| :=
          le_abs_self _
      _ ≤ ∑ d₁ ∈ D, |∑ d₂ ∈ D, lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D, |lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂)| :=
          Finset.sum_le_sum fun d₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D, |sieveRem I a (gProd g) (Nat.lcm d₁ d₂)| := by
          refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun d₂ _ => ?_
          rw [abs_mul, abs_mul]
          have h1 : |lam d₁| ≤ 1 := abs_selbergLam_le_one hP hg xi d₁
          have h2 : |lam d₂| ≤ 1 := abs_selbergLam_le_one hP hg xi d₂
          calc |lam d₁| * |lam d₂| * |sieveRem I a (gProd g) (Nat.lcm d₁ d₂)|
              ≤ 1 * 1 * |sieveRem I a (gProd g) (Nat.lcm d₁ d₂)| := by gcongr
            _ = |sieveRem I a (gProd g) (Nat.lcm d₁ d₂)| := by ring
      _ = ∑ p ∈ D ×ˢ D, |sieveRem I a (gProd g) (Nat.lcm p.1 p.2)| := by
          rw [← Finset.sum_product']
      _ = ∑ L ∈ D_xi P (xi ^ 2),
            ∑ p ∈ (D ×ˢ D).filter (fun p => Nat.lcm p.1 p.2 = L),
              |sieveRem I a (gProd g) (Nat.lcm p.1 p.2)| := by
          symm
          refine Finset.sum_fiberwise_of_maps_to ?_ _
          rintro ⟨d₁, d₂⟩ hp
          rcases Finset.mem_product.mp hp with ⟨hd₁, hd₂⟩
          exact lcm_mem_D_xi_sq hP hd₁ hd₂
      _ ≤ ∑ L ∈ D_xi P (xi ^ 2), (3 : ℝ) ^ L.primeFactors.card * |sieveRem I a (gProd g) L| := by
          refine Finset.sum_le_sum fun L hL => ?_
          have hconst : ∑ p ∈ (D ×ˢ D).filter (fun p => Nat.lcm p.1 p.2 = L),
                |sieveRem I a (gProd g) (Nat.lcm p.1 p.2)| =
              (((D ×ˢ D).filter (fun p => Nat.lcm p.1 p.2 = L)).card : ℝ) *
                |sieveRem I a (gProd g) L| := by
            trans ∑ _p ∈ (D ×ˢ D).filter (fun p => Nat.lcm p.1 p.2 = L), |sieveRem I a (gProd g) L|
            · refine Finset.sum_congr rfl fun p hp => ?_
              rw [(Finset.mem_filter.mp hp).2]
            · rw [Finset.sum_const, nsmul_eq_mul]
          rw [hconst]
          have hL_sq : Squarefree L := squarefree_of_mem_D_xi hP hL
          have hL_ne : L ≠ 0 := hL_sq.ne_zero
          have hsub_fib : (D ×ˢ D).filter (fun p => Nat.lcm p.1 p.2 = L) ⊆
              (L.divisors ×ˢ L.divisors).filter (fun p => Nat.lcm p.1 p.2 = L) := by
            rintro ⟨d₁, d₂⟩ hp
            simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hp ⊢
            exact ⟨⟨⟨hp.2 ▸ Nat.dvd_lcm_left d₁ d₂, hL_ne⟩,
              ⟨hp.2 ▸ Nat.dvd_lcm_right d₁ d₂, hL_ne⟩⟩, hp.2⟩
          have hcard : ((D ×ˢ D).filter (fun p => Nat.lcm p.1 p.2 = L)).card ≤
              3 ^ L.primeFactors.card :=
            (Finset.card_le_card hsub_fib).trans_eq (card_lcm_pairs_eq_three_pow hL_sq)
          have hcardR : (((D ×ˢ D).filter (fun p => Nat.lcm p.1 p.2 = L)).card : ℝ) ≤
              (3 : ℝ) ^ L.primeFactors.card := by
            exact_mod_cast hcard
          gcongr
  calc sieveCount I a P
      ≤ ∑ n ∈ I.filter (fun n => ∀ d ∈ D, d ∣ n → d = 1), a n := hcount_le
    _ ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
          ∑ n ∈ I.filter (fun n => Nat.lcm d₁ d₂ ∣ n), a n := hsieve
    _ = sieveMass I a / selbergJ g P xi +
          ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * sieveRem I a (gProd g) (Nat.lcm d₁ d₂) := by
        rw [hsplit, hmain]
    _ ≤ sieveMass I a / selbergJ g P xi +
          ∑ L ∈ D_xi P (xi ^ 2), (3 : ℝ) ^ L.primeFactors.card * |sieveRem I a (gProd g) L| := by
        gcongr

/-! ### Prime-Omission Monotonicity for `V(P) * J(P, ξ)` -/

/-- Omitting primes from `P` does not decrease `eulerProd g P * selbergJ g P xi`. -/
theorem eulerProd_mul_selbergJ_omission_mono (P' P : Finset ℕ) (g : ℕ → ℝ) (xi : ℕ)
    (hsub : P' ⊆ P) (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 < g p ∧ g p < 1) :
    eulerProd g P * selbergJ g P xi ≤ eulerProd g P' * selbergJ g P' xi := by
  set Q := P \ P'
  have hdisj : Disjoint Q P' := disjoint_sdiff_self_left
  have hunion : Q ∪ P' = P := Finset.sdiff_union_of_subset hsub
  have hQ_sub : Q ⊆ P := Finset.sdiff_subset
  have hP'_pr : ∀ p ∈ P', p.Prime := fun p hp => hP p (hsub hp)
  have hQ_pr : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQ_sub hp)
  have hV_split : eulerProd g P = eulerProd g Q * eulerProd g P' := by
    unfold eulerProd
    rw [← hunion, Finset.prod_union hdisj]
  have hVQ_pos : 0 < eulerProd g Q :=
    Finset.prod_pos fun p hp => sub_pos.mpr (hg p (hQ_sub hp)).2
  have hVP'_pos : 0 < eulerProd g P' :=
    Finset.prod_pos fun p hp => sub_pos.mpr (hg p (hsub hp)).2
  have hJ_le : selbergJ g P xi ≤
      (∏ p ∈ Q, (1 / (1 - g p))) * selbergJ g P' xi := by
    have hprod_Q : ∏ p ∈ Q, (1 / (1 - g p)) = ∑ S ∈ Q.powerset, selbergH g (∏ p ∈ S, p) := by
      have h1 : ∀ p ∈ Q, 1 / (1 - g p) = 1 + g p / (1 - g p) := by
        intro p hp
        have hne : 1 - g p ≠ 0 := (sub_pos.mpr (hg p (hQ_sub hp)).2).ne'
        field_simp [hne]
        ring
      rw [Finset.prod_congr rfl h1, Finset.prod_one_add]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hS_pr : ∀ p ∈ S, p.Prime := fun p hp => hQ_pr p (Finset.mem_powerset.mp hS hp)
      simp [selbergH, Nat.primeFactors_prod hS_pr]
    rw [hprod_Q, Finset.sum_mul]
    have hprod_sum :
        ∑ S ∈ Q.powerset, selbergH g (∏ p ∈ S, p) * selbergJ g P' xi =
          ∑ p ∈ Q.powerset ×ˢ D_xi P' xi, selbergH g ((∏ q ∈ p.1, q) * p.2) := by
      unfold selbergJ
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_product']
      refine Finset.sum_congr rfl fun ⟨S, d'⟩ hp => ?_
      rcases Finset.mem_product.mp hp with ⟨hS, hd'⟩
      have hS_sub : S ⊆ Q := Finset.mem_powerset.mp hS
      have hS_pr : ∀ q ∈ S, q.Prime := fun q hq => hQ_pr q (hS_sub hq)
      have hS_ne : (∏ q ∈ S, q) ≠ 0 := (Finset.prod_pos fun q hq => (hS_pr q hq).pos).ne'
      have hd'_ne : d' ≠ 0 := ne_zero_of_mem_D_xi hP'_pr hd'
      have hd'_sub : d'.primeFactors ⊆ P' := primeFactors_subset_of_mem_D_xi hP'_pr hd'
      have hcop : Nat.Coprime (∏ q ∈ S, q) d' := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        have hpos : 0 < Nat.gcd (∏ q ∈ S, q) d' := Nat.gcd_pos_of_pos_left d' (Nat.pos_of_ne_zero hS_ne)
        have hlt1 : 1 < Nat.gcd (∏ q ∈ S, q) d' := by omega
        obtain ⟨p, hp_pr, hpg⟩ := Nat.exists_prime_and_dvd hlt1.ne'
        have hpS : p ∈ (∏ q ∈ S, q).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp_pr, hpg.trans (Nat.gcd_dvd_left _ _), hS_ne⟩
        have hpd' : p ∈ d'.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp_pr, hpg.trans (Nat.gcd_dvd_right _ _), hd'_ne⟩
        rw [Nat.primeFactors_prod hS_pr] at hpS
        exact Finset.disjoint_left.mp hdisj (hS_sub hpS) (hd'_sub hpd')
      exact (selbergH_mul_of_coprime g hcop hS_ne hd'_ne).symm
    rw [hprod_sum]
    set f : Finset ℕ × ℕ → ℕ := fun p => (∏ q ∈ p.1, q) * p.2
    have hD_sub : D_xi P xi ⊆ (Q.powerset ×ˢ D_xi P' xi).image f := by
      intro d hd
      rcases (mem_D_xi_iff P xi d).mp hd with ⟨⟨S, hSP, rfl⟩, hle⟩
      let S₁ := S ∩ Q
      let S₂ := S ∩ P'
      have hS_split : S = S₁ ∪ S₂ := by
        ext p
        simp only [S₁, S₂, Finset.mem_union, Finset.mem_inter]
        constructor
        · intro hp
          have hpP := hSP hp
          rw [← hunion, Finset.mem_union] at hpP
          rcases hpP with hpQ | hpP'
          · exact Or.inl ⟨hp, hpQ⟩
          · exact Or.inr ⟨hp, hpP'⟩
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      have hS₁₂_disj : Disjoint S₁ S₂ := by
        refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
        exact Finset.disjoint_left.mp hdisj (Finset.mem_inter.mp hp1).2 (Finset.mem_inter.mp hp2).2
      have hprod_eq : (∏ p ∈ S, p) = (∏ p ∈ S₁, p) * (∏ p ∈ S₂, p) := by
        conv_lhs => rw [hS_split]
        exact Finset.prod_union hS₁₂_disj
      have hS₁_sub : S₁ ⊆ Q := Finset.inter_subset_right
      have hS₂_sub : S₂ ⊆ P' := Finset.inter_subset_right
      have hS₁_pos : 1 ≤ ∏ p ∈ S₁, p :=
        Finset.prod_pos fun p hp => (hQ_pr p (hS₁_sub hp)).pos
      have hS₂_le : ∏ p ∈ S₂, p ≤ xi := by
        calc ∏ p ∈ S₂, p = 1 * ∏ p ∈ S₂, p := (one_mul _).symm
          _ ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := Nat.mul_le_mul_right _ hS₁_pos
          _ = ∏ p ∈ S, p := hprod_eq.symm
          _ ≤ xi := hle
      have hd'_mem : (∏ p ∈ S₂, p) ∈ D_xi P' xi :=
        (mem_D_xi_iff P' xi _).mpr ⟨⟨S₂, hS₂_sub, rfl⟩, hS₂_le⟩
      exact Finset.mem_image.mpr ⟨(S₁, ∏ p ∈ S₂, p),
        Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hS₁_sub, hd'_mem⟩, hprod_eq.symm⟩
    have himg_nn : ∀ d ∈ (Q.powerset ×ˢ D_xi P' xi).image f, 0 ≤ selbergH g d := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨⟨S, d'⟩, hp, rfl⟩
      rcases Finset.mem_product.mp hp with ⟨hS, hd'⟩
      have hS_sub := (Finset.mem_powerset.mp hS).trans hQ_sub
      have hS_pr : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS_sub hp)
      have hS_ne : (∏ p ∈ S, p) ≠ 0 := (Finset.prod_pos fun p hp => (hS_pr p hp).pos).ne'
      have hd'_ne : d' ≠ 0 := ne_zero_of_mem_D_xi hP'_pr hd'
      have hd'_sub := (primeFactors_subset_of_mem_D_xi hP'_pr hd').trans hsub
      have hpf : ((∏ p ∈ S, p) * d').primeFactors ⊆ P := by
        rw [Nat.primeFactors_mul hS_ne hd'_ne, Nat.primeFactors_prod hS_pr]
        exact Finset.union_subset hS_sub hd'_sub
      exact selbergH_nonneg hg hpf
    calc selbergJ g P xi
        = ∑ d ∈ D_xi P xi, selbergH g d := rfl
      _ ≤ ∑ d ∈ (Q.powerset ×ˢ D_xi P' xi).image f, selbergH g d :=
          Finset.sum_le_sum_of_subset_of_nonneg hD_sub (fun d hd _ => himg_nn d hd)
      _ ≤ ∑ p ∈ Q.powerset ×ˢ D_xi P' xi, selbergH g (f p) :=
          Finset.sum_image_le_of_nonneg himg_nn
  calc eulerProd g P * selbergJ g P xi
      = eulerProd g Q * eulerProd g P' * selbergJ g P xi := by rw [hV_split]
    _ ≤ eulerProd g Q * eulerProd g P' * ((∏ p ∈ Q, (1 / (1 - g p))) * selbergJ g P' xi) := by
        gcongr
    _ = (eulerProd g Q * ∏ p ∈ Q, (1 / (1 - g p))) * (eulerProd g P' * selbergJ g P' xi) := by
        ring
    _ = 1 * (eulerProd g P' * selbergJ g P' xi) := by
        congr 1
        unfold eulerProd
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun p hp => ?_
        have hne : 1 - g p ≠ 0 := (sub_pos.mpr (hg p (hQ_sub hp)).2).ne'
        field_simp [hne]
    _ = eulerProd g P' * selbergJ g P' xi := one_mul _

end BuchstabSwitching
