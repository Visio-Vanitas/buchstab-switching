import BuchstabSwitchingK2.Core.ShiftedPrimesK2.Sets

/-!
# Injectivity of the Shifted Triple Map on `bTriples`

Proves that `(p₁, p₂, p₃) ↦ N - p₁ * p₂ * p₃` is injective on `bTriples N z y`,
using unique prime factorization (`Nat.primeFactorsList_unique`) and the ordering
`p₁ < y ≤ p₂ ≤ p₃`. Consequently `(bSet N z y).card = (bTriples N z y).card`.
-/

namespace BuchstabSwitchingK2

/-- The shifted product map `t ↦ N - t.1 * t.2.1 * t.2.2` is injective on `bTriples N z y`. -/
theorem bTriples_injOn (N z y : ℕ) :
    Set.InjOn (fun t : ℕ × ℕ × ℕ => N - t.1 * t.2.1 * t.2.2) (bTriples N z y) := by
  rintro ⟨p₁, p₂, p₃⟩ hp ⟨q₁, q₂, q₃⟩ hq heq
  rw [Finset.mem_coe] at hp hq
  simp only [bTriples, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Ico] at hp hq
  dsimp only at hp hq heq
  rcases hp with ⟨⟨⟨_hp₁_ge, hp₁_lt⟩, ⟨_hp₂_ge, _hp₂_lt⟩, ⟨_hp₃_ge, _hp₃_lt⟩⟩,
    hp₂₃, hp₁_prime, hp₂_prime, hp₃_prime, -, -, -, hp_prod_lt⟩
  rcases hq with ⟨⟨⟨_hq₁_ge, hq₁_lt⟩, ⟨hq₂_ge, _hq₂_lt⟩, ⟨hq₃_ge, _hq₃_lt⟩⟩,
    hq₂₃, hq₁_prime, hq₂_prime, hq₃_prime, -, -, -, hq_prod_lt⟩
  have hprod : p₁ * p₂ * p₃ = q₁ * q₂ * q₃ := by omega
  have hp_perm : List.Perm [p₁, p₂, p₃] (p₁ * p₂ * p₃).primeFactorsList :=
    Nat.primeFactorsList_unique (by simp [mul_assoc]) (by simp [hp₁_prime, hp₂_prime, hp₃_prime])
  have hq_perm : List.Perm [q₁, q₂, q₃] (q₁ * q₂ * q₃).primeFactorsList :=
    Nat.primeFactorsList_unique (by simp [mul_assoc]) (by simp [hq₁_prime, hq₂_prime, hq₃_prime])
  have hperm : List.Perm [p₁, p₂, p₃] [q₁, q₂, q₃] := by
    rw [hprod] at hp_perm
    exact hp_perm.trans hq_perm.symm
  have hp₁_mem : p₁ ∈ [q₁, q₂, q₃] := hperm.mem_iff.mp (by simp)
  have hp₁_eq : p₁ = q₁ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp₁_mem
    rcases hp₁_mem with rfl | rfl | rfl
    · rfl
    · omega
    · omega
  subst hp₁_eq
  have hperm2 : List.Perm [p₂, p₃] [q₂, q₃] := hperm.cons_inv
  have hp₂_mem : p₂ ∈ [q₂, q₃] := hperm2.mem_iff.mp (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp₂_mem
  have hp₂_eq : p₂ = q₂ ∧ p₃ = q₃ := by
    rcases hp₂_mem with h2 | h2
    · rw [h2] at hperm2
      have hperm3 : List.Perm [p₃] [q₃] := hperm2.cons_inv
      have hp₃_mem : p₃ ∈ [q₃] := hperm3.mem_iff.mp (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp₃_mem
      exact ⟨h2, hp₃_mem⟩
    · rw [h2] at hperm2
      have hperm3 : List.Perm [q₃, p₃] [q₃, q₂] := hperm2.trans (List.Perm.swap q₃ q₂ [])
      have hperm4 : List.Perm [p₃] [q₂] := hperm3.cons_inv
      have hp₃_mem : p₃ ∈ [q₂] := hperm4.mem_iff.mp (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp₃_mem
      omega
  rcases hp₂_eq with ⟨rfl, rfl⟩
  rfl

/-- Cardinality of `bSet N z y` equals cardinality of `bTriples N z y`. -/
theorem card_bSet_eq_card_bTriples (N z y : ℕ) :
    (bSet N z y).card = (bTriples N z y).card :=
  Finset.card_image_of_injOn (bTriples_injOn N z y)

end BuchstabSwitchingK2
