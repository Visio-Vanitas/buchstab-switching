import BuchstabSwitchingK2.Core.ShiftedPrimesK2.Sets

/-!
# Chen Pinch Criterion for `Ω(N - p) ≤ 2`

Proves `omegaMult_le_two_of_chen_pinch`: under `2 ≤ z ≤ y`, `N ≤ y^3`, `z`-roughness
of `N - p`, squarefreeness on `[z, y)`, and at most one prime divisor of `N - p` in
`[z, y)`, either `Ω(N - p) ≤ 2` or `p` lies in `sievedBSet N z y ∪ smallPrimes N y`.
-/

namespace BuchstabSwitchingK2

/--
Chen pinch lemma for `k = 2`:
If `2 ≤ z ≤ y`, `N ≤ y ^ 3`, `p < N` is prime with `¬ p ∣ N`, and `N - p` has no prime
divisor `< z`, no square `q ^ 2` for `q ∈ midPrimes N z y`, and at most one prime divisor
in `midPrimes N z y`, then either `omegaMult (N - p) ≤ 2` or
`p ∈ sievedBSet N z y ∪ smallPrimes N y`.
-/
theorem omegaMult_le_two_of_chen_pinch {N z y p : ℕ}
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3)
    (hpN : p < N) (hp_prime : p.Prime) (hp_ndvd : ¬ p ∣ N)
    (hrough : ∀ r : ℕ, r.Prime → r < z → ¬ r ∣ N - p)
    (hsq : ∀ q ∈ midPrimes N z y, ¬ q ^ 2 ∣ N - p)
    (hmid : ((midPrimes N z y).filter (fun q => q ∣ N - p)).card ≤ 1) :
    omegaMult (N - p) ≤ 2 ∨ p ∈ sievedBSet N z y ∪ smallPrimes N y := by
  set m := N - p
  have hm_pos : 0 < m := Nat.sub_pos_of_lt hpN
  have hm_lt : m < N := Nat.sub_lt (lt_trans hp_prime.pos hpN) hp_prime.pos
  have hy1 : 1 ≤ y := le_trans (by omega) (le_trans hz2 hzy)
  set S := (midPrimes N z y).filter (fun q => q ∣ m)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hmid with h0 | h1
  · have hall : ∀ r : ℕ, r.Prime → r ∣ m → y ≤ r := by
      intro r hr hrm
      by_contra hlt
      push Not at hlt
      have hrz : z ≤ r := by
        by_contra hltz
        push Not at hltz
        exact hrough r hr hltz hrm
      have hrN : ¬ r ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hr hrm
      have hr_mem : r ∈ S := by
        simp only [S, midPrimes, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨⟨hrz, hlt⟩, hr, hrN⟩, hrm⟩
      rw [Finset.card_eq_zero] at h0
      simp [h0] at hr_mem
    have hm_lt_y3 : m < y ^ 3 := lt_of_lt_of_le hm_lt hy3
    have hlt3 := omegaMult_lt_of_lt_pow hm_pos hy1 hm_lt_y3 hall
    exact Or.inl (by omega)
  · rcases Finset.card_eq_one.mp h1 with ⟨p₁, hSp₁⟩
    have hp₁_mem : p₁ ∈ S := by
      rw [hSp₁]
      exact Finset.mem_singleton_self p₁
    have hp₁_mid : p₁ ∈ midPrimes N z y := (Finset.mem_filter.mp hp₁_mem).1
    have hp₁m : p₁ ∣ m := (Finset.mem_filter.mp hp₁_mem).2
    have hp₁_bounds : z ≤ p₁ ∧ p₁ < y := Finset.mem_Ico.mp (Finset.mem_filter.mp hp₁_mid).1
    have hp₁_prime : p₁.Prime := (Finset.mem_filter.mp hp₁_mid).2.1
    have hp₁_ndvd_N : ¬ p₁ ∣ N := (Finset.mem_filter.mp hp₁_mid).2.2
    have hp₁_sq : ¬ p₁ ^ 2 ∣ m := hsq p₁ hp₁_mid
    rcases hp₁m with ⟨m', hm_eq⟩
    have hm'_pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with rfl | hpos
      · simp at hm_eq
        omega
      · exact hpos
    have hp₁_ndvd_m' : ¬ p₁ ∣ m' := by
      intro hp₁m'
      apply hp₁_sq
      rcases hp₁m' with ⟨k, rfl⟩
      exact ⟨k, by rw [hm_eq]; ring⟩
    have hm'_ge_y : ∀ r : ℕ, r.Prime → r ∣ m' → y ≤ r := by
      intro r hr hrm'
      have hrm : r ∣ m := hm_eq ▸ dvd_mul_of_dvd_right hrm' p₁
      by_contra hlt
      push Not at hlt
      have hrz : z ≤ r := by
        by_contra hltz
        push Not at hltz
        exact hrough r hr hltz hrm
      have hrN : ¬ r ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hr hrm
      have hrS : r ∈ S := by
        simp only [S, midPrimes, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨⟨hrz, hlt⟩, hr, hrN⟩, hrm⟩
      rw [hSp₁, Finset.mem_singleton] at hrS
      subst hrS
      exact hp₁_ndvd_m' hrm'
    have hm'_le_m : m' ≤ m := by
      rw [hm_eq]
      exact Nat.le_mul_of_pos_left m' hp₁_prime.pos
    have hm'_lt_y3 : m' < y ^ 3 := lt_of_le_of_lt hm'_le_m (lt_of_lt_of_le hm_lt hy3)
    have hlt3 : omegaMult m' < 3 := omegaMult_lt_of_lt_pow hm'_pos hy1 hm'_lt_y3 hm'_ge_y
    by_cases hω1 : omegaMult m' ≤ 1
    · left
      rw [hm_eq, omegaMult_mul hp₁_prime.ne_zero hm'_pos.ne', omegaMult_prime hp₁_prime]
      omega
    · have hω2 : m'.primeFactorsList.length = 2 := by
        change omegaMult m' = 2
        omega
      match hlist : m'.primeFactorsList with
      | [] => simp [hlist] at hω2
      | [_] => simp [hlist] at hω2
      | _ :: _ :: _ :: _ =>
        exfalso
        simp only [hlist, List.length_cons] at hω2
        omega
      | [a, b] =>
        have ha_mem : a ∈ m'.primeFactorsList := by simp [hlist]
        have hb_mem : b ∈ m'.primeFactorsList := by simp [hlist]
        have ha_prime : a.Prime := Nat.prime_of_mem_primeFactorsList ha_mem
        have hb_prime : b.Prime := Nat.prime_of_mem_primeFactorsList hb_mem
        have ha_ge : y ≤ a := hm'_ge_y a ha_prime (Nat.dvd_of_mem_primeFactorsList ha_mem)
        have hb_ge : y ≤ b := hm'_ge_y b hb_prime (Nat.dvd_of_mem_primeFactorsList hb_mem)
        have hab_prod : a * b = m' := by
          have hp := Nat.prod_primeFactorsList hm'_pos.ne'
          rw [hlist] at hp
          simpa [mul_one] using hp
        have h_ord : ∃ p₂ p₃ : ℕ,
            p₂ ≤ p₃ ∧ p₂.Prime ∧ p₃.Prime ∧ y ≤ p₂ ∧ y ≤ p₃ ∧ p₂ * p₃ = m' := by
          by_cases hab : a ≤ b
          · exact ⟨a, b, hab, ha_prime, hb_prime, ha_ge, hb_ge, hab_prod⟩
          · exact ⟨b, a, le_of_not_ge hab, hb_prime, ha_prime, hb_ge, ha_ge,
              by rw [mul_comm]; exact hab_prod⟩
        rcases h_ord with ⟨p₂, p₃, hp₂₃, hp₂_prime, hp₃_prime, hp₂_ge, hp₃_ge, hp₂₃_prod⟩
        have hm_prod : p₁ * p₂ * p₃ = m := by
          rw [mul_assoc, hp₂₃_prod, ← hm_eq]
        have hprod_lt : p₁ * p₂ * p₃ < N := hm_prod ▸ hm_lt
        have hp₂_lt : p₂ < N := by
          have hle : 2 * p₂ ≤ p₁ * p₂ * p₃ := by
            calc
              2 * p₂ ≤ p₁ * p₂ := Nat.mul_le_mul_right p₂ hp₁_prime.two_le
              _ = p₁ * p₂ * 1 := (mul_one _).symm
              _ ≤ p₁ * p₂ * p₃ := Nat.mul_le_mul_left _ hp₃_prime.pos
          have hp₂_pos : 0 < p₂ := hp₂_prime.pos
          omega
        have hp₃_lt : p₃ < N := by
          have hle : 2 * p₃ ≤ p₁ * p₂ * p₃ := by
            calc
              2 * p₃ ≤ p₁ * p₃ := Nat.mul_le_mul_right p₃ hp₁_prime.two_le
              _ ≤ p₁ * (p₂ * p₃) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left p₃ hp₂_prime.pos)
              _ = p₁ * p₂ * p₃ := (mul_assoc _ _ _).symm
          have hp₃_pos : 0 < p₃ := hp₃_prime.pos
          omega
        have hp₂_dvd_m : p₂ ∣ m := ⟨p₁ * p₃, by rw [← hm_prod]; ring⟩
        have hp₃_dvd_m : p₃ ∣ m := ⟨p₁ * p₂, by rw [← hm_prod]; ring⟩
        have hp₂_ndvd_N : ¬ p₂ ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hp₂_prime hp₂_dvd_m
        have hp₃_ndvd_N : ¬ p₃ ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hp₃_prime hp₃_dvd_m
        have htriple : (p₁, p₂, p₃) ∈ bTriples N z y := by
          simp only [bTriples, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
            Finset.mem_Ico]
          exact ⟨⟨hp₁_bounds, ⟨hp₂_ge, hp₂_lt⟩, ⟨hp₃_ge, hp₃_lt⟩⟩,
            hp₂₃, hp₁_prime, hp₂_prime, hp₃_prime, hp₁_ndvd_N, hp₂_ndvd_N, hp₃_ndvd_N, hprod_lt⟩
        have hp_bSet : p ∈ bSet N z y := by
          rw [bSet, Finset.mem_image]
          refine ⟨(p₁, p₂, p₃), htriple, ?_⟩
          dsimp only
          rw [hm_prod]
          exact Nat.sub_sub_self (le_of_lt hpN)
        right
        by_cases hpy : p < y
        · exact Finset.mem_union_right _ (by
            simp only [smallPrimes, Finset.mem_filter, Finset.mem_range]
            exact ⟨hpy, hp_prime, hp_ndvd⟩)
        · apply Finset.mem_union_left
          simp only [sievedBSet, Finset.mem_filter]
          refine ⟨hp_bSet, ?_⟩
          intro r hr_range hr_prime _hr_ndvd hr_dvd_p
          have hr_lt_y : r < y := Finset.mem_range.mp hr_range
          have hr_eq_p : r = p := (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp hr_dvd_p
          omega

end BuchstabSwitchingK2
