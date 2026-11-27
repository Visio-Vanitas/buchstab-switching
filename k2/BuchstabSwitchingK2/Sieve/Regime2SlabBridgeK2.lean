import BuchstabSwitchingK2.Sieve.ChenSwitching
import BuchstabSwitchingK2.Sieve.PreSieveBonferroni
import BuchstabSwitchingK2.Sieve.BSetSieveBridge
import BuchstabSwitchingK2.Certificates.Soundness
import Mathlib.Tactic

/-!
# Regime 2 Finite-Slab Assembly Bridge (`1 + 2` & Chen/Wu Lemma 2.1)

Proves the normalized switching-balance assembly lemmas for finite certified slabs
(both 1-step Chen `switchingBalance1p2` and `+S_4` Lemma 2.1 `switchingBalance1p2WithS4`),
connecting explicit lower/upper bounds on `S(A_N)`, `S(A_{N,q})`, `S(B_N)`, and `S₄`
to `exists_prime_add_omegaMult_le_two_of_switching_pos` and
`exists_prime_add_omegaMult_le_two_of_switchingWithS4_pos` with zero `sorry`.
-/

namespace BuchstabSwitchingK2

section Regime2SlabBridgeK2

/-- Finite-slab 1-step assembly over `ℚ`: given explicit rational bounds relative to
`0 < scale` matching `c : SlabCert`, proves `(c.main_lb - c.err_ub) * scale ≤ switchingBalance1p2 N c.z c.y`
and deduces a `1 + 2` prime + almost-prime representation whenever `c.valid = true`. -/
theorem exists_prime_add_omegaMult_le_two_of_slab_pieces
    (N : ℕ) (c : SlabCert) (hc : c.valid = true)
    (_hlo : c.X_lo ≤ N) (hhi : N < c.X_hi)
    (scale tA_lo err_tot : ℚ) (hscale : 0 < scale)
    (hA : tA_lo * scale ≤ ((sievedShifted N c.z).card : ℚ))
    (hErr :
      (1 / 2 : ℚ) * ∑ q ∈ midPrimes N c.z c.y,
          (((divisibleSievedShifted N c.z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ)) +
        (1 / 2 : ℚ) * (((sievedBSet N c.z c.y).card : ℚ) + ((smallPrimes N c.y).card : ℚ)) ≤
          err_tot * scale)
    (hmain : c.main_lb ≤ tA_lo)
    (herr : err_tot ≤ c.err_ub) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  rcases SlabCert.valid_sound hc with ⟨_, hz2, hzy, hy3, hnet_pos, hnet_le⟩
  have hy3_N : N ≤ c.y ^ 3 := le_trans (le_of_lt hhi) hy3
  have hbal : (c.main_lb - c.err_ub) * scale ≤ switchingBalance1p2 N c.z c.y := by
    have hm : c.main_lb * scale ≤ tA_lo * scale :=
      mul_le_mul_of_nonneg_right hmain hscale.le
    have he : err_tot * scale ≤ c.err_ub * scale :=
      mul_le_mul_of_nonneg_right herr hscale.le
    unfold switchingBalance1p2
    linarith
  have hpos : (0 : ℚ) < switchingBalance1p2 N c.z c.y := by
    have hm_pos : (0 : ℚ) < (c.main_lb - c.err_ub) * scale :=
      mul_pos (lt_of_lt_of_le hnet_pos hnet_le) hscale
    exact lt_of_lt_of_le hm_pos hbal
  exact exists_prime_add_omegaMult_le_two_of_switching_pos N c.z c.y hz2 hzy hy3_N hpos

/-- Finite-slab Chen (1978) / Wu (2008) Lemma 2.1 (`+S₄`) assembly over `ℚ`:
given `2 ≤ z ≤ w ≤ y`, `N ≤ y^3`, `0 < scale`, and positive net margin after adding
`(1/2) * |s4Shifted N z w|`, deduces a `1 + 2` representation `p + m = N` with `Ω(m) ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_lemma21_pieces
    (N z y w : ℕ) (hz2 : 2 ≤ z) (hzw : z ≤ w) (hwy : w ≤ y) (hy3 : N ≤ y ^ 3)
    (scale main_lb s4_lb err_ub : ℚ) (hscale : 0 < scale)
    (hnet : 0 < main_lb + s4_lb - err_ub)
    (hA : main_lb * scale ≤ ((sievedShifted N z).card : ℚ))
    (hS4 : s4_lb * scale ≤ (1 / 2 : ℚ) * ((s4Shifted N z w).card : ℚ))
    (hErr :
      (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
          (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ)) +
        (1 / 2 : ℚ) * (((sievedBSet N z y).card : ℚ) + ((smallPrimes N y).card : ℚ)) ≤
          err_ub * scale) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hbal : (main_lb + s4_lb - err_ub) * scale ≤ switchingBalance1p2WithS4 N z y w := by
    unfold switchingBalance1p2WithS4 switchingBalance1p2
    linarith
  have hpos : (0 : ℚ) < switchingBalance1p2WithS4 N z y w :=
    lt_of_lt_of_le (mul_pos hnet hscale) hbal
  exact exists_prime_add_omegaMult_le_two_of_switchingWithS4_pos
    N z y w hz2 (le_trans hzw hwy) hwy hy3 hpos

end Regime2SlabBridgeK2

end BuchstabSwitchingK2
