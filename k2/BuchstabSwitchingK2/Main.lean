import BuchstabSwitchingK2.Core.ShiftedPrimesK2
import BuchstabSwitchingK2.Sieve.ChenSwitching
import BuchstabSwitchingK2.Certificates.Soundness
import BuchstabSwitchingK2.External.Bridge
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Top-Level Conditional `Ω(m) ≤ 2` Shifted Representation Theorem

Combines the zero-`sorry` combinatorial Chen `1 + 2` switching engine (`Sieve.ChenSwitching`),
the verified regime partition and asymptotic ray certificate (`Certificates.Soundness`), and
the isolated external analytic bridges (`External.Bridge`) to deduce:
1. the standalone asymptotic ray theorem for all even `N ≥ asymptoticCert.X_LS`
   (`even_eq_prime_add_omegaMult_le_two_above_ray`, `chen_above_ray_of_premises`), depending
   only on `DirichletLNonvanishingRightOfHalf` and `AsymptoticRayEnclosurePremiseK2`;
2. the conditional all-even Chen `1 + 2` theorem for all even `N ≥ 4`
   (`even_eq_prime_add_omegaMult_le_two`, `all_even_one_plus_two_of_premises`).
-/

namespace BuchstabSwitchingK2

open scoped ArithmeticFunction.Omega

/-- Target statement matching the repository `Challenge` convention (`0 < m` and Mathlib `Ω`). -/
def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

/-- Standalone asymptotic ray theorem: assuming `DirichletLNonvanishingRightOfHalf` and
`AsymptoticRayEnclosurePremiseK2`, every even `N ≥ asymptoticCert.X_LS` splits as `p + m = N`
with `Nat.Prime p` and `omegaMult m ≤ 2`. -/
theorem even_eq_prime_add_omegaMult_le_two_above_ray
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hRayExt : External.AsymptoticRayEnclosurePremiseK2)
    (N : ℕ) (hEven : Even N) (hN : asymptoticCert.X_LS ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hray_valid := RayCert.valid_sound asymptoticCert_verified
  rcases hRayExt hGRH N hEven hN with ⟨z, y, scale, hz2, hzy, hy3, hscale_pos, hbal⟩
  have hmargin_pos : (0 : ℚ) < (asymptoticCert.main_lb - asymptoticCert.err_ub) * scale :=
    mul_pos (lt_of_lt_of_le hray_valid.2.1 hray_valid.2.2) hscale_pos
  exact exists_prime_add_omegaMult_le_two_of_switching_pos N z y
    hz2 hzy hy3 (lt_of_lt_of_le hmargin_pos hbal)

/-- Challenge-aligned asymptotic ray phrasing (`0 < m` and Mathlib `Ω m ≤ 2`) for all even
`N ≥ asymptoticCert.X_LS`. -/
theorem chen_above_ray_of_premises
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hRayExt : External.RayExternalPremisesK2) :
    ∀ N : ℕ, asymptoticCert.X_LS ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  intro N hN hEven
  rcases even_eq_prime_add_omegaMult_le_two_above_ray hGRH hRayExt.ray_enclosure N hEven hN with
    ⟨p, m, hp, hm, hpN⟩
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := by omega
    subst hm_zero
    have h2N : 2 ∣ N := even_iff_two_dvd.mp hEven
    have hp_eq : p = N := by omega
    have h2p : 2 ∣ p := hp_eq ▸ h2N
    have hN_ge : 4 ≤ N := by
      have hray := (RayCert.valid_sound asymptoticCert_verified).1
      omega
    rcases hp.eq_one_or_self_of_dvd 2 h2p with h1 | h2
    · omega
    · omega
  refine ⟨p, m, hp, hm_pos, hpN.symm, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply, omegaMult] using hm

/-- Main conditional all-even theorem: assuming `DirichletLNonvanishingRightOfHalf` and
`External.ExternalPremisesK2`, every even `N ≥ 4` satisfies `p + m = N` with `Nat.Prime p`
and `omegaMult m ≤ 2`. -/
theorem even_eq_prime_add_omegaMult_le_two
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremisesK2)
    (N : ℕ) (hEven : Even N) (hN : 4 ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  rcases exists_small_or_gap_or_ray N with hSmall | ⟨hlo, hhi⟩ | hRay
  · -- Regime 1: `4 ≤ N < 4 * 10^18`
    rcases hExt.small_even N hEven hN hSmall with ⟨p, q, hp, hq, hpq⟩
    refine ⟨p, q, hp, ?_, hpq⟩
    rw [omegaMult_prime hq]
    decide
  · -- Regime 2: Finite sieve gap `[4 * 10^18, asymptoticCert.X_LS)`
    rcases hExt.slab_gap_enclosure hGRH N hEven hlo hhi with
      ⟨z, y, scale, margin, hz2, hzy, hy3, hmargin_pos, hscale_pos, hbal⟩
    have hpos : (0 : ℚ) < switchingBalance1p2 N z y :=
      lt_of_lt_of_le (mul_pos hmargin_pos hscale_pos) hbal
    exact exists_prime_add_omegaMult_le_two_of_switching_pos N z y hz2 hzy hy3 hpos
  · -- Regime 3: Asymptotic monotone ray `N ≥ asymptoticCert.X_LS`
    exact even_eq_prime_add_omegaMult_le_two_above_ray hGRH hExt.ray_enclosure N hEven hRay

/-- Challenge-aligned phrasing (`AllEvenPrimePlusAlmostPrime 2` with `0 < m` and Mathlib `Ω`). -/
theorem all_even_one_plus_two_of_premises
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremisesK2) :
    AllEvenPrimePlusAlmostPrime 2 := by
  intro N hN hEven
  rcases even_eq_prime_add_omegaMult_le_two hGRH hExt N hEven hN with ⟨p, m, hp, hm, hpN⟩
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := by omega
    subst hm_zero
    have h2N : 2 ∣ N := even_iff_two_dvd.mp hEven
    have hp_eq : p = N := by omega
    have h2p : 2 ∣ p := hp_eq ▸ h2N
    rcases hp.eq_one_or_self_of_dvd 2 h2p with h1 | h2
    · omega
    · omega
  refine ⟨p, m, hp, hm_pos, hpN.symm, ?_⟩
  simpa [ArithmeticFunction.cardFactors_apply, omegaMult] using hm

#print axioms even_eq_prime_add_omegaMult_le_two_above_ray
#print axioms chen_above_ray_of_premises
#print axioms even_eq_prime_add_omegaMult_le_two
#print axioms all_even_one_plus_two_of_premises

end BuchstabSwitchingK2
