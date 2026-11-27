import BuchstabSwitching.Core.ShiftedPrimes
import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Certificates.Soundness
import BuchstabSwitching.External.Bridge
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Top-Level Conditional `Ω(m) ≤ 3` Shifted Representation Theorem

Combines the zero-`sorry` combinatorial one-step switching engine (`Sieve.OneStepSwitching`),
the kernel-verified contiguous slab chain and asymptotic ray (`Certificates.Soundness`), and
the isolated external analytic bridge (`External.ExternalPremises`) to deduce that every even
integer `N ≥ 4` splits as `N = p + m` with `p` prime, `0 < m`, and `Ω m ≤ 3`.
-/

namespace BuchstabSwitching

open scoped ArithmeticFunction.Omega

/-- Target statement matching the repository `Challenge` convention (`0 < m` and Mathlib `Ω`). -/
def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

/-- Main conditional theorem: assuming `DirichletLNonvanishingRightOfHalf` and the external
analytic bridges in `External.ExternalPremises`, every even `N ≥ 4` satisfies `N = p + m`
with `Nat.Prime p` and `omegaMult m ≤ 3`. -/
theorem even_eq_prime_add_omegaMult_le_three
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremises)
    (N : ℕ) (hEven : Even N) (hN : 4 ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 3 ∧ p + m = N := by
  rcases exists_slab_or_ray N hN with hSmall | hSlab | hRay
  · -- Regime 1: `4 ≤ N < 4 * 10^18`
    rcases hExt.small_even N hEven hN hSmall with ⟨p, q, hp, hq, hpq⟩
    refine ⟨p, q, hp, ?_, hpq⟩
    rw [omegaMult_prime hq]
    decide
  · -- Regime 2: Finite contiguous certified slab `c ∈ allSlabs`
    rcases hSlab with ⟨c, hc, hlo, hhi⟩
    rcases mem_allSlabs_valid hc with ⟨_, hz2, hzy, hy4, hzy3, hnet_pos, hnet_le⟩
    have hN_le_hi : N ≤ c.X_hi := le_of_lt hhi
    have hy4_N : N ≤ c.y ^ 4 := le_trans hN_le_hi hy4
    have hzy3_N : N ≤ c.z * c.y ^ 3 := le_trans hN_le_hi hzy3
    rcases hExt.slab_enclosure hGRH c hc N hEven hlo hhi with ⟨scale, hscale_pos, hbal⟩
    have hmargin_pos : (0 : ℚ) < (c.main_lb - c.err_ub) * scale :=
      mul_pos (lt_of_lt_of_le hnet_pos hnet_le) hscale_pos
    exact exists_prime_add_omegaMult_le_three_of_switching_pos N c.z c.y
      hz2 hzy hy4_N hzy3_N (lt_of_lt_of_le hmargin_pos hbal)
  · -- Regime 3: Asymptotic monotone ray `N ≥ asymptoticCert.X_LS`
    have hray_valid := RayCert.valid_sound asymptoticCert_verified
    rcases hExt.ray_enclosure hGRH N hEven hRay with
      ⟨z, y, scale, hz2, hzy, hy4, hzy3, hscale_pos, hbal⟩
    have hmargin_pos : (0 : ℚ) < (asymptoticCert.main_lb - asymptoticCert.err_ub) * scale :=
      mul_pos (lt_of_lt_of_le hray_valid.2.1 hray_valid.2.2) hscale_pos
    exact exists_prime_add_omegaMult_le_three_of_switching_pos N z y
      hz2 hzy hy4 hzy3 (lt_of_lt_of_le hmargin_pos hbal)

/-- Challenge-aligned phrasing (`AllEvenPrimePlusAlmostPrime 3` with `0 < m` and Mathlib `Ω`). -/
theorem all_even_one_plus_three_of_premises
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremises) :
    AllEvenPrimePlusAlmostPrime 3 := by
  intro N hN hEven
  rcases even_eq_prime_add_omegaMult_le_three hGRH hExt N hEven hN with ⟨p, m, hp, hm, hpN⟩
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

/-- End-to-end conditional `1 + 3` theorem directly from the five classical premises in
`External.ClassicalBasicLemmas consts` plus GRH (`External.DirichletLNonvanishingRightOfHalf`). -/
theorem all_even_one_plus_three_of_classical
    (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : External.ClassicalBasicLemmas consts) :
    AllEvenPrimePlusAlmostPrime 3 :=
  all_even_one_plus_three_of_premises hGRH (External.externalPremises_of_classical hCls)

#print axioms even_eq_prime_add_omegaMult_le_three
#print axioms all_even_one_plus_three_of_premises
#print axioms all_even_one_plus_three_of_classical

end BuchstabSwitching
