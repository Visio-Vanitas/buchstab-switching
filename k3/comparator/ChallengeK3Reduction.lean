import ChallengeK3Data
import ChallengeK3MertensTwoVar
import ChallengeK3DirichletGRH
import ChallengeK3Schoenfeld
import ChallengeK3MertensExt
import ChallengeK3EulerV
import ChallengeK3Constants
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace BuchstabSwitching

def omegaMult (m : ℕ) : ℕ :=
  m.primeFactorsList.length

def shiftedCoprimePrimes (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)

def midPrimes (N z y : ℕ) : Finset ℕ :=
  (Finset.Ico z y).filter (fun q => q.Prime ∧ ¬ q ∣ N)

def sievedShifted (N z : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p)

def divisibleSievedShifted (N z q : ℕ) : Finset ℕ :=
  (sievedShifted N z).filter (fun p => q ∣ N - p)

def squareDivisibleShifted (N q : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => q ^ 2 ∣ N - p)

def switchingBalance (N z y : ℕ) : ℚ :=
  ((sievedShifted N z).card : ℚ) -
    (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
      (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ))

namespace External

def finiteCutoff : ℕ := 4 * 10 ^ 18

def SmallEvenPremise : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → N < finiteCutoff →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

def SlabSieveEnclosurePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ c ∈ BuchstabSwitching.allSlabs, ∀ N : ℕ,
      Even N → c.X_lo ≤ N → N < c.X_hi →
      ∃ scale : ℚ, 0 < scale ∧
        (c.main_lb - c.err_ub) * scale ≤ BuchstabSwitching.switchingBalance N c.z c.y

def AsymptoticRayEnclosurePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → BuchstabSwitching.asymptoticCert.X_LS ≤ N →
      ∃ (z y : ℕ) (scale : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 4 ∧ N ≤ z * y ^ 3 ∧ 0 < scale ∧
        (BuchstabSwitching.asymptoticCert.main_lb - BuchstabSwitching.asymptoticCert.err_ub) *
          scale ≤ BuchstabSwitching.switchingBalance N z y

structure ExternalPremises : Prop where
  small_even : SmallEvenPremise
  slab_enclosure : SlabSieveEnclosurePremise
  ray_enclosure : AsymptoticRayEnclosurePremise

structure ClassicalBasicLemmas (consts : CertifiedConstants) : Prop where
  small_even : SmallEvenPremise
  js_ap : JSLemma51Premise consts.li2
  schoenfeld : SchoenfeldPrimePremise consts.li2
  mertens : MertensPrimeSumPremise consts.M0
  euler_v : EulerProductVPremise consts.U_c consts.eNegGamma

theorem externalPremises_of_classical
    {consts : CertifiedConstants} (hCls : ClassicalBasicLemmas consts) :
    ExternalPremises := by
  sorry

end External

open scoped ArithmeticFunction.Omega

def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

theorem even_eq_prime_add_omegaMult_le_three
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremises)
    (N : ℕ) (hEven : Even N) (hN : 4 ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 3 ∧ p + m = N := by
  sorry

theorem all_even_one_plus_three_of_premises
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremises) :
    AllEvenPrimePlusAlmostPrime 3 := by
  sorry

theorem all_even_one_plus_three_of_classical
    (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : External.ClassicalBasicLemmas consts) :
    AllEvenPrimePlusAlmostPrime 3 := by
  sorry

end BuchstabSwitching
