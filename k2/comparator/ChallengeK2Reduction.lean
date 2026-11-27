import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Standalone Comparator Challenge Specification for `BuchstabSwitchingK2` (`1 + 2`)

Mirrors the exact definitions and theorem statements of `BuchstabSwitchingK2` with `sorry`
proofs so `comparator/ChallengeK2Reduction.lean` typechecks standalone against Mathlib.
`DirichletLNonvanishingRightOfHalf` matches verbatim `grh-compact/src/Statements.lean` in
`https://github.com/lsernau/grh-lean` (commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`).
-/

namespace BuchstabSwitchingK2

structure SlabCert where
  X_lo : ℕ
  X_hi : ℕ
  z : ℕ
  y : ℕ
  main_num : ℕ
  err_num : ℕ
  net_num : ℕ
  den : ℕ
  deriving Repr, DecidableEq

def SlabCert.main_lb (c : SlabCert) : ℚ := (c.main_num : ℚ) / (c.den : ℚ)

def SlabCert.err_ub (c : SlabCert) : ℚ := (c.err_num : ℚ) / (c.den : ℚ)

def SlabCert.net_lb (c : SlabCert) : ℚ := (c.net_num : ℚ) / (c.den : ℚ)

structure RayCert where
  X_LS : ℕ
  main_num : ℕ
  err_num : ℕ
  net_num : ℕ
  den : ℕ
  deriving Repr, DecidableEq

def RayCert.main_lb (r : RayCert) : ℚ := (r.main_num : ℚ) / (r.den : ℚ)

def RayCert.err_ub (r : RayCert) : ℚ := (r.err_num : ℚ) / (r.den : ℚ)

def RayCert.net_lb (r : RayCert) : ℚ := (r.net_num : ℚ) / (r.den : ℚ)

def asymptoticCert_old : RayCert where
  X_LS := 10 ^ 1831
  main_num := 11110466
  err_num := 11103630
  net_num := 6836
  den := 1000000

def asymptoticCert_new : RayCert where
  X_LS := 10 ^ 1668
  main_num := 11118411
  err_num := 11111613
  net_num := 6798
  den := 1000000

def asymptoticCert : RayCert := asymptoticCert_new

def allSlabs : List SlabCert := []

def omegaMult (m : ℕ) : ℕ :=
  m.primeFactorsList.length

def shiftedCoprimePrimes (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)

def midPrimes (N z y : ℕ) : Finset ℕ :=
  (Finset.Ico z y).filter (fun q => q.Prime ∧ ¬ q ∣ N)

def smallPrimes (N y : ℕ) : Finset ℕ :=
  (Finset.range y).filter (fun p => p.Prime ∧ ¬ p ∣ N)

def bTriples (N z y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Ico z y).product ((Finset.Ico y N).product (Finset.Ico y N))).filter
    fun ⟨p₁, p₂, p₃⟩ =>
      p₂ ≤ p₃ ∧ p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
      ¬ p₁ ∣ N ∧ ¬ p₂ ∣ N ∧ ¬ p₃ ∣ N ∧ p₁ * p₂ * p₃ < N

def bSet (N z y : ℕ) : Finset ℕ :=
  (bTriples N z y).image (fun t => N - t.1 * t.2.1 * t.2.2)

def sievedBSet (N z y : ℕ) : Finset ℕ :=
  (bSet N z y).filter (fun b => ∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b)

def sievedShifted (N z : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p)

def divisibleSievedShifted (N z q : ℕ) : Finset ℕ :=
  (sievedShifted N z).filter (fun p => q ∣ N - p)

def squareDivisibleShifted (N q : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => q ^ 2 ∣ N - p)

def switchingBalance1p2 (N z y : ℕ) : ℚ :=
  ((sievedShifted N z).card : ℚ) -
    (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
      (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ)) -
    (1 / 2 : ℚ) * (((sievedBSet N z y).card : ℚ) + ((smallPrimes N y).card : ℚ))

namespace External

def finiteCutoff : ℕ := 4 * 10 ^ 18

def SmallEvenPremise : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → N < finiteCutoff →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def SlabSieveEnclosurePremiseK2 : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ c ∈ BuchstabSwitchingK2.allSlabs, ∀ N : ℕ,
      Even N → c.X_lo ≤ N → N < c.X_hi →
      ∃ scale : ℚ, 0 < scale ∧
        (c.main_lb - c.err_ub) * scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N c.z c.y

def LowDecadeGapPremiseK2 : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → 4 * 10 ^ 18 ≤ N → N < BuchstabSwitchingK2.asymptoticCert.X_LS →
      ∃ (z y : ℕ) (scale margin : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 3 ∧ 0 < margin ∧ 0 < scale ∧
        margin * scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N z y

def AsymptoticRayEnclosurePremiseK2 : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → BuchstabSwitchingK2.asymptoticCert.X_LS ≤ N →
      ∃ (z y : ℕ) (scale : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 3 ∧ 0 < scale ∧
        (BuchstabSwitchingK2.asymptoticCert.main_lb - BuchstabSwitchingK2.asymptoticCert.err_ub) *
          scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N z y

structure RayExternalPremisesK2 : Prop where
  ray_enclosure : AsymptoticRayEnclosurePremiseK2

structure ExternalPremisesK2 : Prop where
  small_even : SmallEvenPremise
  slab_gap_enclosure : LowDecadeGapPremiseK2
  ray_enclosure : AsymptoticRayEnclosurePremiseK2

end External

open scoped ArithmeticFunction.Omega

def AllEvenPrimePlusAlmostPrime (K : ℕ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ K

theorem even_eq_prime_add_omegaMult_le_two_above_ray
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hRayExt : External.AsymptoticRayEnclosurePremiseK2)
    (N : ℕ) (hEven : Even N) (hN : asymptoticCert.X_LS ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  sorry

theorem chen_above_ray_of_premises
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hRayExt : External.RayExternalPremisesK2) :
    ∀ N : ℕ, asymptoticCert.X_LS ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 2 := by
  sorry

theorem even_eq_prime_add_omegaMult_le_two
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremisesK2)
    (N : ℕ) (hEven : Even N) (hN : 4 ≤ N) :
    ∃ p m : ℕ, Nat.Prime p ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  sorry

theorem all_even_one_plus_two_of_premises
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hExt : External.ExternalPremisesK2) :
    AllEvenPrimePlusAlmostPrime 2 := by
  sorry

end BuchstabSwitchingK2
