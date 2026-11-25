import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.External.CharacterSums.DirichletGRH

/-!
# Linear-Sieve Asymptotic Ray Enclosure Interface (`N ≥ X_LS`)

States `AsymptoticRayEnclosurePremise`: under `DirichletLNonvanishingRightOfHalf`, for all
even `N ≥ asymptoticCert.X_LS`, there exist valid switching cutoffs `2 ≤ z ≤ y` with
`N ≤ y^4`, `N ≤ z * y^3`, and positive normalization `scale` such that
`(asymptoticCert.main_lb - asymptoticCert.err_ub) * scale ≤ switchingBalance N z y`.

Discharging this premise against Mathlib requires:
1. Closed-form BJS linear-sieve remainder inequality (`arXiv:2207.09452`, Theorem 6 / Table 1)
   with uniform two-variable pre-sieve error `ε_sup(p_*)`;
2. Buchstab lower-function quadrature `f(s)` on `4 ≤ s ≤ 6`;
3. Monotone pre-sieve-free Selberg `Λ²` upper bound using `V_N(z) * J_full(z, ξ)` via
   `Sieve.SelbergLambdaSq` and two-prime inclusion-exclusion.
-/

namespace BuchstabSwitching.External

/-- Under `DirichletLNonvanishingRightOfHalf`, every even `N ≥ asymptoticCert.X_LS` inherits
the certified uniform positive switching coefficient from `asymptoticCert`. -/
def AsymptoticRayEnclosurePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → BuchstabSwitching.asymptoticCert.X_LS ≤ N →
      ∃ (z y : ℕ) (scale : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 4 ∧ N ≤ z * y ^ 3 ∧ 0 < scale ∧
        (BuchstabSwitching.asymptoticCert.main_lb - BuchstabSwitching.asymptoticCert.err_ub) *
          scale ≤ BuchstabSwitching.switchingBalance N z y

end BuchstabSwitching.External
