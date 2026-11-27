import BuchstabSwitchingK2.Sieve.ChenSwitching
import BuchstabSwitchingK2.Certificates.Data
import BuchstabSwitchingK2.External.CharacterSums.DirichletGRH

/-!
# Linear-Sieve Asymptotic Ray Enclosure Interface (`N ≥ X_LS`)

States `AsymptoticRayEnclosurePremiseK2`: under `DirichletLNonvanishingRightOfHalf`, for all
even `N ≥ asymptoticCert.X_LS`, there exist valid Chen `1 + 2` switching cutoffs `2 ≤ z ≤ y`
with `N ≤ y^3` and positive normalization `scale` such that
`(asymptoticCert.main_lb - asymptoticCert.err_ub) * scale ≤ switchingBalance1p2 N z y`.
-/

namespace BuchstabSwitchingK2.External

/-- Under `DirichletLNonvanishingRightOfHalf`, every even `N ≥ asymptoticCert.X_LS` inherits
the certified uniform positive switching coefficient from `asymptoticCert`. -/
def AsymptoticRayEnclosurePremiseK2 : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, Even N → BuchstabSwitchingK2.asymptoticCert.X_LS ≤ N →
      ∃ (z y : ℕ) (scale : ℚ),
        2 ≤ z ∧ z ≤ y ∧ N ≤ y ^ 3 ∧ 0 < scale ∧
        (BuchstabSwitchingK2.asymptoticCert.main_lb - BuchstabSwitchingK2.asymptoticCert.err_ub) *
          scale ≤ BuchstabSwitchingK2.switchingBalance1p2 N z y

end BuchstabSwitchingK2.External
