import BuchstabSwitchingK2.External.FiniteVerification.SmallEven
import BuchstabSwitchingK2.External.CharacterSums.DirichletGRH
import BuchstabSwitchingK2.External.LargeSieve.MultiplicativeLargeSieve
import BuchstabSwitchingK2.External.MultiplicativeBounds.SlabSieveEnclosure
import BuchstabSwitchingK2.External.LinearSieve.AsymptoticRayEnclosure

/-!
# Bundled External Analytic Bridge (`RayExternalPremisesK2` & `ExternalPremisesK2`)

Combines the external premise interfaces for `BuchstabSwitchingK2`:
- `RayExternalPremisesK2` for the standalone asymptotic ray theorem (`N ≥ asymptoticCert.X_LS`);
- `ExternalPremisesK2` for the full all-even `1 + 2` theorem (`N ≥ 4`), together with
  `ExternalPremisesK2.toRay` and `ExternalPremisesK2.ofSlabChain`.
-/

namespace BuchstabSwitchingK2.External

/-- External premises needed for the standalone asymptotic ray theorem (`N ≥ asymptoticCert.X_LS`). -/
structure RayExternalPremisesK2 : Prop where
  ray_enclosure : AsymptoticRayEnclosurePremiseK2

/-- Complete bundle of external analytic and computational inputs for the conditional
all-even `Ω(m) ≤ 2` shifted-prime theorem (`N ≥ 4`). -/
structure ExternalPremisesK2 : Prop where
  small_even : SmallEvenPremise
  slab_gap_enclosure : LowDecadeGapPremiseK2
  ray_enclosure : AsymptoticRayEnclosurePremiseK2

/-- Projects full `ExternalPremisesK2` down to `RayExternalPremisesK2`. -/
theorem ExternalPremisesK2.toRay (hExt : ExternalPremisesK2) : RayExternalPremisesK2 :=
  ⟨hExt.ray_enclosure⟩

/-- Constructs `ExternalPremisesK2` from `SmallEvenPremise`, a verified contiguous slab chain
covering `[4 * 10^18, asymptoticCert.X_LS)`, `SlabSieveEnclosurePremiseK2`, and
`AsymptoticRayEnclosurePremiseK2`. -/
theorem ExternalPremisesK2.ofSlabChain
    (hSmall : SmallEvenPremise)
    (hchain :
      BuchstabSwitchingK2.checkSlabChain
        (4 * 10 ^ 18) BuchstabSwitchingK2.asymptoticCert.X_LS BuchstabSwitchingK2.allSlabs = true)
    (hSlab : SlabSieveEnclosurePremiseK2)
    (hRay : AsymptoticRayEnclosurePremiseK2) :
    ExternalPremisesK2 where
  small_even := hSmall
  slab_gap_enclosure := lowDecadeGapPremiseK2_of_slabChain hchain hSlab
  ray_enclosure := hRay

end BuchstabSwitchingK2.External
