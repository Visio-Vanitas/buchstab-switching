import BuchstabSwitching.External.FiniteVerification.SmallEven
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEnclosure
import BuchstabSwitching.External.LinearSieve.AsymptoticRayEnclosure

/-!
# Bundled External Analytic Bridge (`ExternalPremises`)

Combines the three independent external premise interfaces (finite initial check,
finite-slab GRH sieve enclosure, and asymptotic linear-sieve ray enclosure) into a single
`Prop` structure consumed by `BuchstabSwitching/Main.lean`. No `axiom` declarations are
used anywhere in this project.
-/

namespace BuchstabSwitching.External

/-- Complete bundle of unformalized analytic and computational inputs for the conditional
`Ω(m) ≤ 3` shifted prime theorem. -/
structure ExternalPremises : Prop where
  small_even : SmallEvenPremise
  slab_enclosure : SlabSieveEnclosurePremise
  ray_enclosure : AsymptoticRayEnclosurePremise

end BuchstabSwitching.External
