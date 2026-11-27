import BuchstabSwitching.External.FiniteVerification.SmallEven
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.SchoenfeldRH.PrimeCountingRH
import BuchstabSwitching.External.RobinOmega.PrimeFactorCount
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.EulerProductV.EulerProductProof
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.NumericalConstants.CanonicalConstants
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEnclosure
import BuchstabSwitching.External.LinearSieve.AsymptoticRayEnclosure
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst

/-!
# Bundled External Analytic Bridge (`ExternalPremises`)

Combines the three independent external premise interfaces (finite initial check,
finite-slab GRH sieve enclosure, and asymptotic linear-sieve ray enclosure) into a single
`Prop` structure consumed by `BuchstabSwitching/Main.lean`.

Also provides `ClassicalBasicLemmas`, gathering the four remaining classical/computational
external premises (`SmallEvenPremise`, `JSLemma51Premise canonicalLi2`,
`SchoenfeldPrimePremise canonicalLi2`, and `MertensPrimeSumPremise meisselMertensConst`),
together with `externalPremises_of_classical`, which discharges `ExternalPremises` through
`robinOmegaBound_holds` (`RobinOmega/PrimeFactorCount.lean`), `canonicalConstants`
(`NumericalConstants/CanonicalConstants.lean`),
`eulerProductVPremise_of_schoenfeld_and_mertens` (`EulerProductV/EulerProductProof.lean`),
the kernel-instantiated `127`-slab bridge (`SlabCertInst`), and the `L = 120` asymptotic ray
bridge (`RayCertInst`). No custom `axiom` declarations are used anywhere in this project.
-/

namespace BuchstabSwitching.External

/-- Complete bundle of unformalized analytic and computational inputs for the conditional
`Ω(m) ≤ 3` shifted prime theorem. -/
structure ExternalPremises : Prop where
  small_even : SmallEvenPremise
  slab_enclosure : SlabSieveEnclosurePremise
  ray_enclosure : AsymptoticRayEnclosurePremise

/-- Consolidated classical/computational premise bundle across the four remaining independent
external premises (`SmallEvenPremise`, `JSLemma51Premise canonicalLi2`,
`SchoenfeldPrimePremise canonicalLi2`, and `MertensPrimeSumPremise meisselMertensConst`).
`RobinOmegaBound` (`robinOmegaBound_holds`), `CertifiedConstants` (`canonicalConstants`),
`EulerProductVPremise` (`eulerProductVPremise_of_schoenfeld_and_mertens`), `BuchstabSeries`
(`buchstabSeriesPremise_proved`), closed-interval `(H*)`, and all Regime 2 (`127/127` slabs)
and Regime 3 (`L = 120` ray strips) sieve certificates are discharged internally. -/
structure ClassicalBasicLemmas : Prop where
  small_even : SmallEvenPremise
  js_ap : JSLemma51Premise canonicalLi2
  schoenfeld : SchoenfeldPrimePremise canonicalLi2
  mertens : MertensPrimeSumPremise meisselMertensConst

/-- Discharges `ExternalPremises` from `ClassicalBasicLemmas` via `robinOmegaBound_holds`,
`canonicalConstants`, `eulerProductVPremise_of_schoenfeld_and_mertens`, and the formalized
Regime 2 (`127`-slab) and Regime 3 (`L = 120` ray) sieve bridges. -/
theorem externalPremises_of_classical
    (hCls : ClassicalBasicLemmas) :
    ExternalPremises :=
  have hli2 : (1 / 3 : ℝ) < canonicalConstants.li2 ∧ canonicalConstants.li2 < 3 :=
    ⟨by linarith [canonicalConstants.li2_bounds.1], by linarith [canonicalConstants.li2_bounds.2]⟩
  { small_even := hCls.small_even
    slab_enclosure := slabSieveEnclosurePremise_of_sieveBridge
      ⟨⟨hCls.js_ap, hCls.schoenfeld, robinOmegaBound_holds, hli2⟩, hCls.mertens,
        BuchstabSwitching.SieveInst.allSlabs_bridges_inst canonicalConstants⟩
    ray_enclosure := asymptoticRayEnclosurePremise_of_canonical
      ⟨hCls.js_ap, hCls.schoenfeld, robinOmegaBound_holds, hli2⟩ hCls.mertens }

end BuchstabSwitching.External
