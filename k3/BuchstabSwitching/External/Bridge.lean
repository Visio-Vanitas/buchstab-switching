import BuchstabSwitching.External.FiniteVerification.SmallEven
import BuchstabSwitching.External.CharacterSums.DirichletGRH
import BuchstabSwitching.External.SchoenfeldRH.PrimeCountingRH
import BuchstabSwitching.External.RobinOmega.PrimeFactorCount
import BuchstabSwitching.External.MertensSums.ReciprocalPrimeSums
import BuchstabSwitching.External.EulerProductV.ProductAsymptotic
import BuchstabSwitching.External.BuchstabSeries.DelayDiffEqIdentity
import BuchstabSwitching.External.NumericalConstants.ExplicitConstants
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEnclosure
import BuchstabSwitching.External.LinearSieve.AsymptoticRayEnclosure
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst

/-!
# Bundled External Analytic Bridge (`ExternalPremises`)

Combines the three independent external premise interfaces (finite initial check,
finite-slab GRH sieve enclosure, and asymptotic linear-sieve ray enclosure) into a single
`Prop` structure consumed by `BuchstabSwitching/Main.lean`.

Also provides `ClassicalBasicLemmas`, gathering the five remaining classical/computational
external premises (`SmallEvenPremise`, `JSLemma51Premise`, `SchoenfeldPrimePremise`,
`MertensPrimeSumPremise`, and unconditional BJS v6 Lemma 38 `EulerProductVPremise`), together
with `externalPremises_of_classical`, which discharges `ExternalPremises` through the
unconditionally proved `robinOmegaBound_holds` (`RobinOmega/PrimeFactorCount.lean`), the
kernel-instantiated `127`-slab bridge (`SlabCertInst`), and the `L = 120` asymptotic ray bridge
(`RayCertInst`). No custom `axiom` declarations are used anywhere in this project.
-/

namespace BuchstabSwitching.External

/-- Complete bundle of unformalized analytic and computational inputs for the conditional
`Ω(m) ≤ 3` shifted prime theorem. -/
structure ExternalPremises : Prop where
  small_even : SmallEvenPremise
  slab_enclosure : SlabSieveEnclosurePremise
  ray_enclosure : AsymptoticRayEnclosurePremise

/-- Consolidated classical/computational premise bundle across the five remaining independent
external premises (`SmallEvenPremise`, `JSLemma51Premise`, `SchoenfeldPrimePremise`,
`MertensPrimeSumPremise`, and unconditional BJS v6 Lemma 38 `EulerProductVPremise`).
`RobinOmegaBound` (`robinOmegaBound_holds`), `BuchstabSeries` (`buchstabSeriesPremise_proved`),
closed-interval `(H*)`, and all Regime 2 (`127/127` slabs) and Regime 3 (`L = 120` ray strips)
sieve certificates are discharged internally. -/
structure ClassicalBasicLemmas (consts : CertifiedConstants) : Prop where
  small_even : SmallEvenPremise
  js_ap : JSLemma51Premise consts.li2
  schoenfeld : SchoenfeldPrimePremise consts.li2
  mertens : MertensPrimeSumPremise consts.M0
  euler_v : EulerProductVPremise consts.U_c consts.eNegGamma

/-- Discharges `ExternalPremises` from `ClassicalBasicLemmas consts` via `robinOmegaBound_holds`
and the formalized Regime 2 (`127`-slab) and Regime 3 (`L = 120` ray) sieve bridges. -/
theorem externalPremises_of_classical
    {consts : CertifiedConstants} (hCls : ClassicalBasicLemmas consts) :
    ExternalPremises :=
  have hli2 : (1 / 3 : ℝ) < consts.li2 ∧ consts.li2 < 3 :=
    ⟨by linarith [consts.li2_bounds.1], by linarith [consts.li2_bounds.2]⟩
  { small_even := hCls.small_even
    slab_enclosure := slabSieveEnclosurePremise_of_sieveBridge
      ⟨⟨hCls.js_ap, hCls.schoenfeld, robinOmegaBound_holds, hli2⟩, hCls.mertens,
        BuchstabSwitching.SieveInst.allSlabs_bridges_inst consts⟩
    ray_enclosure := asymptoticRayEnclosurePremise_of_sieveBridge
      ⟨⟨hCls.js_ap, hCls.schoenfeld, robinOmegaBound_holds, hli2⟩, hCls.mertens, hCls.euler_v⟩ }

end BuchstabSwitching.External
