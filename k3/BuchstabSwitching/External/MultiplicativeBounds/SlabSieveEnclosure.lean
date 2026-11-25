import BuchstabSwitching.Sieve.OneStepSwitching
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.External.CharacterSums.DirichletGRH

/-!
# Multiplicative & Finite-Slab Sieve Enclosure Interface

States `SlabSieveEnclosurePremise`: under `DirichletLNonvanishingRightOfHalf`, each finite
slab `c ∈ allSlabs` enjoys a normalized lower bound on `switchingBalance N c.z c.y` at
least `(c.main_lb - c.err_ub) * scale` with `0 < scale`.

Discharging this premise against Mathlib splits naturally into:
1. Mertens `∑_{p < x} 1/p` & `V_N(z)` Euler-product bounds (`Rosser–Schoenfeld 1962`,
   `Johnston–Starichkova arXiv:2208.01229v3`);
2. Odd squarefree divisor counting `∑_{d ≤ X, 2 ∤ d} μ²(d) ≤ (4/π²) X + √X`;
3. Connecting `Sieve.BonferroniHybrid` and `Sieve.SelbergLambdaSq` (with `J_odd`/`J_full`)
   to the explicit `DirichletGRH` remainder bounds.
-/

namespace BuchstabSwitching.External

/-- Under `DirichletLNonvanishingRightOfHalf`, every slab `c ∈ allSlabs` encloses
`switchingBalance N c.z c.y ≥ (c.main_lb - c.err_ub) * scale` with positive normalization
`scale` (`|A_N|` on `2a/2b`, or `|A_N| * V_N(z)` on `2c`). -/
def SlabSieveEnclosurePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ c ∈ BuchstabSwitching.allSlabs, ∀ N : ℕ,
      Even N → c.X_lo ≤ N → N < c.X_hi →
      ∃ scale : ℚ, 0 < scale ∧
        (c.main_lb - c.err_ub) * scale ≤ BuchstabSwitching.switchingBalance N c.z c.y

end BuchstabSwitching.External
