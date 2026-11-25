# Contributing to `buchstab-switching`

Pull requests and independent verification audits are welcome, especially toward discharging
the external analytic modules in `BuchstabSwitching/External/` against Mathlib.

## Verification Standards

1. **Zero `sorry` and standard axioms only**:
   Every merged Lean module must compile under `lake build` with zero `sorry`, zero `admit`,
   zero `axiom` declarations, and `#print axioms BuchstabSwitching.even_eq_prime_add_omegaMult_le_three`
   reporting only `[propext, Quot.sound, Classical.choice]`.
2. **Modular premise replacement**:
   To discharge an external premise, prove the target `Prop` inside its subfolder under
   `BuchstabSwitching/External/` (`FiniteVerification/`, `CharacterSums/`,
   `MultiplicativeBounds/`, `LinearSieve/`) and supply it when constructing
   `External.ExternalPremises`.
3. **Zero-float certificate discipline**:
   All numeric sieve verification scripts under `scripts/sieve_cert/` must use only
   outward-rounded `decimal.Decimal`, `fractions.Fraction`, and exact `int` arithmetic.
   Run `python3 scripts/quick_verify.py` before opening a PR.
