# Contributing to `buchstab-switching`

Pull requests and independent verification audits are welcome, especially toward discharging
the external analytic modules in `BuchstabSwitching/External/` against Mathlib.

## Verification Standards

1. **Zero `sorry`, zero `native_decide`, and standard axioms only**:
   Every merged Lean module (`<= 750` lines per file) must compile under `lake build` with zero
   `sorry`, zero `admit`, zero `axiom` declarations, zero `native_decide`, and both
   `lake env lean AxiomsCheckK3.lean` and `lake env lean BuchstabSwitching/Sieve/AxiomsAudit.lean`
   reporting only `[propext, Quot.sound, Classical.choice]` (including
   `all_even_one_plus_three_of_classical` and `even_eq_prime_add_omegaMult_le_three`).
2. **Modular premise replacement (`ClassicalBasicLemmas`)**:
   Regime 2 (`127/127` slabs), Regime 3 (`120` ray strips), `BuchstabSeries`, `RobinOmegaBound`,
   and closed `(H*)` are already discharged in Lean. To discharge one of the five remaining
   classical premises in `External.ClassicalBasicLemmas`, prove the target `Prop` inside its
   subfolder under `BuchstabSwitching/External/` (`FiniteVerification/`, `CharacterSums/`,
   `SchoenfeldRH/`, `MertensSums/`, `EulerProductV/`, `NumericalConstants/`) and supply it to
   `External.externalPremises_of_classical`.
3. **Zero-float certificate & binary-witness discipline**:
   All numeric sieve verification scripts under `scripts/sieve_cert/` must use only
   outward-rounded `decimal.Decimal` (with global `Inexact`/`Rounded` traps armed),
   `fractions.Fraction`, and exact `int` arithmetic. If modifying slab certificates, regenerate
   `Data.lean` (`python3 scripts/generate_lean_data.py`) and the 12 binary `Dyadic` witness
   shards (`python3 -m scripts.sieve_cert.slab_witness_export`), and run
   `python3 scripts/quick_verify.py` before opening a PR.
