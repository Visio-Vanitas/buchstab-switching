# Contributing to `buchstab-switching` (`on-dev`)

Pull requests and independent verification audits are welcome. All PRs discharging the remaining
classical analytic lemmas in `BuchstabSwitching/External/` should target the **`on-dev`** branch
(`leanprover/lean4:v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).

## Open Formalization Targets on `on-dev`

Regime 2 (`127/127` slabs), Regime 3 (`120` ray strips), closed `(H*)`, `BuchstabSeriesPremise`
(`buchstabSeriesPremise_proved`), and `RobinOmegaBound` (`robinOmegaBound_holds`, PR `#4`) are
already proved unconditionally in Lean 4.

> **Out of Scope (`SmallEvenPremise`)**: `External/FiniteVerification/SmallEven.lean`
> (`4 ≤ N < 4 * 10^18` distributed binary prime verification, Oliveira e Silva–Herzog–Pardi 2014)
> is intentionally retained as the sole external computational table premise and is **excluded**
> from formalization PRs on `on-dev`.

| Field / Target | Interface Module | Mathematical Goal |
| :--- | :--- | :--- |
| `js_ap : JSLemma51Premise consts.li2` | `External/CharacterSums/DirichletGRH.lean` | Prove Grenié–Molteni (2019, Cor. 1) / Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 5.1) explicit AP bound from `DirichletLNonvanishingRightOfHalf` |
| `schoenfeld : SchoenfeldPrimePremise consts.li2` | `External/SchoenfeldRH/PrimeCountingRH.lean` | Prove Schoenfeld (1976, Cor. 1) explicit RH bound `\|π(x) - li(x)\| ≤ √x log x / (8π)` (`x ≥ 2657`) from `DirichletLNonvanishingRightOfHalf` |
| `mertens : MertensPrimeSumPremise consts.M0` | `External/MertensSums/ReciprocalPrimeSums.lean` | Prove explicit Mertens reciprocal-prime sum bounds (`jsMertensLoErr` / `jsMertensHiErr`, JS Lemma 3.2 & BJS Lemmas 16–17) |
| `euler_v : EulerProductVPremise consts.U_c consts.eNegGamma` | `External/EulerProductV/ProductAsymptotic.lean` | Prove unconditional BJS (`arXiv:2207.09452v6`, Lemma 38 `vjlem`) shifted-prime Euler product asymptotic `V_N(⌈x⌉)` (`x ≥ 285`) |
| `consts : CertifiedConstants` | `External/NumericalConstants/ExplicitConstants.lean` | Construct a concrete `CertifiedConstants` inhabitant with proved rational interval bounds for `γ`, `e^γ`, `e^{-γ}`, `M_0`, `C_{2,twin}`, `U_c`, `H_0`, `li(2)`, `α_0`, `H_σ`, `C_J`, `H̃`, `log 2`, `e^2` |

To discharge a target:
1. Keep the existing `def <TargetPremise> : Prop` signature unchanged in its subfolder under
   `BuchstabSwitching/External/` and prove `theorem <target>_holds : <TargetPremise>` (splitting
   helper files `<= 750` lines inside that subfolder as in `External/RobinOmega/`).
2. Remove the corresponding field from `External.ClassicalBasicLemmas` in `External/Bridge.lean`,
   supply `<target>_holds` in `External.externalPremises_of_classical`, update `#print axioms` in
   `AxiomsCheckK3.lean` / `Sieve/AxiomsAudit.lean`, and mirror the signature removal in
   `comparator/ChallengeK3Reduction.lean`.

## Verification Standards & Fast Local Testing

1. **Zero `sorry`, zero `native_decide`, and standard axioms only**:
   Every merged Lean module (`<= 750` lines per file, LF line endings) must compile under
   `lake build --wfail` with zero `sorry`, zero `admit`, zero `axiom` declarations, zero
   `native_decide`, and `#print axioms` reporting only `[propext, Classical.choice, Quot.sound]`.
2. **Fast local compilation workflow**:
   - **Subfolder iteration (~5–30s)**: None of the 5 target subfolders above import
     `SlabCertInst*`, so during development run:
     ```bash
     cd k3 && lake exe cache get
     lake build --wfail BuchstabSwitching.External.<Subfolder>.<Module>
     ```
   - **Full end-to-end integration (~2–3 min on 16–24 GB machines)**: Merge your branch locally
     with `origin/lean-v4.36.0-native` (which accelerates only the 27 existing finite-certificate
     shards via `native_decide` while keeping `External/` pure-kernel) to run
     `lake build --wfail BuchstabSwitching`, `lake env lean AxiomsCheckK3.lean`, and
     `lake env lean BuchstabSwitching/Sieve/AxiomsAudit.lean`, then run `python3 -I scripts/quick_verify.py`
     on your clean `on-dev` branch before opening a PR.
3. **Zero-float certificate & binary-witness discipline**:
   All numeric sieve verification scripts under `scripts/sieve_cert/` must use only
   outward-rounded `decimal.Decimal` (with global `Inexact`/`Rounded` traps armed),
   `fractions.Fraction`, and exact `int` arithmetic. If modifying slab certificates, regenerate
   `Data.lean` (`python3 scripts/generate_lean_data.py`) and the 12 binary `Dyadic` witness
   shards (`python3 -m scripts.sieve_cert.slab_witness_export`), and run
   `python3 scripts/quick_verify.py` before opening a PR.
