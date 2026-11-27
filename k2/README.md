# BuchstabSwitchingK2 (`1 + 2`, Pure GRH + Unconditional Kernel)

Lean 4 / Mathlib formalization and zero-float 90-digit interval certification for pure-GRH
and unconditional kernel `1 + 2` results (`AllEvenPrimePlusAlmostPrime 2`), completely free of
beyond-$\sqrt{N}$ or sub-$\sqrt{N}$ cancellation conjectures.

## Toolchain & Upstream GRH Pin

- **Lean:** `leanprover/lean4:v4.36.0` (`lean-toolchain`)
- **Mathlib:** `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`lakefile.toml`, `lake-manifest.json`;
  zero `native_decide` anywhere in the codebase)
- **Pinned GRH Statement:** `DirichletLNonvanishingRightOfHalf` is copied verbatim in
  [`Challenge.lean`](Challenge.lean), [`DirichletGRH.lean`](BuchstabSwitchingK2/External/CharacterSums/DirichletGRH.lean),
  and [`CitedPremisesK2.lean`](BuchstabSwitchingK2/External/CitedPremisesK2.lean) from
  [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207` (`grh-compact/src/Statements.lean`), where
  `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` is proved.
  [`AxiomsCheckK2.lean`](AxiomsCheckK2.lean) verifies definitional agreement (`Iff.rfl`) across all
  five challenge predicates (`AllEvenPrimePlusAlmostPrime`, `DirichletLNonvanishingRightOfHalf`,
  `DirichletLZerosOnLine`, `PrimitiveDirichletLZerosOnLine`, and `RiemannZetaZerosOnLine`).

## Pure-GRH & Unconditional Kernel Scope

- **Unconditional Foundations (`BuchstabSwitchingK2/Core/`, `Sieve/`, `External/`)**:
  - Chen `1 + 2` combinatorial switching (`switchingBalance1p2`, `varWeightSwitchingBalance1p2`,
    `quadAbstractBalance`), real-to-rational density transfers (`RealToRatBridge.lean`,
    `PureGRHShowcaseK2.lean`), and kernel-proved parity/dual-indistinguishability barriers
    (`Barriers.adversarial_*_balance_nonpos`);
  - Unconditional multiplicative large sieve (`multiplicativeLargeSieve`), smoothed bilinear
    dispersion eliminating the $B_N$ parity error above $10^{50}$ (`smoothedBilinearDispersion`),
    Selberg $\Lambda^2$ / $L^1$ bounds (`SelbergL1Cancellation.lean`), and primitive-character
    1D explicit-formula reductions (`CitedPremisesK2.lean`, `KernelSieveAssemblyK2.lean`).
- **Certified Pure-GRH `1 + 2` Rays (`PureGRHShowcaseK2.lean`, `scripts/certify_pure_grh_1p2.py`)**:
  - **Conservative Parzen (`δ = 1/25`, `κ₁ = 4`, `κ₀ = 11`, standard cited explicit-formula premise)**:
    - `chen_above_parzen_quad_smooth_pure_grh`: 2-step quadratic role-reversal LP ray for
      $N \ge 10^{316}$ (`net_lo = +0.001251`, disjoint-modulus `c_mult = 1`, `7,864` squarefree +
      non-squarefree multisets verified in exact `Fraction`);
    - `chen_above_parzen_varWeight_smooth_pure_grh`: 1-step variable-weight LP ray for
      $N \ge 10^{320}$ (`net_lo = +0.007149`);
    - `chen_above_1e390_parzen_smooth_pure_grh`: 1-step constant-weight ray for $N \ge 10^{390}$
      (`net_lo = +0.000318`);
  - **Flat-top plateau bump (`κ₁ = 9/10`, `κ₀ = 14/5`, explicitly conditioned on open calibration
    lemma `PlateauKernelCalibrationLemma`)**:
    - `chen_above_plateau_quad_of_calibration`: 2-step quadratic role-reversal LP ray for
      $N \ge 10^{280}$ (`net_lo = +0.000216`);
    - `chen_above_plateau_varWeight_of_calibration`: 1-step variable-weight LP ray for
      $N \ge 10^{284}$ (`net_lo = +0.008941`);
    - `chen_above_plateau_const_of_calibration` / `chen_above_1e344_plateau_smooth_pure_grh`:
      1-step constant-weight ray for $N \ge 10^{344}$ (`net_lo = +0.001777`);
  - **Sharp-cutoff & general contour corollaries**: `chen_above_1e1668_sharp_grh` ($N \ge 10^{1668}$),
    `chen_above_1e325_smooth_pure_grh`, `chen_above_varWeight_of_primitive_contour_grh`, and
    `chen_above_quad_of_primitive_contour_grh`.
- **Full-Range Reduction Interface (`Main.lean`, `comparator/ChallengeK2Reduction.lean`)**:
  - `even_eq_prime_add_omegaMult_le_two` & `all_even_one_plus_two_of_premises` reduce full
    `AllEvenPrimePlusAlmostPrime 2` (`N ≥ 4`) to `ExternalPremisesK2`. Notice that without
    additional distribution inputs, the low finite gap `[4 * 10^18, ~10^300)` remains open under
    pure GRH + linear/quadratic switching cones.

## Verification

```sh
lake exe cache get
lake build Challenge BuchstabSwitchingK2
lake env lean AxiomsCheckK2.lean
python3 scripts/quick_verify.py
python3 scripts/certify_pure_grh_1p2.py
bash comparator/run_comparator.sh
```

All library theorems depend strictly on `[propext, Classical.choice, Quot.sound]` (`[propext]`
on decidable ray-certificate checks); `sorryAx` appears only on the standalone challenge signature
`_root_.all_even_one_plus_two`.
