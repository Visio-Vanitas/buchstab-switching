# External Analytic Premises Directory

`BuchstabSwitching/Main.lean` proves `BuchstabSwitching.even_eq_prime_add_omegaMult_le_three` and
`BuchstabSwitching.all_even_one_plus_three_of_premises` with **zero `sorry`** and **only the three
standard Lean axioms** (`propext`, `Quot.sound`, `Classical.choice`), parameterized explicitly over
the analytic and computational interfaces collected in this directory.

The directory is organized into **8 independent classical lemma subfolders**, **2 sieve-enclosure
bridges**, and the top-level bundle `Bridge.lean`:

## 1. Independent Classical Lemma Subfolders (8 modules)

| Subfolder / Module | Key Interfaces & Proved Lemmas | Literature Reference |
| :--- | :--- | :--- |
| `FiniteVerification/SmallEven.lean` | `SmallEvenPremise`, `finiteCutoff` (`4 ≤ N < 4 * 10^18`) | Oliveira e Silva, Herzog, Pardi, *Math. Comp.* **83** (2014), 2033–2060 |
| `CharacterSums/DirichletGRH.lean` | `DirichletLNonvanishingRightOfHalf`, `ExplicitPrimeInAPPremise`, `primeCountingAP`, `offsetLogIntegral`, `c_pi`, `GrenieMolteniAPBound`, `JSLemma51Premise` | `https://github.com/lsernau/grh-lean@72fead1` (`grh-compact/src/Statements.lean`); Grenié–Molteni, *J. Number Theory* **200** (2019), Cor. 1 & *Ramanujan J.* **49** (2019), 535–548; Johnston–Starichkova (`arXiv:2208.01229v3` [JS v3], Lemma 5.1) |
| `SchoenfeldRH/PrimeCountingRH.lean` | `primeCounting`, `logIntegral`, `SchoenfeldRHBound`, `SchoenfeldPrimePremise`, `RosserSchoenfeldPiBound` | Schoenfeld, *Math. Comp.* **30** (1976), Cor. 1 (`x ≥ 2657`); Rosser–Schoenfeld, *Illinois J. Math.* **6** (1962), Cor. 1, eq. (3.6) |
| `RobinOmega/PrimeFactorCount.lean` | `RobinOmegaBound`, `omegaUpperFn`, and proved monotonicity / antitonicity lemmas | Robin, *Acta Arith.* **42** (1983), Théorème 11 |
| `MertensSums/ReciprocalPrimeSums.lean` | `jsMertensLoErr`, `jsMertensHiErr`, `MertensPrimeSumPremise`, `RosserSchoenfeldChebyshevBound` | Johnston–Starichkova (`arXiv:2208.01229v3` [JS v3], Lemma 3.2); Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6` [BJS v6], Lemmas 16–17); Rosser–Schoenfeld (1962, Thm. 1, eq. (3.2)) |
| `EulerProductV/ProductAsymptotic.lean` | `VN`, `deltaV_bjs`, `deltaV_bs`, `UN_ratio`, `EulerProductVPremise`, `EulerProductVGRHPremise`, `VN_pos_of_even`, `VN_le_one`, `UN_ratio_ge_Uc` | Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6` [BJS v6], Lemma 38 `vjlem`); Bordignon–Starichkova (`arXiv:2211.08844v1` [BS v1], Lemma 11 `vjlem`) |
| `BuchstabSeries/DelayDiffEqIdentity.lean` & `AdjointEvaluation.lean` | `BuchstabSeriesPremise`, `hasSum_odd`, `hasSum_even`, `buchstabf_le_one_sub_sum`, `one_add_sum_le_buchstabF`, and **unconditional Lean proof** `buchstabSeriesPremise_proved` | Nathanson, *Additive Number Theory: The Classical Bases*, GTM 164 (1996), Ch. 9, Thm. 9.4; Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6` [BJS v6], §2.1) |
| `NumericalConstants/ExplicitConstants.lean` | `CertifiedConstants`, `cPi`, `epdNorm`, `liRatioUb`, `vFullLb`, `rayErrorSum` (integer-cutoff `z_int_lb` aligned), `TwoVarMertensExcursion`, `FiniteMertensExcursionPremise`, `SlabNumericCertPremise`, `RayNumericCertPremise` | `k3/scripts/sieve_cert/` (`constants.py`, `primes_and_mertens.py`, `regime_slabs.py`, `regime_asymptotic.py`) |

## 2. Sieve-Enclosure Bridges & Top-Level Bundle (2 bridges + `Bridge.lean`)

| Subfolder / Module | Mathematical Role | Formal Sieve & Literature Links |
| :--- | :--- | :--- |
| `MultiplicativeBounds/SlabSieveEnclosure.lean` & `SlabSieveEngineWiring.lean` | `SlabSieveEnclosurePremise`, constructive derivation `slabSieveEnclosurePremise_of_sieveBridge` from `SlabAnalyticPremises`, plus `Regime2abSlabBridge.of_sieveEngines` and `Regime2cSlabBridge.of_sieveEngines` wiring all Regime `2a`/`2b`/`2c` lower, slice, and `q²` engines | `Sieve/Regime2SlabBridge.lean` (`regime2ab_switchingBalance_lb`, `regime2c_switchingBalance_lb`), `Sieve/BrunBlockSieve.lean` (`brun_block_sieve_lower_bound`, `brun_block_omission_mono`), `Sieve/ShiftedPrimeRemainder.lean`; Rosser–Schoenfeld (1962); Johnston–Starichkova (`arXiv:2208.01229v3` [JS v3]) |
| `LinearSieve/AsymptoticRayEnclosure.lean` | `AsymptoticRayEnclosurePremise` plus `asymptoticRayEnclosurePremise_of_sieveBridge` for `N ≥ asymptoticCert.X_LS` (`10^600`), discharging `BuchstabSeriesPremise` (`buchstabSeriesPremise_proved`) and closed-interval `(H*)` over `Q0_100` (`closedHStarCond_Q0_100`) internally with `certifiedDecaySeq` (`C_2 ≤ 494`) | `Sieve/Regime3RayBridge.lean` (`regime3_ray_switchingBalance_lb_of_analytic`), `Sieve/LinearSieveBJS/CertifiedC2.lean`; Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6` [BJS v6], Thm. 6); Bordignon–Starichkova (`arXiv:2211.08844v1` [BS v1]) |
| `Bridge.lean` | Bundles `SmallEvenPremise`, `SlabSieveEnclosurePremise`, and `AsymptoticRayEnclosurePremise` into `ExternalPremises` | Top-level interface consumed by `BuchstabSwitching/Main.lean` |

Contributors wishing to eliminate an assumption can prove the corresponding `Prop` inside
its own subfolder and substitute the proof term into `ExternalPremises` (or via bridges such as
`slabSieveEnclosurePremise_of_sieveBridge`) without touching `Core/`, `Sieve/`, or `Certificates/`.
