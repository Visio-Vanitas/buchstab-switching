# Independent Verification Report (feat/one-plus-one-v436 @ a477ae93)

- **Verifier**: @Timtim00214
- **Date**: 2026-11-28 23:39:17 +08:00
- **Target Branch**: feat/one-plus-one-v436
- **Verified Commit**: a477ae933c0384b8a8318d1736e60fd07f865898
- **Toolchain**: Lean (version 4.36.0, x86_64-w64-windows-gnu, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release) \vert{}Lake version 5.0.0-src+611c117 (Lean version 4.36.0)

## 1. Zero-Float Script & Data Replay
``text
[1/4] AST ZERO-FLOAT & DECIMAL-TRAP AUDIT
  PASS scripts\certify_exceptional_short.py: ZERO_FLOAT_LEAKS=[]
  PASS scripts\certify_linnik_r.py: ZERO_FLOAT_LEAKS=[]
  PASS scripts\quick_verify.py: ZERO_FLOAT_LEAKS=[]
[2/4] ZERO-FLOAT CERTIFIER REPLAY & DATA CROSS-CHECK
  PASS certify_exceptional_short.py exact match with data/certify_exceptional_short_output.txt
  PASS certify_linnik_r.py exact match with data/certify_linnik_r_output.txt
[3/4] LEAN CERTIFICATES/DATA.LEAN CONSISTENCY
  PASS 15/15 CertifiedCell rows in Data.lean match certified v2 bounds (exact 10^-8 scale)
  PASS 6/6 LinnikCheckpointCell rows in Data.lean match certify_linnik_r_output.txt (v2 K=18)
[4/4] LEAN HYGIENE AUDIT
  PASS 10 Lean files clean (zero sorry/admit/axiom/native_decide/unsafe)
ALL 4 CHECKS PASSED.

```n
## 2. Lean 4 Build & Axioms Audit
```text
Build completed successfully (7412 jobs).
'OnePlusOne.hasLinnikRep_of_isGoldbachEven' depends on axioms: [propext, Quot.sound]
'OnePlusOne.exceptionalCount_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.exceptionalCount_eq_zero_of_empirical' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Arithmetic.major_arcs_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Arithmetic.ratio_2p_sub_1_le_pow_eighth' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Arithmetic.twin_prime_partial_product_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Arithmetic.totient_sq_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Arithmetic.dyadic_geom_sum_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Arithmetic.fouradic_geom_sum_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Certificates.certifiedCells_valid' does not depend on any axioms
'OnePlusOne.Certificates.certifiedCells_count' does not depend on any axioms
'OnePlusOne.Certificates.fouradic_16_rat_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Certificates.linnikCheckpointCells_valid' does not depend on any axioms
'OnePlusOne.Certificates.linnikCheckpointCells_count' does not depend on any axioms
'OnePlusOne.Certificates.linnik_tail_growth_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Exceptional.exceptional_all_range_of_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Exceptional.exceptional_all_range_of_fouradic' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Exceptional.fouradic_multiplier_le_16' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Exceptional.fouradic_of_parseval_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Exceptional.theorem_1A_of_fouradic' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.ShortInterval.one_lt_log_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.ShortInterval.short_interval_small_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.ShortInterval.exists_goldbach_of_weighted_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.ShortInterval.short_interval_all_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Linnik.hasLinnikRep_mono' depends on axioms: [propext]
'OnePlusOne.Linnik.binary_goldbach_bridge_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Linnik.all_even_exact_linnik_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.Linnik.all_even_linnik_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.theorem_1A_all_even_exceptional_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.theorem_1B_all_even_short_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.theorem_3A_all_even_exact_linnik_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'OnePlusOne.theorem_3_all_even_linnik_goldbach' depends on axioms: [propext, Classical.choice, Quot.sound]
```
