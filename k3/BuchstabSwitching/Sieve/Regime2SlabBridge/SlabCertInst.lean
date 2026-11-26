import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2ab
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c

/-!
# Complete Regime `2` Slab Bridge Instantiation (`127` Slabs)

Combines `allSlabs2ab_bridges_inst` (`61` Regime `2a`/`2b` slabs) and
`allSlabs2c_bridges_inst` (`66` Regime `2c` slabs) symbolically via
`(List.take_append_drop 61 BuchstabSwitching.allSlabs).symm` to prove
`External.SlabCertBridge` for every slab `c ∈ BuchstabSwitching.allSlabs`.
-/

namespace BuchstabSwitching.SieveInst

/-- Every slab `c ∈ BuchstabSwitching.allSlabs` (`127/127` slabs covering
`[4 * 10^18, 10^600)`) satisfies `External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs_bridges_inst (consts : External.CertifiedConstants) :
    ∀ c ∈ BuchstabSwitching.allSlabs, External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [(List.take_append_drop 61 BuchstabSwitching.allSlabs).symm, List.mem_append] at hc
  rcases hc with hab | h2c
  · exact allSlabs2ab_bridges_inst consts c hab
  · exact allSlabs2c_bridges_inst consts c h2c

end BuchstabSwitching.SieveInst
