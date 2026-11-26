import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c1
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c2

/-!
# Regime `2c` Slab Bridge Instantiation Aggregator (`66` Slabs)

Combines `allSlabs2c1_bridges_inst` (`33` slabs) and `allSlabs2c2_bridges_inst` (`33` slabs)
symbolically via `List.take_append_drop 33` to discharge `External.SlabCertBridge` on all
`66` Regime `2c` slabs (`BuchstabSwitching.allSlabs.drop 61`).
-/

namespace BuchstabSwitching.SieveInst

/-- Every Regime `2c` slab `c ∈ BuchstabSwitching.allSlabs.drop 61` satisfies
`External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs2c_bridges_inst (consts : External.CertifiedConstants) :
    ∀ c ∈ BuchstabSwitching.allSlabs.drop 61,
      External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [← List.take_append_drop 33 (BuchstabSwitching.allSlabs.drop 61), List.mem_append] at hc
  rcases hc with hc1 | hc2
  · exact allSlabs2c1_bridges_inst consts c hc1
  · exact allSlabs2c2_bridges_inst consts c hc2

end BuchstabSwitching.SieveInst
