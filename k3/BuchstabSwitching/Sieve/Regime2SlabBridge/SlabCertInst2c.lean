import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c1
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c2
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c3
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c4
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c5
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2c6

/-!
# Regime `2c` Slab Bridge Instantiation Aggregator (`66` Slabs)

Combines `allSlabs2c1_bridges_inst`..`allSlabs2c6_bridges_inst` (`6 × 11 = 66` slabs)
symbolically via `List.take_append_drop 11` to discharge `External.SlabCertBridge` on all
`66` Regime `2c` slabs (`BuchstabSwitching.allSlabs.drop 61`).
-/

namespace BuchstabSwitching.SieveInst

private lemma drop_61_eq_append {α : Type*} (l : List α) :
    l.drop 61 = (l.drop 61).take 11 ++ (l.drop 72).take 11 ++ (l.drop 83).take 11 ++
      (l.drop 94).take 11 ++ (l.drop 105).take 11 ++ l.drop 116 := by
  have s1 : l.drop 61 = (l.drop 61).take 11 ++ l.drop 72 := by
    simpa [List.drop_drop] using (List.take_append_drop 11 (l.drop 61)).symm
  have s2 : l.drop 72 = (l.drop 72).take 11 ++ l.drop 83 := by
    simpa [List.drop_drop] using (List.take_append_drop 11 (l.drop 72)).symm
  have s3 : l.drop 83 = (l.drop 83).take 11 ++ l.drop 94 := by
    simpa [List.drop_drop] using (List.take_append_drop 11 (l.drop 83)).symm
  have s4 : l.drop 94 = (l.drop 94).take 11 ++ l.drop 105 := by
    simpa [List.drop_drop] using (List.take_append_drop 11 (l.drop 94)).symm
  have s5 : l.drop 105 = (l.drop 105).take 11 ++ l.drop 116 := by
    simpa [List.drop_drop] using (List.take_append_drop 11 (l.drop 105)).symm
  have p45 : l.drop 94 = (l.drop 94).take 11 ++ ((l.drop 105).take 11 ++ l.drop 116) :=
    s4.trans (congrArg _ s5)
  have p35 : l.drop 83 = (l.drop 83).take 11 ++
      ((l.drop 94).take 11 ++ ((l.drop 105).take 11 ++ l.drop 116)) :=
    s3.trans (congrArg _ p45)
  have p25 : l.drop 72 = (l.drop 72).take 11 ++ ((l.drop 83).take 11 ++
      ((l.drop 94).take 11 ++ ((l.drop 105).take 11 ++ l.drop 116))) :=
    s2.trans (congrArg _ p35)
  have p15 : l.drop 61 = (l.drop 61).take 11 ++ ((l.drop 72).take 11 ++ ((l.drop 83).take 11 ++
      ((l.drop 94).take 11 ++ ((l.drop 105).take 11 ++ l.drop 116)))) :=
    s1.trans (congrArg _ p25)
  simpa only [List.append_assoc] using p15

/-- Every Regime `2c` slab `c ∈ BuchstabSwitching.allSlabs.drop 61` satisfies
`External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs2c_bridges_inst (consts : External.CertifiedConstants) :
    ∀ c ∈ BuchstabSwitching.allSlabs.drop 61,
      External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [drop_61_eq_append, List.mem_append, List.mem_append, List.mem_append,
    List.mem_append, List.mem_append] at hc
  rcases hc with ((((hc1 | hc2) | hc3) | hc4) | hc5) | hc6
  · exact allSlabs2c1_bridges_inst consts c hc1
  · exact allSlabs2c2_bridges_inst consts c hc2
  · exact allSlabs2c3_bridges_inst consts c hc3
  · exact allSlabs2c4_bridges_inst consts c hc4
  · exact allSlabs2c5_bridges_inst consts c hc5
  · exact allSlabs2c6_bridges_inst consts c hc6

end BuchstabSwitching.SieveInst
