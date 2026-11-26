import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2ab1
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2ab2
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInst2ab3

/-!
# Regime `2a`/`2b` Slab Bridge Aggregator (`61` Slabs)

Aggregates `allSlabs2ab1_bridges_inst` (`21` slabs), `allSlabs2ab2_bridges_inst` (`20` slabs),
and `allSlabs2ab3_bridges_inst` (`20` slabs) into `allSlabs2ab_bridges_inst` covering
`BuchstabSwitching.allSlabs.take 61` via pure symbolic list identities.
-/

namespace BuchstabSwitching.SieveInst

private lemma take_61_eq_append {α : Type*} (l : List α) :
    l.take 61 = l.take 21 ++ (l.drop 21).take 20 ++ (l.drop 41).take 20 := by
  have h1 : l.take 61 = l.take 21 ++ (l.drop 21).take 40 := by
    have h := (List.take_append_drop 21 (l.take 61)).symm
    rw [List.take_take, List.drop_take] at h
    simpa using h
  have h2 : (l.drop 21).take 40 = (l.drop 21).take 20 ++ (l.drop 41).take 20 := by
    have h := (List.take_append_drop 20 ((l.drop 21).take 40)).symm
    rw [List.take_take, List.drop_take, List.drop_drop] at h
    simpa using h
  rw [h1, h2, List.append_assoc]

/-- Every slab `c ∈ BuchstabSwitching.allSlabs.take 61` satisfies
`External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs2ab_bridges_inst (consts : External.CertifiedConstants) :
    ∀ c ∈ BuchstabSwitching.allSlabs.take 61, External.SlabCertBridge consts.li2 consts c := by
  intro c hc hGRH hCls hMert
  rw [take_61_eq_append, List.mem_append, List.mem_append] at hc
  rcases hc with (hc1 | hc2) | hc3
  · exact allSlabs2ab1_bridges_inst consts hGRH hCls hMert c hc1 hGRH hCls hMert
  · exact allSlabs2ab2_bridges_inst consts hGRH hCls hMert c hc2 hGRH hCls hMert
  · exact allSlabs2ab3_bridges_inst consts hGRH hCls hMert c hc3 hGRH hCls hMert

end BuchstabSwitching.SieveInst
