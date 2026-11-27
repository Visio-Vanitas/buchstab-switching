import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2ab
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2b3
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2b4

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# Regime `2b3`/`2b4` Slab Bridge Instantiation (`20` Slabs)

Verifies the remaining `20` Regime `2b` slabs (`2b3` + `2b4`, i.e.,
`(BuchstabSwitching.allSlabs.drop 41).take 20`) against the machine-generated witness shards
`witnesses2b3` and `witnesses2b4` using isolated `1`-slab kernel checks
and packages `allSlabs2ab3_bridges_inst`.
-/

namespace BuchstabSwitching.SieveInst

/-- Regime `2b3` and `2b4` slabs (`20` slabs, indices `41..60` of `BuchstabSwitching.allSlabs`). -/
def slabs2ab3 : List BuchstabSwitching.SlabCert :=
  (BuchstabSwitching.allSlabs.drop 41).take 20

/-- Concatenation of the `20` Regime `2b3`/`2b4` witness records. -/
def witnesses2ab3 : List Slab2abWitness :=
  witnesses2b3 ++ witnesses2b4

/-- Zipped list of `(slab, witness)` pairs for Regimes `2b3`/`2b4`. -/
def pairs2ab3 : List (BuchstabSwitching.SlabCert × Slab2abWitness) :=
  slabs2ab3.zip witnesses2ab3

/-- Decidable batch check for Regime `2b3`/`2b4` `(slab, witness)` pairs. -/
noncomputable def checkBatch2ab3 (pairs : List (BuchstabSwitching.SlabCert × Slab2abWitness)) : Bool :=
  pairs.all (fun p => decide (p.1.X_hi ≤ 10 ^ 84) && checkSlab2abWitness p.1 p.2)

private lemma slabs2ab3_len : slabs2ab3.length = 20 := by decide

private lemma witnesses2ab3_len : witnesses2ab3.length = 20 := by decide

private lemma slabs2ab3_zip_len : slabs2ab3.length = witnesses2ab3.length := by decide

private lemma pairs2ab3_len : pairs2ab3.length = 20 := by
  simp [pairs2ab3, slabs2ab3_len, witnesses2ab3_len]

private lemma step_batch2ab3 {k n : ℕ}
    (h1 : checkBatch2ab3 ((pairs2ab3.drop k).take n) = true)
    (h2 : checkBatch2ab3 (pairs2ab3.drop (k + n)) = true) :
    checkBatch2ab3 (pairs2ab3.drop k) = true := by
  have hsplit : pairs2ab3.drop k = (pairs2ab3.drop k).take n ++ pairs2ab3.drop (k + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  unfold checkBatch2ab3 at h1 h2 ⊢
  rw [hsplit, List.all_append, h1, h2]
  rfl

private lemma b2ab3_0 : checkBatch2ab3 ((pairs2ab3.drop 0).take 1) = true := by decide
private lemma b2ab3_1 : checkBatch2ab3 ((pairs2ab3.drop 1).take 1) = true := by decide
private lemma b2ab3_2 : checkBatch2ab3 ((pairs2ab3.drop 2).take 1) = true := by decide
private lemma b2ab3_3 : checkBatch2ab3 ((pairs2ab3.drop 3).take 1) = true := by decide
private lemma b2ab3_4 : checkBatch2ab3 ((pairs2ab3.drop 4).take 1) = true := by decide
private lemma b2ab3_5 : checkBatch2ab3 ((pairs2ab3.drop 5).take 1) = true := by decide
private lemma b2ab3_6 : checkBatch2ab3 ((pairs2ab3.drop 6).take 1) = true := by decide
private lemma b2ab3_7 : checkBatch2ab3 ((pairs2ab3.drop 7).take 1) = true := by decide
private lemma b2ab3_8 : checkBatch2ab3 ((pairs2ab3.drop 8).take 1) = true := by decide
private lemma b2ab3_9 : checkBatch2ab3 ((pairs2ab3.drop 9).take 1) = true := by decide
private lemma b2ab3_10 : checkBatch2ab3 ((pairs2ab3.drop 10).take 1) = true := by decide
private lemma b2ab3_11 : checkBatch2ab3 ((pairs2ab3.drop 11).take 1) = true := by decide
private lemma b2ab3_12 : checkBatch2ab3 ((pairs2ab3.drop 12).take 1) = true := by decide
private lemma b2ab3_13 : checkBatch2ab3 ((pairs2ab3.drop 13).take 1) = true := by decide
private lemma b2ab3_14 : checkBatch2ab3 ((pairs2ab3.drop 14).take 1) = true := by decide
private lemma b2ab3_15 : checkBatch2ab3 ((pairs2ab3.drop 15).take 1) = true := by decide
private lemma b2ab3_16 : checkBatch2ab3 ((pairs2ab3.drop 16).take 1) = true := by decide
private lemma b2ab3_17 : checkBatch2ab3 ((pairs2ab3.drop 17).take 1) = true := by decide
private lemma b2ab3_18 : checkBatch2ab3 ((pairs2ab3.drop 18).take 1) = true := by decide
private lemma b2ab3_19 : checkBatch2ab3 ((pairs2ab3.drop 19).take 1) = true := by decide

private lemma checkBatch2ab3_pairs2ab3 : checkBatch2ab3 pairs2ab3 = true := by
  have h20 : checkBatch2ab3 (pairs2ab3.drop 20) = true := by
    have hnil : pairs2ab3.drop 20 = [] := List.drop_eq_nil_of_le (by rw [pairs2ab3_len])
    rw [hnil]
    rfl
  have h19 := step_batch2ab3 b2ab3_19 h20
  have h18 := step_batch2ab3 b2ab3_18 h19
  have h17 := step_batch2ab3 b2ab3_17 h18
  have h16 := step_batch2ab3 b2ab3_16 h17
  have h15 := step_batch2ab3 b2ab3_15 h16
  have h14 := step_batch2ab3 b2ab3_14 h15
  have h13 := step_batch2ab3 b2ab3_13 h14
  have h12 := step_batch2ab3 b2ab3_12 h13
  have h11 := step_batch2ab3 b2ab3_11 h12
  have h10 := step_batch2ab3 b2ab3_10 h11
  have h9 := step_batch2ab3 b2ab3_9 h10
  have h8 := step_batch2ab3 b2ab3_8 h9
  have h7 := step_batch2ab3 b2ab3_7 h8
  have h6 := step_batch2ab3 b2ab3_6 h7
  have h5 := step_batch2ab3 b2ab3_5 h6
  have h4 := step_batch2ab3 b2ab3_4 h5
  have h3 := step_batch2ab3 b2ab3_3 h4
  have h2 := step_batch2ab3 b2ab3_2 h3
  have h1 := step_batch2ab3 b2ab3_1 h2
  have h0 := step_batch2ab3 b2ab3_0 h1
  simpa using h0

private theorem bridge2ab3_of_pair_ok (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {c : BuchstabSwitching.SlabCert} {w : Slab2abWitness}
    (hok : (decide (c.X_hi ≤ 10 ^ 84) && checkSlab2abWitness c w) = true) :
    External.SlabCertBridge consts.li2 consts c := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨hXhi, hw⟩
  intro _ _ _
  split_ifs
  exact checkSlab2abWitness_sound consts hGRH hCls hMert hw

/-- Every slab `c ∈ slabs2ab3` satisfies `External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs2ab3_bridges_inst (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0) :
    ∀ c ∈ slabs2ab3, External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hlen : i < pairs2ab3.length := by
    simpa [pairs2ab3_len, slabs2ab3_len] using hi
  have hpair_mem : pairs2ab3[i] ∈ pairs2ab3 := List.getElem_mem hlen
  have hok := List.all_eq_true.mp checkBatch2ab3_pairs2ab3 pairs2ab3[i] hpair_mem
  have hpair_eq : pairs2ab3[i] = (slabs2ab3[i], witnesses2ab3[i]'(by
      simpa [← slabs2ab3_zip_len] using hi)) := by
    simp only [pairs2ab3, List.getElem_zip]
    rfl
  rw [hpair_eq] at hok
  exact bridge2ab3_of_pair_ok consts hGRH hCls hMert hok

end BuchstabSwitching.SieveInst
