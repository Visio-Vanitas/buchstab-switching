import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2ab
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2a1
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2a2

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# Regime `2a` Slab Bridge Instantiation (`21` Slabs, Shard 1)

Verifies the first `21` slabs (`BuchstabSwitching.allSlabs.take 21`, Regime `2a`)
against the witness shards `witnesses2a1` (`10`) and `witnesses2a2` (`11`) using
sequential `1`-slab kernel checks (`Elab.async false`), and packages
`allSlabs2ab1_bridges_inst`.
-/

namespace BuchstabSwitching.SieveInst

/-- First `21` slabs of `BuchstabSwitching.allSlabs` (Regime `2a`). -/
def slabs2ab1 : List BuchstabSwitching.SlabCert :=
  BuchstabSwitching.allSlabs.take 21

/-- Concatenation of all `21` Regime `2a` witness records. -/
def witnesses2ab1 : List Slab2abWitness :=
  witnesses2a1 ++ witnesses2a2

/-- Zipped list of `(slab, witness)` pairs for Regime `2a`. -/
def pairs2ab1 : List (BuchstabSwitching.SlabCert × Slab2abWitness) :=
  slabs2ab1.zip witnesses2ab1

/-- Decidable batch check for Regime `2a` `(slab, witness)` pairs. -/
def checkBatch2ab1 (pairs : List (BuchstabSwitching.SlabCert × Slab2abWitness)) : Bool :=
  pairs.all (fun p => decide (p.1.X_hi ≤ 10 ^ 84) && checkSlab2abWitness p.1 p.2)

private lemma slabs2ab1_len : slabs2ab1.length = 21 := by native_decide

private lemma witnesses2ab1_len : witnesses2ab1.length = 21 := by native_decide

private lemma slabs2ab1_zip_len : slabs2ab1.length = witnesses2ab1.length := by native_decide

private lemma pairs2ab1_len : pairs2ab1.length = 21 := by
  simp [pairs2ab1, slabs2ab1_len, witnesses2ab1_len]

private lemma step_batch2ab1 {k n : ℕ}
    (h1 : checkBatch2ab1 ((pairs2ab1.drop k).take n) = true)
    (h2 : checkBatch2ab1 (pairs2ab1.drop (k + n)) = true) :
    checkBatch2ab1 (pairs2ab1.drop k) = true := by
  have hsplit : pairs2ab1.drop k = (pairs2ab1.drop k).take n ++ pairs2ab1.drop (k + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  unfold checkBatch2ab1 at h1 h2 ⊢
  rw [hsplit, List.all_append, h1, h2]
  rfl

private lemma b2ab1_0 : checkBatch2ab1 ((pairs2ab1.drop 0).take 1) = true := by native_decide
private lemma b2ab1_1 : checkBatch2ab1 ((pairs2ab1.drop 1).take 1) = true := by native_decide
private lemma b2ab1_2 : checkBatch2ab1 ((pairs2ab1.drop 2).take 1) = true := by native_decide
private lemma b2ab1_3 : checkBatch2ab1 ((pairs2ab1.drop 3).take 1) = true := by native_decide
private lemma b2ab1_4 : checkBatch2ab1 ((pairs2ab1.drop 4).take 1) = true := by native_decide
private lemma b2ab1_5 : checkBatch2ab1 ((pairs2ab1.drop 5).take 1) = true := by native_decide
private lemma b2ab1_6 : checkBatch2ab1 ((pairs2ab1.drop 6).take 1) = true := by native_decide
private lemma b2ab1_7 : checkBatch2ab1 ((pairs2ab1.drop 7).take 1) = true := by native_decide
private lemma b2ab1_8 : checkBatch2ab1 ((pairs2ab1.drop 8).take 1) = true := by native_decide
private lemma b2ab1_9 : checkBatch2ab1 ((pairs2ab1.drop 9).take 1) = true := by native_decide
private lemma b2ab1_10 : checkBatch2ab1 ((pairs2ab1.drop 10).take 1) = true := by native_decide
private lemma b2ab1_11 : checkBatch2ab1 ((pairs2ab1.drop 11).take 1) = true := by native_decide
private lemma b2ab1_12 : checkBatch2ab1 ((pairs2ab1.drop 12).take 1) = true := by native_decide
private lemma b2ab1_13 : checkBatch2ab1 ((pairs2ab1.drop 13).take 1) = true := by native_decide
private lemma b2ab1_14 : checkBatch2ab1 ((pairs2ab1.drop 14).take 1) = true := by native_decide
private lemma b2ab1_15 : checkBatch2ab1 ((pairs2ab1.drop 15).take 1) = true := by native_decide
private lemma b2ab1_16 : checkBatch2ab1 ((pairs2ab1.drop 16).take 1) = true := by native_decide
private lemma b2ab1_17 : checkBatch2ab1 ((pairs2ab1.drop 17).take 1) = true := by native_decide
private lemma b2ab1_18 : checkBatch2ab1 ((pairs2ab1.drop 18).take 1) = true := by native_decide
private lemma b2ab1_19 : checkBatch2ab1 ((pairs2ab1.drop 19).take 1) = true := by native_decide
private lemma b2ab1_20 : checkBatch2ab1 ((pairs2ab1.drop 20).take 1) = true := by native_decide

private lemma checkBatch2ab1_pairs2ab1 : checkBatch2ab1 pairs2ab1 = true := by
  have h21 : checkBatch2ab1 (pairs2ab1.drop 21) = true := by
    have hnil : pairs2ab1.drop 21 = [] := List.drop_eq_nil_of_le (by rw [pairs2ab1_len])
    rw [hnil]
    rfl
  have h20 := step_batch2ab1 b2ab1_20 h21
  have h19 := step_batch2ab1 b2ab1_19 h20
  have h18 := step_batch2ab1 b2ab1_18 h19
  have h17 := step_batch2ab1 b2ab1_17 h18
  have h16 := step_batch2ab1 b2ab1_16 h17
  have h15 := step_batch2ab1 b2ab1_15 h16
  have h14 := step_batch2ab1 b2ab1_14 h15
  have h13 := step_batch2ab1 b2ab1_13 h14
  have h12 := step_batch2ab1 b2ab1_12 h13
  have h11 := step_batch2ab1 b2ab1_11 h12
  have h10 := step_batch2ab1 b2ab1_10 h11
  have h9 := step_batch2ab1 b2ab1_9 h10
  have h8 := step_batch2ab1 b2ab1_8 h9
  have h7 := step_batch2ab1 b2ab1_7 h8
  have h6 := step_batch2ab1 b2ab1_6 h7
  have h5 := step_batch2ab1 b2ab1_5 h6
  have h4 := step_batch2ab1 b2ab1_4 h5
  have h3 := step_batch2ab1 b2ab1_3 h4
  have h2 := step_batch2ab1 b2ab1_2 h3
  have h1 := step_batch2ab1 b2ab1_1 h2
  have h0 := step_batch2ab1 b2ab1_0 h1
  simpa using h0

private theorem bridge2ab1_of_pair_ok (consts : External.CertifiedConstants)
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

/-- Every slab `c ∈ slabs2ab1` satisfies `External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs2ab1_bridges_inst (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0) :
    ∀ c ∈ slabs2ab1, External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hlen : i < pairs2ab1.length := by
    simpa [pairs2ab1_len, slabs2ab1_len] using hi
  have hpair_mem : pairs2ab1[i] ∈ pairs2ab1 := List.getElem_mem hlen
  have hok := List.all_eq_true.mp checkBatch2ab1_pairs2ab1 pairs2ab1[i] hpair_mem
  have hpair_eq : pairs2ab1[i] = (slabs2ab1[i], witnesses2ab1[i]'(by
      simpa [← slabs2ab1_zip_len] using hi)) := by
    simp only [pairs2ab1, List.getElem_zip]
    rfl
  rw [hpair_eq] at hok
  exact bridge2ab1_of_pair_ok consts hGRH hCls hMert hok

end BuchstabSwitching.SieveInst
