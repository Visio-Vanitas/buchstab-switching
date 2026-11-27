import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2ab
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2b1
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2b2

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# Regime `2b1`/`2b2` Slab Bridge Instantiation (`20` Slabs, Shard 2)

Verifies the middle `20` Regime `2b` slabs in `(BuchstabSwitching.allSlabs.drop 21).take 20`
against the witness shards `witnesses2b1` (`10`) and `witnesses2b2` (`10`) using per-slab
`1`-slab kernel checks, and packages `allSlabs2ab2_bridges_inst`.
-/

namespace BuchstabSwitching.SieveInst

/-- Middle `20` slabs of `BuchstabSwitching.allSlabs` (`2b1` + `2b2`). -/
def slabs2ab2 : List BuchstabSwitching.SlabCert :=
  (BuchstabSwitching.allSlabs.drop 21).take 20

/-- Concatenation of the `20` witness records (`witnesses2b1 ++ witnesses2b2`). -/
def witnesses2ab2 : List Slab2abWitness :=
  witnesses2b1 ++ witnesses2b2

/-- Zipped list of `(slab, witness)` pairs for `2b1` + `2b2`. -/
def pairs2ab2 : List (BuchstabSwitching.SlabCert × Slab2abWitness) :=
  slabs2ab2.zip witnesses2ab2

/-- Decidable batch check for `2b1` + `2b2` `(slab, witness)` pairs. -/
def checkBatch2ab2 (pairs : List (BuchstabSwitching.SlabCert × Slab2abWitness)) : Bool :=
  pairs.all (fun p => decide (p.1.X_hi ≤ 10 ^ 84) && checkSlab2abWitness p.1 p.2)

private lemma slabs2ab2_len : slabs2ab2.length = 20 := by native_decide

private lemma witnesses2ab2_len : witnesses2ab2.length = 20 := by native_decide

private lemma slabs2ab2_zip_len : slabs2ab2.length = witnesses2ab2.length := by native_decide

private lemma pairs2ab2_len : pairs2ab2.length = 20 := by
  simp [pairs2ab2, slabs2ab2_len, witnesses2ab2_len]

private lemma step_batch2ab2 {k n : ℕ}
    (h1 : checkBatch2ab2 ((pairs2ab2.drop k).take n) = true)
    (h2 : checkBatch2ab2 (pairs2ab2.drop (k + n)) = true) :
    checkBatch2ab2 (pairs2ab2.drop k) = true := by
  have hsplit : pairs2ab2.drop k = (pairs2ab2.drop k).take n ++ pairs2ab2.drop (k + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  unfold checkBatch2ab2 at h1 h2 ⊢
  rw [hsplit, List.all_append, h1, h2]
  rfl

private lemma b2ab2_0 : checkBatch2ab2 ((pairs2ab2.drop 0).take 1) = true := by native_decide
private lemma b2ab2_1 : checkBatch2ab2 ((pairs2ab2.drop 1).take 1) = true := by native_decide
private lemma b2ab2_2 : checkBatch2ab2 ((pairs2ab2.drop 2).take 1) = true := by native_decide
private lemma b2ab2_3 : checkBatch2ab2 ((pairs2ab2.drop 3).take 1) = true := by native_decide
private lemma b2ab2_4 : checkBatch2ab2 ((pairs2ab2.drop 4).take 1) = true := by native_decide
private lemma b2ab2_5 : checkBatch2ab2 ((pairs2ab2.drop 5).take 1) = true := by native_decide
private lemma b2ab2_6 : checkBatch2ab2 ((pairs2ab2.drop 6).take 1) = true := by native_decide
private lemma b2ab2_7 : checkBatch2ab2 ((pairs2ab2.drop 7).take 1) = true := by native_decide
private lemma b2ab2_8 : checkBatch2ab2 ((pairs2ab2.drop 8).take 1) = true := by native_decide
private lemma b2ab2_9 : checkBatch2ab2 ((pairs2ab2.drop 9).take 1) = true := by native_decide
private lemma b2ab2_10 : checkBatch2ab2 ((pairs2ab2.drop 10).take 1) = true := by native_decide
private lemma b2ab2_11 : checkBatch2ab2 ((pairs2ab2.drop 11).take 1) = true := by native_decide
private lemma b2ab2_12 : checkBatch2ab2 ((pairs2ab2.drop 12).take 1) = true := by native_decide
private lemma b2ab2_13 : checkBatch2ab2 ((pairs2ab2.drop 13).take 1) = true := by native_decide
private lemma b2ab2_14 : checkBatch2ab2 ((pairs2ab2.drop 14).take 1) = true := by native_decide
private lemma b2ab2_15 : checkBatch2ab2 ((pairs2ab2.drop 15).take 1) = true := by native_decide
private lemma b2ab2_16 : checkBatch2ab2 ((pairs2ab2.drop 16).take 1) = true := by native_decide
private lemma b2ab2_17 : checkBatch2ab2 ((pairs2ab2.drop 17).take 1) = true := by native_decide
private lemma b2ab2_18 : checkBatch2ab2 ((pairs2ab2.drop 18).take 1) = true := by native_decide
private lemma b2ab2_19 : checkBatch2ab2 ((pairs2ab2.drop 19).take 1) = true := by native_decide

private lemma checkBatch2ab2_pairs2ab2 : checkBatch2ab2 pairs2ab2 = true := by
  have h20 : checkBatch2ab2 (pairs2ab2.drop 20) = true := by
    have hnil : pairs2ab2.drop 20 = [] := List.drop_eq_nil_of_le (by rw [pairs2ab2_len])
    rw [hnil]
    rfl
  have h19 := step_batch2ab2 b2ab2_19 h20
  have h18 := step_batch2ab2 b2ab2_18 h19
  have h17 := step_batch2ab2 b2ab2_17 h18
  have h16 := step_batch2ab2 b2ab2_16 h17
  have h15 := step_batch2ab2 b2ab2_15 h16
  have h14 := step_batch2ab2 b2ab2_14 h15
  have h13 := step_batch2ab2 b2ab2_13 h14
  have h12 := step_batch2ab2 b2ab2_12 h13
  have h11 := step_batch2ab2 b2ab2_11 h12
  have h10 := step_batch2ab2 b2ab2_10 h11
  have h9 := step_batch2ab2 b2ab2_9 h10
  have h8 := step_batch2ab2 b2ab2_8 h9
  have h7 := step_batch2ab2 b2ab2_7 h8
  have h6 := step_batch2ab2 b2ab2_6 h7
  have h5 := step_batch2ab2 b2ab2_5 h6
  have h4 := step_batch2ab2 b2ab2_4 h5
  have h3 := step_batch2ab2 b2ab2_3 h4
  have h2 := step_batch2ab2 b2ab2_2 h3
  have h1 := step_batch2ab2 b2ab2_1 h2
  have h0 := step_batch2ab2 b2ab2_0 h1
  simpa using h0

private theorem bridge2ab2_of_pair_ok (consts : External.CertifiedConstants)
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

/-- Every slab `c ∈ slabs2ab2` satisfies `External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs2ab2_bridges_inst (consts : External.CertifiedConstants)
    (hGRH : External.DirichletLNonvanishingRightOfHalf)
    (hCls : BuchstabSwitching.ClassicalPrimePremises consts.li2)
    (hMert : External.MertensPrimeSumPremise consts.M0) :
    ∀ c ∈ slabs2ab2, External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hlen : i < pairs2ab2.length := by
    simpa [pairs2ab2_len, slabs2ab2_len] using hi
  have hpair_mem : pairs2ab2[i] ∈ pairs2ab2 := List.getElem_mem hlen
  have hok := List.all_eq_true.mp checkBatch2ab2_pairs2ab2 pairs2ab2[i] hpair_mem
  have hpair_eq : pairs2ab2[i] = (slabs2ab2[i], witnesses2ab2[i]'(by
      simpa [← slabs2ab2_zip_len] using hi)) := by
    simp only [pairs2ab2, List.getElem_zip]
    rfl
  rw [hpair_eq] at hok
  exact bridge2ab2_of_pair_ok consts hGRH hCls hMert hok

end BuchstabSwitching.SieveInst
