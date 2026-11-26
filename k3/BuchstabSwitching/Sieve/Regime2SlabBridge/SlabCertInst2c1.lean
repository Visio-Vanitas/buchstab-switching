import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cSlices
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2c1
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2c2
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2c3

set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 10000

/-!
# Regime `2c1`–`2c3` Slab Bridge Instantiation (`33` Slabs)

Verifies the first `33` Regime `2c` slabs (`(BuchstabSwitching.allSlabs.drop 61).take 33`)
against the machine-generated witness shards `witnesses2c1`, `witnesses2c2`, and `witnesses2c3`
using `1`-slab kernel checks and packages `allSlabs2c1_bridges_inst`.
-/

namespace BuchstabSwitching.SieveInst

/-- First `33` Regime `2c` slabs (indices `61..93` of `BuchstabSwitching.allSlabs`). -/
def slabs2c1 : List BuchstabSwitching.SlabCert :=
  (BuchstabSwitching.allSlabs.drop 61).take 33

/-- Concatenation of the `33` Regime `2c1`–`2c3` witness records. -/
def witnesses2c1_batch : List Slab2cWitness :=
  witnesses2c1 ++ witnesses2c2 ++ witnesses2c3

/-- Zipped list of `(slab, witness)` pairs for Regimes `2c1`–`2c3`. -/
def pairs2c1 : List (BuchstabSwitching.SlabCert × Slab2cWitness) :=
  slabs2c1.zip witnesses2c1_batch

/-- Kernel-reducible batch check for Regime `2c1`–`2c3` `(slab, witness)` pairs. -/
noncomputable def checkBatch2c1 (pairs : List (BuchstabSwitching.SlabCert × Slab2cWitness)) : Bool :=
  pairs.all (fun p => decide (¬ p.1.X_hi ≤ 10 ^ 84) && checkSlab2cWitness p.1 p.2)

private lemma slabs2c1_len : slabs2c1.length = 33 := by decide

private lemma witnesses2c1_batch_len : witnesses2c1_batch.length = 33 := by decide

private lemma slabs2c1_zip_len : slabs2c1.length = witnesses2c1_batch.length := by
  rw [slabs2c1_len, witnesses2c1_batch_len]

private lemma pairs2c1_len : pairs2c1.length = 33 := by
  simp [pairs2c1, slabs2c1_len, witnesses2c1_batch_len]

private lemma step_batch2c1 {k n : ℕ}
    (h1 : checkBatch2c1 ((pairs2c1.drop k).take n) = true)
    (h2 : checkBatch2c1 (pairs2c1.drop (k + n)) = true) :
    checkBatch2c1 (pairs2c1.drop k) = true := by
  have hsplit : pairs2c1.drop k = (pairs2c1.drop k).take n ++ pairs2c1.drop (k + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  unfold checkBatch2c1 at h1 h2 ⊢
  rw [hsplit, List.all_append, h1, h2]
  rfl

private theorem bridge2c1_of_pair_ok (consts : External.CertifiedConstants)
    {c : BuchstabSwitching.SlabCert} {w : Slab2cWitness}
    (hok : (decide (¬ c.X_hi ≤ 10 ^ 84) && checkSlab2cWitness c w) = true) :
    External.SlabCertBridge consts.li2 consts c := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨hXhi, hw⟩
  intro hGRH hCls hMert
  split_ifs
  exact checkSlab2cWitness_sound consts hGRH hCls hMert hw

private lemma b2c1_0 : checkBatch2c1 ((pairs2c1.drop 0).take 1) = true := by decide
private lemma b2c1_1 : checkBatch2c1 ((pairs2c1.drop 1).take 1) = true := by decide
private lemma b2c1_2 : checkBatch2c1 ((pairs2c1.drop 2).take 1) = true := by decide
private lemma b2c1_3 : checkBatch2c1 ((pairs2c1.drop 3).take 1) = true := by decide
private lemma b2c1_4 : checkBatch2c1 ((pairs2c1.drop 4).take 1) = true := by decide
private lemma b2c1_5 : checkBatch2c1 ((pairs2c1.drop 5).take 1) = true := by decide
private lemma b2c1_6 : checkBatch2c1 ((pairs2c1.drop 6).take 1) = true := by decide
private lemma b2c1_7 : checkBatch2c1 ((pairs2c1.drop 7).take 1) = true := by decide
private lemma b2c1_8 : checkBatch2c1 ((pairs2c1.drop 8).take 1) = true := by decide
private lemma b2c1_9 : checkBatch2c1 ((pairs2c1.drop 9).take 1) = true := by decide
private lemma b2c1_10 : checkBatch2c1 ((pairs2c1.drop 10).take 1) = true := by decide
private lemma b2c1_11 : checkBatch2c1 ((pairs2c1.drop 11).take 1) = true := by decide
private lemma b2c1_12 : checkBatch2c1 ((pairs2c1.drop 12).take 1) = true := by decide
private lemma b2c1_13 : checkBatch2c1 ((pairs2c1.drop 13).take 1) = true := by decide
private lemma b2c1_14 : checkBatch2c1 ((pairs2c1.drop 14).take 1) = true := by decide
private lemma b2c1_15 : checkBatch2c1 ((pairs2c1.drop 15).take 1) = true := by decide
private lemma b2c1_16 : checkBatch2c1 ((pairs2c1.drop 16).take 1) = true := by decide
private lemma b2c1_17 : checkBatch2c1 ((pairs2c1.drop 17).take 1) = true := by decide
private lemma b2c1_18 : checkBatch2c1 ((pairs2c1.drop 18).take 1) = true := by decide
private lemma b2c1_19 : checkBatch2c1 ((pairs2c1.drop 19).take 1) = true := by decide
private lemma b2c1_20 : checkBatch2c1 ((pairs2c1.drop 20).take 1) = true := by decide
private lemma b2c1_21 : checkBatch2c1 ((pairs2c1.drop 21).take 1) = true := by decide
private lemma b2c1_22 : checkBatch2c1 ((pairs2c1.drop 22).take 1) = true := by decide
private lemma b2c1_23 : checkBatch2c1 ((pairs2c1.drop 23).take 1) = true := by decide
private lemma b2c1_24 : checkBatch2c1 ((pairs2c1.drop 24).take 1) = true := by decide
private lemma b2c1_25 : checkBatch2c1 ((pairs2c1.drop 25).take 1) = true := by decide
private lemma b2c1_26 : checkBatch2c1 ((pairs2c1.drop 26).take 1) = true := by decide
private lemma b2c1_27 : checkBatch2c1 ((pairs2c1.drop 27).take 1) = true := by decide
private lemma b2c1_28 : checkBatch2c1 ((pairs2c1.drop 28).take 1) = true := by decide
private lemma b2c1_29 : checkBatch2c1 ((pairs2c1.drop 29).take 1) = true := by decide
private lemma b2c1_30 : checkBatch2c1 ((pairs2c1.drop 30).take 1) = true := by decide
private lemma b2c1_31 : checkBatch2c1 ((pairs2c1.drop 31).take 1) = true := by decide
private lemma b2c1_32 : checkBatch2c1 ((pairs2c1.drop 32).take 1) = true := by decide

private lemma checkBatch2c1_pairs2c1 : checkBatch2c1 pairs2c1 = true := by
  have h33 : checkBatch2c1 (pairs2c1.drop 33) = true := by
    have hnil : pairs2c1.drop 33 = [] := List.drop_eq_nil_of_le (by rw [pairs2c1_len])
    rw [hnil]
    rfl
  have h32 := step_batch2c1 b2c1_32 h33
  have h31 := step_batch2c1 b2c1_31 h32
  have h30 := step_batch2c1 b2c1_30 h31
  have h29 := step_batch2c1 b2c1_29 h30
  have h28 := step_batch2c1 b2c1_28 h29
  have h27 := step_batch2c1 b2c1_27 h28
  have h26 := step_batch2c1 b2c1_26 h27
  have h25 := step_batch2c1 b2c1_25 h26
  have h24 := step_batch2c1 b2c1_24 h25
  have h23 := step_batch2c1 b2c1_23 h24
  have h22 := step_batch2c1 b2c1_22 h23
  have h21 := step_batch2c1 b2c1_21 h22
  have h20 := step_batch2c1 b2c1_20 h21
  have h19 := step_batch2c1 b2c1_19 h20
  have h18 := step_batch2c1 b2c1_18 h19
  have h17 := step_batch2c1 b2c1_17 h18
  have h16 := step_batch2c1 b2c1_16 h17
  have h15 := step_batch2c1 b2c1_15 h16
  have h14 := step_batch2c1 b2c1_14 h15
  have h13 := step_batch2c1 b2c1_13 h14
  have h12 := step_batch2c1 b2c1_12 h13
  have h11 := step_batch2c1 b2c1_11 h12
  have h10 := step_batch2c1 b2c1_10 h11
  have h9 := step_batch2c1 b2c1_9 h10
  have h8 := step_batch2c1 b2c1_8 h9
  have h7 := step_batch2c1 b2c1_7 h8
  have h6 := step_batch2c1 b2c1_6 h7
  have h5 := step_batch2c1 b2c1_5 h6
  have h4 := step_batch2c1 b2c1_4 h5
  have h3 := step_batch2c1 b2c1_3 h4
  have h2 := step_batch2c1 b2c1_2 h3
  have h1 := step_batch2c1 b2c1_1 h2
  have h0 := step_batch2c1 b2c1_0 h1
  simpa using h0

/-- Every slab `c ∈ slabs2c1` satisfies `External.SlabCertBridge consts.li2 consts c`. -/
theorem allSlabs2c1_bridges_inst (consts : External.CertifiedConstants) :
    ∀ c ∈ slabs2c1, External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hlen : i < pairs2c1.length := by
    simpa [pairs2c1_len, slabs2c1_len] using hi
  have hpair_mem : pairs2c1[i] ∈ pairs2c1 := List.getElem_mem hlen
  have hok := List.all_eq_true.mp checkBatch2c1_pairs2c1 pairs2c1[i] hpair_mem
  have hpair_eq : pairs2c1[i] = (slabs2c1[i], witnesses2c1_batch[i]'(by
      simpa [← slabs2c1_zip_len] using hi)) := by
    simp only [pairs2c1, List.getElem_zip]
    rfl
  rw [hpair_eq] at hok
  exact bridge2c1_of_pair_ok consts hok

end BuchstabSwitching.SieveInst
