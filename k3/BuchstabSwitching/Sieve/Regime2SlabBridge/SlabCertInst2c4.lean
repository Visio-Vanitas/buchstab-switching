import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cSlices
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2c4

set_option maxRecDepth 200000
set_option maxHeartbeats 16000000

/-!
# Regime `2c4` Slab Bridge Instantiation (`11` Slabs, Indices `94..104`)
-/

namespace BuchstabSwitching.SieveInst

def slabs2c4 : List BuchstabSwitching.SlabCert :=
  (BuchstabSwitching.allSlabs.drop 94).take 11

def pairs2c4 : List (BuchstabSwitching.SlabCert × Slab2cWitness) :=
  slabs2c4.zip witnesses2c4

def checkBatch2c4 (pairs : List (BuchstabSwitching.SlabCert × Slab2cWitness)) : Bool :=
  pairs.all (fun p => decide (¬ p.1.X_hi ≤ 10 ^ 84) && checkSlab2cWitness p.1 p.2)

private lemma slabs2c4_len : slabs2c4.length = 11 := by native_decide
private lemma witnesses2c4_len : witnesses2c4.length = 11 := by native_decide
private lemma slabs2c4_zip_len : slabs2c4.length = witnesses2c4.length := by
  rw [slabs2c4_len, witnesses2c4_len]
private lemma pairs2c4_len : pairs2c4.length = 11 := by
  simp [pairs2c4, slabs2c4_len, witnesses2c4_len]

private lemma step_batch2c4 {k n : ℕ}
    (h1 : checkBatch2c4 ((pairs2c4.drop k).take n) = true)
    (h2 : checkBatch2c4 (pairs2c4.drop (k + n)) = true) :
    checkBatch2c4 (pairs2c4.drop k) = true := by
  have hsplit : pairs2c4.drop k = (pairs2c4.drop k).take n ++ pairs2c4.drop (k + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  unfold checkBatch2c4 at h1 h2 ⊢
  rw [hsplit, List.all_append, h1, h2]; rfl

private theorem bridge2c4_of_pair_ok (consts : External.CertifiedConstants)
    {c : BuchstabSwitching.SlabCert} {w : Slab2cWitness}
    (hok : (decide (¬ c.X_hi ≤ 10 ^ 84) && checkSlab2cWitness c w) = true) :
    External.SlabCertBridge consts.li2 consts c := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨hXhi, hw⟩
  intro hGRH hCls hMert; split_ifs
  exact checkSlab2cWitness_sound consts hGRH hCls hMert hw

private lemma b2c4_0 : checkBatch2c4 ((pairs2c4.drop 0).take 1) = true := by native_decide
private lemma b2c4_1 : checkBatch2c4 ((pairs2c4.drop 1).take 1) = true := by native_decide
private lemma b2c4_2 : checkBatch2c4 ((pairs2c4.drop 2).take 1) = true := by native_decide
private lemma b2c4_3 : checkBatch2c4 ((pairs2c4.drop 3).take 1) = true := by native_decide
private lemma b2c4_4 : checkBatch2c4 ((pairs2c4.drop 4).take 1) = true := by native_decide
private lemma b2c4_5 : checkBatch2c4 ((pairs2c4.drop 5).take 1) = true := by native_decide
private lemma b2c4_6 : checkBatch2c4 ((pairs2c4.drop 6).take 1) = true := by native_decide
private lemma b2c4_7 : checkBatch2c4 ((pairs2c4.drop 7).take 1) = true := by native_decide
private lemma b2c4_8 : checkBatch2c4 ((pairs2c4.drop 8).take 1) = true := by native_decide
private lemma b2c4_9 : checkBatch2c4 ((pairs2c4.drop 9).take 1) = true := by native_decide
private lemma b2c4_10 : checkBatch2c4 ((pairs2c4.drop 10).take 1) = true := by native_decide

private lemma checkBatch2c4_pairs2c4 : checkBatch2c4 pairs2c4 = true := by
  have h11 : checkBatch2c4 (pairs2c4.drop 11) = true := by
    rw [List.drop_eq_nil_of_le (by rw [pairs2c4_len])]; rfl
  have h10 := step_batch2c4 b2c4_10 h11
  have h9 := step_batch2c4 b2c4_9 h10
  have h8 := step_batch2c4 b2c4_8 h9
  have h7 := step_batch2c4 b2c4_7 h8
  have h6 := step_batch2c4 b2c4_6 h7
  have h5 := step_batch2c4 b2c4_5 h6
  have h4 := step_batch2c4 b2c4_4 h5
  have h3 := step_batch2c4 b2c4_3 h4
  have h2 := step_batch2c4 b2c4_2 h3
  have h1 := step_batch2c4 b2c4_1 h2
  have h0 := step_batch2c4 b2c4_0 h1
  simpa using h0

theorem allSlabs2c4_bridges_inst (consts : External.CertifiedConstants) :
    ∀ c ∈ slabs2c4, External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hlen : i < pairs2c4.length := by simpa [pairs2c4_len, slabs2c4_len] using hi
  have hok := List.all_eq_true.mp checkBatch2c4_pairs2c4 pairs2c4[i] (List.getElem_mem hlen)
  have hpair_eq : pairs2c4[i] = (slabs2c4[i], witnesses2c4[i]'(by simpa [← slabs2c4_zip_len] using hi)) := by
    simp only [pairs2c4, List.getElem_zip]; rfl
  rw [hpair_eq] at hok
  exact bridge2c4_of_pair_ok consts hok

end BuchstabSwitching.SieveInst
