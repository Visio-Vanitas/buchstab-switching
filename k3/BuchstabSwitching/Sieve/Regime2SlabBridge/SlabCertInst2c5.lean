import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cSlices
import BuchstabSwitching.Certificates.Data
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstData2c5

set_option maxRecDepth 200000
set_option maxHeartbeats 16000000

/-!
# Regime `2c5` Slab Bridge Instantiation (`11` Slabs, Indices `105..115`)
-/

namespace BuchstabSwitching.SieveInst

def slabs2c5 : List BuchstabSwitching.SlabCert :=
  (BuchstabSwitching.allSlabs.drop 105).take 11

def pairs2c5 : List (BuchstabSwitching.SlabCert × Slab2cWitness) :=
  slabs2c5.zip witnesses2c5

noncomputable def checkBatch2c5 (pairs : List (BuchstabSwitching.SlabCert × Slab2cWitness)) : Bool :=
  pairs.all (fun p => decide (¬ p.1.X_hi ≤ 10 ^ 84) && checkSlab2cWitness p.1 p.2)

private lemma slabs2c5_len : slabs2c5.length = 11 := by decide
private lemma witnesses2c5_len : witnesses2c5.length = 11 := by decide
private lemma slabs2c5_zip_len : slabs2c5.length = witnesses2c5.length := by
  rw [slabs2c5_len, witnesses2c5_len]
private lemma pairs2c5_len : pairs2c5.length = 11 := by
  simp [pairs2c5, slabs2c5_len, witnesses2c5_len]

private lemma step_batch2c5 {k n : ℕ}
    (h1 : checkBatch2c5 ((pairs2c5.drop k).take n) = true)
    (h2 : checkBatch2c5 (pairs2c5.drop (k + n)) = true) :
    checkBatch2c5 (pairs2c5.drop k) = true := by
  have hsplit : pairs2c5.drop k = (pairs2c5.drop k).take n ++ pairs2c5.drop (k + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  unfold checkBatch2c5 at h1 h2 ⊢
  rw [hsplit, List.all_append, h1, h2]; rfl

private theorem bridge2c5_of_pair_ok (consts : External.CertifiedConstants)
    {c : BuchstabSwitching.SlabCert} {w : Slab2cWitness}
    (hok : (decide (¬ c.X_hi ≤ 10 ^ 84) && checkSlab2cWitness c w) = true) :
    External.SlabCertBridge consts.li2 consts c := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨hXhi, hw⟩
  intro hGRH hCls hMert; split_ifs
  exact checkSlab2cWitness_sound consts hGRH hCls hMert hw

private lemma b2c5_0 : checkBatch2c5 ((pairs2c5.drop 0).take 1) = true := by decide
private lemma b2c5_1 : checkBatch2c5 ((pairs2c5.drop 1).take 1) = true := by decide
private lemma b2c5_2 : checkBatch2c5 ((pairs2c5.drop 2).take 1) = true := by decide
private lemma b2c5_3 : checkBatch2c5 ((pairs2c5.drop 3).take 1) = true := by decide
private lemma b2c5_4 : checkBatch2c5 ((pairs2c5.drop 4).take 1) = true := by decide
private lemma b2c5_5 : checkBatch2c5 ((pairs2c5.drop 5).take 1) = true := by decide
private lemma b2c5_6 : checkBatch2c5 ((pairs2c5.drop 6).take 1) = true := by decide
private lemma b2c5_7 : checkBatch2c5 ((pairs2c5.drop 7).take 1) = true := by decide
private lemma b2c5_8 : checkBatch2c5 ((pairs2c5.drop 8).take 1) = true := by decide
private lemma b2c5_9 : checkBatch2c5 ((pairs2c5.drop 9).take 1) = true := by decide
private lemma b2c5_10 : checkBatch2c5 ((pairs2c5.drop 10).take 1) = true := by decide

private lemma checkBatch2c5_pairs2c5 : checkBatch2c5 pairs2c5 = true := by
  have h11 : checkBatch2c5 (pairs2c5.drop 11) = true := by
    rw [List.drop_eq_nil_of_le (by rw [pairs2c5_len])]; rfl
  have h10 := step_batch2c5 b2c5_10 h11
  have h9 := step_batch2c5 b2c5_9 h10
  have h8 := step_batch2c5 b2c5_8 h9
  have h7 := step_batch2c5 b2c5_7 h8
  have h6 := step_batch2c5 b2c5_6 h7
  have h5 := step_batch2c5 b2c5_5 h6
  have h4 := step_batch2c5 b2c5_4 h5
  have h3 := step_batch2c5 b2c5_3 h4
  have h2 := step_batch2c5 b2c5_2 h3
  have h1 := step_batch2c5 b2c5_1 h2
  have h0 := step_batch2c5 b2c5_0 h1
  simpa using h0

theorem allSlabs2c5_bridges_inst (consts : External.CertifiedConstants) :
    ∀ c ∈ slabs2c5, External.SlabCertBridge consts.li2 consts c := by
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hlen : i < pairs2c5.length := by simpa [pairs2c5_len, slabs2c5_len] using hi
  have hok := List.all_eq_true.mp checkBatch2c5_pairs2c5 pairs2c5[i] (List.getElem_mem hlen)
  have hpair_eq : pairs2c5[i] = (slabs2c5[i], witnesses2c5[i]'(by simpa [← slabs2c5_zip_len] using hi)) := by
    simp only [pairs2c5, List.getElem_zip]; rfl
  rw [hpair_eq] at hok
  exact bridge2c5_of_pair_ok consts hok

end BuchstabSwitching.SieveInst
