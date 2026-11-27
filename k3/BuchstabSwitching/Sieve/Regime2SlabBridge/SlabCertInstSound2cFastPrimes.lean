import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstDefs
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTable
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTree
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2abLower
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Odd-Prime Prefix Splitting & `smallOddPrimes40` Helpers for Regime `2c`

Provides `oddPrimesLt27000_pairwise_lt`, `oddPrimesLt27000_split_props`, and $O(1)$
prefix-indexing / `PrimeLeafEntry` helpers (`smallOddPrimes40`, `smallOddEntries40`)
on top of the static segment tree `oddPrimeTree`.
-/

namespace BuchstabSwitching.SieveInst

section

lemma oddPrimesLt27000_pairwise_lt : oddPrimesLt27000.Pairwise (· < ·) := by
  have hp := primesLt27000_pairwise_lt
  rw [oddPrimesLt27000_cons, List.pairwise_cons] at hp
  exact hp.2

lemma oddPrimesLt27000_split_props {a z bLast : ℕ}
    (ha : a < oddPrimesLt27000.length) (hbz : bLast ≤ z)
    (hpa : (if a = 0 then 2 else oddPrimesLt27000[a - 1]'(by omega)) < bLast)
    (hb_le : bLast ≤ oddPrimesLt27000[a]) :
    let Q₁ : Finset ℕ := (oddPrimesLt27000.take a).toFinset
    let P₂ : Finset ℕ := (Finset.Ico bLast z).filter Nat.Prime
    Disjoint Q₁ P₂ ∧ Q₁ ∪ P₂ = BuchstabSwitching.fullOddPrimesBelow z ∧ Q₁.card = a ∧
      (∀ p ∈ Q₁, p.Prime ∧ 2 < p ∧ p < bLast) ∧
      (∀ p ∈ P₂, p.Prime ∧ bLast ≤ p ∧ oddPrimesLt27000[a] ≤ p) := by
  intro Q₁ P₂
  have hQ_lt : ∀ p ∈ Q₁, p.Prime ∧ 2 < p ∧ p < bLast := by
    intro p hp
    have hp_mem := List.mem_toFinset.mp hp
    have hp_full := mem_oddPrimesLt27000_iff.mp (List.mem_of_mem_take hp_mem)
    rcases List.mem_iff_getElem.mp hp_mem with ⟨j, hj, rfl⟩
    rw [List.length_take, Nat.min_eq_left ha.le] at hj
    have ha0 : a ≠ 0 := by omega
    simp only [ha0, ↓reduceIte] at hpa
    have hle_last : oddPrimesLt27000[j] ≤ oddPrimesLt27000[a - 1]'(by omega) := by
      rcases eq_or_lt_of_le (by omega : j ≤ a - 1) with rfl | hlt
      · exact le_rfl
      · exact ((List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt) j (a - 1) (by omega) (by omega) hlt).le
    have hp_eq : (oddPrimesLt27000.take a)[j] = oddPrimesLt27000[j] := List.getElem_take
    rw [hp_eq] at hp_full ⊢
    exact ⟨hp_full.2.1, by have := hp_full.2.2; omega, lt_of_le_of_lt hle_last hpa⟩
  have hidx_lt : ∀ p, p.Prime → 3 ≤ p → p < oddPrimesLt27000[a] → p ∈ oddPrimesLt27000.take a := by
    intro p hp_pr hp3 hplt
    have ha_mem := mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)
    rcases List.mem_iff_getElem.mp (mem_oddPrimesLt27000_iff.mpr ⟨hplt.trans ha_mem.1, hp_pr, hp3⟩)
      with ⟨j, hj, rfl⟩
    have hj_lt : j < a := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · exact absurd hplt (lt_irrefl _)
      · exact absurd ((List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt) a j ha hj hgt) (by omega)
    exact List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take, Nat.min_eq_left ha.le]; exact hj_lt,
      by simp [List.getElem_take]⟩
  have h3_b : 3 ≤ bLast := by
    split_ifs at hpa with ha0
    · omega
    · exact (mem_oddPrimesLt27000_iff.mp
        (List.getElem_mem (by omega : a - 1 < oddPrimesLt27000.length))).2.2.trans hpa.le
  have hP_ge : ∀ p ∈ P₂, p.Prime ∧ bLast ≤ p ∧ oddPrimesLt27000[a] ≤ p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIco, hp_pr⟩
    rw [Finset.mem_Ico] at hpIco
    refine ⟨hp_pr, hpIco.1, ?_⟩
    by_contra hge
    have hlt : p < oddPrimesLt27000[a] := Nat.lt_of_not_ge hge
    exact absurd (hQ_lt p (List.mem_toFinset.mpr (hidx_lt p hp_pr (by omega) hlt))).2.2 (by omega)
  refine ⟨Finset.disjoint_left.mpr fun p h1 h2 => by linarith [(hQ_lt p h1).2.2, (hP_ge p h2).2.1], ?_,
    by rw [List.toFinset_card_of_nodup oddPrimesLt27000_nodup.take, List.length_take, Nat.min_eq_left ha.le],
    hQ_lt, hP_ge⟩
  ext p
  simp only [Finset.mem_union, BuchstabSwitching.fullOddPrimesBelow_mem_iff]
  constructor
  · rintro (h1 | h2)
    · exact ⟨lt_of_lt_of_le (hQ_lt p h1).2.2 hbz, (hQ_lt p h1).1, (hQ_lt p h1).2.1⟩
    · exact ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).2, (hP_ge p h2).1,
        by have := (hP_ge p h2).2.1; omega⟩
  · rintro ⟨hpz, hp_pr, hp2⟩
    by_cases hpb : p < bLast
    · exact Or.inl (List.mem_toFinset.mpr (hidx_lt p hp_pr (by omega) (lt_of_lt_of_le hpb hb_le)))
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hpz⟩, hp_pr⟩)

lemma smallOddPrimes40_len_le : smallOddPrimes40.length ≤ oddPrimesLt27000.length := by
  have h := congrArg List.length smallOddPrimes40_eq_take
  rw [List.length_take] at h
  have h40 : smallOddPrimes40.length = 40 := rfl
  omega

lemma smallOddPrimes40_getElem {i : ℕ} (hi : i < smallOddPrimes40.length) :
    smallOddPrimes40[i] = oddPrimesLt27000[i]'(lt_of_lt_of_le hi smallOddPrimes40_len_le) := by
  simp [← smallOddPrimes40_eq_take]

lemma smallOddPrimes40_take {i : ℕ} (hi : i ≤ smallOddPrimes40.length) :
    smallOddPrimes40.take i = oddPrimesLt27000.take i := by
  have hi40 : i ≤ 40 := hi
  rw [← smallOddPrimes40_eq_take, List.take_take, Nat.min_eq_left hi40]

/-- Pre-filtered first 40 odd-prime `PrimeLeafEntry` records (`3 ≤ p ≤ 179`), evaluated in $O(1)$
via a single leaf of `oddPrimeTree`. -/
def smallOddEntries40 : List PrimeLeafEntry := (oddPrimeEntriesList 180).take 40

lemma smallOddEntries40_primes : smallOddEntries40.map PrimeLeafEntry.p = smallOddPrimes40 := by native_decide

lemma smallOddEntries40_ok : ∀ e ∈ smallOddEntries40, checkPrimeLeafEntry e = true :=
  fun e he => (oddPrimeEntriesList_ok 180 e (List.mem_of_mem_take he)).1

lemma smallOddEntries40_take_primes {i : ℕ} (hi : i ≤ smallOddPrimes40.length) :
    (smallOddEntries40.take i).map PrimeLeafEntry.p = oddPrimesLt27000.take i := by
  rw [List.map_take, smallOddEntries40_primes, smallOddPrimes40_take hi]

end

end BuchstabSwitching.SieveInst
