import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstElemBounds
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEngineWiring
import Mathlib.Tactic

/-!
# Soundness Helpers & Lower-Sieve Witness Verification for Regimes `2a` & `2b`

Provides:
1. `SciNat` interval helpers (`sciScale`, `SciProofs.ofNat_toReal`, `SciProofs.mul_toReal`,
   `SciProofs.add_toReal`, `SciProofs.ble_sound`, `SciNat.blt_sound`, `sciPowUb`).
2. `List ℕ` -> `Finset ℕ` splitting lemmas for `Q₁ ∪ P₂ = fullOddPrimesBelow z` and
   `bonfDivisors` size/product bounds, specialized to `oddPrimesList z`.
3. Fast `10^24`-scaled `List ℕ` accumulators (`v2ListLb`, `v2ListUb`, `invPhiListUb`,
   `sumG1ListUb`, `sumG2ListUb`) and `elemSymSums` over `elemSymInterval`.
4. Shared `checkAnalyticV2Lb` and `checkLower2abWitness` + `checkLower2abWitness_sound`
   constructing `LowerEngine2ab.oddBonf`.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

section SciNatSound

/-- Fixed `10^24` decimal scale used for fast `List ℕ` prime product/sum accumulators. -/
def sciScale : ℕ := 10 ^ 24

lemma sciScale_pos_nat : 0 < sciScale := by unfold sciScale; positivity
lemma sciScale_pos : (0 : ℝ) < (sciScale : ℝ) := by exact_mod_cast sciScale_pos_nat
lemma sciScale_cast : ((sciScale : ℕ) : ℝ) = (10 : ℝ) ^ 24 := by unfold sciScale; norm_num

lemma sciNat_scale_toReal (m : ℕ) :
    (⟨m, 24⟩ : SciNat).toReal = (m : ℝ) / (sciScale : ℝ) := by
  simp only [SciNat.toReal, sciScale_cast]

lemma floorDiv_le_real {a b : ℕ} (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

/-- Outward-rounded power `a^k` in `SciNat`, trimmed at exponent `30` after each step. -/
def sciPowUb (a : SciNat) : ℕ → SciNat
  | 0 => SciNat.ofNat 1
  | k + 1 => ((sciPowUb a k).mul a).trimUb 30

lemma sciPowUb_sound (a : SciNat) (k : ℕ) :
    a.toReal ^ k ≤ (sciPowUb a k).toReal := by
  induction k with
  | zero => simp [sciPowUb, SciProofs.ofNat_toReal]
  | succ k ih =>
    unfold sciPowUb
    refine le_trans ?_ (SciProofs.trimUb_le _ 30)
    rw [SciProofs.mul_toReal, pow_succ]
    exact mul_le_mul_of_nonneg_right ih a.toReal_nonneg

end SciNatSound

section PrimeListSplitting

/-- Exact strictly-increasing list of odd primes `< z` (complete for `z ≤ 27000`). -/
def oddPrimesList (z : ℕ) : List ℕ :=
  primesLt27000.filter (fun p => 3 ≤ p ∧ p < z)

lemma oddPrimesList_pairwise_lt (z : ℕ) : (oddPrimesList z).Pairwise (· < ·) :=
  primesLt27000_pairwise_lt.filter _

lemma oddPrimesList_nodup (z : ℕ) : (oddPrimesList z).Nodup :=
  primesLt27000_nodup.filter _

lemma oddPrimesList_props (z : ℕ) : ∀ p ∈ oddPrimesList z, p.Prime ∧ 2 < p ∧ p < z := by
  intro p hp
  have hf := List.mem_filter.mp hp
  have hpr := (mem_primesLt27000_iff.mp hf.1).2
  have hb := hf.2
  simp only [decide_eq_true_eq] at hb
  exact ⟨hpr, by omega, hb.2⟩

lemma oddPrimesList_toFinset {z : ℕ} (hz : z ≤ 27000) :
    (oddPrimesList z).toFinset = BuchstabSwitching.fullOddPrimesBelow z :=
  (oddPrimesBelow_eq_filter hz).symm

lemma pairwise_lt_nodup {L : List ℕ} (h : L.Pairwise (· < ·)) : L.Nodup :=
  h.imp (fun {_ _} hlt => Nat.ne_of_lt hlt)

lemma take_drop_disjoint {ps : List ℕ} (hps : ps.Pairwise (· < ·)) (a : ℕ) :
    Disjoint (ps.take a).toFinset (ps.drop a).toFinset := by
  have htd : (ps.take a ++ ps.drop a).Pairwise (· < ·) := by rw [List.take_append_drop]; exact hps
  have hcross := (List.pairwise_append.mp htd).2.2
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [List.mem_toFinset] at hx1 hx2
  exact Nat.lt_irrefl x (hcross x hx1 x hx2)

lemma take_drop_union {ps : List ℕ} (a : ℕ) :
    (ps.take a).toFinset ∪ (ps.drop a).toFinset = ps.toFinset := by
  ext x
  simp only [Finset.mem_union, List.mem_toFinset]
  constructor
  · rintro (h | h)
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop h
  · intro h
    have hmem : x ∈ ps.take a ++ ps.drop a := by rw [List.take_append_drop]; exact h
    exact List.mem_append.mp hmem

lemma take_toFinset_card {ps : List ℕ} (hps : ps.Pairwise (· < ·)) {a : ℕ} (ha : a ≤ ps.length) :
    (ps.take a).toFinset.card = a := by
  rw [List.toFinset_card_of_nodup (pairwise_lt_nodup hps).take, List.length_take, Nat.min_eq_left ha]

lemma drop_toFinset_card {ps : List ℕ} (hps : ps.Pairwise (· < ·)) (a : ℕ) :
    (ps.drop a).toFinset.card = (ps.drop a).length :=
  List.toFinset_card_of_nodup (pairwise_lt_nodup hps).drop

lemma bonfDivisors_le_take_mul_rev_drop {ps : List ℕ} (hps : ps.Pairwise (· < ·))
    (hpos : ∀ p ∈ ps, 1 ≤ p) (a k : ℕ) :
    ∀ d ∈ BuchstabSwitching.bonfDivisors (ps.take a).toFinset (ps.drop a).toFinset k,
      d ≤ (ps.take a).prod * ((ps.drop a).reverse.take k).prod := by
  intro d hd
  have htd : (ps.take a ++ ps.drop a).Pairwise (· < ·) := by rw [List.take_append_drop]; exact hps
  have hpair := List.pairwise_append.mp htd
  have hQ_nd : (ps.take a).Nodup := pairwise_lt_nodup hpair.1
  have hP_lt : (ps.drop a).Pairwise (· < ·) := hpair.2.1
  have hP_nd : (ps.drop a).Nodup := pairwise_lt_nodup hP_lt
  have hQ_pos : ∀ p ∈ (ps.take a).toFinset, 1 ≤ p := fun p hp =>
    hpos p (List.mem_of_mem_take (List.mem_toFinset.mp hp))
  have hP_pos : ∀ p ∈ (ps.drop a).toFinset, 1 ≤ p := fun p hp =>
    hpos p (List.mem_of_mem_drop (List.mem_toFinset.mp hp))
  have hbd := BuchstabSwitching.bonfDivisors_le_prod_mul_top_k hQ_pos hP_pos hd
  have hQ_prod : ∏ p ∈ (ps.take a).toFinset, p = (ps.take a).prod := by
    simpa using List.prod_toFinset (fun x => x) hQ_nd
  have hrev_nd : (ps.drop a).reverse.Nodup := List.nodup_reverse.mpr hP_nd
  have hrev_ge : (ps.drop a).reverse.Pairwise (· ≥ ·) :=
    (List.pairwise_reverse.mpr hP_lt).imp fun {_ _} hlt => le_of_lt hlt
  have hrev_fin : (ps.drop a).reverse.toFinset = (ps.drop a).toFinset := by ext x; simp
  have hsort : (ps.drop a).toFinset.sort (· ≥ ·) = (ps.drop a).reverse := by
    have hres := (List.toFinset_sort (· ≥ ·) hrev_nd).mpr hrev_ge
    rw [hrev_fin] at hres
    exact hres
  have htake_prod :
      ∏ p ∈ (((ps.drop a).toFinset.sort (· ≥ ·)).take k).toFinset, p =
        ((ps.drop a).reverse.take k).prod := by
    rw [hsort]
    simpa using List.prod_toFinset (fun x => x) hrev_nd.take
  rw [hQ_prod, htake_prod] at hbd
  exact hbd

lemma card_bonfDivisors_take_drop {ps : List ℕ} (hps : ps.Pairwise (· < ·))
    (hpr : ∀ p ∈ ps, p.Prime) {a : ℕ} (ha : a ≤ ps.length) (k : ℕ) :
    (BuchstabSwitching.bonfDivisors (ps.take a).toFinset (ps.drop a).toFinset k).card =
      2 ^ a * ∑ j ∈ Finset.range (k + 1), (ps.drop a).length.choose j := by
  have hQ_pr : ∀ p ∈ (ps.take a).toFinset, p.Prime := fun p hp =>
    hpr p (List.mem_of_mem_take (List.mem_toFinset.mp hp))
  have hP_pr : ∀ p ∈ (ps.drop a).toFinset, p.Prime := fun p hp =>
    hpr p (List.mem_of_mem_drop (List.mem_toFinset.mp hp))
  rw [BuchstabSwitching.card_bonfDivisors (take_drop_disjoint hps a) hQ_pr hP_pr,
    take_toFinset_card hps ha, drop_toFinset_card hps a]

end PrimeListSplitting

section FastListAccumulators

private def foldProdLb (num den : ℕ → ℕ) (acc : ℕ) (L : List ℕ) : ℕ :=
  L.foldl (fun a p => (a * num p) / den p) acc

private def foldProdUb (num den : ℕ → ℕ) (acc : ℕ) (L : List ℕ) : ℕ :=
  L.foldl (fun a p => SciNat.ceilDiv (a * num p) (den p)) acc

private def foldSumUb (den : ℕ → ℕ) (acc : ℕ) (L : List ℕ) : ℕ :=
  L.foldl (fun a p => a + SciNat.ceilDiv sciScale (den p)) acc

private lemma foldProdLb_sound (num den : ℕ → ℕ) (f : ℕ → ℝ) :
    ∀ (L : List ℕ) (acc : ℕ), L.Nodup →
      (∀ p ∈ L, 0 < den p ∧ 0 ≤ f p ∧ f p = (num p : ℝ) / (den p : ℝ)) →
      ((foldProdLb num den acc L : ℕ) : ℝ) / (sciScale : ℝ) ≤
        ((acc : ℝ) / (sciScale : ℝ)) * ∏ p ∈ L.toFinset, f p
  | [], acc, _, _ => by simp [foldProdLb]
  | p :: tl, acc, hnd, hprop => by
    rcases List.nodup_cons.mp hnd with ⟨hptl, htl_nd⟩
    have hp := hprop p List.mem_cons_self
    have htl := fun q hq => hprop q (List.mem_cons_of_mem p hq)
    set acc' : ℕ := (acc * num p) / den p
    have hrec := foldProdLb_sound num den f tl acc' htl_nd htl
    have hprod_nn : 0 ≤ ∏ q ∈ tl.toFinset, f q :=
      Finset.prod_nonneg fun q hq => (htl q (List.mem_toFinset.mp hq)).2.1
    have hfl : ((acc' : ℕ) : ℝ) / (sciScale : ℝ) ≤ ((acc : ℝ) / (sciScale : ℝ)) * f p := by
      have h1 := floorDiv_le_real (a := acc * num p) hp.1
      have h2 := div_le_div_of_nonneg_right h1 sciScale_pos.le
      rw [hp.2.2]
      refine h2.trans_eq ?_; push_cast; ring
    rw [foldProdLb, List.foldl_cons, List.toFinset_cons,
      Finset.prod_insert (by simpa [List.mem_toFinset] using hptl)]
    change ((foldProdLb num den acc' tl : ℕ) : ℝ) / (sciScale : ℝ) ≤ _
    calc ((foldProdLb num den acc' tl : ℕ) : ℝ) / (sciScale : ℝ)
        ≤ ((acc' : ℝ) / (sciScale : ℝ)) * ∏ q ∈ tl.toFinset, f q := hrec
      _ ≤ ((acc : ℝ) / (sciScale : ℝ)) * f p * ∏ q ∈ tl.toFinset, f q :=
          mul_le_mul_of_nonneg_right hfl hprod_nn
      _ = ((acc : ℝ) / (sciScale : ℝ)) * (f p * ∏ q ∈ tl.toFinset, f q) := by ring

private lemma foldProdUb_sound (num den : ℕ → ℕ) (f : ℕ → ℝ) :
    ∀ (L : List ℕ) (acc : ℕ), L.Nodup →
      (∀ p ∈ L, 0 < den p ∧ 0 ≤ f p ∧ f p = (num p : ℝ) / (den p : ℝ)) →
      ((acc : ℝ) / (sciScale : ℝ)) * (∏ p ∈ L.toFinset, f p) ≤
        ((foldProdUb num den acc L : ℕ) : ℝ) / (sciScale : ℝ)
  | [], acc, _, _ => by simp [foldProdUb]
  | p :: tl, acc, hnd, hprop => by
    rcases List.nodup_cons.mp hnd with ⟨hptl, htl_nd⟩
    have hp := hprop p List.mem_cons_self
    have htl := fun q hq => hprop q (List.mem_cons_of_mem p hq)
    set acc' : ℕ := SciNat.ceilDiv (acc * num p) (den p)
    have hrec := foldProdUb_sound num den f tl acc' htl_nd htl
    have hprod_nn : 0 ≤ ∏ q ∈ tl.toFinset, f q :=
      Finset.prod_nonneg fun q hq => (htl q (List.mem_toFinset.mp hq)).2.1
    have hceil : ((acc : ℝ) / (sciScale : ℝ)) * f p ≤ ((acc' : ℕ) : ℝ) / (sciScale : ℝ) := by
      have h1 := SciProofs.ceilDiv_ge (n := acc * num p) hp.1
      have h2 := div_le_div_of_nonneg_right h1 sciScale_pos.le
      rw [hp.2.2]
      refine le_trans (le_of_eq ?_) h2; push_cast; ring
    rw [foldProdUb, List.foldl_cons, List.toFinset_cons,
      Finset.prod_insert (by simpa [List.mem_toFinset] using hptl)]
    change _ ≤ ((foldProdUb num den acc' tl : ℕ) : ℝ) / (sciScale : ℝ)
    calc ((acc : ℝ) / (sciScale : ℝ)) * (f p * ∏ q ∈ tl.toFinset, f q)
        = ((acc : ℝ) / (sciScale : ℝ)) * f p * ∏ q ∈ tl.toFinset, f q := by ring
      _ ≤ ((acc' : ℝ) / (sciScale : ℝ)) * ∏ q ∈ tl.toFinset, f q :=
          mul_le_mul_of_nonneg_right hceil hprod_nn
      _ ≤ ((foldProdUb num den acc' tl : ℕ) : ℝ) / (sciScale : ℝ) := hrec

private lemma foldSumUb_sound (den : ℕ → ℕ) (f : ℕ → ℝ) :
    ∀ (L : List ℕ) (acc : ℕ), L.Nodup →
      (∀ p ∈ L, 0 < den p ∧ f p = 1 / (den p : ℝ)) →
      ((acc : ℝ) / (sciScale : ℝ)) + ∑ p ∈ L.toFinset, f p ≤
        ((foldSumUb den acc L : ℕ) : ℝ) / (sciScale : ℝ)
  | [], acc, _, _ => by simp [foldSumUb]
  | p :: tl, acc, hnd, hprop => by
    rcases List.nodup_cons.mp hnd with ⟨hptl, htl_nd⟩
    have hp := hprop p List.mem_cons_self
    have htl := fun q hq => hprop q (List.mem_cons_of_mem p hq)
    set acc' : ℕ := acc + SciNat.ceilDiv sciScale (den p)
    have hrec := foldSumUb_sound den f tl acc' htl_nd htl
    have hceil : f p ≤ ((SciNat.ceilDiv sciScale (den p) : ℕ) : ℝ) / (sciScale : ℝ) := by
      have h1 := SciProofs.ceilDiv_ge (n := sciScale) hp.1
      have h2 := div_le_div_of_nonneg_right h1 sciScale_pos.le
      rw [hp.2]
      refine le_trans (le_of_eq ?_) h2
      field_simp [sciScale_pos.ne', (by exact_mod_cast hp.1.ne' : (den p : ℝ) ≠ 0)]
    rw [foldSumUb, List.foldl_cons, List.toFinset_cons,
      Finset.sum_insert (by simpa [List.mem_toFinset] using hptl)]
    change _ ≤ ((foldSumUb den acc' tl : ℕ) : ℝ) / (sciScale : ℝ)
    have hacc' : ((acc' : ℕ) : ℝ) / (sciScale : ℝ) =
        (acc : ℝ) / (sciScale : ℝ) + ((SciNat.ceilDiv sciScale (den p) : ℕ) : ℝ) / (sciScale : ℝ) := by
      dsimp [acc']; push_cast; ring
    linarith

def v2ListLb (L : List ℕ) : SciNat := ⟨foldProdLb (· - 2) (· - 1) sciScale L, 24⟩
def v2ListUb (L : List ℕ) : SciNat := ⟨foldProdUb (· - 2) (· - 1) sciScale L, 24⟩
def invPhiListUb (L : List ℕ) : SciNat := ⟨foldProdUb id (· - 1) sciScale L, 24⟩
def sumG1ListUb (L : List ℕ) : SciNat := ⟨foldSumUb (· - 1) 0 L, 24⟩
def sumG2ListUb (L : List ℕ) : SciNat := ⟨foldSumUb (fun p => (p - 1) ^ 2) 0 L, 24⟩

private lemma one_sub_gTot_prop {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    0 < p - 1 ∧ 0 ≤ 1 - BuchstabSwitching.gTot p ∧
      1 - BuchstabSwitching.gTot p = ((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  have hbd := BuchstabSwitching.gTot_prime_bounds hp hp2
  refine ⟨by omega, by linarith [hbd.2], ?_⟩
  rw [BuchstabSwitching.gTot_prime hp, Nat.cast_sub (by omega : 2 ≤ p),
    Nat.cast_sub (by omega : 1 ≤ p)]
  push_cast
  have hden : (p : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
    linarith
  field_simp [hden]; ring

lemma v2ListLb_sound {L : List ℕ} (hnd : L.Nodup) (hpr : ∀ p ∈ L, p.Prime ∧ 2 < p) :
    (v2ListLb L).toReal ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot L.toFinset := by
  unfold v2ListLb BuchstabSwitching.V2
  rw [sciNat_scale_toReal]
  have h := foldProdLb_sound (· - 2) (· - 1) (fun p => 1 - BuchstabSwitching.gTot p)
    L sciScale hnd (fun p hp => one_sub_gTot_prop (hpr p hp).1 (hpr p hp).2)
  rwa [div_self sciScale_pos.ne', one_mul] at h

lemma v2ListUb_sound {L : List ℕ} (hnd : L.Nodup) (hpr : ∀ p ∈ L, p.Prime ∧ 2 < p) :
    BuchstabSwitching.V2 BuchstabSwitching.gTot L.toFinset ≤ (v2ListUb L).toReal := by
  unfold v2ListUb BuchstabSwitching.V2
  rw [sciNat_scale_toReal]
  have h := foldProdUb_sound (· - 2) (· - 1) (fun p => 1 - BuchstabSwitching.gTot p)
    L sciScale hnd (fun p hp => one_sub_gTot_prop (hpr p hp).1 (hpr p hp).2)
  rwa [div_self sciScale_pos.ne', one_mul] at h

lemma invPhiListUb_sound {L : List ℕ} (hnd : L.Nodup) (hp2 : ∀ p ∈ L, 2 ≤ p) :
    (∏ p ∈ L.toFinset, (p : ℝ) / ((p : ℝ) - 1)) ≤ (invPhiListUb L).toReal := by
  unfold invPhiListUb
  rw [sciNat_scale_toReal]
  have h := foldProdUb_sound id (· - 1) (fun p => (p : ℝ) / ((p : ℝ) - 1)) L sciScale hnd
    (fun p hp => by
      have hpn : 2 ≤ p := hp2 p hp
      have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpn
      refine ⟨by omega, div_nonneg (by positivity) (by linarith), ?_⟩
      rw [id_eq, Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; rfl)
  rwa [div_self sciScale_pos.ne', one_mul] at h

lemma sumG1ListUb_sound {L : List ℕ} (hnd : L.Nodup) (hpr : ∀ p ∈ L, p.Prime ∧ 2 < p) :
    ∑ p ∈ L.toFinset, BuchstabSwitching.gTot p ≤ (sumG1ListUb L).toReal := by
  unfold sumG1ListUb
  rw [sciNat_scale_toReal]
  have h := foldSumUb_sound (· - 1) BuchstabSwitching.gTot L 0 hnd (fun p hp => by
    have hpp := hpr p hp
    refine ⟨by omega, ?_⟩
    rw [BuchstabSwitching.gTot_prime hpp.1, Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; rfl)
  simpa using h

lemma sumG2ListUb_sound {L : List ℕ} (hnd : L.Nodup) (hpr : ∀ p ∈ L, p.Prime ∧ 2 < p) :
    ∑ p ∈ L.toFinset, (BuchstabSwitching.gTot p) ^ 2 ≤ (sumG2ListUb L).toReal := by
  unfold sumG2ListUb
  rw [sciNat_scale_toReal]
  have h := foldSumUb_sound (fun p => (p - 1) ^ 2) (fun p => (BuchstabSwitching.gTot p) ^ 2)
    L 0 hnd (fun p hp => by
      have hpp := hpr p hp
      refine ⟨by have := hpp.2; exact pow_pos (by omega) 2, ?_⟩
      rw [BuchstabSwitching.gTot_prime hpp.1, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p),
        one_div_pow]; push_cast; rfl)
  simpa using h

end FastListAccumulators

section ElemSymSums

/-- Accumulates `(evenLo, evenHi, oddLo, oddHi)` over an interval DP list `dp`. -/
def elemSymSumsAux : ℕ → List (SciNat × SciNat) →
    SciNat × SciNat × SciNat × SciNat → SciNat × SciNat × SciNat × SciNat
  | _, [], acc => acc
  | j, (lo, hi) :: rest, (eLo, eHi, oLo, oHi) =>
    if j % 2 == 0 then
      elemSymSumsAux (j + 1) rest (eLo.add lo, eHi.add hi, oLo, oHi)
    else
      elemSymSumsAux (j + 1) rest (eLo, eHi, oLo.add lo, oHi.add hi)

def elemSymSums (dp : List (SciNat × SciNat)) : SciNat × SciNat × SciNat × SciNat :=
  elemSymSumsAux 0 dp (⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩)

private lemma elemSymSumsAux_sound : ∀ (dp : List (SciNat × SciNat)) (j : ℕ)
    (acc : SciNat × SciNat × SciNat × SciNat) (f : ℕ → ℝ),
    (∀ k (hk : k < dp.length),
      (dp[k]'hk).1.toReal ≤ f (j + k) ∧ f (j + k) ≤ (dp[k]'hk).2.toReal) →
    let res := elemSymSumsAux j dp acc
    res.1.toReal - res.2.2.2.toReal ≤
        acc.1.toReal - acc.2.2.2.toReal + ∑ k ∈ Finset.range dp.length, (-1 : ℝ) ^ (j + k) * f (j + k) ∧
      acc.2.1.toReal - acc.2.2.1.toReal + ∑ k ∈ Finset.range dp.length, (-1 : ℝ) ^ (j + k) * f (j + k) ≤
        res.2.1.toReal - res.2.2.1.toReal ∧
      acc.2.1.toReal + acc.2.2.2.toReal + ∑ k ∈ Finset.range dp.length, f (j + k) ≤
        res.2.1.toReal + res.2.2.2.toReal
  | [], _, acc, _, _ => by simp [elemSymSumsAux]
  | (lo, hi) :: rest, j, (eLo, eHi, oLo, oHi), f, hf => by
    have hf0 := hf 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hf0
    have hf_rest : ∀ k (hk : k < rest.length),
        (rest[k]'hk).1.toReal ≤ f ((j + 1) + k) ∧ f ((j + 1) + k) ≤ (rest[k]'hk).2.toReal := by
      intro k hk
      have h := hf (k + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using h
    have hsplit1 : ∑ k ∈ Finset.range (rest.length + 1), (-1 : ℝ) ^ (j + k) * f (j + k) =
        (-1 : ℝ) ^ j * f j +
          ∑ k ∈ Finset.range rest.length, (-1 : ℝ) ^ (j + 1 + k) * f (j + 1 + k) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show j + (k + 1) = j + 1 + k by omega]
    have hsplit2 : ∑ k ∈ Finset.range (rest.length + 1), f (j + k) =
        f j + ∑ k ∈ Finset.range rest.length, f (j + 1 + k) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show j + (k + 1) = j + 1 + k by omega]
    by_cases hj : j % 2 == 0
    · have hj_even : Even j := Nat.even_iff.mpr (beq_iff_eq.mp hj)
      have hpow : (-1 : ℝ) ^ j = 1 := hj_even.neg_one_pow
      have hrec := elemSymSumsAux_sound rest (j + 1) (eLo.add lo, eHi.add hi, oLo, oHi) f hf_rest
      simp only [elemSymSumsAux, hj, ↓reduceIte, List.length_cons] at hrec ⊢
      rw [SciProofs.add_toReal, SciProofs.add_toReal] at hrec
      rw [hsplit1, hsplit2, hpow, one_mul]
      exact ⟨by linarith [hrec.1], by linarith [hrec.2.1], by linarith [hrec.2.2]⟩
    · have hj_mod : j % 2 = 1 := by
        have hne : j % 2 ≠ 0 := fun h0 => hj (beq_iff_eq.mpr h0)
        omega
      have hj_odd : Odd j := Nat.odd_iff.mpr hj_mod
      have hpow : (-1 : ℝ) ^ j = -1 := hj_odd.neg_one_pow
      have hrec := elemSymSumsAux_sound rest (j + 1) (eLo, eHi, oLo.add lo, oHi.add hi) f hf_rest
      simp only [elemSymSumsAux, hj, ↓reduceIte, Bool.false_eq_true, List.length_cons] at hrec ⊢
      rw [SciProofs.add_toReal, SciProofs.add_toReal] at hrec
      rw [hsplit1, hsplit2, hpow]
      exact ⟨by linarith [hrec.1], by linarith [hrec.2.1], by linarith [hrec.2.2]⟩

lemma elemSymSums_interval_sound {ps : List ℕ} (hnd : ps.Nodup) (hpr : ∀ p ∈ ps, p.Prime)
    (m : ℕ) :
    let res := elemSymSums (elemSymInterval ps m)
    res.1.toReal - res.2.2.2.toReal ≤ BuchstabSwitching.gTrunc BuchstabSwitching.gTot ps.toFinset m ∧
      BuchstabSwitching.gTrunc BuchstabSwitching.gTot ps.toFinset m ≤ res.2.1.toReal - res.2.2.1.toReal ∧
      ∑ j ∈ Finset.range (m + 1), BuchstabSwitching.elemSym BuchstabSwitching.gTot ps.toFinset j ≤
        (res.2.1.add res.2.2.2).toReal := by
  have hlen := elemSymInterval_length ps m
  have hdp := elemSymInterval_sound hnd hpr m
  have haux := elemSymSumsAux_sound (elemSymInterval ps m) 0
    (⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩) (BuchstabSwitching.elemSym BuchstabSwitching.gTot ps.toFinset)
    (fun k hk => by simpa using hdp k (by omega))
  have h0 : (⟨0, 0⟩ : SciNat).toReal = 0 := by simp [SciNat.toReal]
  simp only [hlen, h0, sub_zero, add_zero, zero_add] at haux
  dsimp only
  rw [SciProofs.add_toReal]
  exact ⟨haux.1, haux.2.1, haux.2.2⟩

end ElemSymSums

section Lower2abChecker

/-- Shared analytic `V2` lower-bound checker on `p2` via `analytic_bonf_V2_lb` + `checkExpNeg`. -/
def checkAnalyticV2Lb (p2 : List ℕ) (gLb : SciNat) : Bool :=
  match p2 with
  | [] => decide (0 < gLb.m) && gLb.ble (SciNat.ofNat 1)
  | pMin :: _ =>
    let s1Ub := sumG1ListUb p2
    let s2Ub := sumG2ListUb p2
    let cLog2Ub := SciNat.divUb (SciNat.ofNat (pMin - 1)) (SciNat.ofNat (2 * (pMin - 2))) 24
    let argUb := s1Ub.add (cLog2Ub.mul s2Ub)
    decide (0 < gLb.m) && checkExpNeg argUb gLb

lemma checkAnalyticV2Lb_sound {p2 : List ℕ} (hps : p2.Pairwise (· < ·))
    (hpr : ∀ p ∈ p2, p.Prime ∧ 2 < p) {gLb : SciNat} (h : checkAnalyticV2Lb p2 gLb = true) :
    0 < gLb.toReal ∧ gLb.toReal ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot p2.toFinset := by
  cases p2 with
  | nil =>
    simp only [checkAnalyticV2Lb, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpos : 0 < gLb.toReal := by unfold SciNat.toReal; exact div_pos (by exact_mod_cast h.1) (by positivity)
    have hle := SciProofs.ble_sound h.2
    rw [SciProofs.ofNat_toReal, Nat.cast_one] at hle
    simpa [BuchstabSwitching.V2] using ⟨hpos, hle⟩
  | cons pMin tl =>
    simp only [checkAnalyticV2Lb, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpos : 0 < gLb.toReal := by unfold SciNat.toReal; exact div_pos (by exact_mod_cast h.1) (by positivity)
    have hpMin := hpr pMin List.mem_cons_self
    have hpMin3 : 3 ≤ pMin := by omega
    have hP2_min : ∀ p ∈ (pMin :: tl).toFinset, p.Prime ∧ pMin ≤ p := by
      intro p hp
      rw [List.mem_toFinset] at hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact ⟨hpMin.1, le_rfl⟩
      · have hlt := (List.pairwise_cons.mp hps).1 p hmem
        exact ⟨(hpr p hp).1, hlt.le⟩
    have hnd := pairwise_lt_nodup hps
    have hS1 := sumG1ListUb_sound hnd hpr
    have hS2 := sumG2ListUb_sound hnd hpr
    have hV2 := BuchstabSwitching.analytic_bonf_V2_lb hpMin3 hP2_min hS1 hS2
    dsimp only at hV2
    set s1Ub := sumG1ListUb (pMin :: tl)
    set s2Ub := sumG2ListUb (pMin :: tl)
    set cLog2Ub := SciNat.divUb (SciNat.ofNat (pMin - 1)) (SciNat.ofNat (2 * (pMin - 2))) 24
    set argUb := s1Ub.add (cLog2Ub.mul s2Ub)
    have hc_le : 1 / (2 * (1 - 1 / ((pMin : ℝ) - 1))) ≤ cLog2Ub.toReal := by
      have hdiv := SciProofs.divUb_le (SciNat.ofNat (pMin - 1)) (SciNat.ofNat (2 * (pMin - 2))) 24
      rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, Nat.cast_sub (by omega : 1 ≤ pMin),
        Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ pMin)] at hdiv
      push_cast at hdiv
      have hp3 : (3 : ℝ) ≤ (pMin : ℝ) := by exact_mod_cast hpMin3
      have hden1 : (pMin : ℝ) - 1 ≠ 0 := by linarith
      have hden2 : (pMin : ℝ) - 2 ≠ 0 := by linarith
      refine le_trans (le_of_eq ?_) hdiv
      have h1m : 1 - 1 / ((pMin : ℝ) - 1) = ((pMin : ℝ) - 2) / ((pMin : ℝ) - 1) := by
        field_simp [hden1]; ring
      rw [h1m]; field_simp [hden1, hden2]
    have hS2_nn : 0 ≤ s2Ub.toReal := s2Ub.toReal_nonneg
    have harg_le : s1Ub.toReal + 1 / (2 * (1 - 1 / ((pMin : ℝ) - 1))) * s2Ub.toReal ≤ argUb.toReal := by
      dsimp only [argUb]
      rw [SciProofs.add_toReal, SciProofs.mul_toReal]
      linarith [mul_le_mul_of_nonneg_right hc_le hS2_nn]
    have hexp := checkExpNeg_sound h.2
    exact ⟨hpos, hexp.trans ((Real.exp_le_exp.mpr (by linarith)).trans hV2)⟩

/-- Computable `RTrunc` odd lower-bound checker on `p2`. -/
def checkLowerRatLb (useAnalytic : Bool) (p2 : List ℕ) (mOdd : ℕ) (ratLb gLb : SciNat) : Bool :=
  let k := 2 * mOdd + 1
  if !useAnalytic then
    match p2 with
    | [] => ratLb.ble (SciNat.ofNat 1)
    | _ :: _ =>
      let sums := elemSymSums (elemSymInterval p2 k)
      let gP2Ub := v2ListUb p2
      ((ratLb.mul gP2Ub).add sums.2.2.2).ble sums.1
  else
    let s1Ub := sumG1ListUb p2
    let errNum := sciPowUb s1Ub (k + 1)
    let errDen := (SciNat.ofNat (Nat.factorial (k + 1))).mul gLb
    let errUb := errNum.divUb errDen 24
    checkAnalyticV2Lb p2 gLb &&
      match p2 with
      | [] => ratLb.ble (SciNat.ofNat 1)
      | _ :: _ => (ratLb.add errUb).ble (SciNat.ofNat 1)

private lemma checkLowerRatLb_sound {useAnalytic : Bool} {p2 : List ℕ}
    (hP2_lt : p2.Pairwise (· < ·)) (hP2_pr : ∀ p ∈ p2, p.Prime ∧ 2 < p)
    {mOdd : ℕ} {ratLb gLb : SciNat}
    (h : checkLowerRatLb useAnalytic p2 mOdd ratLb gLb = true) :
    ratLb.toReal ≤ BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset (2 * mOdd + 1) := by
  unfold checkLowerRatLb at h
  dsimp only at h
  have hP2_nd : p2.Nodup := pairwise_lt_nodup hP2_lt
  have hP2_fin_pr : ∀ p ∈ p2.toFinset, p.Prime ∧ 2 < p := fun p hp =>
    hP2_pr p (List.mem_toFinset.mp hp)
  by_cases hana : useAnalytic = false
  · simp only [hana, Bool.not_false, ↓reduceIte] at h
    cases p2 with
    | nil =>
      rw [List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
      simpa [SciProofs.ofNat_toReal] using SciProofs.ble_sound h
    | cons p0 tl =>
      have hble := SciProofs.ble_sound h
      rw [SciProofs.add_toReal, SciProofs.mul_toReal] at hble
      have hsum := elemSymSums_interval_sound hP2_nd (fun p hp => (hP2_pr p hp).1) (2 * mOdd + 1)
      have hgUb := v2ListUb_sound hP2_nd hP2_pr
      have hV2_pos : 0 < BuchstabSwitching.V2 BuchstabSwitching.gTot (p0 :: tl).toFinset :=
        BuchstabSwitching.V2_pos fun p hp =>
          (BuchstabSwitching.gTot_prime_bounds (hP2_fin_pr p hp).1 (hP2_fin_pr p hp).2).2
      have hmul_le : ratLb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot (p0 :: tl).toFinset ≤
          BuchstabSwitching.gTrunc BuchstabSwitching.gTot (p0 :: tl).toFinset (2 * mOdd + 1) := by
        have h1 : ratLb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot (p0 :: tl).toFinset ≤
            ratLb.toReal * (v2ListUb (p0 :: tl)).toReal :=
          mul_le_mul_of_nonneg_left hgUb ratLb.toReal_nonneg
        linarith [hsum.1]
      rw [BuchstabSwitching.RTrunc]
      exact (le_div_iff₀ hV2_pos).mpr hmul_le
  · have hana_t : useAnalytic = true := Bool.eq_true_of_not_eq_false hana
    simp only [hana_t, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    have hg := checkAnalyticV2Lb_sound hP2_lt hP2_pr h.1
    cases p2 with
    | nil =>
      rw [List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
      simpa [SciProofs.ofNat_toReal] using SciProofs.ble_sound h.2
    | cons p0 tl =>
      have hble := SciProofs.ble_sound h.2
      rw [SciProofs.add_toReal, SciProofs.ofNat_toReal, Nat.cast_one] at hble
      have hS1 := sumG1ListUb_sound hP2_nd hP2_pr
      have hR := BuchstabSwitching.analytic_bonf_RTrunc_odd_lb hP2_fin_pr mOdd hg.1 hg.2 hS1
      set s1Ub := sumG1ListUb (p0 :: tl)
      set errNum := sciPowUb s1Ub ((2 * mOdd + 1) + 1)
      set errDen := (SciNat.ofNat (Nat.factorial ((2 * mOdd + 1) + 1))).mul gLb
      set errUb := errNum.divUb errDen 24
      have herr_le : s1Ub.toReal ^ (2 * mOdd + 2) /
          ((Nat.factorial (2 * mOdd + 2) : ℝ) * gLb.toReal) ≤ errUb.toReal := by
        have hpow := sciPowUb_sound s1Ub ((2 * mOdd + 1) + 1)
        have hk_eq : (2 * mOdd + 1) + 1 = 2 * mOdd + 2 := by omega
        have hden_eq : errDen.toReal = (Nat.factorial (2 * mOdd + 2) : ℝ) * gLb.toReal := by
          dsimp [errDen]; rw [SciProofs.mul_toReal, SciProofs.ofNat_toReal, hk_eq]
        have h1 : s1Ub.toReal ^ (2 * mOdd + 2) /
            ((Nat.factorial (2 * mOdd + 2) : ℝ) * gLb.toReal) ≤
            errNum.toReal / errDen.toReal := by
          rw [hden_eq, ← hk_eq]
          exact div_le_div_of_nonneg_right hpow (mul_nonneg (by positivity) hg.1.le)
        exact h1.trans (SciProofs.divUb_le errNum errDen 24)
      dsimp only [errUb, s1Ub] at herr_le
      linarith

/-- Computable Regime `2a`/`2b` lower-sieve witness verifier (`LowerEngine2ab.oddBonf`). -/
def checkLower2abWitness (c : BuchstabSwitching.SlabCert) (lo : Lower2abWitness) : Bool :=
  let ps := oddPrimesList c.z
  let q1 := ps.take lo.a
  let p2 := ps.drop lo.a
  let k := 2 * lo.mOdd + 1
  decide (c.z ≤ pExact) &&
  decide (lo.a ≤ ps.length) &&
  decide (q1.prod * (p2.reverse.take k).prod ≤ lo.dMax) &&
  decide (lo.dMax ^ 2 ≤ c.X_lo) &&
  decide (2 ^ lo.a * (∑ j ∈ Finset.range (k + 1), p2.length.choose j) ≤ lo.nD) &&
  lo.vFullLb.ble (exactProdOneSubInvPredLb 3 c.z 24) &&
  (exactProdOneSubInvPredUb 3 c.z 24).ble lo.vFullUb &&
  checkLowerRatLb lo.useAnalytic p2 lo.mOdd lo.ratLb lo.gLb

/-- Soundness of `checkLower2abWitness`: constructs `LowerEngine2ab.oddBonf` at `X_lo = c.X_lo`,
together with `lo_eng.rOdd = lo.ratLb.toReal`, `lo.vFullLb.toReal ≤ VN 2 c.z`,
`VN 2 c.z ≤ lo.vFullUb.toReal`, and `lo_eng.remA li2 ≤ lo.nD * epdUb` whenever
`epdNormFn c.X_lo li2 c.X_lo ≤ epdUb`. -/
theorem checkLower2abWitness_sound (c : BuchstabSwitching.SlabCert) (lo : Lower2abWitness)
    (h : checkLower2abWitness c lo = true) :
    ∃ lo_eng : BuchstabSwitching.External.LowerEngine2ab c (c.X_lo : ℝ),
      lo_eng.rOdd = lo.ratLb.toReal ∧
      (∀ li2 epdUb : ℝ,
        BuchstabSwitching.epdNormFn (c.X_lo : ℝ) li2 (c.X_lo : ℝ) ≤ epdUb →
        0 ≤ epdUb →
        lo_eng.remA li2 ≤ (lo.nD : ℝ) * epdUb) ∧
      lo.vFullLb.toReal ≤ BuchstabSwitching.External.VN 2 c.z ∧
      BuchstabSwitching.External.VN 2 c.z ≤ lo.vFullUb.toReal := by
  unfold checkLower2abWitness at h
  set ps := oddPrimesList c.z
  set q1 := ps.take lo.a
  set p2 := ps.drop lo.a
  set k := 2 * lo.mOdd + 1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hz_ex, ha_le⟩, hd_prod⟩, hd_sq⟩, hnd_nat⟩, hv_lb⟩, hv_ub⟩, hrat_chk⟩
  have hps_lt : ps.Pairwise (· < ·) := oddPrimesList_pairwise_lt c.z
  have hps_pr : ∀ p ∈ ps, p.Prime ∧ 2 < p ∧ p < c.z := oddPrimesList_props c.z
  have hps_fin : ps.toFinset = BuchstabSwitching.fullOddPrimesBelow c.z :=
    oddPrimesList_toFinset hz_ex
  have htd : (q1 ++ p2).Pairwise (· < ·) := by
    dsimp only [q1, p2]
    rw [List.take_append_drop]
    exact hps_lt
  have hP2_lt : p2.Pairwise (· < ·) := (List.pairwise_append.mp htd).2.1
  have hP2_pr : ∀ p ∈ p2, p.Prime ∧ 2 < p := fun p hp =>
    let h := hps_pr p (List.mem_of_mem_drop hp); ⟨h.1, h.2.1⟩
  have hdisj : Disjoint q1.toFinset p2.toFinset := take_drop_disjoint hps_lt lo.a
  have hunion : q1.toFinset ∪ p2.toFinset = BuchstabSwitching.fullOddPrimesBelow c.z := by
    rw [take_drop_union, hps_fin]
  have hd_le : ∀ d ∈ BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k, (d : ℝ) ≤ (lo.dMax : ℝ) :=
    fun d hd => by
      exact_mod_cast (bonfDivisors_le_take_mul_rev_drop hps_lt
        (fun p hp => (hps_pr p hp).1.one_lt.le) lo.a k d hd).trans hd_prod
  have hd_sqrt : (lo.dMax : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast hd_sq
  have hnd : ((BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k).card : ℝ) ≤ (lo.nD : ℝ) := by
    exact_mod_cast (card_bonfDivisors_take_drop hps_lt (fun p hp => (hps_pr p hp).1) ha_le k).trans_le hnd_nat
  have hrat : lo.ratLb.toReal ≤ BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset k :=
    checkLowerRatLb_sound hP2_lt hP2_pr hrat_chk
  let spec : BuchstabSwitching.External.OddBonfLowerSpec c (c.X_lo : ℝ) :=
    { Q₁ := q1.toFinset
      P₂ := p2.toFinset
      hdisj := hdisj
      hunion := hunion
      m_odd := lo.mOdd
      d_max := (lo.dMax : ℝ)
      hd_le := hd_le
      hd_sqrt := hd_sqrt
      n_d := (lo.nD : ℝ)
      rat_lb := lo.ratLb.toReal
      hnd := hnd
      hrat := hrat }
  refine ⟨.oddBonf spec, rfl, fun li2 epdUb hepd _ => ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left hepd (Nat.cast_nonneg _)
  · exact (SciProofs.ble_sound hv_lb).trans (exactProdOneSubInvPredLb_le_VN_two hz_ex 24)
  · exact (VN_two_le_exactProdOneSubInvPredUb hz_ex 24).trans (SciProofs.ble_sound hv_ub)

end Lower2abChecker

end

end BuchstabSwitching.SieveInst
