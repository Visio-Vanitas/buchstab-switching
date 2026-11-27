import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstElemBounds
import BuchstabSwitching.Sieve.Regime2SlabBridge.BonferroniHelpers
import BuchstabSwitching.External.MultiplicativeBounds.SlabSieveEngineWiring
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Soundness Helpers & Lower-Sieve Witness Verification for Regimes `2a` & `2b` (`Dyadic` + Q64)

Provides:
1. `List ℕ` -> `Finset ℕ` splitting lemmas for `Q₁ ∪ P₂ = fullOddPrimesBelow z` and
   `bonfDivisors` size/product bounds (`fastChoose` + bitshifts `1 <<< a`).
2. Division-free Q64 accumulators over `List PrimeLeafEntry` (`v2EntriesLb`, `v2EntriesUb`,
   `invPhiEntriesUb`, `sumG1EntriesUb`, `sumG2EntriesUb`) and `elemSymSums` over `elemSymInterval64`.
3. Witness-verified `checkAnalyticV2Lb` and `checkLower2abWitness` + `checkLower2abWitness_sound`
   constructing `LowerEngine2ab.oddBonf`.
-/

namespace BuchstabSwitching.SieveInst

section

section PrimeListSplitting

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
  exact ⟨by rintro (h | h); exact List.mem_of_mem_take h; exact List.mem_of_mem_drop h,
    fun h => List.mem_append.mp (by rwa [List.take_append_drop])⟩

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
    rwa [hrev_fin] at hres
  have htake_prod :
      ∏ p ∈ (((ps.drop a).toFinset.sort (· ≥ ·)).take k).toFinset, p =
        ((ps.drop a).reverse.take k).prod := by
    rw [hsort]; simpa using List.prod_toFinset (fun x => x) hrev_nd.take
  rwa [hQ_prod, htake_prod] at hbd

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

private lemma foldl_add_nat_eq_local (L : List ℕ) (f : ℕ → ℕ) (acc : ℕ) :
    L.foldl (fun s x => s + f x) acc = acc + (L.map f).sum := by
  induction L generalizing acc with
  | nil => simp
  | cons x tl ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

lemma foldl_range_sum_eq (n : ℕ) (f : ℕ → ℕ) :
    (List.range n).foldl (fun s x => s + f x) 0 = ∑ x ∈ Finset.range n, f x := by
  rw [foldl_add_nat_eq_local, zero_add]
  induction n with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

def bonfCardNat (a len k : ℕ) : ℕ :=
  (1 <<< a) * ((List.range (k + 1)).foldl (fun acc j => acc + fastChoose len j) 0)

lemma bonfCardNat_eq (a len k : ℕ) :
    bonfCardNat a len k = 2 ^ a * ∑ j ∈ Finset.range (k + 1), len.choose j := by
  unfold bonfCardNat
  rw [Nat.shiftLeft_eq, Nat.one_mul, foldl_range_sum_eq]
  congr 1
  exact Finset.sum_congr rfl fun j _ => fastChoose_eq_choose len j

end PrimeListSplitting

section FastEntryAccumulators

private def foldProdQ64Lb (val64 : PrimeLeafEntry → ℕ) (acc : ℕ) (es : List PrimeLeafEntry) : ℕ :=
  es.foldl (fun a e => (a * val64 e) >>> 64) acc

private def foldProdQ64Ub (val64 : PrimeLeafEntry → ℕ) (acc : ℕ) (es : List PrimeLeafEntry) : ℕ :=
  es.foldl (fun a e => Dyadic.ceilShr (a * val64 e) 64) acc

private def foldSumQ64Ub (val64 : PrimeLeafEntry → ℕ) (acc : ℕ) (es : List PrimeLeafEntry) : ℕ :=
  es.foldl (fun a e => a + val64 e) acc

private lemma foldProdQ64Lb_sound (val64 : PrimeLeafEntry → ℕ) (f : ℕ → ℝ)
    (es : List PrimeLeafEntry) :
    ∀ (acc : ℕ), (es.map PrimeLeafEntry.p).Nodup →
      (∀ e ∈ es, 0 ≤ f e.p ∧ ((val64 e : ℝ) / (q64Scale : ℝ)) ≤ f e.p) →
      ((foldProdQ64Lb val64 acc es : ℕ) : ℝ) / (q64Scale : ℝ) ≤
        ((acc : ℝ) / (q64Scale : ℝ)) * ∏ p ∈ (es.map PrimeLeafEntry.p).toFinset, f p := by
  induction es with
  | nil => intro acc _ _; simp [foldProdQ64Lb]
  | cons e tl ih =>
    intro acc hnd hprop
    rw [List.map_cons, List.nodup_cons] at hnd
    have he := hprop e List.mem_cons_self
    have htl := fun x hx => hprop x (List.mem_cons_of_mem e hx)
    set acc' := (acc * val64 e) >>> 64
    have hrec := ih acc' hnd.2 htl
    have hprod_nn : 0 ≤ ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q :=
      Finset.prod_nonneg fun q hq => by
        rcases List.mem_map.mp (List.mem_toFinset.mp hq) with ⟨x, hx, rfl⟩
        exact (htl x hx).1
    have hstep : ((acc' : ℕ) : ℝ) / (q64Scale : ℝ) ≤ ((acc : ℝ) / (q64Scale : ℝ)) * f e.p :=
      (q64MulLb_le acc (val64 e)).trans
        (mul_le_mul_of_nonneg_left he.2 (div_nonneg (Nat.cast_nonneg _) q64Scale_pos.le))
    have hcons : foldProdQ64Lb val64 acc (e :: tl) = foldProdQ64Lb val64 acc' tl := by
      unfold foldProdQ64Lb; rw [List.foldl_cons]
    rw [hcons, List.map_cons, List.toFinset_cons,
      Finset.prod_insert (by simpa [List.mem_toFinset] using hnd.1)]
    calc ((foldProdQ64Lb val64 acc' tl : ℕ) : ℝ) / (q64Scale : ℝ)
        ≤ ((acc' : ℝ) / (q64Scale : ℝ)) * ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q := hrec
      _ ≤ ((acc : ℝ) / (q64Scale : ℝ)) * f e.p * ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q :=
          mul_le_mul_of_nonneg_right hstep hprod_nn
      _ = ((acc : ℝ) / (q64Scale : ℝ)) * (f e.p * ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q) := by ring

private lemma foldProdQ64Ub_sound (val64 : PrimeLeafEntry → ℕ) (f : ℕ → ℝ)
    (es : List PrimeLeafEntry) :
    ∀ (acc : ℕ), (es.map PrimeLeafEntry.p).Nodup →
      (∀ e ∈ es, 0 ≤ f e.p ∧ f e.p ≤ ((val64 e : ℝ) / (q64Scale : ℝ))) →
      ((acc : ℝ) / (q64Scale : ℝ)) * (∏ p ∈ (es.map PrimeLeafEntry.p).toFinset, f p) ≤
        ((foldProdQ64Ub val64 acc es : ℕ) : ℝ) / (q64Scale : ℝ) := by
  induction es with
  | nil => intro acc _ _; simp [foldProdQ64Ub]
  | cons e tl ih =>
    intro acc hnd hprop
    rw [List.map_cons, List.nodup_cons] at hnd
    have he := hprop e List.mem_cons_self
    have htl := fun x hx => hprop x (List.mem_cons_of_mem e hx)
    set acc' := Dyadic.ceilShr (acc * val64 e) 64
    have hrec := ih acc' hnd.2 htl
    have hprod_nn : 0 ≤ ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q :=
      Finset.prod_nonneg fun q hq => by
        rcases List.mem_map.mp (List.mem_toFinset.mp hq) with ⟨x, hx, rfl⟩
        exact (htl x hx).1
    have hstep : ((acc : ℝ) / (q64Scale : ℝ)) * f e.p ≤ ((acc' : ℕ) : ℝ) / (q64Scale : ℝ) :=
      (mul_le_mul_of_nonneg_left he.2 (div_nonneg (Nat.cast_nonneg _) q64Scale_pos.le)).trans
        (le_q64MulUb acc (val64 e))
    have hcons : foldProdQ64Ub val64 acc (e :: tl) = foldProdQ64Ub val64 acc' tl := by
      unfold foldProdQ64Ub; rw [List.foldl_cons]
    rw [hcons, List.map_cons, List.toFinset_cons,
      Finset.prod_insert (by simpa [List.mem_toFinset] using hnd.1)]
    calc ((acc : ℝ) / (q64Scale : ℝ)) * (f e.p * ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q)
        = ((acc : ℝ) / (q64Scale : ℝ)) * f e.p * ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q := by ring
      _ ≤ ((acc' : ℝ) / (q64Scale : ℝ)) * ∏ q ∈ (tl.map PrimeLeafEntry.p).toFinset, f q :=
          mul_le_mul_of_nonneg_right hstep hprod_nn
      _ ≤ ((foldProdQ64Ub val64 acc' tl : ℕ) : ℝ) / (q64Scale : ℝ) := hrec

private lemma foldSumQ64Ub_sound (val64 : PrimeLeafEntry → ℕ) (f : ℕ → ℝ)
    (es : List PrimeLeafEntry) :
    ∀ (acc : ℕ), (es.map PrimeLeafEntry.p).Nodup →
      (∀ e ∈ es, f e.p ≤ ((val64 e : ℝ) / (q64Scale : ℝ))) →
      ((acc : ℝ) / (q64Scale : ℝ)) + ∑ p ∈ (es.map PrimeLeafEntry.p).toFinset, f p ≤
        ((foldSumQ64Ub val64 acc es : ℕ) : ℝ) / (q64Scale : ℝ) := by
  induction es with
  | nil => intro acc _ _; simp [foldSumQ64Ub]
  | cons e tl ih =>
    intro acc hnd hprop
    rw [List.map_cons, List.nodup_cons] at hnd
    have he := hprop e List.mem_cons_self
    have htl := fun x hx => hprop x (List.mem_cons_of_mem e hx)
    set acc' := acc + val64 e
    have hrec := ih acc' hnd.2 htl
    have hcons : foldSumQ64Ub val64 acc (e :: tl) = foldSumQ64Ub val64 acc' tl := by
      unfold foldSumQ64Ub; rw [List.foldl_cons]
    rw [hcons, List.map_cons, List.toFinset_cons,
      Finset.sum_insert (by simpa [List.mem_toFinset] using hnd.1)]
    have hacc' : ((acc' : ℕ) : ℝ) / (q64Scale : ℝ) =
        (acc : ℝ) / (q64Scale : ℝ) + (val64 e : ℝ) / (q64Scale : ℝ) := by
      dsimp [acc']; push_cast; ring
    linarith [hrec, hacc', he]

def v2EntriesLb (es : List PrimeLeafEntry) : Dyadic :=
  Dyadic.ofQ64 (foldProdQ64Lb (·.vLb64) q64Scale es)
def v2EntriesUb (es : List PrimeLeafEntry) : Dyadic :=
  Dyadic.ofQ64 (foldProdQ64Ub (·.vUb64) q64Scale es)
def invPhiEntriesUb (es : List PrimeLeafEntry) : Dyadic :=
  Dyadic.ofQ64 (foldProdQ64Ub (·.phiUb64) q64Scale es)
def sumG1EntriesUb (es : List PrimeLeafEntry) : Dyadic :=
  Dyadic.ofQ64 (foldSumQ64Ub (·.gUb64) 0 es)
def sumG2EntriesUb (es : List PrimeLeafEntry) : Dyadic :=
  Dyadic.ofQ64 (foldSumQ64Ub (·.sqUb64) 0 es)

lemma v2EntriesLb_sound {es : List PrimeLeafEntry} (hnd : (es.map PrimeLeafEntry.p).Nodup)
    (hok : ∀ e ∈ es, checkPrimeLeafEntry e = true ∧ e.p.Prime) :
    (v2EntriesLb es).toReal ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset := by
  unfold v2EntriesLb BuchstabSwitching.V2
  rw [Dyadic.ofQ64_toReal]
  have h := foldProdQ64Lb_sound (·.vLb64) (fun p => 1 - BuchstabSwitching.gTot p) es q64Scale hnd
    (fun e he => by
      have hp := checkPrimeLeafEntry_props (hok e he).1
      have hbd := BuchstabSwitching.gTot_prime_bounds (hok e he).2 (by omega)
      refine ⟨by linarith [hbd.2], ?_⟩
      rw [BuchstabSwitching.gTot_prime (hok e he).2]; exact hp.2.2.2.2.2.1)
  rwa [div_self q64Scale_pos.ne', one_mul] at h

lemma v2EntriesUb_sound {es : List PrimeLeafEntry} (hnd : (es.map PrimeLeafEntry.p).Nodup)
    (hok : ∀ e ∈ es, checkPrimeLeafEntry e = true ∧ e.p.Prime) :
    BuchstabSwitching.V2 BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset ≤ (v2EntriesUb es).toReal := by
  unfold v2EntriesUb BuchstabSwitching.V2
  rw [Dyadic.ofQ64_toReal]
  have h := foldProdQ64Ub_sound (·.vUb64) (fun p => 1 - BuchstabSwitching.gTot p) es q64Scale hnd
    (fun e he => by
      have hp := checkPrimeLeafEntry_props (hok e he).1
      have hbd := BuchstabSwitching.gTot_prime_bounds (hok e he).2 (by omega)
      refine ⟨by linarith [hbd.2], ?_⟩
      rw [BuchstabSwitching.gTot_prime (hok e he).2]; exact hp.2.2.2.2.2.2.1)
  rwa [div_self q64Scale_pos.ne', one_mul] at h

lemma invPhiEntriesUb_sound {es : List PrimeLeafEntry} (hnd : (es.map PrimeLeafEntry.p).Nodup)
    (hok : ∀ e ∈ es, checkPrimeLeafEntry e = true) :
    (∏ p ∈ (es.map PrimeLeafEntry.p).toFinset, (p : ℝ) / ((p : ℝ) - 1)) ≤ (invPhiEntriesUb es).toReal := by
  unfold invPhiEntriesUb
  rw [Dyadic.ofQ64_toReal]
  have h := foldProdQ64Ub_sound (·.phiUb64) (fun p => (p : ℝ) / ((p : ℝ) - 1)) es q64Scale hnd
    (fun e he => by
      have hp := checkPrimeLeafEntry_props (hok e he)
      have hp3 : (3 : ℝ) ≤ (e.p : ℝ) := by exact_mod_cast hp.1
      exact ⟨div_nonneg (by positivity) (by linarith), hp.2.2.2.2.2.2.2⟩)
  rwa [div_self q64Scale_pos.ne', one_mul] at h

lemma sumG1EntriesUb_sound {es : List PrimeLeafEntry} (hnd : (es.map PrimeLeafEntry.p).Nodup)
    (hok : ∀ e ∈ es, checkPrimeLeafEntry e = true ∧ e.p.Prime) :
    ∑ p ∈ (es.map PrimeLeafEntry.p).toFinset, BuchstabSwitching.gTot p ≤ (sumG1EntriesUb es).toReal := by
  unfold sumG1EntriesUb
  rw [Dyadic.ofQ64_toReal]
  have h := foldSumQ64Ub_sound (·.gUb64) BuchstabSwitching.gTot es 0 hnd (fun e he => by
    rw [BuchstabSwitching.gTot_prime (hok e he).2]
    exact (checkPrimeLeafEntry_props (hok e he).1).2.2.1)
  simpa using h

lemma sumG2EntriesUb_sound {es : List PrimeLeafEntry} (hnd : (es.map PrimeLeafEntry.p).Nodup)
    (hok : ∀ e ∈ es, checkPrimeLeafEntry e = true ∧ e.p.Prime) :
    ∑ p ∈ (es.map PrimeLeafEntry.p).toFinset, (BuchstabSwitching.gTot p) ^ 2 ≤ (sumG2EntriesUb es).toReal := by
  unfold sumG2EntriesUb
  rw [Dyadic.ofQ64_toReal]
  have h := foldSumQ64Ub_sound (·.sqUb64) (fun p => (BuchstabSwitching.gTot p) ^ 2) es 0 hnd (fun e he => by
    rw [BuchstabSwitching.gTot_prime (hok e he).2, one_div_pow]
    exact (checkPrimeLeafEntry_props (hok e he).1).2.2.2.2.1)
  simpa using h

end FastEntryAccumulators

section ElemSymSums

def elemSymStep64 (e : PrimeLeafEntry) (dp : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (q64Scale, q64Scale) :: List.zipWith (fun cur prev =>
    (cur.1 + ((e.gLb64 * prev.1) >>> 64),
     cur.2 + Dyadic.ceilShr (e.gUb64 * prev.2) 64)) dp.tail dp

def elemSymInterval64 (es : List PrimeLeafEntry) (m : ℕ) : List (Dyadic × Dyadic) :=
  (es.foldl (fun dp e => elemSymStep64 e dp)
    ((q64Scale, q64Scale) :: List.replicate m (0, 0))).map
    (fun pair => (Dyadic.ofQ64 pair.1, Dyadic.ofQ64 pair.2))

private lemma elemSymStep64_length (e : PrimeLeafEntry) {dp : List (ℕ × ℕ)} {m : ℕ}
    (hdp : dp.length = m + 1) : (elemSymStep64 e dp).length = m + 1 := by
  simp [elemSymStep64, hdp]

private lemma foldl_elemSymStep64_length (es : List PrimeLeafEntry) (m : ℕ) :
    ∀ dp : List (ℕ × ℕ), dp.length = m + 1 →
      (es.foldl (fun acc e => elemSymStep64 e acc) dp).length = m + 1 := by
  induction es with
  | nil => intro dp hdp; exact hdp
  | cons e tl ih => intro dp hdp; rw [List.foldl_cons]; exact ih _ (elemSymStep64_length e hdp)

lemma elemSymInterval64_length (es : List PrimeLeafEntry) (m : ℕ) :
    (elemSymInterval64 es m).length = m + 1 := by
  simp [elemSymInterval64, foldl_elemSymStep64_length]

private lemma elemSymStep64_sound {e : PrimeLeafEntry}
    (hok : checkPrimeLeafEntry e = true) (hp : e.p.Prime) {T : Finset ℕ} (hpT : e.p ∉ T)
    {dp : List (ℕ × ℕ)} {m : ℕ} (hdp : dp.length = m + 1)
    (hinv : ∀ j (hj : j ≤ m),
      ((dp[j]'(by omega)).1 : ℝ) / (q64Scale : ℝ) ≤ BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ≤ ((dp[j]'(by omega)).2 : ℝ) / (q64Scale : ℝ)) :
    ∀ j (hj : j ≤ m),
      (((elemSymStep64 e dp)[j]'(by rw [elemSymStep64_length e hdp]; omega)).1 : ℝ) / (q64Scale : ℝ) ≤
        BuchstabSwitching.elemSym BuchstabSwitching.gTot (insert e.p T) j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot (insert e.p T) j ≤
        (((elemSymStep64 e dp)[j]'(by rw [elemSymStep64_length e hdp]; omega)).2 : ℝ) / (q64Scale : ℝ) := by
  intro j hj
  cases j with
  | zero =>
    simp [elemSymStep64, div_self q64Scale_pos.ne', BuchstabSwitching.elemSym_zero]
  | succ k =>
    have hk_dp : k < dp.length := by omega
    have hk1_dp : k + 1 < dp.length := by omega
    have hget : (elemSymStep64 e dp)[k + 1]'(by rw [elemSymStep64_length e hdp]; omega) =
        ((dp[k + 1]'hk1_dp).1 + ((e.gLb64 * (dp[k]'hk_dp).1) >>> 64),
         (dp[k + 1]'hk1_dp).2 + Dyadic.ceilShr (e.gUb64 * (dp[k]'hk_dp).2) 64) := by
      simp [elemSymStep64, List.getElem_zipWith, List.getElem_tail]
    rw [hget, BuchstabSwitching.elemSym_insert BuchstabSwitching.gTot hpT k]
    dsimp only
    have he_props := checkPrimeLeafEntry_props hok
    have hw_lo : (e.gLb64 : ℝ) / (q64Scale : ℝ) ≤ BuchstabSwitching.gTot e.p := by
      rw [BuchstabSwitching.gTot_prime hp]; exact he_props.2.1
    have hw_ub : BuchstabSwitching.gTot e.p ≤ (e.gUb64 : ℝ) / (q64Scale : ℝ) := by
      rw [BuchstabSwitching.gTot_prime hp]; exact he_props.2.2.1
    have hcur := hinv (k + 1) hj
    have hprev := hinv k (by omega)
    have hprev_nn : 0 ≤ BuchstabSwitching.elemSym BuchstabSwitching.gTot T k :=
      BuchstabSwitching.elemSym_nonneg (fun q _ => BuchstabSwitching.gTot_nonneg q) k
    constructor
    · rw [Nat.cast_add, add_div]
      refine add_le_add hcur.1 ((q64MulLb_le e.gLb64 (dp[k]'hk_dp).1).trans ?_)
      exact mul_le_mul hw_lo hprev.1 (div_nonneg (Nat.cast_nonneg _) q64Scale_pos.le)
        (BuchstabSwitching.gTot_nonneg e.p)
    · rw [Nat.cast_add, add_div]
      refine add_le_add hcur.2 (le_trans ?_ (le_q64MulUb e.gUb64 (dp[k]'hk_dp).2))
      exact mul_le_mul hw_ub hprev.2 hprev_nn (div_nonneg (Nat.cast_nonneg _) q64Scale_pos.le)

private lemma elemSymInterval64Aux_sound (es : List PrimeLeafEntry) (m : ℕ) :
    ∀ (T : Finset ℕ) (dp : List (ℕ × ℕ)) (hdp : dp.length = m + 1),
      (es.map PrimeLeafEntry.p).Nodup → (∀ e ∈ es, checkPrimeLeafEntry e = true ∧ e.p.Prime ∧ e.p ∉ T) →
      (∀ j (hj : j ≤ m),
        ((dp[j]'(by omega)).1 : ℝ) / (q64Scale : ℝ) ≤ BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ∧
        BuchstabSwitching.elemSym BuchstabSwitching.gTot T j ≤ ((dp[j]'(by omega)).2 : ℝ) / (q64Scale : ℝ)) →
      ∀ j (hj : j ≤ m),
        (((es.foldl (fun acc e => elemSymStep64 e acc) dp)[j]'(by
          rw [foldl_elemSymStep64_length es m dp hdp]; omega)).1 : ℝ) / (q64Scale : ℝ) ≤
          BuchstabSwitching.elemSym BuchstabSwitching.gTot (T ∪ (es.map PrimeLeafEntry.p).toFinset) j ∧
        BuchstabSwitching.elemSym BuchstabSwitching.gTot (T ∪ (es.map PrimeLeafEntry.p).toFinset) j ≤
          (((es.foldl (fun acc e => elemSymStep64 e acc) dp)[j]'(by
            rw [foldl_elemSymStep64_length es m dp hdp]; omega)).2 : ℝ) / (q64Scale : ℝ) := by
  induction es with
  | nil => intro T dp hdp _ _ hinv j hj; simpa using hinv j hj
  | cons e tl ih =>
    intro T dp hdp hnd hes hinv j hj
    rw [List.map_cons, List.nodup_cons] at hnd
    have he := hes e List.mem_cons_self
    have hstep := elemSymStep64_sound he.1 he.2.1 he.2.2 hdp hinv
    have hrec := ih (insert e.p T) (elemSymStep64 e dp) (elemSymStep64_length e hdp) hnd.2
      (fun x hx => ⟨(hes x (List.mem_cons_of_mem e hx)).1, (hes x (List.mem_cons_of_mem e hx)).2.1,
        fun hmem => by
          rcases Finset.mem_insert.mp hmem with hxp | hmem
          · exact hnd.1 (hxp ▸ List.mem_map_of_mem hx)
          · exact (hes x (List.mem_cons_of_mem e hx)).2.2 hmem⟩) hstep j hj
    have hun : insert e.p T ∪ (tl.map PrimeLeafEntry.p).toFinset = T ∪ ((e :: tl).map PrimeLeafEntry.p).toFinset := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, List.map_cons, List.toFinset_cons]; tauto
    simpa [List.foldl_cons, hun] using hrec

theorem elemSymInterval64_sound {es : List PrimeLeafEntry} (hnodup : (es.map PrimeLeafEntry.p).Nodup)
    (hok : ∀ e ∈ es, checkPrimeLeafEntry e = true ∧ e.p.Prime) (m : ℕ) :
    ∀ j (hj : j ≤ m),
      ((elemSymInterval64 es m)[j]'(by rw [elemSymInterval64_length]; omega)).1.toReal ≤
        BuchstabSwitching.elemSym BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset j ≤
        ((elemSymInterval64 es m)[j]'(by rw [elemSymInterval64_length]; omega)).2.toReal := by
  have hinit : ∀ j (hj : j ≤ m),
      ((((q64Scale, q64Scale) :: List.replicate m (0, 0) : List (ℕ × ℕ))[j]'(by simp; omega)).1 : ℝ) / (q64Scale : ℝ) ≤
        BuchstabSwitching.elemSym BuchstabSwitching.gTot ∅ j ∧
      BuchstabSwitching.elemSym BuchstabSwitching.gTot ∅ j ≤
        ((((q64Scale, q64Scale) :: List.replicate m (0, 0) : List (ℕ × ℕ))[j]'(by simp; omega)).2 : ℝ) / (q64Scale : ℝ) := by
    intro j hj; cases j with
    | zero => simp [div_self q64Scale_pos.ne', BuchstabSwitching.elemSym_zero]
    | succ k =>
      simp [BuchstabSwitching.elemSym_eq_zero_of_lt (show (∅ : Finset ℕ).card < k + 1 by simp)]
  have hres := elemSymInterval64Aux_sound es m ∅
    ((q64Scale, q64Scale) :: List.replicate m (0, 0)) (by simp)
    hnodup (fun e he => ⟨(hok e he).1, (hok e he).2, by simp⟩) hinit
  intro j hj
  have hj_res := hres j hj
  simpa [elemSymInterval64, List.getElem_map, Dyadic.ofQ64_toReal] using hj_res

/-- Accumulates `(evenLo, evenHi, oddLo, oddHi)` over an interval DP list `dp`. -/
def elemSymSumsAux : ℕ → List (Dyadic × Dyadic) →
    Dyadic × Dyadic × Dyadic × Dyadic → Dyadic × Dyadic × Dyadic × Dyadic
  | _, [], acc => acc
  | j, (lo, hi) :: rest, (eLo, eHi, oLo, oHi) =>
    if j % 2 == 0 then
      elemSymSumsAux (j + 1) rest (eLo.add lo, eHi.add hi, oLo, oHi)
    else
      elemSymSumsAux (j + 1) rest (eLo, eHi, oLo.add lo, oHi.add hi)

def elemSymSums (dp : List (Dyadic × Dyadic)) : Dyadic × Dyadic × Dyadic × Dyadic :=
  elemSymSumsAux 0 dp (dyZero, dyZero, dyZero, dyZero)

private lemma elemSymSumsAux_sound : ∀ (dp : List (Dyadic × Dyadic)) (j : ℕ)
    (acc : Dyadic × Dyadic × Dyadic × Dyadic) (f : ℕ → ℝ),
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
      have hk1 := hf (k + 1) (by simp; omega)
      simpa [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 k] using hk1
    have hsplit1 : ∑ k ∈ Finset.range (rest.length + 1), (-1 : ℝ) ^ (j + k) * f (j + k) =
        (-1 : ℝ) ^ j * f j +
          ∑ k ∈ Finset.range rest.length, (-1 : ℝ) ^ (j + 1 + k) * f (j + 1 + k) := by
      rw [Finset.sum_range_succ']; simp only [Nat.add_zero]; rw [add_comm]
      congr 1; refine Finset.sum_congr rfl fun k _ => ?_; rw [show j + (k + 1) = j + 1 + k by omega]
    have hsplit2 : ∑ k ∈ Finset.range (rest.length + 1), f (j + k) =
        f j + ∑ k ∈ Finset.range rest.length, f (j + 1 + k) := by
      rw [Finset.sum_range_succ']; simp only [Nat.add_zero]; rw [add_comm]
      congr 1; refine Finset.sum_congr rfl fun k _ => ?_; rw [show j + (k + 1) = j + 1 + k by omega]
    by_cases hj : j % 2 == 0
    · have hj_even : Even j := Nat.even_iff.mpr (beq_iff_eq.mp hj)
      have hpow : (-1 : ℝ) ^ j = 1 := hj_even.neg_one_pow
      have hrec := elemSymSumsAux_sound rest (j + 1) (eLo.add lo, eHi.add hi, oLo, oHi) f hf_rest
      simp only [elemSymSumsAux, hj, ↓reduceIte, List.length_cons] at hrec ⊢
      rw [Dyadic.add_toReal, Dyadic.add_toReal] at hrec
      rw [hsplit1, hsplit2, hpow, one_mul]
      exact ⟨by linarith [hrec.1], by linarith [hrec.2.1], by linarith [hrec.2.2]⟩
    · have hj_mod : j % 2 = 1 := by
        have hne : j % 2 ≠ 0 := fun h0 => hj (beq_iff_eq.mpr h0); omega
      have hj_odd : Odd j := Nat.odd_iff.mpr hj_mod
      have hpow : (-1 : ℝ) ^ j = -1 := hj_odd.neg_one_pow
      have hrec := elemSymSumsAux_sound rest (j + 1) (eLo, eHi, oLo.add lo, oHi.add hi) f hf_rest
      simp only [elemSymSumsAux, hj, ↓reduceIte, Bool.false_eq_true, List.length_cons] at hrec ⊢
      rw [Dyadic.add_toReal, Dyadic.add_toReal] at hrec
      rw [hsplit1, hsplit2, hpow]
      exact ⟨by linarith [hrec.1], by linarith [hrec.2.1], by linarith [hrec.2.2]⟩

lemma elemSymSums_interval64_sound {es : List PrimeLeafEntry} (hnd : (es.map PrimeLeafEntry.p).Nodup)
    (hok : ∀ e ∈ es, checkPrimeLeafEntry e = true ∧ e.p.Prime) (m : ℕ) :
    let res := elemSymSums (elemSymInterval64 es m)
    res.1.toReal - res.2.2.2.toReal ≤ BuchstabSwitching.gTrunc BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset m ∧
      BuchstabSwitching.gTrunc BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset m ≤ res.2.1.toReal - res.2.2.1.toReal ∧
      ∑ j ∈ Finset.range (m + 1), BuchstabSwitching.elemSym BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset j ≤
        (res.2.1.add res.2.2.2).toReal := by
  have hlen := elemSymInterval64_length es m
  have hdp := elemSymInterval64_sound hnd hok m
  have haux := elemSymSumsAux_sound (elemSymInterval64 es m) 0
    (dyZero, dyZero, dyZero, dyZero) (BuchstabSwitching.elemSym BuchstabSwitching.gTot (es.map PrimeLeafEntry.p).toFinset)
    (fun k hk => by simpa using hdp k (by omega))
  simp only [hlen, dyZero_toReal, sub_zero, add_zero, zero_add] at haux
  dsimp only
  rw [Dyadic.add_toReal]
  exact ⟨haux.1, haux.2.1, haux.2.2⟩

end ElemSymSums

section Lower2abChecker

/-- Division-free analytic `V2` lower-bound checker on `p2e` via `analytic_bonf_V2_lb` + `expUbDyadic`. -/
def checkAnalyticV2Lb (p2e : List PrimeLeafEntry) (c2Ub gLb : Dyadic) : Bool :=
  match p2e with
  | [] => decide (0 < gLb.m) && gLb.ble dyOne
  | eMin :: _ =>
    let s1Ub := sumG1EntriesUb p2e
    let s2Ub := sumG2EntriesUb p2e
    let (okExp, eUb) := expUbDyadic (s1Ub.add (c2Ub.mulUb s2Ub))
    decide (0 < gLb.m) &&
    (Dyadic.ofNat (eMin.p - 1)).ble (c2Ub.mulLb (Dyadic.ofNat (2 * (eMin.p - 2)))) &&
    okExp && (gLb.mulUb eUb).ble dyOne

lemma checkAnalyticV2Lb_sound {p2e : List PrimeLeafEntry}
    (hps : (p2e.map PrimeLeafEntry.p).Pairwise (· < ·))
    (hok : ∀ e ∈ p2e, checkPrimeLeafEntry e = true ∧ e.p.Prime)
    {c2Ub gLb : Dyadic} (h : checkAnalyticV2Lb p2e c2Ub gLb = true) :
    0 < gLb.toReal ∧ gLb.toReal ≤ BuchstabSwitching.V2 BuchstabSwitching.gTot (p2e.map PrimeLeafEntry.p).toFinset := by
  cases p2e with
  | nil =>
    simp only [checkAnalyticV2Lb, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpos : 0 < gLb.toReal := Dyadic.toReal_pos_of_m h.1
    have hle := (Dyadic.ble_sound h.2).trans_eq dyOne_toReal
    simpa [BuchstabSwitching.V2] using ⟨hpos, hle⟩
  | cons eMin tl =>
    unfold checkAnalyticV2Lb at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨h123, hmul1⟩
    rcases (Bool.and_eq_true _ _).mp h123 with ⟨h12, hokExp⟩
    rcases (Bool.and_eq_true _ _).mp h12 with ⟨hgpos_b, hc2⟩
    have hpos : 0 < gLb.toReal := Dyadic.toReal_pos_of_m (decide_eq_true_eq.mp hgpos_b)
    have heMin := hok eMin List.mem_cons_self
    have hpMin3 : 3 ≤ eMin.p := (checkPrimeLeafEntry_props heMin.1).1
    have hP2_min : ∀ p ∈ ((eMin :: tl).map PrimeLeafEntry.p).toFinset, p.Prime ∧ eMin.p ≤ p := by
      intro p hp
      rcases List.mem_map.mp (List.mem_toFinset.mp hp) with ⟨x, hx, rfl⟩
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact ⟨heMin.2, le_rfl⟩
      · rw [List.map_cons, List.pairwise_cons] at hps
        exact ⟨(hok x hx).2, (hps.1 x.p (List.mem_map_of_mem hmem)).le⟩
    have hnd := pairwise_lt_nodup hps
    have hS1 := sumG1EntriesUb_sound hnd hok
    have hS2 := sumG2EntriesUb_sound hnd hok
    have hV2 := BuchstabSwitching.analytic_bonf_V2_lb hpMin3 hP2_min hS1 hS2
    dsimp only at hV2
    have hc2_le : 1 / (2 * (1 - 1 / ((eMin.p : ℝ) - 1))) ≤ c2Ub.toReal := by
      have heq : 1 / (2 * (1 - 1 / ((eMin.p : ℝ) - 1))) =
          ((eMin.p - 1 : ℕ) : ℝ) / ((2 * (eMin.p - 2) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ eMin.p), Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ eMin.p),
          Nat.cast_one, Nat.cast_ofNat]
        have hp_r : (3 : ℝ) ≤ (eMin.p : ℝ) := by exact_mod_cast hpMin3
        have h1' : (eMin.p : ℝ) - 1 ≠ 0 := by linarith
        have h2' : (eMin.p : ℝ) - 2 ≠ 0 := by linarith
        have h1m : 1 - 1 / ((eMin.p : ℝ) - 1) = ((eMin.p : ℝ) - 2) / ((eMin.p : ℝ) - 1) := by
          field_simp [h1']; ring
        rw [h1m]; field_simp [h1', h2']
      have hden_pos : (0 : ℝ) < ((2 * (eMin.p - 2) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * (eMin.p - 2))
      rw [heq]
      exact Dyadic.div_le_of_ble_mulLb (by rw [Dyadic.ofNat_toReal]) hden_pos
        (by rw [Dyadic.ofNat_toReal]) hc2
    set s1Ub := sumG1EntriesUb (eMin :: tl)
    set s2Ub := sumG2EntriesUb (eMin :: tl)
    set eUb := (expUbDyadic (s1Ub.add (c2Ub.mulUb s2Ub))).2
    have hexp := (expUbDyadic_sound hokExp).1
    have he_pos : 0 < eUb.toReal := lt_of_lt_of_le (Real.exp_pos _) hexp
    have hmul_le : gLb.toReal * eUb.toReal ≤ 1 :=
      (Dyadic.le_mulUb gLb eUb).trans ((Dyadic.ble_sound hmul1).trans_eq dyOne_toReal)
    have hinv : gLb.toReal ≤ 1 / eUb.toReal := (le_div_iff₀ he_pos).mpr hmul_le
    have harg : -(s1Ub.add (c2Ub.mulUb s2Ub)).toReal ≤
        -(s1Ub.toReal + (1 / (2 * (1 - 1 / ((eMin.p : ℝ) - 1)))) * s2Ub.toReal) := by
      rw [Dyadic.add_toReal]
      have hc2s := (mul_le_mul_of_nonneg_right hc2_le s2Ub.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
      linarith
    refine ⟨hpos, hinv.trans ?_⟩
    rw [one_div]; refine (inv_anti₀ (Real.exp_pos _) hexp).trans ?_
    rw [← Real.exp_neg]; exact (Real.exp_le_exp.mpr harg).trans hV2

/-- Computable `RTrunc` odd lower-bound checker on `p2e`. -/
def checkLowerRatLb (useAnalytic : Bool) (p2e : List PrimeLeafEntry) (mOdd : ℕ)
    (ratLb c2Ub gLb errUb : Dyadic) : Bool :=
  let k := 2 * mOdd + 1
  if !useAnalytic then
    match p2e with
    | [] => ratLb.ble dyOne
    | _ :: _ =>
      let sums := elemSymSums (elemSymInterval64 p2e k)
      let gP2Ub := v2EntriesUb p2e
      ((ratLb.mulUb gP2Ub).add sums.2.2.2).ble sums.1
  else
    let s1Ub := sumG1EntriesUb p2e
    let errDen := (Dyadic.ofNat (Nat.factorial (k + 1))).mulLb gLb
    checkAnalyticV2Lb p2e c2Ub gLb &&
      match p2e with
      | [] => ratLb.ble dyOne
      | _ :: _ =>
        (s1Ub.powUb (k + 1)).ble (errUb.mulLb errDen) &&
        (ratLb.add errUb).ble dyOne

private lemma checkLowerRatLb_sound {useAnalytic : Bool} {p2e : List PrimeLeafEntry}
    (hP2_lt : (p2e.map PrimeLeafEntry.p).Pairwise (· < ·))
    (hP2_ok : ∀ e ∈ p2e, checkPrimeLeafEntry e = true ∧ e.p.Prime)
    {mOdd : ℕ} {ratLb c2Ub gLb errUb : Dyadic}
    (h : checkLowerRatLb useAnalytic p2e mOdd ratLb c2Ub gLb errUb = true) :
    ratLb.toReal ≤ BuchstabSwitching.RTrunc BuchstabSwitching.gTot (p2e.map PrimeLeafEntry.p).toFinset (2 * mOdd + 1) := by
  unfold checkLowerRatLb at h; dsimp only at h
  have hP2_nd : (p2e.map PrimeLeafEntry.p).Nodup := pairwise_lt_nodup hP2_lt
  have hP2_fin_pr : ∀ p ∈ (p2e.map PrimeLeafEntry.p).toFinset, p.Prime ∧ 2 < p := fun p hp => by
    rcases List.mem_map.mp (List.mem_toFinset.mp hp) with ⟨e, he, rfl⟩
    have hp3 := (checkPrimeLeafEntry_props (hP2_ok e he).1).1
    exact ⟨(hP2_ok e he).2, by omega⟩
  by_cases hana : useAnalytic = false
  · simp only [hana, Bool.not_false, ↓reduceIte] at h
    cases p2e with
    | nil =>
      rw [List.map_nil, List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
      exact (Dyadic.ble_sound h).trans_eq dyOne_toReal
    | cons e0 tl =>
      have hble := Dyadic.ble_sound h
      rw [Dyadic.add_toReal] at hble
      have hsum := elemSymSums_interval64_sound hP2_nd hP2_ok (2 * mOdd + 1)
      have hgUb := v2EntriesUb_sound hP2_nd hP2_ok
      have hV2_pos : 0 < BuchstabSwitching.V2 BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset :=
        BuchstabSwitching.V2_pos fun p hp =>
          (BuchstabSwitching.gTot_prime_bounds (hP2_fin_pr p hp).1 (hP2_fin_pr p hp).2).2
      have hmul_le : ratLb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset ≤
          BuchstabSwitching.gTrunc BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset (2 * mOdd + 1) := by
        have h1 : ratLb.toReal * BuchstabSwitching.V2 BuchstabSwitching.gTot ((e0 :: tl).map PrimeLeafEntry.p).toFinset ≤
            (ratLb.mulUb (v2EntriesUb (e0 :: tl))).toReal :=
          (mul_le_mul_of_nonneg_left hgUb ratLb.toReal_nonneg).trans (Dyadic.le_mulUb _ _)
        linarith [hsum.1]
      rw [BuchstabSwitching.RTrunc]
      exact (le_div_iff₀ hV2_pos).mpr hmul_le
  · have hana_t : useAnalytic = true := Bool.eq_true_of_not_eq_false hana
    simp only [hana_t, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨hv2_chk, hm_chk⟩
    have hg := checkAnalyticV2Lb_sound hP2_lt hP2_ok hv2_chk
    cases p2e with
    | nil =>
      rw [List.map_nil, List.toFinset_nil, BuchstabSwitching.RTrunc_empty]
      exact (Dyadic.ble_sound hm_chk).trans_eq dyOne_toReal
    | cons e0 tl =>
      rcases (Bool.and_eq_true _ _).mp hm_chk with ⟨herr_ble, hadd_ble⟩
      have hS1 := sumG1EntriesUb_sound hP2_nd hP2_ok
      have hR := BuchstabSwitching.analytic_bonf_RTrunc_odd_lb hP2_fin_pr mOdd hg.1 hg.2 hS1
      set s1Ub := sumG1EntriesUb (e0 :: tl)
      have hk_eq : (2 * mOdd + 1) + 1 = 2 * mOdd + 2 := by omega
      have hden_le : ((Dyadic.ofNat (Nat.factorial (2 * mOdd + 2))).mulLb gLb).toReal ≤
          (Nat.factorial (2 * mOdd + 2) : ℝ) * gLb.toReal :=
        (Dyadic.mulLb_le _ _).trans (by rw [Dyadic.ofNat_toReal])
      have herr_le : s1Ub.toReal ^ (2 * mOdd + 2) /
          ((Nat.factorial (2 * mOdd + 2) : ℝ) * gLb.toReal) ≤ errUb.toReal := by
        rw [hk_eq] at herr_ble
        exact Dyadic.div_le_of_ble_mulLb (Dyadic.powUb_sound s1Ub (2 * mOdd + 2))
          (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hg.1) hden_le herr_ble
      have hsum1 : ratLb.toReal + errUb.toReal ≤ 1 := by
        have hb := (Dyadic.ble_sound hadd_ble).trans_eq dyOne_toReal
        rwa [Dyadic.add_toReal] at hb
      linarith

/-- Computable Regime `2a`/`2b` lower-sieve witness verifier (`LowerEngine2ab.oddBonf`). -/
def checkLower2abWitness (c : BuchstabSwitching.SlabCert) (lo : Lower2abWitness) : Bool :=
  let es := oddPrimeEntriesList c.z
  let ps := es.map PrimeLeafEntry.p
  let q1 := ps.take lo.a
  let p2 := ps.drop lo.a
  let p2e := es.drop lo.a
  let k := 2 * lo.mOdd + 1
  decide (c.z ≤ pExact) &&
  decide (lo.a ≤ ps.length) &&
  decide (q1.prod * (p2.reverse.take k).prod ≤ lo.dMax) &&
  decide (lo.dMax ^ 2 ≤ c.X_lo) &&
  decide (bonfCardNat lo.a p2.length k ≤ lo.nD) &&
  lo.vFullLb.ble (exactProdOneSubInvPredLb 3 c.z) &&
  (exactProdOneSubInvPredUb 3 c.z).ble lo.vFullUb &&
  checkLowerRatLb lo.useAnalytic p2e lo.mOdd lo.ratLb lo.c2Ub lo.gLb lo.errUb

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
  set es := oddPrimeEntriesList c.z
  set ps := es.map PrimeLeafEntry.p
  set q1 := ps.take lo.a
  set p2 := ps.drop lo.a
  set p2e := es.drop lo.a
  set k := 2 * lo.mOdd + 1
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hz_ex, ha_le, hd_prod, hd_sq, hnd_nat, hv_lb, hv_ub, hrat_chk⟩
  have hps_eq : ps = oddPrimesList c.z := rfl
  have hps_lt : ps.Pairwise (· < ·) := hps_eq ▸ oddPrimesList_pairwise_lt c.z
  have hps_pr : ∀ p ∈ ps, p.Prime ∧ 2 < p ∧ p < c.z := hps_eq ▸ oddPrimesList_props c.z
  have hps_fin : ps.toFinset = BuchstabSwitching.fullOddPrimesBelow c.z :=
    hps_eq ▸ oddPrimesList_toFinset hz_ex
  have hp2_map : p2e.map PrimeLeafEntry.p = p2 := by dsimp [p2e, p2, ps]; exact List.map_drop
  have htd : (q1 ++ p2).Pairwise (· < ·) := by dsimp only [q1, p2]; rw [List.take_append_drop]; exact hps_lt
  have hP2_lt : (p2e.map PrimeLeafEntry.p).Pairwise (· < ·) := hp2_map ▸ (List.pairwise_append.mp htd).2.1
  have hP2_ok : ∀ e ∈ p2e, checkPrimeLeafEntry e = true ∧ e.p.Prime := fun e he =>
    let ho := oddPrimeEntriesList_ok c.z e (List.mem_of_mem_drop he); ⟨ho.1, ho.2.1⟩
  have hdisj : Disjoint q1.toFinset p2.toFinset := take_drop_disjoint hps_lt lo.a
  have hunion : q1.toFinset ∪ p2.toFinset = BuchstabSwitching.fullOddPrimesBelow c.z := by
    rw [take_drop_union, hps_fin]
  have hd_le : ∀ d ∈ BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k, (d : ℝ) ≤ (lo.dMax : ℝ) :=
    fun d hd => by
      exact_mod_cast (bonfDivisors_le_take_mul_rev_drop hps_lt
        (fun p hp => (hps_pr p hp).1.one_lt.le) lo.a k d hd).trans hd_prod
  have hd_sqrt : (lo.dMax : ℝ) ≤ Real.sqrt (c.X_lo : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]; exact_mod_cast hd_sq
  have hnd : ((BuchstabSwitching.bonfDivisors q1.toFinset p2.toFinset k).card : ℝ) ≤ (lo.nD : ℝ) := by
    rw [bonfCardNat_eq] at hnd_nat
    exact_mod_cast (card_bonfDivisors_take_drop hps_lt (fun p hp => (hps_pr p hp).1) ha_le k).trans_le hnd_nat
  have hrat : lo.ratLb.toReal ≤ BuchstabSwitching.RTrunc BuchstabSwitching.gTot p2.toFinset k := by
    rw [← hp2_map]; exact checkLowerRatLb_sound hP2_lt hP2_ok hrat_chk
  let spec : BuchstabSwitching.External.OddBonfLowerSpec c (c.X_lo : ℝ) :=
    { Q₁ := q1.toFinset, P₂ := p2.toFinset, hdisj := hdisj, hunion := hunion,
      m_odd := lo.mOdd, d_max := (lo.dMax : ℝ), hd_le := hd_le, hd_sqrt := hd_sqrt,
      n_d := (lo.nD : ℝ), rat_lb := lo.ratLb.toReal, hnd := hnd, hrat := hrat }
  refine ⟨.oddBonf spec, rfl, fun li2 epdUb hepd _ => ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left hepd (Nat.cast_nonneg _)
  · exact (Dyadic.ble_sound hv_lb).trans (exactProdOneSubInvPredLb_le_VN_two hz_ex)
  · exact (VN_two_le_exactProdOneSubInvPredUb hz_ex).trans (Dyadic.ble_sound hv_ub)

end Lower2abChecker

end

end BuchstabSwitching.SieveInst
