import BuchstabSwitching.Sieve.RosserIwaniecComb.Weights
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Combinatorial Rosser–Iwaniec Main-Term Identities (`β = 2`)

Defines `sieveV`, `riTermCond`, `riTermPred`, `T_sum`, `WPlus`, `WMinus`, and proves
the recursion `T_sum_recursion` together with the exact main-term Buchstab identities
`ri_main_term_upper_eq` and `ri_main_term_lower_eq`.
-/

namespace BuchstabSwitching

noncomputable section

/-! ### 2. `T_sum`, Recursion, and Exact Main-Term Identities -/

/-- Euler-type sieve density product `V(g, P) = ∏_{p ∈ P} (1 - g(p))`. -/
def sieveV (g : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - g p)

/-- Rosser–Iwaniec remainder condition on a nonempty descending tuple `p_1 > ⋯ > p_n`:
every proper prefix `m < n` with `m ≡ n (mod 2)` satisfies `(∏_{j ≤ m} p_j) * p_m^2 < D`,
and the full `n`-tuple satisfies `D ≤ (∏_{j ≤ n} p_j) * p_n^2`. -/
def riTermCond (D : ℝ) : ℝ → List ℕ → Prop
  | _, [] => False
  | acc, [p] => D ≤ acc * (p : ℝ) ^ 3
  | acc, p :: q :: L =>
      (if L.length % 2 = 1 then acc * (p : ℝ) ^ 3 < D else True) ∧
        riTermCond D (acc * (p : ℝ)) (q :: L)

/-- Predicate on `S : Finset ℕ` expressing `riTermCond` on `descPrimes S`. -/
def riTermPred (D : ℝ) (S : Finset ℕ) : Prop := riTermCond D 1 (descPrimes S)

noncomputable instance instDecidablePredRiTermPred (D : ℝ) : DecidablePred (riTermPred D) :=
  Classical.decPred _

/-- Exact `n`-th Rosser–Iwaniec boundary sum `T_n(D, P)` weighted by `g`. -/
def T_sum (g : ℕ → ℝ) (n : ℕ) (D : ℝ) (P : Finset ℕ) : ℝ :=
  ∑ S ∈ (P.powersetCard n).filter (riTermPred D),
    if hS : S.Nonempty then
      (∏ p ∈ S, g p) * sieveV g (P.filter (· < S.min' hS))
    else 0

/-- Alternating Rosser–Iwaniec upper sieve sum weighted by `g`. -/
def WPlus (g : ℕ → ℝ) (D : ℝ) (P : Finset ℕ) : ℝ :=
  ∑ S ∈ P.powerset.filter (DPlus D), (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p

/-- Alternating Rosser–Iwaniec lower sieve sum weighted by `g`. -/
def WMinus (g : ℕ → ℝ) (D : ℝ) (P : Finset ℕ) : ℝ :=
  ∑ S ∈ P.powerset.filter (DMinus D), (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p

lemma riTermCond_iff_forall (D acc : ℝ) (L : List ℕ) (hL : 1 ≤ L.length) :
    riTermCond D acc L ↔
      (∀ (i : ℕ), i < L.length - 1 → i % 2 = (L.length - 1) % 2 →
        acc * (∏ j ∈ Finset.range (i + 1), (L.getD j 0 : ℝ)) * (L.getD i 0 : ℝ) ^ 2 < D) ∧
      D ≤ acc * (∏ j ∈ Finset.range L.length, (L.getD j 0 : ℝ)) *
        (L.getD (L.length - 1) 0 : ℝ) ^ 2 := by
  induction L generalizing acc with
  | nil => simp at hL
  | cons p L ih =>
      cases L with
      | nil =>
          simp [riTermCond, mul_assoc, pow_succ]
      | cons q L' =>
          have hqL : 1 ≤ (q :: L').length := by simp
          have ih' := ih (acc * (p : ℝ)) hqL
          simp only [riTermCond]
          constructor
          · rintro ⟨hhead, htail⟩
            rcases ih'.mp htail with ⟨ht1, ht2⟩
            refine ⟨fun i hi hpar => ?_, ?_⟩
            · cases i with
              | zero =>
                  have hlen_sub : (p :: q :: L').length - 1 = L'.length + 1 := by simp
                  have hodd : L'.length % 2 = 1 := by
                    rw [hlen_sub] at hpar
                    omega
                  simp only [hodd, ↓reduceIte] at hhead
                  simpa [Finset.prod_range_one, List.getD_cons_zero, mul_assoc, pow_succ] using hhead
              | succ i' =>
                  have hi' : i' < (q :: L').length - 1 := by simp at hi ⊢; omega
                  have hlen1 : (q :: L').length - 1 = L'.length := by simp
                  have hlen2 : (p :: q :: L').length - 1 = L'.length + 1 := by simp
                  have hpar' : i' % 2 = ((q :: L').length - 1) % 2 := by
                    rw [hlen1]; rw [hlen2] at hpar; omega
                  have hlt := ht1 i' hi' hpar'
                  rw [prod_range_cons_getD, List.getD_cons_succ]
                  simpa [mul_assoc] using hlt
            · have hlast :
                  (p :: q :: L').getD ((p :: q :: L').length - 1) 0 =
                    (q :: L').getD ((q :: L').length - 1) 0 := by
                simp
              rw [hlast, List.length_cons, prod_range_cons_getD]
              simpa [mul_assoc] using ht2
          · rintro ⟨h1, h2⟩
            refine ⟨?_, ih'.mpr ⟨?_, ?_⟩⟩
            · split_ifs with hodd
              have hpar0 : 0 % 2 = ((p :: q :: L').length - 1) % 2 := by
                have hlen2 : (p :: q :: L').length - 1 = L'.length + 1 := by simp
                rw [hlen2]; omega
              have h0 := h1 0 (by simp) hpar0
              simpa [Finset.prod_range_one, List.getD_cons_zero, mul_assoc, pow_succ] using h0
            · intro i' hi' hpar'
              have hi : i' + 1 < (p :: q :: L').length - 1 := by simp at hi' ⊢; omega
              have hlen1 : (q :: L').length - 1 = L'.length := by simp
              have hlen2 : (p :: q :: L').length - 1 = L'.length + 1 := by simp
              have hpar : (i' + 1) % 2 = ((p :: q :: L').length - 1) % 2 := by
                rw [hlen2]; rw [hlen1] at hpar'; omega
              have hlt := h1 (i' + 1) hi hpar
              rw [prod_range_cons_getD, List.getD_cons_succ] at hlt
              simpa [mul_assoc] using hlt
            · have hlast :
                  (p :: q :: L').getD ((p :: q :: L').length - 1) 0 =
                    (q :: L').getD ((q :: L').length - 1) 0 := by
                simp
              rw [hlast, List.length_cons, prod_range_cons_getD] at h2
              simpa [mul_assoc] using h2

lemma riTermCond_mul (D c acc : ℝ) (hc : 0 < c) (L : List ℕ) :
    riTermCond D (c * acc) L ↔ riTermCond (D / c) acc L := by
  induction L generalizing acc with
  | nil => simp [riTermCond]
  | cons p L ih =>
      cases L with
      | nil =>
          rw [riTermCond, riTermCond, div_le_iff₀ hc]
          constructor <;> intro h <;> linarith [show c * acc * (p : ℝ) ^ 3 = acc * (p : ℝ) ^ 3 * c by ring]
      | cons q L' =>
          simp only [riTermCond]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨?_, (ih (acc * (p : ℝ))).mp (by simpa [mul_assoc] using h2)⟩
            split_ifs with hodd
            simp only [hodd, ↓reduceIte] at h1
            rw [lt_div_iff₀ hc]
            linarith [show c * acc * (p : ℝ) ^ 3 = acc * (p : ℝ) ^ 3 * c by ring]
          · rintro ⟨h1, h2⟩
            refine ⟨?_, ?_⟩
            · split_ifs with hodd
              simp only [hodd, ↓reduceIte] at h1
              have h1' := (lt_div_iff₀ hc).mp h1
              linarith [show c * acc * (p : ℝ) ^ 3 = acc * (p : ℝ) ^ 3 * c by ring]
            · simpa [mul_assoc] using (ih (acc * (p : ℝ))).mpr h2

lemma riTermPred_singleton (D : ℝ) (p : ℕ) :
    riTermPred D {p} ↔ D ≤ (p : ℝ) ^ 3 := by
  simp [riTermPred, descPrimes_singleton, riTermCond]

lemma riTermPred_insert {D : ℝ} {p : ℕ} {S : Finset ℕ}
    (hp_pos : 0 < p) (hp_gt : ∀ q ∈ S, q < p) (hS : S.Nonempty) :
    riTermPred D (insert p S) ↔
      (if S.card % 2 = 0 then (p : ℝ) ^ 3 < D else True) ∧ riTermPred (D / (p : ℝ)) S := by
  have hp_real : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
  have hlen_pos : 0 < (descPrimes S).length := by
    rw [descPrimes, Finset.length_sort]
    exact Finset.card_pos.mpr hS
  obtain ⟨q, L', hL⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hlen_pos)
  have hlen : S.card = L'.length + 1 := by
    rw [← Finset.length_sort (s := S) (· ≥ ·)]
    change (descPrimes S).length = _
    rw [hL, List.length_cons]
  have hpar : S.card % 2 = 0 ↔ L'.length % 2 = 1 := by omega
  rw [riTermPred, descPrimes_insert hp_gt, hL, riTermCond]
  simp only [one_mul, hpar]
  have hsc := riTermCond_mul D (p : ℝ) 1 hp_real (q :: L')
  simpa [mul_one, riTermPred, hL] using and_congr_right fun _ => hsc

lemma T_sum_zero (g : ℕ → ℝ) (D : ℝ) (P : Finset ℕ) : T_sum g 0 D P = 0 := by
  rw [T_sum]
  refine Finset.sum_eq_zero fun S hS => ?_
  have hmem := Finset.mem_filter.mp hS
  have hcard : S.card = 0 := (Finset.mem_powersetCard.mp hmem.1).2
  have hS_empty : S = ∅ := Finset.card_eq_zero.mp hcard
  have hfalse : riTermPred D S := hmem.2
  simp [hS_empty, riTermPred, descPrimes_empty, riTermCond] at hfalse

lemma T_sum_eq_zero_of_card_lt {g : ℕ → ℝ} {n : ℕ} {D : ℝ} {P : Finset ℕ} (hn : P.card < n) :
    T_sum g n D P = 0 := by
  rw [T_sum]
  have hempty : P.powersetCard n = ∅ := by
    ext S
    simp only [Finset.mem_powersetCard, Finset.notMem_empty, iff_false, not_and]
    intro hSP hSc
    exact absurd (Finset.card_le_card hSP) (by omega)
  simp [hempty]

private lemma min'_insert_of_gt {p : ℕ} {S : Finset ℕ} (hp_gt : ∀ q ∈ S, q < p) (hS : S.Nonempty) :
    (insert p S).min' (Finset.insert_nonempty p S) = S.min' hS := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.min'_mem S hS))
  · refine Finset.le_min' (insert p S) (Finset.insert_nonempty p S) (S.min' hS) fun x hx => ?_
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact le_of_lt (hp_gt _ (Finset.min'_mem S hS))
    · exact Finset.min'_le _ _ hxS

private lemma filter_lt_insert_eq {P : Finset ℕ} {p : ℕ} {q : ℕ} (hq : q < p) :
    P.filter (· < q) = (P.filter (· < p)).filter (· < q) := by
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hxP, hxq⟩ => ⟨⟨hxP, lt_trans hxq hq⟩, hxq⟩, fun ⟨⟨hxP, _⟩, hxq⟩ => ⟨hxP, hxq⟩⟩

lemma T_sum_one (g : ℕ → ℝ) (D : ℝ) (P : Finset ℕ) :
    T_sum g 1 D P =
      ∑ p ∈ P.filter (fun p : ℕ => D ≤ (p : ℝ) ^ 3), g p * sieveV g (P.filter (· < p)) := by
  rw [T_sum]
  refine Finset.sum_bij (fun S hS => S.min' (Finset.card_pos.mp (by
      have := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
      omega))) ?_ ?_ ?_ ?_
  · intro S hS
    have hmem := Finset.mem_filter.mp hS
    rcases Finset.mem_powersetCard.mp hmem.1 with ⟨hSP, hcard⟩
    rcases Finset.card_eq_one.mp hcard with ⟨p, rfl⟩
    simp only [Finset.min'_singleton, Finset.mem_filter]
    exact ⟨hSP (Finset.mem_singleton_self p), (riTermPred_singleton D p).mp hmem.2⟩
  · intro S₁ hS₁ S₂ hS₂ heq
    have hc1 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS₁).1).2
    have hc2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS₂).1).2
    rcases Finset.card_eq_one.mp hc1 with ⟨p₁, rfl⟩
    rcases Finset.card_eq_one.mp hc2 with ⟨p₂, rfl⟩
    simp only [Finset.min'_singleton] at heq
    subst heq; rfl
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    refine ⟨{p}, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.singleton_subset_iff.mpr hp'.1,
      Finset.card_singleton p⟩, (riTermPred_singleton D p).mpr hp'.2⟩, by simp⟩
  · intro S hS
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
    rcases Finset.card_eq_one.mp hc with ⟨p, rfl⟩
    simp

/-- General recursion for `T_sum` at `n + 1` (`n ≥ 1`): sums over the largest chosen element `p ∈ P`. -/
theorem T_sum_recursion (g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (D : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    T_sum g (n + 1) D P =
      ∑ p ∈ P,
        if (if n % 2 = 0 then (p : ℝ) ^ 3 < D else True) then
          g p * T_sum g n (D / (p : ℝ)) (P.filter (· < p))
        else 0 := by
  rw [T_sum]
  symm
  calc ∑ p ∈ P,
        (if (if n % 2 = 0 then (p : ℝ) ^ 3 < D else True) then
          g p * T_sum g n (D / (p : ℝ)) (P.filter (· < p))
        else 0)
    _ = ∑ p ∈ P,
          ∑ S ∈ ((P.filter (· < p)).powersetCard n).filter
            (fun S => (if n % 2 = 0 then (p : ℝ) ^ 3 < D else True) ∧ riTermPred (D / (p : ℝ)) S),
            if hS : S.Nonempty then
              g p * ((∏ q ∈ S, g q) * sieveV g ((P.filter (· < p)).filter (· < S.min' hS)))
            else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hcond : (if n % 2 = 0 then (p : ℝ) ^ 3 < D else True)
        · have hfilt_eq :
              ((P.filter (· < p)).powersetCard n).filter (riTermPred (D / (p : ℝ))) =
              ((P.filter (· < p)).powersetCard n).filter
                (fun S => (if n % 2 = 0 then (p : ℝ) ^ 3 < D else True) ∧ riTermPred (D / (p : ℝ)) S) := by
            ext S
            simp only [Finset.mem_filter]
            exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hcond, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
          rw [← hfilt_eq]
          simp only [hcond, ↓reduceIte, T_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ => ?_
          split_ifs <;> ring
        · have hempty : ((P.filter (· < p)).powersetCard n).filter
              (fun S => (if n % 2 = 0 then (p : ℝ) ^ 3 < D else True) ∧
                riTermPred (D / (p : ℝ)) S) = ∅ := by
            ext S
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro _ hc _
            exact hcond hc
          rw [hempty, Finset.sum_empty]
          simp [hcond]
    _ = ∑ x ∈ P.sigma (fun p => ((P.filter (· < p)).powersetCard n).filter
            (fun S => (if n % 2 = 0 then (p : ℝ) ^ 3 < D else True) ∧ riTermPred (D / (p : ℝ)) S)),
          if hS : x.2.Nonempty then
            g x.1 * ((∏ q ∈ x.2, g q) * sieveV g ((P.filter (· < x.1)).filter (· < x.2.min' hS)))
          else 0 := by
        rw [Finset.sum_sigma]
    _ = ∑ S ∈ (P.powersetCard (n + 1)).filter (riTermPred D),
          if hS : S.Nonempty then
            (∏ p ∈ S, g p) * sieveV g (P.filter (· < S.min' hS))
          else 0 := by
        refine Finset.sum_bij (fun x _ => insert x.1 x.2) ?_ ?_ ?_ ?_
        · rintro ⟨p, S'⟩ hx
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powersetCard] at hx
          rcases hx with ⟨hpP, ⟨⟨hS'sub, hS'card⟩, hcond, hri'⟩⟩
          have hp_gt : ∀ q ∈ S', q < p := fun q hq => (Finset.mem_filter.mp (hS'sub hq)).2
          have hp_nmem : p ∉ S' := fun h => Nat.lt_irrefl p (hp_gt p h)
          have hS'ne : S'.Nonempty := Finset.card_pos.mp (by rw [hS'card]; omega)
          have hS'P : S' ⊆ P := fun q hq => (Finset.mem_filter.mp (hS'sub hq)).1
          rw [Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨Finset.insert_subset_iff.mpr ⟨hpP, hS'P⟩,
            by rw [Finset.card_insert_of_notMem hp_nmem, hS'card]⟩, ?_⟩
          rw [riTermPred_insert (hP p hpP) hp_gt hS'ne, hS'card]
          exact ⟨hcond, hri'⟩
        · rintro ⟨p₁, S₁⟩ hx₁ ⟨p₂, S₂⟩ hx₂ heq
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powersetCard] at hx₁ hx₂
          have hgt₁ : ∀ q ∈ S₁, q < p₁ := fun q hq => (Finset.mem_filter.mp (hx₁.2.1.1 hq)).2
          have hgt₂ : ∀ q ∈ S₂, q < p₂ := fun q hq => (Finset.mem_filter.mp (hx₂.2.1.1 hq)).2
          have hm₁ : (insert p₁ S₁).max' (Finset.insert_nonempty p₁ S₁) = p₁ := by
            apply le_antisymm
            · refine Finset.max'_le _ _ _ fun q hq => ?_
              rcases Finset.mem_insert.mp hq with rfl | hqS₁
              · exact le_rfl
              · exact le_of_lt (hgt₁ q hqS₁)
            · exact Finset.le_max' _ _ (Finset.mem_insert_self p₁ S₁)
          have hm₂ : (insert p₂ S₂).max' (Finset.insert_nonempty p₂ S₂) = p₂ := by
            apply le_antisymm
            · refine Finset.max'_le _ _ _ fun q hq => ?_
              rcases Finset.mem_insert.mp hq with rfl | hqS₂
              · exact le_rfl
              · exact le_of_lt (hgt₂ q hqS₂)
            · exact Finset.le_max' _ _ (Finset.mem_insert_self p₂ S₂)
          have hp_eq : p₁ = p₂ := by
            calc p₁ = (insert p₁ S₁).max' (Finset.insert_nonempty p₁ S₁) := hm₁.symm
              _ = (insert p₂ S₂).max' (Finset.insert_nonempty p₂ S₂) := by simp [heq]
              _ = p₂ := hm₂
          subst hp_eq
          have hn₁ : p₁ ∉ S₁ := fun h => Nat.lt_irrefl p₁ (hgt₁ p₁ h)
          have hn₂ : p₁ ∉ S₂ := fun h => Nat.lt_irrefl p₁ (hgt₂ p₁ h)
          have hS_eq : S₁ = S₂ := by
            have := congrArg (fun T => T.erase p₁) heq
            simpa [Finset.erase_insert hn₁, Finset.erase_insert hn₂] using this
          subst hS_eq; rfl
        · intro S hS
          rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
          rcases hS with ⟨⟨hSP, hScard⟩, hri⟩
          have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
          set p := S.max' hSne
          set S' := S.erase p
          have hpS : p ∈ S := Finset.max'_mem S hSne
          have hpP : p ∈ P := hSP hpS
          have hS'card : S'.card = n := by
            rw [Finset.card_erase_of_mem hpS, hScard]; omega
          have hS'ne : S'.Nonempty := Finset.card_pos.mp (by omega)
          have hp_gt : ∀ q ∈ S', q < p := fun q hq => by
            have hq' := Finset.mem_erase.mp hq
            exact lt_of_le_of_ne (Finset.le_max' S q hq'.2) hq'.1
          have hS'sub : S' ⊆ P.filter (· < p) := fun q hq =>
            Finset.mem_filter.mpr ⟨hSP (Finset.erase_subset p S hq), hp_gt q hq⟩
          have hS_eq : insert p S' = S := Finset.insert_erase hpS
          have hri' := hri
          rw [← hS_eq, riTermPred_insert (hP p hpP) hp_gt hS'ne, hS'card] at hri'
          refine ⟨⟨p, S'⟩, Finset.mem_sigma.mpr ⟨hpP, Finset.mem_filter.mpr
            ⟨Finset.mem_powersetCard.mpr ⟨hS'sub, hS'card⟩, hri'⟩⟩, hS_eq⟩
        · rintro ⟨p, S'⟩ hx
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powersetCard] at hx
          rcases hx with ⟨_, ⟨hS'sub, hS'card⟩, _⟩
          have hS'ne : S'.Nonempty := Finset.card_pos.mp (by rw [hS'card]; omega)
          have hp_gt : ∀ q ∈ S', q < p := fun q hq => (Finset.mem_filter.mp (hS'sub hq)).2
          have hp_nmem : p ∉ S' := fun h => Nat.lt_irrefl p (hp_gt p h)
          have hmin_lt : S'.min' hS'ne < p := hp_gt _ (Finset.min'_mem S' hS'ne)
          have hmin_eq : (insert p S').min' (Finset.insert_nonempty p S') = S'.min' hS'ne :=
            min'_insert_of_gt hp_gt hS'ne
          simp only [hS'ne, Finset.insert_nonempty, ↓reduceDIte,
            Finset.prod_insert hp_nmem, hmin_eq, ← filter_lt_insert_eq hmin_lt, mul_assoc]

theorem T_sum_recursion_even_step (g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hn_odd : n % 2 = 1)
    (D : ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    T_sum g (n + 1) D P = ∑ p ∈ P, g p * T_sum g n (D / (p : ℝ)) (P.filter (· < p)) := by
  rw [T_sum_recursion g n hn D P hP]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hne0 : n % 2 ≠ 0 := by omega
  simp [hne0]

theorem T_sum_recursion_odd_step (g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hn_even : n % 2 = 0)
    (D : ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    T_sum g (n + 1) D P =
      ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ^ 3 < D),
        g p * T_sum g n (D / (p : ℝ)) (P.filter (· < p)) := by
  rw [T_sum_recursion g n hn D P hP, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [hn_even]

/-! #### Splitting on `P.max'` for `sieveV`, `WPlus`, `WMinus`, and `T_sum` -/

private lemma filter_lt_max'_eq_erase {P : Finset ℕ} (hP : P.Nonempty) :
    P.filter (· < P.max' hP) = P.erase (P.max' hP) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hqP, hqlt⟩
    exact ⟨ne_of_lt hqlt, hqP⟩
  · rintro ⟨hqne, hqP⟩
    exact ⟨hqP, lt_of_le_of_ne (Finset.le_max' P q hqP) hqne⟩

private lemma sieveV_erase_max' (g : ℕ → ℝ) {P : Finset ℕ} (hP : P.Nonempty) :
    sieveV g P = sieveV g (P.erase (P.max' hP)) - g (P.max' hP) * sieveV g (P.erase (P.max' hP)) := by
  set p := P.max' hP
  set P' := P.erase p
  have hpP : p ∈ P := Finset.max'_mem P hP
  have hp_nmem : p ∉ P' := Finset.notMem_erase p P
  have hins : insert p P' = P := Finset.insert_erase hpP
  calc sieveV g P
    _ = ∏ q ∈ insert p P', (1 - g q) := by rw [sieveV, hins]
    _ = (1 - g p) * sieveV g P' := by rw [Finset.prod_insert hp_nmem, sieveV]
    _ = sieveV g P' - g p * sieveV g P' := by ring

private lemma powerset_filter_split {P : Finset ℕ} (hP : P.Nonempty) (Q : Finset ℕ → Prop)
    [DecidablePred Q] :
    P.powerset.filter Q =
      ((P.erase (P.max' hP)).powerset.filter Q) ∪
        (((P.erase (P.max' hP)).powerset.filter (fun S => Q (insert (P.max' hP) S))).image
          (insert (P.max' hP))) := by
  set p := P.max' hP
  set P' := P.erase p
  have hpP : p ∈ P := Finset.max'_mem P hP
  ext S
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hSP, hQS⟩
    by_cases hpS : p ∈ S
    · right
      refine ⟨S.erase p, ⟨⟨?_, ?_⟩, ?_⟩⟩
      · intro q hq
        rcases Finset.mem_erase.mp hq with ⟨hqne, hqS⟩
        exact Finset.mem_erase.mpr ⟨hqne, hSP hqS⟩
      · simpa [Finset.insert_erase hpS] using hQS
      · exact Finset.insert_erase hpS
    · left
      refine ⟨fun q hq => Finset.mem_erase.mpr ⟨fun h => hpS (h ▸ hq), hSP hq⟩, hQS⟩
  · rintro (⟨hSP', hQS⟩ | ⟨S', ⟨hS'P', hQins⟩, rfl⟩)
    · exact ⟨hSP'.trans (Finset.erase_subset p P), hQS⟩
    · refine ⟨Finset.insert_subset_iff.mpr ⟨hpP, hS'P'.trans (Finset.erase_subset p P)⟩, hQins⟩

private lemma powerset_filter_split_disjoint {P : Finset ℕ} (hP : P.Nonempty) (Q : Finset ℕ → Prop)
    [DecidablePred Q] :
    Disjoint ((P.erase (P.max' hP)).powerset.filter Q)
      (((P.erase (P.max' hP)).powerset.filter (fun S => Q (insert (P.max' hP) S))).image
        (insert (P.max' hP))) := by
  set p := P.max' hP
  refine Finset.disjoint_left.mpr fun S hS1 hS2 => ?_
  have hp_nmem : p ∉ S := fun hpS =>
    Finset.notMem_erase p P ((Finset.mem_powerset.mp (Finset.mem_filter.mp hS1).1) hpS)
  rcases Finset.mem_image.mp hS2 with ⟨S', _, rfl⟩
  exact hp_nmem (Finset.mem_insert_self p S')

private lemma WPlus_erase_max' (g : ℕ → ℝ) (D : ℝ) {P : Finset ℕ} (hP : P.Nonempty)
    (hpos : ∀ p ∈ P, 1 ≤ p) :
    WPlus g D P = WPlus g D (P.erase (P.max' hP)) -
      if (P.max' hP : ℝ) ^ 3 < D then g (P.max' hP) * WMinus g (D / (P.max' hP : ℝ)) (P.erase (P.max' hP)) else 0 := by
  set p := P.max' hP
  set P' := P.erase p
  have hpP : p ∈ P := Finset.max'_mem P hP
  have hp_pos : 0 < p := hpos p hpP
  have hp_gt : ∀ S ∈ P'.powerset, ∀ q ∈ S, q < p := fun S hS q hq => by
    have hq' := Finset.mem_erase.mp (Finset.mem_powerset.mp hS hq)
    exact lt_of_le_of_ne (Finset.le_max' P q hq'.2) hq'.1
  rw [WPlus, powerset_filter_split hP (DPlus D),
    Finset.sum_union (powerset_filter_split_disjoint hP (DPlus D))]
  rw [show ∑ S ∈ P'.powerset.filter (DPlus D), (-1 : ℝ) ^ S.card * ∏ q ∈ S, g q = WPlus g D P' from rfl]
  rw [Finset.sum_image]
  · have hfilt : P'.powerset.filter (fun S => DPlus D (insert p S)) =
        if (p : ℝ) ^ 3 < D then P'.powerset.filter (DMinus (D / (p : ℝ))) else ∅ := by
      split_ifs with hlt
      · ext S
        simp only [Finset.mem_filter]
        refine ⟨fun ⟨hS, hD⟩ => ⟨hS, ((DPlus_insert hp_pos (hp_gt S hS)).mp hD).2⟩,
          fun ⟨hS, hD⟩ => ⟨hS, (DPlus_insert hp_pos (hp_gt S hS)).mpr ⟨hlt, hD⟩⟩⟩
      · ext S
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hS hD
        exact hlt ((DPlus_insert hp_pos (hp_gt S hS)).mp hD).1
    rw [hfilt]
    split_ifs with hlt
    · have hterm : ∑ S ∈ P'.powerset.filter (DMinus (D / (p : ℝ))),
          (-1 : ℝ) ^ (insert p S).card * ∏ q ∈ insert p S, g q =
          - (g p * WMinus g (D / (p : ℝ)) P') := by
        rw [WMinus, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hSP' : S ∈ P'.powerset := (Finset.mem_filter.mp hS).1
        have hp_nmem : p ∉ S := fun h => Nat.lt_irrefl p (hp_gt S hSP' p h)
        rw [Finset.card_insert_of_notMem hp_nmem, Finset.prod_insert hp_nmem, pow_succ]
        ring
      rw [hterm, sub_eq_add_neg]
    · simp
  · intro S₁ hS₁ S₂ hS₂ heq
    have hn₁ : p ∉ S₁ := fun h => Nat.lt_irrefl p (hp_gt S₁ (Finset.mem_filter.mp hS₁).1 p h)
    have hn₂ : p ∉ S₂ := fun h => Nat.lt_irrefl p (hp_gt S₂ (Finset.mem_filter.mp hS₂).1 p h)
    have h_er := congrArg (fun T => T.erase p) heq
    simpa [p, Finset.erase_insert hn₁, Finset.erase_insert hn₂] using h_er

private lemma WMinus_erase_max' (g : ℕ → ℝ) (D : ℝ) {P : Finset ℕ} (hP : P.Nonempty)
    (hpos : ∀ p ∈ P, 1 ≤ p) :
    WMinus g D P = WMinus g D (P.erase (P.max' hP)) -
      g (P.max' hP) * WPlus g (D / (P.max' hP : ℝ)) (P.erase (P.max' hP)) := by
  set p := P.max' hP
  set P' := P.erase p
  have hpP : p ∈ P := Finset.max'_mem P hP
  have hp_pos : 0 < p := hpos p hpP
  have hp_gt : ∀ S ∈ P'.powerset, ∀ q ∈ S, q < p := fun S hS q hq => by
    have hq' := Finset.mem_erase.mp (Finset.mem_powerset.mp hS hq)
    exact lt_of_le_of_ne (Finset.le_max' P q hq'.2) hq'.1
  rw [WMinus, powerset_filter_split hP (DMinus D),
    Finset.sum_union (powerset_filter_split_disjoint hP (DMinus D))]
  rw [show ∑ S ∈ P'.powerset.filter (DMinus D), (-1 : ℝ) ^ S.card * ∏ q ∈ S, g q = WMinus g D P' from rfl]
  rw [Finset.sum_image]
  · have hfilt : P'.powerset.filter (fun S => DMinus D (insert p S)) =
        P'.powerset.filter (DPlus (D / (p : ℝ))) := by
      ext S
      simp only [Finset.mem_filter]
      refine ⟨fun ⟨hS, hD⟩ => ⟨hS, (DMinus_insert hp_pos (hp_gt S hS)).mp hD⟩,
        fun ⟨hS, hD⟩ => ⟨hS, (DMinus_insert hp_pos (hp_gt S hS)).mpr hD⟩⟩
    rw [hfilt]
    have hterm : ∑ S ∈ P'.powerset.filter (DPlus (D / (p : ℝ))),
        (-1 : ℝ) ^ (insert p S).card * ∏ q ∈ insert p S, g q =
        - (g p * WPlus g (D / (p : ℝ)) P') := by
      rw [WPlus, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hSP' : S ∈ P'.powerset := (Finset.mem_filter.mp hS).1
      have hp_nmem : p ∉ S := fun h => Nat.lt_irrefl p (hp_gt S hSP' p h)
      rw [Finset.card_insert_of_notMem hp_nmem, Finset.prod_insert hp_nmem, pow_succ]
      ring
    rw [hterm, sub_eq_add_neg]
  · intro S₁ hS₁ S₂ hS₂ heq
    have hn₁ : p ∉ S₁ := fun h => Nat.lt_irrefl p (hp_gt S₁ (Finset.mem_filter.mp hS₁).1 p h)
    have hn₂ : p ∉ S₂ := fun h => Nat.lt_irrefl p (hp_gt S₂ (Finset.mem_filter.mp hS₂).1 p h)
    have h_er := congrArg (fun T => T.erase p) heq
    simpa [p, Finset.erase_insert hn₁, Finset.erase_insert hn₂] using h_er

private lemma T_sum_erase_max'_one (g : ℕ → ℝ) (D : ℝ) {P : Finset ℕ} (hP : P.Nonempty) :
    T_sum g 1 D P = T_sum g 1 D (P.erase (P.max' hP)) +
      (if D ≤ (P.max' hP : ℝ) ^ 3 then g (P.max' hP) * sieveV g (P.erase (P.max' hP)) else 0) := by
  set p := P.max' hP
  set P' := P.erase p
  have hpP : p ∈ P := Finset.max'_mem P hP
  have hp_nmem : p ∉ P' := Finset.notMem_erase p P
  rw [T_sum_one, T_sum_one]
  have hfilt_eq : P.filter (fun q : ℕ => D ≤ (q : ℝ) ^ 3) =
      (if D ≤ (p : ℝ) ^ 3 then insert p (P'.filter (fun q : ℕ => D ≤ (q : ℝ) ^ 3))
       else P'.filter (fun q : ℕ => D ≤ (q : ℝ) ^ 3)) := by
    ext q
    by_cases hcond : D ≤ (p : ℝ) ^ 3
    · simp only [hcond, ↓reduceIte, Finset.mem_insert, Finset.mem_filter, P', Finset.mem_erase]
      constructor
      · rintro ⟨hqP, hqD⟩
        by_cases hqp : q = p
        · left; exact hqp
        · right; exact ⟨⟨hqp, hqP⟩, hqD⟩
      · rintro (rfl | ⟨⟨_, hqP⟩, hqD⟩)
        · exact ⟨hpP, hcond⟩
        · exact ⟨hqP, hqD⟩
    · simp only [hcond, ↓reduceIte, Finset.mem_filter, P', Finset.mem_erase]
      constructor
      · rintro ⟨hqP, hqD⟩
        have hne : q ≠ p := fun h => hcond (h ▸ hqD)
        exact ⟨⟨hne, hqP⟩, hqD⟩
      · rintro ⟨⟨_, hqP⟩, hqD⟩
        exact ⟨hqP, hqD⟩
  rw [hfilt_eq]
  have hcongr : ∑ q ∈ P'.filter (fun q : ℕ => D ≤ (q : ℝ) ^ 3), g q * sieveV g (P.filter (· < q)) =
      ∑ q ∈ P'.filter (fun q : ℕ => D ≤ (q : ℝ) ^ 3), g q * sieveV g (P'.filter (· < q)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_erase.mp (Finset.mem_filter.mp hq).1
    have hql : q < p := lt_of_le_of_ne (Finset.le_max' P q hq'.2) hq'.1
    rw [filter_lt_insert_eq hql, filter_lt_max'_eq_erase hP]
  split_ifs with hcond
  · have hp_nf : p ∉ P'.filter (fun q : ℕ => D ≤ (q : ℝ) ^ 3) := fun h =>
      hp_nmem (Finset.mem_filter.mp h).1
    rw [Finset.sum_insert hp_nf, hcongr, filter_lt_max'_eq_erase hP, add_comm]
  · rw [hcongr, add_zero]

private lemma T_sum_erase_max'_succ (g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (D : ℝ) {P : Finset ℕ}
    (hP : P.Nonempty) (hpos : ∀ p ∈ P, 1 ≤ p) :
    T_sum g (n + 1) D P = T_sum g (n + 1) D (P.erase (P.max' hP)) +
      (if (if n % 2 = 0 then (P.max' hP : ℝ) ^ 3 < D else True) then
        g (P.max' hP) * T_sum g n (D / (P.max' hP : ℝ)) (P.erase (P.max' hP)) else 0) := by
  set p := P.max' hP
  set P' := P.erase p
  have hpP : p ∈ P := Finset.max'_mem P hP
  have hPpos' : ∀ q ∈ P', 1 ≤ q := fun q hq => hpos q (Finset.erase_subset p P hq)
  rw [T_sum_recursion g n hn D P hpos, T_sum_recursion g n hn D P' hPpos']
  rw [← Finset.sum_erase_add P _ hpP]
  have hsum_eq :
      ∑ q ∈ P',
        (if (if n % 2 = 0 then (q : ℝ) ^ 3 < D else True) then
          g q * T_sum g n (D / (q : ℝ)) (P.filter (· < q))
        else 0) =
      ∑ q ∈ P',
        (if (if n % 2 = 0 then (q : ℝ) ^ 3 < D else True) then
          g q * T_sum g n (D / (q : ℝ)) (P'.filter (· < q))
        else 0) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_erase.mp hq
    have hql : q < p := lt_of_le_of_ne (Finset.le_max' P q hq'.2) hq'.1
    rw [filter_lt_insert_eq hql, filter_lt_max'_eq_erase hP]
  change (∑ q ∈ P', _) + _ = _
  rw [hsum_eq, filter_lt_max'_eq_erase hP]

private theorem ri_main_term_eq_aux (m : ℕ) :
    ∀ (P : Finset ℕ), P.card = m → (∀ p ∈ P, 1 ≤ p) → ∀ (g : ℕ → ℝ) (D : ℝ),
      (WPlus g D P = sieveV g P + ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k - 1) D P) ∧
      (WMinus g D P = sieveV g P - ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k) D P) := by
  induction m with
  | zero =>
      intro P hcard _ g D
      have hP : P = ∅ := Finset.card_eq_zero.mp hcard
      subst hP
      have hfp : Finset.filter (DPlus D) ({∅} : Finset (Finset ℕ)) = {∅} :=
        Finset.filter_true_of_mem fun S hS => by
          rcases Finset.mem_singleton.mp hS with rfl
          exact DPlus_empty D
      have hfm : Finset.filter (DMinus D) ({∅} : Finset (Finset ℕ)) = {∅} :=
        Finset.filter_true_of_mem fun S hS => by
          rcases Finset.mem_singleton.mp hS with rfl
          exact DMinus_empty D
      simp only [WPlus, WMinus, sieveV, Finset.powerset_empty, hfp, hfm, Finset.sum_singleton,
        Finset.card_empty, pow_zero, Finset.prod_empty, mul_one]
      norm_num
  | succ m ih =>
      intro P hcard hpos g D
      have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
      set p := P.max' hPne
      set P' := P.erase p
      have hpP : p ∈ P := Finset.max'_mem P hPne
      have hP'card : P'.card = m := by rw [Finset.card_erase_of_mem hpP, hcard]; omega
      have hP'pos : ∀ q ∈ P', 1 ≤ q := fun q hq => hpos q (Finset.erase_subset p P hq)
      have ih_D := ih P' hP'card hP'pos g D
      have ih_Dp := ih P' hP'card hP'pos g (D / (p : ℝ))
      have hsum_odd_P' :
          ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k - 1) D P' =
            ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) D P' := by
        rw [hcard, hP'card, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        have hzero : T_sum g (2 * (m + 1) - 1) D P' = 0 :=
          T_sum_eq_zero_of_card_lt (by rw [hP'card]; omega)
        rw [hzero, add_zero]
      have hsum_even_P' :
          ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k) D P' =
            ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) D P' := by
        rw [hcard, hP'card, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        have hzero : T_sum g (2 * (m + 1)) D P' = 0 :=
          T_sum_eq_zero_of_card_lt (by rw [hP'card]; omega)
        rw [hzero, add_zero]
      constructor
      · -- Upper identity: `WPlus`
        have hsplit_odd :
            ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k - 1) D P =
              (∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) D P') +
                (if (p : ℝ) ^ 3 < D then
                  g p * ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) (D / (p : ℝ)) P'
                 else g p * sieveV g P') := by
          have hIcc : Finset.Icc 1 P.card = insert 1 (Finset.Icc 2 P.card) := by
            ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
          have h1_nmem : 1 ∉ Finset.Icc 2 P.card := by simp
          have hT_split : ∀ k ∈ Finset.Icc 1 P.card,
              T_sum g (2 * k - 1) D P = T_sum g (2 * k - 1) D P' +
                (if k = 1 then (if D ≤ (p : ℝ) ^ 3 then g p * sieveV g P' else 0)
                 else (if (p : ℝ) ^ 3 < D then g p * T_sum g (2 * (k - 1)) (D / (p : ℝ)) P' else 0)) := by
            intro k hk
            have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
            by_cases hk_eq : k = 1
            · subst hk_eq
              simpa [p, P'] using T_sum_erase_max'_one g D hPne
            · have hk2 : 2 ≤ k := by omega
              have hn : 1 ≤ 2 * k - 2 := by omega
              have hev : (2 * k - 2) % 2 = 0 := by omega
              have hsucc : 2 * k - 1 = (2 * k - 2) + 1 := by omega
              rw [hsucc, T_sum_erase_max'_succ g (2 * k - 2) hn D hPne hpos]
              simp only [hk_eq, ↓reduceIte, hev, p, P']
              congr 1
              rw [show 2 * k - 2 = 2 * (k - 1) by omega]
          rw [Finset.sum_congr rfl hT_split, Finset.sum_add_distrib, hsum_odd_P']
          congr 1
          rw [hIcc, Finset.sum_insert h1_nmem]
          simp only [↓reduceIte]
          have hshift :
              ∑ k ∈ Finset.Icc 2 P.card,
                (if k = 1 then (if D ≤ (p : ℝ) ^ 3 then g p * sieveV g P' else 0)
                 else (if (p : ℝ) ^ 3 < D then g p * T_sum g (2 * (k - 1)) (D / (p : ℝ)) P' else 0)) =
              ∑ k ∈ Finset.Icc 1 P'.card,
                (if (p : ℝ) ^ 3 < D then g p * T_sum g (2 * k) (D / (p : ℝ)) P' else 0) := by
            refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
            · intro k hk
              rw [Finset.mem_Icc] at hk ⊢; omega
            · intro k₁ hk₁ k₂ hk₂ heq
              rw [Finset.mem_Icc] at hk₁ hk₂; omega
            · intro k hk
              rw [Finset.mem_Icc] at hk
              refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro k hk
              have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
              have hkne : k ≠ 1 := by omega
              simp [hkne]
          rw [hshift]
          by_cases hlt : (p : ℝ) ^ 3 < D
          · have hnot : ¬ D ≤ (p : ℝ) ^ 3 := not_le_of_gt hlt
            simp [hlt, hnot, Finset.mul_sum]
          · have hle : D ≤ (p : ℝ) ^ 3 := not_lt.mp hlt
            simp [hlt, hle]
        rw [WPlus_erase_max' g D hPne hpos, sieveV_erase_max' g hPne, ih_D.1, ih_Dp.2, hsplit_odd]
        change (sieveV g P' + ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) D P') -
            (if (p : ℝ) ^ 3 < D then
              g p * (sieveV g P' - ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) (D / (p : ℝ)) P')
             else 0) = _
        split_ifs <;> ring
      · -- Lower identity: `WMinus`
        have hsplit_even :
            ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k) D P =
              (∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) D P') +
                g p * ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) (D / (p : ℝ)) P' := by
          have hT_split : ∀ k ∈ Finset.Icc 1 P.card,
              T_sum g (2 * k) D P = T_sum g (2 * k) D P' +
                g p * T_sum g (2 * k - 1) (D / (p : ℝ)) P' := by
            intro k hk
            have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
            have hn : 1 ≤ 2 * k - 1 := by omega
            have hodd : (2 * k - 1) % 2 = 1 := by omega
            have hsucc : 2 * k = (2 * k - 1) + 1 := by omega
            rw [hsucc, T_sum_erase_max'_succ g (2 * k - 1) hn D hPne hpos]
            simp [hodd, p, P']
          rw [Finset.sum_congr rfl hT_split, Finset.sum_add_distrib, hsum_even_P', ← Finset.mul_sum]
          congr 2
          rw [hcard, hP'card, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
          have hzero : T_sum g (2 * (m + 1) - 1) (D / (p : ℝ)) P' = 0 :=
            T_sum_eq_zero_of_card_lt (by rw [hP'card]; omega)
          rw [hzero, add_zero]
        rw [WMinus_erase_max' g D hPne hpos, sieveV_erase_max' g hPne, ih_D.2, ih_Dp.1, hsplit_even]
        change (sieveV g P' - ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k) D P') -
            g p * (sieveV g P' + ∑ k ∈ Finset.Icc 1 P'.card, T_sum g (2 * k - 1) (D / (p : ℝ)) P') = _
        ring

/-- Exact combinatorial Rosser–Iwaniec upper-sieve main-term identity. -/
theorem ri_main_term_upper_eq (g : ℕ → ℝ) (D : ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    ∑ S ∈ P.powerset.filter (DPlus D), (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p =
      sieveV g P + ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k - 1) D P :=
  (ri_main_term_eq_aux P.card P rfl hP g D).1

/-- Exact combinatorial Rosser–Iwaniec lower-sieve main-term identity. -/
theorem ri_main_term_lower_eq (g : ℕ → ℝ) (D : ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    ∑ S ∈ P.powerset.filter (DMinus D), (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p =
      sieveV g P - ∑ k ∈ Finset.Icc 1 P.card, T_sum g (2 * k) D P :=
  (ri_main_term_eq_aux P.card P rfl hP g D).2

end

end BuchstabSwitching
