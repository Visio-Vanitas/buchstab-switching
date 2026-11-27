import BuchstabSwitching.Sieve.LinearSieveInduction.MertensCond
import BuchstabSwitching.Sieve.LinearSieveInduction.AbelSummation
import BuchstabSwitching.Sieve.LinearSieveInduction.ErrorEnvelope
import BuchstabSwitching.Sieve.AbstractSieve
import BuchstabSwitching.Sieve.RosserIwaniecComb
import BuchstabSwitching.Sieve.BuchstabFunctions
import Mathlib.Tactic

/-!
# Inductive BJS Lemma 11 `T_sum` Bound

Proves `T_sum_le_fHat_add_E_bjs_seq` (depth-dependent `K_seq`),
`T_sum_le_fHat_add_E_bjs_of_lower_bound`, and `T_sum_le_fHat_add_E_bjs`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

private lemma T_sum_filter_lt_eq_self {g : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hodd : Odd n) {D : ℝ} (_hD : 0 < D) {P : Finset ℕ} (_hP : ∀ p ∈ P, 1 ≤ p) :
    T_sum g n D P = T_sum g n D (P.filter (fun p : ℕ => (p : ℝ) < D ^ (1 / 3 : ℝ))) := by
  let z' : ℝ := D ^ (1 / 3 : ℝ)
  let P' : Finset ℕ := P.filter (fun p : ℕ => (p : ℝ) < z')
  have hS_sub : ∀ S ∈ (P.powersetCard n).filter (riTermPred D), ∀ p ∈ S, (p : ℝ) < z' := by
    intro S hS p hp
    have hmem := Finset.mem_filter.mp hS
    rcases Finset.mem_powersetCard.mp hmem.1 with ⟨hSP, hScard⟩
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    let L := descPrimes S
    have hlen : L.length = n := by dsimp [L, descPrimes]; rw [Finset.length_sort, hScard]
    have hfor := (riTermCond_iff_forall D 1 L (by omega)).mp hmem.2
    have h0_lt : 0 < L.length - 1 := by omega
    have h0_par : 0 % 2 = (L.length - 1) % 2 := by
      rw [hlen]; obtain ⟨k, hk⟩ := hodd; omega
    have hcond := hfor.1 0 h0_lt h0_par
    rw [one_mul, Finset.prod_range_one] at hcond
    have h0L : 0 < L.length := by omega
    have hmax_eq : L.getD 0 0 = S.max' hSne := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0L]
      apply le_antisymm
      · exact Finset.le_max' S _ ((Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem h0L))
      · refine Finset.max'_le S _ _ fun q hq => ?_
        rcases List.mem_iff_getElem.mp ((Finset.mem_sort (· ≥ ·)).mpr hq) with ⟨i, hi, rfl⟩
        by_cases hi0 : i = 0
        · subst hi0; exact le_rfl
        · exact (S.sortedGT_sort.getElem_lt_getElem_iff.mpr (by omega)).le
    have hmax3 : (S.max' hSne : ℝ) ^ 3 < D := by
      rw [← hmax_eq]
      linarith
    have hp_le_max : (p : ℝ) ≤ (S.max' hSne : ℝ) := Nat.cast_le.mpr (Finset.le_max' S p hp)
    have hp3 : (p : ℝ) ^ 3 < D :=
      lt_of_le_of_lt (pow_le_pow_left₀ (Nat.cast_nonneg _) hp_le_max 3) hmax3
    exact lt_rpow_one_third_of_cube_lt (Nat.cast_nonneg _) hp3
  have hfilt_eq : (P.powersetCard n).filter (riTermPred D) =
      (P'.powersetCard n).filter (riTermPred D) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hSP, hScard⟩, hri⟩
      have hSmem : S ∈ (P.powersetCard n).filter (riTermPred D) :=
        Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hSP, hScard⟩, hri⟩
      exact ⟨⟨fun p hp => Finset.mem_filter.mpr ⟨hSP hp, hS_sub S hSmem p hp⟩, hScard⟩, hri⟩
    · rintro ⟨⟨hSP', hScard⟩, hri⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hSP' hp)).1, hScard⟩, hri⟩
  rw [T_sum, T_sum, hfilt_eq]
  refine Finset.sum_congr rfl fun S hS => ?_
  split_ifs with hSne
  · congr 2
    have hSmem : S ∈ (P.powersetCard n).filter (riTermPred D) := by
      rwa [hfilt_eq]
    have hmin_lt : (S.min' hSne : ℝ) < z' := hS_sub S hSmem (S.min' hSne) (Finset.min'_mem S hSne)
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hqP, hqmin⟩ => ⟨⟨hqP, lt_trans (Nat.cast_lt.mpr hqmin) hmin_lt⟩, hqmin⟩,
      fun ⟨⟨hqP, _⟩, hqmin⟩ => ⟨hqP, hqmin⟩⟩
  · rfl

/-- **Main BJS Lemma 11 Inductive Bound (Depth-Dependent `K_seq`)**:
For `n ≥ 1`, `1 < z`, `z^2 ≤ D` (if `n` even) or `z ≤ D` (if `n` odd), if every step `m ≤ n`
satisfies `1 ≤ K_seq m` and `AllLevelsMertensCondFrom g P u (K_seq m)` for some `1 ≤ u ≤ u_bjs n D z`,
then `T_sum g n D P ≤ sieveV g P * (fHat n s + E_bjs_seq K_seq n s)` where `s = log D / log z`. -/
theorem T_sum_le_fHat_add_E_bjs_seq :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ {g : ℕ → ℝ} {P : Finset ℕ} {z D u : ℝ} {K_seq : ℕ → ℝ},
        1 < z →
        (if n % 2 = 0 then z ^ 2 ≤ D else z ≤ D) →
        (∀ p ∈ P, 2 ≤ p ∧ (p : ℝ) < z) →
        (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) →
        1 ≤ u → u ≤ u_bjs n D z →
        (∀ m, 1 ≤ m → m ≤ n → 1 ≤ K_seq m ∧ AllLevelsMertensCondFrom g P u (K_seq m)) →
        T_sum g n D P ≤
          sieveV g P * (fHat n (Real.log D / Real.log z) + E_bjs_seq K_seq n (Real.log D / Real.log z)) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | m
    · omega
    rcases m with _ | m'
    · -- Base case `n = 1`
      intro g P z D u K_seq hz hDz hP hg hu_ge hu_le hK_seq
      norm_num at hDz
      set s : ℝ := Real.log D / Real.log z
      have hlogz_pos : 0 < Real.log z := Real.log_pos hz
      have hD_gt1 : 1 < D := lt_of_lt_of_le hz hDz
      have hlogD_pos : 0 < Real.log D := Real.log_pos hD_gt1
      have hs_ge1 : 1 ≤ s := (one_le_div hlogz_pos).mpr (Real.log_le_log (by linarith) hDz)
      have hVP_nn : 0 ≤ sieveV g P := sieveV_nonneg fun p hp => (hg p hp).2
      have hK1 : 1 ≤ K_seq 1 := (hK_seq 1 le_rfl le_rfl).1
      have hCond1 : AllLevelsMertensCondFrom g P u (K_seq 1) := (hK_seq 1 le_rfl le_rfl).2
      rcases lt_or_ge s 3 with hs3 | hs3
      · have hD_lt_z3 : D < z ^ 3 := by
          have hlog_lt : Real.log D < 3 * Real.log z := by
            have := (div_lt_iff₀ hlogz_pos).mp hs3
            linarith
          have hlog_z3 : Real.log (z ^ 3) = 3 * Real.log z := by rw [Real.log_pow]; norm_num
          rw [← hlog_z3] at hlog_lt
          exact (Real.log_lt_log_iff (by linarith) (by positivity)).mp hlog_lt
        set w : ℝ := D ^ (1 / 3 : ℝ)
        have hw_gt1 : 1 < w := Real.one_lt_rpow hD_gt1 (by norm_num)
        have hw_ltz : w < z := rpow_one_third_lt_of_lt_cube (by linarith) (by positivity) hD_lt_z3
        have hw_ge_u : u ≤ w := by simpa [u_bjs, w, one_div] using hu_le
        have hT1_eq : T_sum g 1 D P =
            sieveV g (P.filter (fun p : ℕ => (p : ℝ) < w)) - sieveV g P := by
          rw [T_sum_one]
          have hfilt : P.filter (fun p : ℕ => D ≤ (p : ℝ) ^ 3) =
              P.filter (fun p : ℕ => w ≤ (p : ℝ)) := by
            ext p
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hpP, hDp⟩
              refine ⟨hpP, ?_⟩
              have h1 := Real.rpow_le_rpow (by linarith) hDp (by norm_num : (0 : ℝ) ≤ 1 / 3)
              have h2 : ((p : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (p : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
              linarith
            · rintro ⟨hpP, hwp⟩
              refine ⟨hpP, ?_⟩
              have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ w) hwp 3
              have h2 : w ^ 3 = D := by
                dsimp [w]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
              linarith
          rw [hfilt, sum_filter_ge_mul_sieveV_eq]
        have hcond := hCond1 hw_gt1 hw_ge_u hw_ltz.le
        have hfilt_z : P.filter (fun p : ℕ => (p : ℝ) < z) = P := by
          ext p; simp only [Finset.mem_filter]
          exact ⟨fun h => h.1, fun hp => ⟨hp, (hP p hp).2⟩⟩
        rw [hfilt_z] at hcond
        have hlogw : Real.log w = (1 / 3 : ℝ) * Real.log D := by
          dsimp [w]; rw [Real.log_rpow (by linarith)]
        have hratio : Real.log z / Real.log w = 3 / s := by
          rw [hlogw]
          dsimp [s]
          have hlogD_ne : Real.log D ≠ 0 := hlogD_pos.ne'
          have hlogz_ne : Real.log z ≠ 0 := hlogz_pos.ne'
          field_simp [hlogD_ne, hlogz_ne]
        rw [hratio] at hcond
        rw [fHat_one_of_Icc hs_ge1 hs3.le, E_bjs_seq_one_of_Ico K_seq hs_ge1 hs3]
        have hcalc : sieveV g P * ((3 - s) / s + 3 / s * (K_seq 1 - 1)) =
            K_seq 1 * (3 / s) * sieveV g P - sieveV g P := by
          have hs_ne : s ≠ 0 := (by linarith : 0 < s).ne'
          field_simp [hs_ne]; ring
        linarith
      · have hz3_le_D : z ^ 3 ≤ D := by
          have hle : 3 * Real.log z ≤ Real.log D := (le_div_iff₀ hlogz_pos).mp hs3
          have hlog_z3 : Real.log (z ^ 3) = 3 * Real.log z := by rw [Real.log_pow]; norm_num
          rw [← hlog_z3] at hle
          exact (Real.log_le_log_iff (by positivity) (by linarith)).mp hle
        have hT_zero : T_sum g 1 D P = 0 := by
          rw [T_sum_one]
          have hemp : P.filter (fun p : ℕ => D ≤ (p : ℝ) ^ 3) = ∅ := by
            ext p
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro hpP hDp
            have hp_lt : (p : ℝ) ^ 3 < z ^ 3 :=
              pow_lt_pow_left₀ (hP p hpP).2 (Nat.cast_nonneg _) (by norm_num)
            linarith
          rw [hemp, Finset.sum_empty]
        rw [hT_zero, fHat_one_of_ge_three hs3, E_bjs_seq_one_of_ge_three K_seq hs3, add_zero, mul_zero]
    · -- Inductive step `n = m' + 2 ≥ 2`
      intro g P z D u K_seq hz hDz hP hg hu_ge hu_le hK_seq
      set n : ℕ := m' + 2
      have hn2 : 2 ≤ n := by omega
      set m : ℕ := m' + 1
      have hm1 : 1 ≤ m := by omega
      have hmn : m < n := by omega
      set s : ℝ := Real.log D / Real.log z
      have hlogz_pos : 0 < Real.log z := Real.log_pos hz
      have hP_pos : ∀ p ∈ P, 1 ≤ p := fun p hp => by have := (hP p hp).1; omega
      have hP_ltz : ∀ p ∈ P, (p : ℝ) < z := fun p hp => (hP p hp).2
      have hVP_nn : 0 ≤ sieveV g P := sieveV_nonneg fun p hp => (hg p hp).2
      have hstep_ge : ∀ (z₀ : ℝ) (P₀ : Finset ℕ),
          1 < z₀ → z₀ ^ 2 ≤ D → (Odd n → z₀ ^ 3 ≤ D) →
          (∀ p ∈ P₀, 2 ≤ p ∧ (p : ℝ) < z₀) →
          (∀ p ∈ P₀, 0 ≤ g p ∧ g p ≤ 1) →
          u ≤ u_bjs n D z₀ →
          (∀ j, 1 ≤ j → j ≤ n → 1 ≤ K_seq j ∧ AllLevelsMertensCondFrom g P₀ u (K_seq j)) →
          T_sum g n D P₀ ≤
            sieveV g P₀ * (fHat n (Real.log D / Real.log z₀) +
              E_bjs_seq K_seq n (Real.log D / Real.log z₀)) := by
        intro z₀ P₀ hz₀ hz₀2 hz₀3 hP₀ hg₀ hu_le₀ hK_seq₀
        set s₀ : ℝ := Real.log D / Real.log z₀
        have hlogz₀_pos : 0 < Real.log z₀ := Real.log_pos hz₀
        have hD_gt_z₀ : z₀ ≤ D := by nlinarith
        have hD_gt1 : 1 < D := lt_of_lt_of_le hz₀ hD_gt_z₀
        have hD_pos : 0 < D := by linarith
        have hlogD_pos : 0 < Real.log D := Real.log_pos hD_gt1
        have hs₀_ge2 : 2 ≤ s₀ := by
          rw [show s₀ = Real.log D / Real.log z₀ from rfl, le_div_iff₀ hlogz₀_pos]
          have h1 := Real.log_le_log (by positivity) hz₀2
          rw [Real.log_pow] at h1; push_cast at h1; linarith
        have hs₀_pos : 0 < s₀ := by linarith
        have hP₀_pos : ∀ p ∈ P₀, 1 ≤ p := fun p hp => by have := (hP₀ p hp).1; omega
        have hP₀_ltz : ∀ p ∈ P₀, (p : ℝ) < z₀ := fun p hp => (hP₀ p hp).2
        have hT_rec : T_sum g n D P₀ =
            ∑ p ∈ P₀.filter (fun p : ℕ => u ≤ (p : ℝ)),
              g p * T_sum g m (D / (p : ℝ)) (P₀.filter (· < p)) := by
          have hrec_full : T_sum g n D P₀ =
              ∑ p ∈ P₀, g p * T_sum g m (D / (p : ℝ)) (P₀.filter (· < p)) := by
            by_cases hn_ev : n % 2 = 0
            · have hm_odd : m % 2 = 1 := by omega
              exact T_sum_recursion_even_step g m hm1 hm_odd D P₀ hP₀_pos
            · have hn_odd : Odd n := Nat.odd_iff.mpr (by omega)
              have hm_ev : m % 2 = 0 := by omega
              rw [T_sum_recursion_odd_step g m hm1 hm_ev D P₀ hP₀_pos]
              have hfilt : P₀.filter (fun p : ℕ => (p : ℝ) ^ 3 < D) = P₀ := by
                ext p; simp only [Finset.mem_filter]
                exact ⟨fun h => h.1, fun hp => ⟨hp, lt_of_lt_of_le
                  (pow_lt_pow_left₀ (hP₀_ltz p hp) (Nat.cast_nonneg _) (by norm_num)) (hz₀3 hn_odd)⟩⟩
              rw [hfilt]
          rw [hrec_full, Finset.sum_filter]
          refine Finset.sum_congr rfl fun p hp => ?_
          split_ifs with hup
          · rfl
          · have hpu : (p : ℝ) < u := lt_of_not_ge hup
            have hT_zero : T_sum g m (D / (p : ℝ)) (P₀.filter (· < p)) = 0 := by
              rw [T_sum]
              refine Finset.sum_eq_zero fun S' hS' => ?_
              exfalso
              have hmem' := Finset.mem_filter.mp hS'
              rcases Finset.mem_powersetCard.mp hmem'.1 with ⟨hS'sub, hS'card⟩
              have hS'ne : S'.Nonempty := Finset.card_pos.mp (by rw [hS'card]; omega)
              have hp_gt : ∀ q ∈ S', q < p := fun q hq => (Finset.mem_filter.mp (hS'sub hq)).2
              have hp_nmem : p ∉ S' := fun h => Nat.lt_irrefl p (hp_gt p h)
              have hS'P : S' ⊆ P₀ := fun q hq => (Finset.mem_filter.mp (hS'sub hq)).1
              have hcond_ins : if S'.card % 2 = 0 then (p : ℝ) ^ 3 < D else True := by
                split_ifs with hpar
                · have hodd_n : Odd n := by rw [Nat.odd_iff]; omega
                  exact lt_of_lt_of_le
                    (pow_lt_pow_left₀ (hP₀_ltz p hp) (Nat.cast_nonneg _) (by norm_num)) (hz₀3 hodd_n)
              have hri : riTermPred D (insert p S') :=
                (riTermPred_insert (hP₀_pos p hp) hp_gt hS'ne).mpr ⟨hcond_ins, hmem'.2⟩
              have hmem_ins : insert p S' ∈ (P₀.powersetCard n).filter (riTermPred D) :=
                Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨hp, hS'P⟩,
                  by rw [Finset.card_insert_of_notMem hp_nmem, hS'card]⟩, hri⟩
              have hmin_gt := T_sum_prefix_min_gt (by omega : 1 ≤ n) hz₀ hD_gt_z₀ hP₀_pos hP₀_ltz
                hmem_ins (Finset.insert_nonempty p S')
              have hmin_le : ((insert p S').min' (Finset.insert_nonempty p S') : ℝ) ≤ (p : ℝ) :=
                Nat.cast_le.mpr (Finset.min'_le _ _ (Finset.mem_insert_self p S'))
              linarith
            rw [hT_zero, mul_zero]
        have hterm_le : ∀ p ∈ P₀.filter (fun p : ℕ => u ≤ (p : ℝ)),
            g p * T_sum g m (D / (p : ℝ)) (P₀.filter (· < p)) ≤
              g p * sieveV g (P₀.filter (· < p)) *
                (fHat m (Real.log (D / (p : ℝ)) / Real.log (p : ℝ)) +
                  E_bjs_seq K_seq m (Real.log (D / (p : ℝ)) / Real.log (p : ℝ))) := by
          intro p hp
          have hpP : p ∈ P₀ := (Finset.mem_filter.mp hp).1
          have hup : u ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2
          have hp2 : 2 ≤ p := (hP₀ p hpP).1
          have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
          have hp_ltz : (p : ℝ) < z₀ := hP₀_ltz p hpP
          have hDp_cond : if m % 2 = 0 then (p : ℝ) ^ 2 ≤ D / (p : ℝ) else (p : ℝ) ≤ D / (p : ℝ) := by
            split_ifs with hm_ev
            · have hn_odd : Odd n := by rw [Nat.odd_iff]; omega
              have h3 : (p : ℝ) ^ 3 ≤ D :=
                (pow_le_pow_left₀ (Nat.cast_nonneg _) hp_ltz.le 3).trans (hz₀3 hn_odd)
              rw [le_div_iff₀ (by linarith)]; linarith
            · have h2 : (p : ℝ) ^ 2 ≤ D :=
                (pow_le_pow_left₀ (Nat.cast_nonneg _) hp_ltz.le 2).trans hz₀2
              rw [le_div_iff₀ (by linarith)]; linarith
          have hu_le_m : u ≤ u_bjs m (D / (p : ℝ)) (p : ℝ) := by
            refine hu_le₀.trans ?_
            by_cases hm_ev : m % 2 = 0
            · have hn_odd : n % 2 = 1 := by omega
              have hn_eq : (n + 1) / 2 = m / 2 + 1 := by omega
              simp only [u_bjs, hm_ev, hn_odd, one_ne_zero, ↓reduceIte]
              have hp3_le_D : (p : ℝ) ^ 3 ≤ D :=
                (pow_le_pow_left₀ (Nat.cast_nonneg _) hp_ltz.le 3).trans (hz₀3 (Nat.odd_iff.mpr hn_odd))
              have hbase : D ^ (1 / 3 : ℝ) ≤ (D / (p : ℝ)) / (p : ℝ) := by
                have hp2_pos : 0 < (p : ℝ) ^ 2 := by positivity
                rw [div_div, ← sq, le_div_iff₀ hp2_pos]
                have hpow : (p : ℝ) ^ 2 ≤ D ^ (2 / 3 : ℝ) := by
                  have h1 := Real.rpow_le_rpow (by positivity) hp3_le_D (by norm_num : (0 : ℝ) ≤ 2 / 3)
                  have h2 : ((p : ℝ) ^ 3) ^ (2 / 3 : ℝ) = (p : ℝ) ^ 2 := by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast]
                    norm_num
                  linarith
                calc D ^ (1 / 3 : ℝ) * (p : ℝ) ^ 2
                    ≤ D ^ (1 / 3 : ℝ) * D ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left hpow (by positivity)
                  _ = D := by rw [← Real.rpow_add hD_pos]; norm_num
              have hle_rpow := Real.rpow_le_rpow (by positivity) hbase (by positivity : 0 ≤ (1 / 3 : ℝ) ^ (m / 2))
              have hlhs : (D ^ (1 / 3 : ℝ)) ^ ((1 / 3 : ℝ) ^ (m / 2)) = D ^ ((1 / 3 : ℝ) ^ ((n + 1) / 2)) := by
                rw [← Real.rpow_mul hD_pos.le, hn_eq, pow_succ']
              linarith
            · have hn_ev : n % 2 = 0 := by omega
              have hdiv_eq : (m + 1) / 2 = n / 2 := by omega
              simp only [u_bjs, hm_ev, hn_ev, ↓reduceIte, hdiv_eq]
              have hbase : D / z₀ ≤ D / (p : ℝ) := div_le_div_of_nonneg_left hD_pos.le (by linarith) hp_ltz.le
              exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
          have hIH := ih m hmn hm1 (g := g) (P := P₀.filter (· < p)) (z := (p : ℝ)) (D := D / (p : ℝ))
            (u := u) (K_seq := K_seq) hp_gt1 hDp_cond
            (fun q hq => ⟨(hP₀ q (Finset.filter_subset _ P₀ hq)).1,
              Nat.cast_lt.mpr (Finset.mem_filter.mp hq).2⟩)
            (fun q hq => hg₀ q (Finset.filter_subset _ P₀ hq))
            hu_ge hu_le_m
            (fun j hj1 hjm => ⟨(hK_seq₀ j hj1 (by omega)).1,
              (hK_seq₀ j hj1 (by omega)).2.filter_nat_lt (hK_seq₀ j hj1 (by omega)).1
                (fun q hq => (hg₀ q hq).2) p⟩)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hIH (hg₀ p hpP).1
        have hsum_le : T_sum g n D P₀ ≤
            ∑ p ∈ P₀.filter (fun p : ℕ => u ≤ (p : ℝ)),
              g p * sieveV g (P₀.filter (· < p)) *
                (fHat m (Real.log (D / (p : ℝ)) / Real.log (p : ℝ)) +
                  E_bjs_seq K_seq m (Real.log (D / (p : ℝ)) / Real.log (p : ℝ))) := by
          rw [hT_rec]
          exact Finset.sum_le_sum hterm_le
        have hK_m : ∀ j, 1 ≤ j → j ≤ m → 1 ≤ K_seq j := fun j hj1 hjm => (hK_seq₀ j hj1 (by omega)).1
        have hK_n₀ : 1 ≤ K_seq n := (hK_seq₀ n (by omega) le_rfl).1
        have hCond_n₀ : AllLevelsMertensCondFrom g P₀ u (K_seq n) := (hK_seq₀ n (by omega) le_rfl).2
        set φ : ℝ → ℝ := fun x => fHat m x + E_bjs_seq K_seq m x
        have hφ_nn : ∀ t, 1 ≤ t → 0 ≤ φ t := fun t _ =>
          add_nonneg (fHat_nonneg m t) (E_bjs_seq_nonneg m hK_m t)
        have hφ_anti : AntitoneOn φ (Set.Ici 1) :=
          (fHat_antitone m hm1).add (E_bjs_seq_antitone m hm1 hK_m)
        have hφ_supp : ∀ t, (n : ℝ) + 3 ≤ t → φ (t - 1) = 0 := fun t ht => by
          have hm2 : (m : ℝ) + 2 ≤ t - 1 := by
            have hnm : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast (by omega : n = m + 1)
            linarith
          simp [φ, fHat_support m hm1 hm2, E_bjs_seq_support K_seq m hm1 hm2]
        have hs₀M : s₀ ≤ (n : ℝ) + 3 ∨ (n : ℝ) + 3 < s₀ := le_or_gt s₀ ((n : ℝ) + 3)
        rcases hs₀M with hs₀_le | hs₀_gt
        · have habel := abel_summation_bjs hz₀ hz₀2 hK_n₀ hu_ge hs₀_le
            (fun p hp => (hP₀ p hp).1) hP₀_ltz hg₀ hCond_n₀ hφ_nn hφ_anti hφ_supp
          have hE_int : IntervalIntegrable (fun t => E_bjs_seq K_seq m (t - 1)) volume s₀ ((n : ℝ) + 3) := by
            refine AntitoneOn.intervalIntegrable ?_
            rw [uIcc_of_le hs₀_le]
            intro x hx y hy hxy
            exact (E_bjs_seq_antitone m hm1 hK_m)
              (by simp only [Set.mem_Ici]; linarith [hs₀_ge2, hx.1])
              (by simp only [Set.mem_Ici]; linarith [hs₀_ge2, hy.1]) (by linarith)
          have hf_int : IntervalIntegrable (fun t => fHat m (t - 1)) volume s₀ ((n : ℝ) + 3) := by
            refine AntitoneOn.intervalIntegrable ?_
            rw [uIcc_of_le hs₀_le]
            intro x hx y hy hxy
            exact (fHat_antitone m hm1)
              (by simp only [Set.mem_Ici]; linarith [hs₀_ge2, hx.1])
              (by simp only [Set.mem_Ici]; linarith [hs₀_ge2, hy.1]) (by linarith)
          have hI_split : ∫ t in s₀..((n : ℝ) + 3), φ (t - 1) =
              (∫ t in s₀..((n : ℝ) + 3), fHat m (t - 1)) +
              (∫ t in s₀..((n : ℝ) + 3), E_bjs_seq K_seq m (t - 1)) :=
            intervalIntegral.integral_add hf_int hE_int
          have hf_tail : (1 / s₀) * ∫ t in s₀..((n : ℝ) + 3), fHat m (t - 1) = fHat n s₀ := by
            have hm3 : (m : ℝ) + 3 ≤ (n : ℝ) + 3 := by
              have hnm : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast (by omega : n = m + 1)
              linarith
            have htail := fHat_tail_integral m hm1 (s := s₀) (M := (n : ℝ) + 3) hm3
            have hnm_eq : m + 1 = n := by omega
            rw [hnm_eq] at htail
            by_cases hn_ev : Even n
            · exact (htail.1 hn_ev hs₀_ge2).symm
            · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_ev
              have hs₀_ge3 : 3 ≤ s₀ := by
                rw [show s₀ = Real.log D / Real.log z₀ from rfl, le_div_iff₀ hlogz₀_pos]
                have h1 := Real.log_le_log (by positivity) (hz₀3 hn_odd)
                rw [Real.log_pow] at h1; push_cast at h1; linarith
              exact (htail.2 hn_odd hs₀_ge3).symm
          have hE_eq : E_bjs_seq K_seq n s₀ =
              (K_seq n - 1) * (fHat m (s₀ - 1) + E_bjs_seq K_seq m (s₀ - 1)) +
                (K_seq n / s₀) * (∫ t in s₀..((n : ℝ) + 3), E_bjs_seq K_seq m (t - 1)) +
                ((K_seq n - 1) / s₀) * ∫ t in s₀..((n : ℝ) + 3), fHat m (t - 1) := by
            have hmn_sub : n - 1 = m := by omega
            by_cases hn_ev : Even n
            · simpa [hmn_sub] using E_bjs_seq_even_of_ge_two K_seq hn2 hn_ev hs₀_ge2
            · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_ev
              have hn3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hn_odd; omega
              have hs₀_ge3 : 3 ≤ s₀ := by
                rw [show s₀ = Real.log D / Real.log z₀ from rfl, le_div_iff₀ hlogz₀_pos]
                have h1 := Real.log_le_log (by positivity) (hz₀3 hn_odd)
                rw [Real.log_pow] at h1; push_cast at h1; linarith
              simpa [hmn_sub] using E_bjs_seq_odd_of_ge_three K_seq hn3 hn_odd hs₀_ge3
          have hbracket_eq : (K_seq n - 1) * φ (s₀ - 1) +
              (K_seq n / s₀) * ∫ t in s₀..((n : ℝ) + 3), φ (t - 1) =
              fHat n s₀ + E_bjs_seq K_seq n s₀ := by
            rw [hI_split, hE_eq]
            dsimp [φ]
            have h1 : (K_seq n / s₀) * ∫ t in s₀..((n : ℝ) + 3), fHat m (t - 1) =
                (1 / s₀) * (∫ t in s₀..((n : ℝ) + 3), fHat m (t - 1)) +
                ((K_seq n - 1) / s₀) * ∫ t in s₀..((n : ℝ) + 3), fHat m (t - 1) := by
              have hs₀_ne : s₀ ≠ 0 := hs₀_pos.ne'
              field_simp [hs₀_ne]; ring
            linarith [hf_tail]
          have hVP₀_nn : 0 ≤ sieveV g P₀ := sieveV_nonneg fun p hp => (hg₀ p hp).2
          calc T_sum g n D P₀
              ≤ ∑ p ∈ P₀.filter (fun p : ℕ => u ≤ (p : ℝ)),
                  g p * sieveV g (P₀.filter (· < p)) *
                    φ (Real.log (D / (p : ℝ)) / Real.log (p : ℝ)) := hsum_le
            _ ≤ sieveV g P₀ * ((K_seq n - 1) * φ (s₀ - 1) +
                  (K_seq n / s₀) * ∫ t in s₀..((n : ℝ) + 3), φ (t - 1)) := habel
            _ = sieveV g P₀ * (fHat n s₀ + E_bjs_seq K_seq n s₀) := by rw [hbracket_eq]
        · have hsum_zero :
              ∑ p ∈ P₀.filter (fun p : ℕ => u ≤ (p : ℝ)),
                g p * sieveV g (P₀.filter (· < p)) *
                  φ (Real.log (D / (p : ℝ)) / Real.log (p : ℝ)) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have hpP : p ∈ P₀ := (Finset.mem_filter.mp hp).1
            have hp2 : 2 ≤ p := (hP₀ p hpP).1
            have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
            have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
            have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt1
            have hlogp_lt : Real.log (p : ℝ) < Real.log z₀ := Real.log_lt_log hp_pos (hP₀_ltz p hpP)
            have hs_lt : s₀ < Real.log D / Real.log (p : ℝ) :=
              div_lt_div_of_pos_left hlogD_pos hlogp_pos hlogp_lt
            have hsub : Real.log (D / (p : ℝ)) / Real.log (p : ℝ) =
                Real.log D / Real.log (p : ℝ) - 1 := by
              rw [Real.log_div (by linarith : D ≠ 0) hp_pos.ne', sub_div, div_self hlogp_pos.ne']
            have hge_supp : (n : ℝ) + 3 ≤ Real.log (D / (p : ℝ)) / Real.log (p : ℝ) + 1 := by
              linarith
            have hzero := hφ_supp (Real.log (D / (p : ℝ)) / Real.log (p : ℝ) + 1) hge_supp
            simp only [add_sub_cancel_right] at hzero
            rw [hzero, mul_zero]
          have hT_le0 : T_sum g n D P₀ ≤ 0 := by linarith [hsum_le, hsum_zero]
          have hVP₀_nn : 0 ≤ sieveV g P₀ := sieveV_nonneg fun p hp => (hg₀ p hp).2
          have hK_n_all : ∀ j, 1 ≤ j → j ≤ n → 1 ≤ K_seq j := fun j hj1 hjn => (hK_seq₀ j hj1 hjn).1
          have hrhs_nn : 0 ≤ sieveV g P₀ * (fHat n s₀ + E_bjs_seq K_seq n s₀) :=
            mul_nonneg hVP₀_nn (add_nonneg (fHat_nonneg n s₀) (E_bjs_seq_nonneg n hK_n_all s₀))
          linarith
      -- Dispatch on parity of `n` and whether `s ≥ 3` or `1 ≤ s < 3`
      by_cases hn_ev : n % 2 = 0
      · simp only [hn_ev, ↓reduceIte] at hDz
        exact hstep_ge z P hz hDz (fun hodd => absurd (Nat.even_iff.mpr hn_ev) (Nat.not_even_iff_odd.mpr hodd))
          hP hg hu_le hK_seq
      · have hn_odd : Odd n := Nat.odd_iff.mpr (by omega)
        have hn3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hn_odd; omega
        simp only [hn_ev, ↓reduceIte] at hDz
        have hD_gt1 : 1 < D := lt_of_lt_of_le hz hDz
        have hlogD_pos : 0 < Real.log D := Real.log_pos hD_gt1
        have hs_ge1 : 1 ≤ s := (one_le_div hlogz_pos).mpr (Real.log_le_log (by linarith) hDz)
        rcases le_or_gt 3 s with hs3 | hs3
        · have hz3 : z ^ 3 ≤ D := by
            have hle : 3 * Real.log z ≤ Real.log D := (le_div_iff₀ hlogz_pos).mp hs3
            have hlog_z3 : Real.log (z ^ 3) = 3 * Real.log z := by rw [Real.log_pow]; norm_num
            rw [← hlog_z3] at hle
            exact (Real.log_le_log_iff (by positivity) (by linarith)).mp hle
          have hz2 : z ^ 2 ≤ D := by nlinarith
          exact hstep_ge z P hz hz2 (fun _ => hz3) hP hg hu_le hK_seq
        · -- `1 ≤ s < 3` and `n ≥ 3` odd: reduce to `z' = D ^ (1/3)` where `s' = 3`
          set z' : ℝ := D ^ (1 / 3 : ℝ)
          set P' : Finset ℕ := P.filter (fun p : ℕ => (p : ℝ) < z')
          have hz'_gt1 : 1 < z' := Real.one_lt_rpow hD_gt1 (by norm_num)
          have hz'3 : z' ^ 3 = D := by
            dsimp [z']; rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
          have hz'2 : z' ^ 2 ≤ D := by
            have h1 : z' ^ 2 ≤ z' ^ 3 := pow_le_pow_right₀ hz'_gt1.le (by norm_num)
            linarith
          have hz'_lt_z : z' < z := by
            have hD_lt_z3 : D < z ^ 3 := by
              have hlt : Real.log D < 3 * Real.log z := (div_lt_iff₀ hlogz_pos).mp hs3
              have hlog_z3 : Real.log (z ^ 3) = 3 * Real.log z := by rw [Real.log_pow]; norm_num
              rw [← hlog_z3] at hlt
              exact (Real.log_lt_log_iff (by linarith) (by positivity)).mp hlt
            exact rpow_one_third_lt_of_lt_cube (by linarith) (by positivity) hD_lt_z3
          have hu_le' : u ≤ u_bjs n D z' := by
            simpa [u_bjs, hn_ev] using hu_le
          have hK_seq' : ∀ j, 1 ≤ j → j ≤ n → 1 ≤ K_seq j ∧ AllLevelsMertensCondFrom g P' u (K_seq j) :=
            fun j hj1 hjn => ⟨(hK_seq j hj1 hjn).1,
              (hK_seq j hj1 hjn).2.filter_lt (hK_seq j hj1 hjn).1 (fun q hq => (hg q hq).2) z'⟩
          have h3 := hstep_ge z' P' hz'_gt1 hz'2 (fun _ => hz'3.le)
            (fun p hp => ⟨(hP p (Finset.filter_subset _ P hp)).1, (Finset.mem_filter.mp hp).2⟩)
            (fun p hp => hg p (Finset.filter_subset _ P hp)) hu_le' hK_seq'
          have hlogz' : Real.log z' = (1 / 3 : ℝ) * Real.log D := by
            dsimp [z']; rw [Real.log_rpow (by linarith)]
          have hs'_eq : Real.log D / Real.log z' = 3 := by
            rw [hlogz']
            have hlogD_ne : Real.log D ≠ 0 := hlogD_pos.ne'
            field_simp [hlogD_ne]
          rw [hs'_eq] at h3
          have hT_eq : T_sum g n D P = T_sum g n D P' :=
            T_sum_filter_lt_eq_self hn2 hn_odd (by linarith) hP_pos
          have hu_le_z' : u ≤ z' := by
            refine hu_le.trans ?_
            simp only [u_bjs, hn_ev, ↓reduceIte]
            have hexp_le : (1 / 3 : ℝ) ^ ((n + 1) / 2) ≤ 1 / 3 := by
              have hexp1 : 1 ≤ (n + 1) / 2 := by omega
              calc (1 / 3 : ℝ) ^ ((n + 1) / 2) ≤ (1 / 3 : ℝ) ^ 1 :=
                    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp1
                _ = 1 / 3 := pow_one _
            exact Real.rpow_le_rpow_of_exponent_le hD_gt1.le hexp_le
          have hK_n : 1 ≤ K_seq n := (hK_seq n (by omega) le_rfl).1
          have hCond_n : AllLevelsMertensCondFrom g P u (K_seq n) := (hK_seq n (by omega) le_rfl).2
          have hV_ratio : sieveV g P' ≤ (3 * K_seq n / s) * sieveV g P := by
            have hcond := hCond_n hz'_gt1 hu_le_z' hz'_lt_z.le
            have hfilt_z : P.filter (fun p : ℕ => (p : ℝ) < z) = P := by
              ext p; simp only [Finset.mem_filter]
              exact ⟨fun h => h.1, fun hp => ⟨hp, hP_ltz p hp⟩⟩
            rw [hfilt_z] at hcond
            have hratio_eq : Real.log z / Real.log z' = 3 / s := by
              rw [hlogz']
              dsimp [s]
              have hlogD_ne : Real.log D ≠ 0 := hlogD_pos.ne'
              have hlogz_ne : Real.log z ≠ 0 := hlogz_pos.ne'
              field_simp [hlogD_ne, hlogz_ne]
            rw [hratio_eq] at hcond
            exact hcond.trans_eq (by ring)
          have hK_n_all : ∀ j, 1 ≤ j → j ≤ n → 1 ≤ K_seq j := fun j hj1 hjn => (hK_seq j hj1 hjn).1
          have hbr_nn : 0 ≤ fHat n 3 + E_bjs_seq K_seq n 3 :=
            add_nonneg (fHat_nonneg n 3) (E_bjs_seq_nonneg n hK_n_all 3)
          have hf_s_eq : (3 / s) * fHat n 3 = fHat n s := by
            have hnot1 : ¬ s < 1 := by linarith
            have hmod : (m' + 2) % 2 ≠ 0 := by
              intro h0; exact Nat.not_even_iff_odd.mpr hn_odd (Nat.even_iff.mpr h0)
            have hmax3 : max 3 s = 3 := max_eq_left hs3.le
            have hs_def : fHat n s = (1 / s) * ∫ t in (3 : ℝ)..((m' : ℝ) + 4), fHat (m' + 1) (t - 1) := by
              rw [show n = m' + 2 from rfl, fHat]
              simp only [hnot1, ↓reduceIte, hmod, hmax3]
            have h3_def : fHat n 3 = (1 / 3) * ∫ t in (3 : ℝ)..((m' : ℝ) + 4), fHat (m' + 1) (t - 1) := by
              rw [show n = m' + 2 from rfl, fHat]
              have hnot31 : ¬ (3 : ℝ) < 1 := by norm_num
              simp only [hnot31, ↓reduceIte, hmod, max_self]
            rw [hs_def, h3_def]
            have hs_ne : s ≠ 0 := (by linarith : 0 < s).ne'
            field_simp [hs_ne]
          have hE3_eq := E_bjs_seq_odd_of_ge_three K_seq hn3 hn_odd (le_refl 3)
          have hEs_eq := E_bjs_seq_odd_of_Ico K_seq hn3 hn_odd hs_ge1 hs3
          have hf3_eq : fHat n 3 = (1 / 3) * ∫ t in (3 : ℝ)..((n : ℝ) + 3), fHat (n - 1) (t - 1) := by
            have hm3 : (m : ℝ) + 3 ≤ (n : ℝ) + 3 := by
              have hnm : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast (by omega : n = m + 1)
              linarith
            have htail := (fHat_tail_integral m hm1 (s := 3) (M := (n : ℝ) + 3) hm3).2
              (by simpa [show m + 1 = n by omega] using hn_odd) le_rfl
            simpa [show m + 1 = n by omega, show n - 1 = m by omega] using htail
          have hid : (3 * K_seq n / s) * (fHat n 3 + E_bjs_seq K_seq n 3) =
              fHat n s + E_bjs_seq K_seq n s := by
            rw [hE3_eq, hEs_eq, ← hf_s_eq]
            have hs_ne : s ≠ 0 := (by linarith : 0 < s).ne'
            have hsub : (3 * (K_seq n - 1) / s) * fHat n 3 +
                (3 * K_seq n / s) * (((K_seq n - 1) / 3) * (∫ t in (3 : ℝ)..((n : ℝ) + 3), fHat (n - 1) (t - 1))) =
                ((K_seq n ^ 2 - 1) / s) * ∫ t in (3 : ℝ)..((n : ℝ) + 3), fHat (n - 1) (t - 1) := by
              rw [hf3_eq]
              field_simp [hs_ne]
              ring
            calc (3 * K_seq n / s) * (fHat n 3 + ((K_seq n - 1) * (fHat (n - 1) (3 - 1) + E_bjs_seq K_seq (n - 1) (3 - 1)) +
                    K_seq n / 3 * (∫ t in (3 : ℝ)..((n : ℝ) + 3), E_bjs_seq K_seq (n - 1) (t - 1)) +
                    (K_seq n - 1) / 3 * (∫ t in (3 : ℝ)..((n : ℝ) + 3), fHat (n - 1) (t - 1))))
                = (3 / s) * fHat n 3 +
                    ((3 * (K_seq n - 1) / s) * fHat n 3 +
                      (3 * K_seq n / s) * (((K_seq n - 1) / 3) * (∫ t in (3 : ℝ)..((n : ℝ) + 3), fHat (n - 1) (t - 1)))) +
                    (3 * K_seq n * (K_seq n - 1) / s) * (fHat (n - 1) 2 + E_bjs_seq K_seq (n - 1) 2) +
                    (K_seq n ^ 2 / s) * (∫ t in (3 : ℝ)..((n : ℝ) + 3), E_bjs_seq K_seq (n - 1) (t - 1)) := by
                    norm_num; field_simp [hs_ne]; ring
              _ = (3 / s) * fHat n 3 +
                    ((3 * K_seq n * (K_seq n - 1) / s) * (fHat (n - 1) 2 + E_bjs_seq K_seq (n - 1) 2) +
                      K_seq n ^ 2 / s * (∫ t in (3 : ℝ)..((n : ℝ) + 3), E_bjs_seq K_seq (n - 1) (t - 1)) +
                      (K_seq n ^ 2 - 1) / s * (∫ t in (3 : ℝ)..((n : ℝ) + 3), fHat (n - 1) (t - 1))) := by
                    rw [hsub]; ring
          calc T_sum g n D P = T_sum g n D P' := hT_eq
            _ ≤ sieveV g P' * (fHat n 3 + E_bjs_seq K_seq n 3) := h3
            _ ≤ ((3 * K_seq n / s) * sieveV g P) * (fHat n 3 + E_bjs_seq K_seq n 3) :=
                mul_le_mul_of_nonneg_right hV_ratio hbr_nn
            _ = sieveV g P * ((3 * K_seq n / s) * (fHat n 3 + E_bjs_seq K_seq n 3)) := by ring
            _ = sieveV g P * (fHat n s + E_bjs_seq K_seq n s) := by rw [hid]

/-- Constant-`K` BJS Lemma 11 bound using the depth-dependent lower threshold `1 ≤ u ≤ u_bjs n D z`. -/
theorem T_sum_le_fHat_add_E_bjs_of_lower_bound {g : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    {P : Finset ℕ} {z D u K : ℝ} (hz : 1 < z)
    (hDz : if n % 2 = 0 then z ^ 2 ≤ D else z ≤ D)
    (hP : ∀ p ∈ P, 2 ≤ p ∧ (p : ℝ) < z) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1)
    (hK : 1 ≤ K) (hu_ge : 1 ≤ u) (hu_le : u ≤ u_bjs n D z)
    (hCond : AllLevelsMertensCondFrom g P u K) :
    T_sum g n D P ≤ sieveV g P * (fHat n (Real.log D / Real.log z) + E_bjs K n (Real.log D / Real.log z)) :=
  T_sum_le_fHat_add_E_bjs_seq n hn hz hDz hP hg hu_ge hu_le (fun _ _ _ => ⟨hK, hCond⟩)

private lemma u_bjs_gt_one {n : ℕ} (_hn : 1 ≤ n) {D z : ℝ} (hz : 1 < z)
    (hDz : if n % 2 = 0 then z ^ 2 ≤ D else z ≤ D) : 1 < u_bjs n D z := by
  by_cases hev : n % 2 = 0
  · simp only [hev, ↓reduceIte] at hDz
    simp only [u_bjs, hev, ↓reduceIte]
    have hDz1 : 1 < D / z := (one_lt_div (by linarith)).mpr (by nlinarith)
    exact Real.one_lt_rpow hDz1 (by positivity)
  · simp only [hev, ↓reduceIte] at hDz
    simp only [u_bjs, hev, ↓reduceIte]
    exact Real.one_lt_rpow (lt_of_lt_of_le hz hDz) (by positivity)

/-- Uniform `AllLevelsMertensCond` version of the BJS Lemma 11 bound `T_sum_le_fHat_add_E_bjs`. -/
theorem T_sum_le_fHat_add_E_bjs {g : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    {P : Finset ℕ} {z D K : ℝ} (hz : 1 < z)
    (hDz : if n % 2 = 0 then z ^ 2 ≤ D else z ≤ D)
    (hP : ∀ p ∈ P, 2 ≤ p ∧ (p : ℝ) < z) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1)
    (hK : 1 ≤ K) (hCond : AllLevelsMertensCond g P K) :
    T_sum g n D P ≤ sieveV g P * (fHat n (Real.log D / Real.log z) + E_bjs K n (Real.log D / Real.log z)) :=
  T_sum_le_fHat_add_E_bjs_of_lower_bound hn hz hDz hP hg hK le_rfl
    (u_bjs_gt_one hn hz hDz).le (hCond.to_from 1)

end

end BuchstabSwitching
