import BuchstabSwitching.Sieve.RosserIwaniecComb
import BuchstabSwitching.Sieve.BuchstabFunctions
import Mathlib.Tactic

/-!
# BJS Lemma 11 Recursive Error Envelopes and Prefix Prime Lower Bounds

Defines `E_bjs_seq`, `E_bjs`, proves support, nonnegativity, and antitonicity on `[1, ∞)`,
defines the depth-dependent prime lower bound `u_bjs n D z`, and proves `T_sum_prefix_min_gt`.
-/

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 3. Exact BJS Lemma 11 Recursive Error Envelope `E_bjs` and Inductive `T_sum` Bound -/

/-- Depth-dependent BJS Lemma 11 recursive error envelope `E_bjs_seq K_seq n s`. -/
def E_bjs_seq (K_seq : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => if 1 ≤ s ∧ s < 3 then (3 / s) * (K_seq 1 - 1) else 0
  | n + 2, s =>
    let K := K_seq (n + 2)
    if s < 1 then 0
    else if (n + 2) % 2 = 0 then
      let u := max 2 s
      (K - 1) * (fHat (n + 1) (u - 1) + E_bjs_seq K_seq (n + 1) (u - 1)) +
        (K / u) * (∫ t in u..((n : ℝ) + 5), E_bjs_seq K_seq (n + 1) (t - 1)) +
        ((K - 1) / u) * ∫ t in u..((n : ℝ) + 5), fHat (n + 1) (t - 1)
    else if s < 3 then
      (3 * K * (K - 1) / s) * (fHat (n + 1) 2 + E_bjs_seq K_seq (n + 1) 2) +
        (K ^ 2 / s) * (∫ t in (3 : ℝ)..((n : ℝ) + 5), E_bjs_seq K_seq (n + 1) (t - 1)) +
        ((K ^ 2 - 1) / s) * ∫ t in (3 : ℝ)..((n : ℝ) + 5), fHat (n + 1) (t - 1)
    else
      (K - 1) * (fHat (n + 1) (s - 1) + E_bjs_seq K_seq (n + 1) (s - 1)) +
        (K / s) * (∫ t in s..((n : ℝ) + 5), E_bjs_seq K_seq (n + 1) (t - 1)) +
        ((K - 1) / s) * ∫ t in s..((n : ℝ) + 5), fHat (n + 1) (t - 1)

/-- Constant-`K` BJS Lemma 11 recursive error envelope `E_bjs K n s`. -/
def E_bjs (K : ℝ) : ℕ → ℝ → ℝ := E_bjs_seq (fun _ => K)

@[simp]
theorem E_bjs_seq_zero (K_seq : ℕ → ℝ) (s : ℝ) : E_bjs_seq K_seq 0 s = 0 := rfl

@[simp]
theorem E_bjs_zero (K : ℝ) (s : ℝ) : E_bjs K 0 s = 0 := rfl

theorem E_bjs_seq_one_of_Ico (K_seq : ℕ → ℝ) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s < 3) :
    E_bjs_seq K_seq 1 s = (3 / s) * (K_seq 1 - 1) := by
  simp [E_bjs_seq, hs1, hs3]

theorem E_bjs_seq_one_of_ge_three (K_seq : ℕ → ℝ) {s : ℝ} (hs3 : 3 ≤ s) :
    E_bjs_seq K_seq 1 s = 0 := by
  have hnot : ¬ s < 3 := not_lt.mpr hs3
  simp [E_bjs_seq, hnot]

theorem E_bjs_one_of_Ico (K : ℝ) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s < 3) :
    E_bjs K 1 s = (3 / s) * (K - 1) :=
  E_bjs_seq_one_of_Ico (fun _ => K) hs1 hs3

theorem E_bjs_one_of_ge_three (K : ℝ) {s : ℝ} (hs3 : 3 ≤ s) :
    E_bjs K 1 s = 0 :=
  E_bjs_seq_one_of_ge_three (fun _ => K) hs3

theorem E_bjs_seq_even_of_ge_two (K_seq : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) (hev : Even n)
    {s : ℝ} (hs2 : 2 ≤ s) :
    E_bjs_seq K_seq n s =
      (K_seq n - 1) * (fHat (n - 1) (s - 1) + E_bjs_seq K_seq (n - 1) (s - 1)) +
        (K_seq n / s) * (∫ t in s..((n : ℝ) + 3), E_bjs_seq K_seq (n - 1) (t - 1)) +
        ((K_seq n - 1) / s) * ∫ t in s..((n : ℝ) + 3), fHat (n - 1) (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnot1 : ¬ s < 1 := by linarith
  have hmod : (m + 2) % 2 = 0 := Nat.even_iff.mp hev
  have hmax : max 2 s = s := max_eq_right hs2
  have hcast : ((m + 2 : ℕ) : ℝ) + 3 = (m : ℝ) + 5 := by push_cast; ring
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [E_bjs_seq, hnot1, ↓reduceIte, hmod, hmax, hcast, hsub]

theorem E_bjs_seq_odd_of_ge_three (K_seq : ℕ → ℝ) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    {s : ℝ} (hs3 : 3 ≤ s) :
    E_bjs_seq K_seq n s =
      (K_seq n - 1) * (fHat (n - 1) (s - 1) + E_bjs_seq K_seq (n - 1) (s - 1)) +
        (K_seq n / s) * (∫ t in s..((n : ℝ) + 3), E_bjs_seq K_seq (n - 1) (t - 1)) +
        ((K_seq n - 1) / s) * ∫ t in s..((n : ℝ) + 3), fHat (n - 1) (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnot1 : ¬ s < 1 := by linarith
  have hnot3 : ¬ s < 3 := not_lt.mpr hs3
  have hmod : (m + 2) % 2 ≠ 0 := by
    intro h0; exact Nat.not_even_iff_odd.mpr hodd (Nat.even_iff.mpr h0)
  have hcast : ((m + 2 : ℕ) : ℝ) + 3 = (m : ℝ) + 5 := by push_cast; ring
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [E_bjs_seq, hnot1, ↓reduceIte, hmod, hnot3, hcast, hsub]

theorem E_bjs_seq_odd_of_Ico (K_seq : ℕ → ℝ) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s < 3) :
    E_bjs_seq K_seq n s =
      (3 * K_seq n * (K_seq n - 1) / s) * (fHat (n - 1) 2 + E_bjs_seq K_seq (n - 1) 2) +
        (K_seq n ^ 2 / s) * (∫ t in (3 : ℝ)..((n : ℝ) + 3), E_bjs_seq K_seq (n - 1) (t - 1)) +
        ((K_seq n ^ 2 - 1) / s) * ∫ t in (3 : ℝ)..((n : ℝ) + 3), fHat (n - 1) (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hnot1 : ¬ s < 1 := not_lt.mpr hs1
  have hmod : (m + 2) % 2 ≠ 0 := by
    intro h0; exact Nat.not_even_iff_odd.mpr hodd (Nat.even_iff.mpr h0)
  have hcast : ((m + 2 : ℕ) : ℝ) + 3 = (m : ℝ) + 5 := by push_cast; ring
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [E_bjs_seq, hnot1, ↓reduceIte, hmod, hs3, hcast, hsub]

theorem E_bjs_seq_support (K_seq : ℕ → ℝ) :
    ∀ (n : ℕ), 1 ≤ n → ∀ {s : ℝ}, (n : ℝ) + 2 ≤ s → E_bjs_seq K_seq n s = 0 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases n with _ | m
    · intro s hs
      exact E_bjs_seq_one_of_ge_three K_seq (by norm_num at hs ⊢; exact hs)
    · intro s hs
      have hm1 : 1 ≤ m + 1 := by omega
      have hs4 : (m : ℝ) + 4 ≤ s := by push_cast at hs; linarith
      have hnot1 : ¬ s < 1 := by linarith
      have hf_pt : fHat (m + 1) (s - 1) = 0 :=
        fHat_support (m + 1) hm1 (by push_cast; linarith)
      have hE_pt : E_bjs_seq K_seq (m + 1) (s - 1) = 0 :=
        ih hm1 (by push_cast; linarith)
      have hf_int : ∫ t in s..((m : ℝ) + 5), fHat (m + 1) (t - 1) = 0 := by
        have hEq : EqOn (fun t => fHat (m + 1) (t - 1)) (fun _ => 0) (uIcc s ((m : ℝ) + 5)) := by
          intro t ht
          rcases le_or_gt s ((m : ℝ) + 5) with hs5 | hs5
          · rw [uIcc_of_le hs5] at ht
            exact fHat_support (m + 1) hm1 (by push_cast; linarith [ht.1])
          · rw [uIcc_of_ge hs5.le] at ht
            exact fHat_support (m + 1) hm1 (by push_cast; linarith [ht.1])
        rw [integral_congr hEq, intervalIntegral.integral_zero]
      have hE_int : ∫ t in s..((m : ℝ) + 5), E_bjs_seq K_seq (m + 1) (t - 1) = 0 := by
        have hEq : EqOn (fun t => E_bjs_seq K_seq (m + 1) (t - 1)) (fun _ => 0)
            (uIcc s ((m : ℝ) + 5)) := by
          intro t ht
          rcases le_or_gt s ((m : ℝ) + 5) with hs5 | hs5
          · rw [uIcc_of_le hs5] at ht
            exact ih hm1 (by push_cast; linarith [ht.1])
          · rw [uIcc_of_ge hs5.le] at ht
            exact ih hm1 (by push_cast; linarith [ht.1])
        rw [integral_congr hEq, intervalIntegral.integral_zero]
      have hcast : ((m + 2 : ℕ) : ℝ) + 3 = (m : ℝ) + 5 := by push_cast; ring
      have hsub : m + 2 - 1 = m + 1 := by omega
      by_cases hev : Even (m + 2)
      · rw [E_bjs_seq_even_of_ge_two K_seq (by omega) hev (by linarith)]
        rw [hcast, hsub, hf_pt, hE_pt, hf_int, hE_int]
        ring
      · have hodd : Odd (m + 2) := Nat.not_even_iff_odd.mp hev
        have hm3 : 3 ≤ m + 2 := by obtain ⟨k, hk⟩ := hodd; omega
        rw [E_bjs_seq_odd_of_ge_three K_seq hm3 hodd (by linarith)]
        rw [hcast, hsub, hf_pt, hE_pt, hf_int, hE_int]
        ring

theorem E_bjs_support (K : ℝ) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : (n : ℝ) + 2 ≤ s) :
    E_bjs K n s = 0 :=
  E_bjs_seq_support (fun _ => K) n hn hs

theorem E_bjs_seq_nonneg {K_seq : ℕ → ℝ} :
    ∀ (n : ℕ), (∀ m, 1 ≤ m → m ≤ n → 1 ≤ K_seq m) → ∀ (s : ℝ), 0 ≤ E_bjs_seq K_seq n s := by
  intro n
  induction n with
  | zero => intro _ s; simp
  | succ n ih =>
    rcases n with _ | m
    · intro hK s
      unfold E_bjs_seq
      split_ifs with h
      · exact mul_nonneg (div_nonneg (by norm_num) (by linarith [h.1])) (by linarith [hK 1 le_rfl le_rfl])
      · exact le_rfl
    · intro hK s
      have ih' := ih (fun j hj1 hjm => hK j hj1 (Nat.le_succ_of_le hjm))
      by_cases hs1 : s < 1
      · simp [E_bjs_seq, hs1]
      · have hs1' : 1 ≤ s := le_of_not_gt hs1
        have hs0 : 0 < s := by linarith
        by_cases hs4 : (m : ℝ) + 4 ≤ s
        · rw [E_bjs_seq_support K_seq (m + 2) (by omega) (by push_cast; linarith)]
        · have hs5 : s ≤ (m : ℝ) + 5 := by linarith
          have hK_top : 1 ≤ K_seq (m + 2) := hK (m + 2) (by omega) le_rfl
          have hK_nn : 0 ≤ K_seq (m + 2) - 1 := by linarith
          have hK_pos : 0 ≤ K_seq (m + 2) := by linarith
          have hK2_nn : 0 ≤ K_seq (m + 2) ^ 2 - 1 := by nlinarith
          simp only [E_bjs_seq, hs1, ↓reduceIte]
          split_ifs with hev hs3
          · have hu5 : max 2 s ≤ (m : ℝ) + 5 := max_le (by linarith) hs5
            have hI_E : 0 ≤ ∫ t in (max 2 s)..((m : ℝ) + 5), E_bjs_seq K_seq (m + 1) (t - 1) :=
              intervalIntegral.integral_nonneg hu5 fun t _ => ih' (t - 1)
            have hI_f : 0 ≤ ∫ t in (max 2 s)..((m : ℝ) + 5), fHat (m + 1) (t - 1) :=
              intervalIntegral.integral_nonneg hu5 fun t _ => fHat_nonneg (m + 1) (t - 1)
            have hpt : 0 ≤ fHat (m + 1) (max 2 s - 1) + E_bjs_seq K_seq (m + 1) (max 2 s - 1) :=
              add_nonneg (fHat_nonneg _ _) (ih' _)
            have hu0 : 0 < max 2 s := by linarith [le_max_left (2 : ℝ) s]
            exact add_nonneg
              (add_nonneg (mul_nonneg hK_nn hpt) (mul_nonneg (div_nonneg hK_pos hu0.le) hI_E))
              (mul_nonneg (div_nonneg hK_nn hu0.le) hI_f)
          · have h35 : (3 : ℝ) ≤ (m : ℝ) + 5 := by linarith
            have hI_E : 0 ≤ ∫ t in (3 : ℝ)..((m : ℝ) + 5), E_bjs_seq K_seq (m + 1) (t - 1) :=
              intervalIntegral.integral_nonneg h35 fun t _ => ih' (t - 1)
            have hI_f : 0 ≤ ∫ t in (3 : ℝ)..((m : ℝ) + 5), fHat (m + 1) (t - 1) :=
              intervalIntegral.integral_nonneg h35 fun t _ => fHat_nonneg (m + 1) (t - 1)
            have hpt : 0 ≤ fHat (m + 1) 2 + E_bjs_seq K_seq (m + 1) 2 :=
              add_nonneg (fHat_nonneg _ _) (ih' _)
            exact add_nonneg
              (add_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by positivity) hK_nn) hs0.le) hpt)
                (mul_nonneg (div_nonneg (sq_nonneg _) hs0.le) hI_E))
              (mul_nonneg (div_nonneg hK2_nn hs0.le) hI_f)
          · have hI_E : 0 ≤ ∫ t in s..((m : ℝ) + 5), E_bjs_seq K_seq (m + 1) (t - 1) :=
              intervalIntegral.integral_nonneg hs5 fun t _ => ih' (t - 1)
            have hI_f : 0 ≤ ∫ t in s..((m : ℝ) + 5), fHat (m + 1) (t - 1) :=
              intervalIntegral.integral_nonneg hs5 fun t _ => fHat_nonneg (m + 1) (t - 1)
            have hpt : 0 ≤ fHat (m + 1) (s - 1) + E_bjs_seq K_seq (m + 1) (s - 1) :=
              add_nonneg (fHat_nonneg _ _) (ih' _)
            exact add_nonneg
              (add_nonneg (mul_nonneg hK_nn hpt) (mul_nonneg (div_nonneg hK_pos hs0.le) hI_E))
              (mul_nonneg (div_nonneg hK_nn hs0.le) hI_f)

theorem E_bjs_nonneg {K : ℝ} (hK : 1 ≤ K) (n : ℕ) (s : ℝ) : 0 ≤ E_bjs K n s :=
  E_bjs_seq_nonneg n (fun _ _ _ => hK) s

theorem E_bjs_seq_antitone {K_seq : ℕ → ℝ} :
    ∀ (n : ℕ), 1 ≤ n → (∀ m, 1 ≤ m → m ≤ n → 1 ≤ K_seq m) →
      AntitoneOn (E_bjs_seq K_seq n) (Set.Ici 1) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases n with _ | m
    · intro hK a ha b hb hab
      have ha1 : 1 ≤ a := Set.mem_Ici.mp ha
      have hb1 : 1 ≤ b := Set.mem_Ici.mp hb
      by_cases ha3 : a < 3
      · rw [E_bjs_seq_one_of_Ico K_seq ha1 ha3]
        by_cases hb3 : b < 3
        · rw [E_bjs_seq_one_of_Ico K_seq hb1 hb3]
          refine mul_le_mul_of_nonneg_right ?_ (by linarith [hK 1 le_rfl le_rfl])
          exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hab
        · rw [E_bjs_seq_one_of_ge_three K_seq (le_of_not_gt hb3)]
          exact mul_nonneg (by positivity) (by linarith [hK 1 le_rfl le_rfl])
      · rw [E_bjs_seq_one_of_ge_three K_seq (le_of_not_gt ha3),
          E_bjs_seq_one_of_ge_three K_seq (le_trans (le_of_not_gt ha3) hab)]
    · intro hK
      have hK_prev : ∀ j, 1 ≤ j → j ≤ m + 1 → 1 ≤ K_seq j := fun j hj1 hjm =>
        hK j hj1 (Nat.le_succ_of_le hjm)
      have ih' := ih (by omega) hK_prev
      have hm1 : 1 ≤ m + 1 := by omega
      have hf_anti := fHat_antitone (m + 1) hm1
      have hE_int : ∀ u v, 2 ≤ u → u ≤ v →
          IntervalIntegrable (fun t => E_bjs_seq K_seq (m + 1) (t - 1)) volume u v := by
        intro u v hu huv
        refine AntitoneOn.intervalIntegrable ?_
        rw [uIcc_of_le huv]
        intro x hx y hy hxy
        exact ih' (by simp only [Set.mem_Ici]; linarith [hx.1])
          (by simp only [Set.mem_Ici]; linarith [hy.1]) (by linarith)
      have hf_int : ∀ u v, 2 ≤ u → u ≤ v →
          IntervalIntegrable (fun t => fHat (m + 1) (t - 1)) volume u v := by
        intro u v hu huv
        refine AntitoneOn.intervalIntegrable ?_
        rw [uIcc_of_le huv]
        intro x hx y hy hxy
        exact hf_anti (by simp only [Set.mem_Ici]; linarith [hx.1])
          (by simp only [Set.mem_Ici]; linarith [hy.1]) (by linarith)
      have htail_anti : ∀ (φ : ℝ → ℝ),
          (∀ t, 0 ≤ φ t) → (∀ t, (m : ℝ) + 4 ≤ t → φ (t - 1) = 0) →
          (∀ u v, 2 ≤ u → u ≤ v → IntervalIntegrable (fun t => φ (t - 1)) volume u v) →
          ∀ u v, 2 ≤ u → u ≤ v →
            0 ≤ ∫ t in v..((m : ℝ) + 5), φ (t - 1) ∧
            ∫ t in v..((m : ℝ) + 5), φ (t - 1) ≤ ∫ t in u..((m : ℝ) + 5), φ (t - 1) := by
        intro φ hnn hsupp hint u v hu huv
        have hnn_v : 0 ≤ ∫ t in v..((m : ℝ) + 5), φ (t - 1) := by
          rcases le_or_gt ((m : ℝ) + 5) v with hv5 | hv5
          · have hEq : EqOn (fun t => φ (t - 1)) (fun _ => 0) (uIcc v ((m : ℝ) + 5)) := by
              intro t ht
              rw [uIcc_of_ge hv5] at ht
              exact hsupp t (by linarith [ht.1])
            rw [integral_congr hEq, intervalIntegral.integral_zero]
          · exact intervalIntegral.integral_nonneg hv5.le fun t _ => hnn (t - 1)
        have hle_uv : ∫ t in v..((m : ℝ) + 5), φ (t - 1) ≤ ∫ t in u..((m : ℝ) + 5), φ (t - 1) := by
          rcases le_or_gt ((m : ℝ) + 5) v with hv5 | hv5
          · have hzero : ∫ t in v..((m : ℝ) + 5), φ (t - 1) = 0 := by
              have hEq : EqOn (fun t => φ (t - 1)) (fun _ => 0) (uIcc v ((m : ℝ) + 5)) := by
                intro t ht; rw [uIcc_of_ge hv5] at ht; exact hsupp t (by linarith [ht.1])
              rw [integral_congr hEq, intervalIntegral.integral_zero]
            rw [hzero]
            rcases le_or_gt ((m : ℝ) + 5) u with hu5 | hu5
            · have hEq : EqOn (fun t => φ (t - 1)) (fun _ => 0) (uIcc u ((m : ℝ) + 5)) := by
                intro t ht; rw [uIcc_of_ge hu5] at ht; exact hsupp t (by linarith [ht.1])
              rw [integral_congr hEq, intervalIntegral.integral_zero]
            · exact intervalIntegral.integral_nonneg hu5.le fun t _ => hnn (t - 1)
          · have hadd := integral_add_adjacent_intervals
              (hint u v hu huv) (hint v ((m : ℝ) + 5) (hu.trans huv) hv5.le)
            have hnn_uv : 0 ≤ ∫ t in u..v, φ (t - 1) :=
              intervalIntegral.integral_nonneg huv fun t _ => hnn (t - 1)
            linarith
        exact ⟨hnn_v, hle_uv⟩
      have hE_tail := htail_anti (E_bjs_seq K_seq (m + 1)) (E_bjs_seq_nonneg (m + 1) hK_prev)
        (fun t ht => E_bjs_seq_support K_seq (m + 1) hm1 (by push_cast; linarith)) hE_int
      have hf_tail := htail_anti (fHat (m + 1)) (fHat_nonneg (m + 1))
        (fun t ht => fHat_support (m + 1) hm1 (by push_cast; linarith)) hf_int
      intro a ha b hb hab
      have ha1 : 1 ≤ a := Set.mem_Ici.mp ha
      have hb1 : 1 ≤ b := Set.mem_Ici.mp hb
      have ha_not : ¬ a < 1 := not_lt.mpr ha1
      have hb_not : ¬ b < 1 := not_lt.mpr hb1
      set K := K_seq (m + 2)
      have hK1 : 1 ≤ K := hK (m + 2) (by omega) le_rfl
      have hK_nn : 0 ≤ K - 1 := by linarith
      have hK0 : 0 ≤ K := by linarith
      simp only [E_bjs_seq, ha_not, hb_not, ↓reduceIte]
      split_ifs with hev hb3 ha3 ha3
      · have hua : 2 ≤ max 2 a := le_max_left _ _
        have huv : max 2 a ≤ max 2 b := max_le_max le_rfl hab
        have h1 : fHat (m + 1) (max 2 b - 1) ≤ fHat (m + 1) (max 2 a - 1) :=
          hf_anti (by simp only [Set.mem_Ici]; linarith) (by simp only [Set.mem_Ici]; linarith) (by linarith)
        have h2 : E_bjs_seq K_seq (m + 1) (max 2 b - 1) ≤ E_bjs_seq K_seq (m + 1) (max 2 a - 1) :=
          ih' (by simp only [Set.mem_Ici]; linarith) (by simp only [Set.mem_Ici]; linarith) (by linarith)
        obtain ⟨hE_nn, hE_le⟩ := hE_tail (max 2 a) (max 2 b) hua huv
        obtain ⟨hf_nn, hf_le⟩ := hf_tail (max 2 a) (max 2 b) hua huv
        have hdivE : K / max 2 b ≤ K / max 2 a := div_le_div_of_nonneg_left hK0 (by linarith) huv
        have hdivf : (K - 1) / max 2 b ≤ (K - 1) / max 2 a := div_le_div_of_nonneg_left hK_nn (by linarith) huv
        have t1 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK_nn
        have t2 := mul_le_mul hdivE hE_le hE_nn (by positivity)
        have t3 := mul_le_mul hdivf hf_le hf_nn (by positivity)
        dsimp only [K] at t1 t2 t3
        linarith [t1, t2, t3]
      · have hI_E_nn : 0 ≤ ∫ t in (3 : ℝ)..((m : ℝ) + 5), E_bjs_seq K_seq (m + 1) (t - 1) :=
          (hE_tail 3 3 (by norm_num) le_rfl).1
        have hI_f_nn : 0 ≤ ∫ t in (3 : ℝ)..((m : ℝ) + 5), fHat (m + 1) (t - 1) :=
          (hf_tail 3 3 (by norm_num) le_rfl).1
        have hpt_nn : 0 ≤ fHat (m + 1) 2 + E_bjs_seq K_seq (m + 1) 2 :=
          add_nonneg (fHat_nonneg _ _) (E_bjs_seq_nonneg (m + 1) hK_prev _)
        have hd1 : 3 * K * (K - 1) / b ≤ 3 * K * (K - 1) / a :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hab
        have hd2 : K ^ 2 / b ≤ K ^ 2 / a :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hab
        have hd3 : (K ^ 2 - 1) / b ≤ (K ^ 2 - 1) / a :=
          div_le_div_of_nonneg_left (by nlinarith) (by linarith) hab
        have t1 := mul_le_mul_of_nonneg_right hd1 hpt_nn
        have t2 := mul_le_mul_of_nonneg_right hd2 hI_E_nn
        have t3 := mul_le_mul_of_nonneg_right hd3 hI_f_nn
        dsimp only [K] at t1 t2 t3
        linarith [t1, t2, t3]
      · exfalso; exact ha3 (lt_of_le_of_lt hab hb3)
      · have hb3' : 3 ≤ b := le_of_not_gt hb3
        have h1 : fHat (m + 1) (b - 1) ≤ fHat (m + 1) 2 :=
          hf_anti (by simp only [Set.mem_Ici]; norm_num) (by simp only [Set.mem_Ici]; linarith) (by linarith)
        have h2 : E_bjs_seq K_seq (m + 1) (b - 1) ≤ E_bjs_seq K_seq (m + 1) 2 :=
          ih' (by simp only [Set.mem_Ici]; norm_num) (by simp only [Set.mem_Ici]; linarith) (by linarith)
        have hcoeff1 : K - 1 ≤ 3 * K * (K - 1) / a := by
          have h3a : 1 ≤ 3 / a := (one_le_div (by linarith)).mpr ha3.le
          calc K - 1 = 1 * 1 * (K - 1) := by ring
            _ ≤ (3 / a) * K * (K - 1) := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul h3a hK1 (by norm_num) (by positivity)) hK_nn
            _ = 3 * K * (K - 1) / a := by ring
        have hpt_nn : 0 ≤ fHat (m + 1) (b - 1) + E_bjs_seq K_seq (m + 1) (b - 1) :=
          add_nonneg (fHat_nonneg _ _) (E_bjs_seq_nonneg (m + 1) hK_prev _)
        have t1 := mul_le_mul hcoeff1 (add_le_add h1 h2) hpt_nn (by positivity)
        obtain ⟨hE_nn, hE_le⟩ := hE_tail 3 b (by norm_num) hb3'
        obtain ⟨hf_nn, hf_le⟩ := hf_tail 3 b (by norm_num) hb3'
        have hcoeff2 : K / b ≤ K ^ 2 / a := by
          have hba : K / b ≤ K / a := div_le_div_of_nonneg_left hK0 (by linarith) hab
          have hKK : K ≤ K ^ 2 := by nlinarith
          exact hba.trans (div_le_div_of_nonneg_right hKK (by linarith))
        have hcoeff3 : (K - 1) / b ≤ (K ^ 2 - 1) / a := by
          have hba : (K - 1) / b ≤ (K - 1) / a := div_le_div_of_nonneg_left hK_nn (by linarith) hab
          have hKK : K - 1 ≤ K ^ 2 - 1 := by nlinarith
          exact hba.trans (div_le_div_of_nonneg_right hKK (by linarith))
        have t2 := mul_le_mul hcoeff2 hE_le hE_nn (by positivity)
        have hK2a_nn : 0 ≤ (K ^ 2 - 1) / a := div_nonneg (by nlinarith) (by linarith)
        have t3 := mul_le_mul hcoeff3 hf_le hf_nn hK2a_nn
        dsimp only [K] at t1 t2 t3
        linarith [t1, t2, t3]
      · have ha3' : 3 ≤ a := le_of_not_gt ha3
        have h1 : fHat (m + 1) (b - 1) ≤ fHat (m + 1) (a - 1) :=
          hf_anti (by simp only [Set.mem_Ici]; linarith) (by simp only [Set.mem_Ici]; linarith) (by linarith)
        have h2 : E_bjs_seq K_seq (m + 1) (b - 1) ≤ E_bjs_seq K_seq (m + 1) (a - 1) :=
          ih' (by simp only [Set.mem_Ici]; linarith) (by simp only [Set.mem_Ici]; linarith) (by linarith)
        obtain ⟨hE_nn, hE_le⟩ := hE_tail a b (by linarith) hab
        obtain ⟨hf_nn, hf_le⟩ := hf_tail a b (by linarith) hab
        have hdivE : K / b ≤ K / a := div_le_div_of_nonneg_left hK0 (by linarith) hab
        have hdivf : (K - 1) / b ≤ (K - 1) / a := div_le_div_of_nonneg_left hK_nn (by linarith) hab
        have t1 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK_nn
        have t2 := mul_le_mul hdivE hE_le hE_nn (by positivity)
        have t3 := mul_le_mul hdivf hf_le hf_nn (by positivity)
        dsimp only [K] at t1 t2 t3
        linarith [t1, t2, t3]

theorem E_bjs_antitone {K : ℝ} (hK : 1 ≤ K) {n : ℕ} (hn : 1 ≤ n) :
    AntitoneOn (E_bjs K n) (Set.Ici 1) :=
  E_bjs_seq_antitone n hn (fun _ _ _ => hK)

/-- Depth-dependent prime lower bound `u_bjs n D z`:
`(D / z)^{3^{-k}}` for `n = 2k` (`k ≥ 1`) and `D^{3^{-(k+1)}}` for `n = 2k + 1` (`k ≥ 0`). -/
def u_bjs (n : ℕ) (D z : ℝ) : ℝ :=
  if n % 2 = 0 then (D / z) ^ ((1 / 3 : ℝ) ^ (n / 2))
  else D ^ ((1 / 3 : ℝ) ^ ((n + 1) / 2))

lemma rpow_one_third_lt_of_lt_cube {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (h : x < y ^ 3) : x ^ (1 / 3 : ℝ) < y := by
  have hpow : x ^ (1 / 3 : ℝ) < (y ^ 3) ^ (1 / 3 : ℝ) :=
    Real.rpow_lt_rpow hx.le h (by norm_num)
  have heq : (y ^ 3) ^ (1 / 3 : ℝ) = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  linarith

private lemma rpow_one_third_le_of_le_cube {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ y ^ 3) : x ^ (1 / 3 : ℝ) ≤ y := by
  have hpow : x ^ (1 / 3 : ℝ) ≤ (y ^ 3) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hx h (by norm_num)
  have heq : (y ^ 3) ^ (1 / 3 : ℝ) = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  linarith

lemma lt_rpow_one_third_of_cube_lt {x y : ℝ} (hy : 0 ≤ y)
    (h : y ^ 3 < x) : y < x ^ (1 / 3 : ℝ) := by
  have hpow : (y ^ 3) ^ (1 / 3 : ℝ) < x ^ (1 / 3 : ℝ) :=
    Real.rpow_lt_rpow (pow_nonneg hy 3) h (by norm_num)
  have heq : (y ^ 3) ^ (1 / 3 : ℝ) = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  linarith

/-- Every `n`-tuple `S` contributing to `T_sum g n D P` (with `p < z` for `p ∈ P`) satisfies
`u_bjs n D z ≤ S.min'`. -/
theorem T_sum_prefix_min_gt {n : ℕ} (hn : 1 ≤ n) {D z : ℝ} (hz : 1 < z)
    (hDz : z ≤ D) {P : Finset ℕ} (hP_pos : ∀ p ∈ P, 1 ≤ p) (hP_ltz : ∀ p ∈ P, (p : ℝ) < z)
    {S : Finset ℕ} (hS : S ∈ (P.powersetCard n).filter (riTermPred D)) (hSne : S.Nonempty) :
    u_bjs n D z ≤ (S.min' hSne : ℝ) := by
  have hmem := Finset.mem_filter.mp hS
  rcases Finset.mem_powersetCard.mp hmem.1 with ⟨hSP, hScard⟩
  have hD_gt1 : 1 < D := lt_of_lt_of_le hz hDz
  have hD_pos : 0 < D := by linarith
  have hz_pos : 0 < z := by linarith
  set L := descPrimes S
  have hlen : L.length = n := by dsimp [L, descPrimes]; rw [Finset.length_sort, hScard]
  have hL_gt : L.SortedGT := S.sortedGT_sort
  have hL_pos : ∀ i (hi : i < n), (0 : ℝ) < (L.getD i 0 : ℝ) := by
    intro i hi
    have hiL : i < L.length := by rw [hlen]; exact hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL]
    have hmemS : L[i] ∈ S := (Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem hiL)
    exact_mod_cast hP_pos L[i] (hSP hmemS)
  have hL_dec : ∀ i (hi : i + 1 < n), (L.getD (i + 1) 0 : ℝ) < (L.getD i 0 : ℝ) := by
    intro i hi
    have hiL : i < L.length := by rw [hlen]; omega
    have hi1L : i + 1 < L.length := by rw [hlen]; exact hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL,
      List.getElem?_eq_getElem hi1L]
    exact Nat.cast_lt.mpr (hL_gt.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self i))
  have hfor := (riTermCond_iff_forall D 1 L (by omega)).mp hmem.2
  have hmin_eq : (S.min' hSne : ℝ) = (L.getD (n - 1) 0 : ℝ) := by
    have hL_ne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlast : S.min' hSne = L.getLast hL_ne := by
      apply le_antisymm
      · exact Finset.min'_le _ _ ((Finset.mem_sort (· ≥ ·)).mp (List.getLast_mem hL_ne))
      · refine Finset.le_min' _ _ _ fun q hq => ?_
        have hqL : q ∈ L := (Finset.mem_sort (· ≥ ·)).mpr hq
        rcases List.mem_iff_getElem.mp hqL with ⟨i, hi, rfl⟩
        rw [List.getLast_eq_getElem hL_ne]
        by_cases hil : i = L.length - 1
        · subst hil; exact le_rfl
        · exact (hL_gt.getElem_lt_getElem_iff.mpr (by omega)).le
    have hiL : n - 1 < L.length := by rw [hlen]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL]
    congr 1
    rw [hlast, List.getLast_eq_getElem hL_ne]
    congr 1; omega
  rw [hmin_eq]
  let Ppref : ℕ → ℝ := fun r => ∏ j ∈ Finset.range r, (L.getD j 0 : ℝ)
  have hPpref_pos : ∀ r ≤ n, 0 < Ppref r := fun r hr => by
    refine Finset.prod_pos fun j hj => ?_
    exact hL_pos j (lt_of_lt_of_le (Finset.mem_range.mp hj) hr)
  have hlast_ineq : D ≤ Ppref (n - 1) * (L.getD (n - 1) 0 : ℝ) ^ 3 := by
    have h2 := hfor.2
    rw [one_mul, hlen] at h2
    have hsplit : ∏ j ∈ Finset.range n, (L.getD j 0 : ℝ) =
        Ppref (n - 1) * (L.getD (n - 1) 0 : ℝ) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, Finset.prod_range_succ]
    rw [hsplit] at h2
    linarith
  by_cases hn_even : n % 2 = 0
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k ∧ 1 ≤ k := ⟨n / 2, by omega, by omega⟩
    have hu_eq : u_bjs n D z = (D / z) ^ ((1 / 3 : ℝ) ^ k) := by
      simp [u_bjs, hk.1]
    rw [hu_eq]
    have hstep_pref : ∀ j, 1 ≤ j → j ≤ k →
        Ppref (2 * j - 1) < D ^ (1 - (1 / 3 : ℝ) ^ (j - 1)) * z ^ ((1 / 3 : ℝ) ^ (j - 1)) := by
      intro j hj1 hjk
      induction j, hj1 using Nat.le_induction with
      | base =>
        have h0 : (L.getD 0 0 : ℝ) < z := by
          have h0L : 0 < L.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0L]
          exact hP_ltz _ (hSP ((Finset.mem_sort (· ≥ ·)).mp (List.getElem_mem h0L)))
        simpa [Ppref] using h0
      | succ j hj1 ih =>
        have ih' := ih (Nat.le_of_succ_le hjk)
        have h2j_lt : 2 * j - 1 < L.length - 1 := by omega
        have h2j_par : (2 * j - 1) % 2 = (L.length - 1) % 2 := by rw [hlen]; omega
        have hcond := hfor.1 (2 * j - 1) h2j_lt h2j_par
        rw [one_mul] at hcond
        have hpref_split : ∏ r ∈ Finset.range (2 * j - 1 + 1), (L.getD r 0 : ℝ) =
            Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) := by
          rw [Finset.prod_range_succ]
        rw [hpref_split] at hcond
        have hcube_cond : Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) ^ 3 < D := by linarith
        have hdec : (L.getD (2 * j) 0 : ℝ) < (L.getD (2 * j - 1) 0 : ℝ) := by
          have := hL_dec (2 * j - 1) (by omega)
          rwa [show 2 * j - 1 + 1 = 2 * j by omega] at this
        have h2j1_eq : 2 * (j + 1) - 1 = (2 * j - 1) + 2 := by omega
        have hP_next : Ppref (2 * (j + 1) - 1) =
            Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) * (L.getD (2 * j) 0 : ℝ) := by
          rw [h2j1_eq, show (2 * j - 1) + 2 = ((2 * j - 1) + 1) + 1 by ring]
          simp only [Ppref, Finset.prod_range_succ]
          rw [show 2 * j - 1 + 1 = 2 * j by omega]
        have hP_lt : Ppref (2 * (j + 1) - 1) ^ 3 <
            Ppref (2 * j - 1) * (Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) ^ 3) ^ 2 := by
          have hmul : Ppref (2 * (j + 1) - 1) <
              Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) ^ 2 := by
            rw [hP_next]
            have h1 : 0 < Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) :=
              mul_pos (hPpref_pos _ (by omega)) (hL_pos _ (by omega))
            nlinarith
          have hpow := pow_lt_pow_left₀ hmul (hPpref_pos _ (by omega)).le (by norm_num : 3 ≠ 0)
          calc Ppref (2 * (j + 1) - 1) ^ 3
              < (Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) ^ 2) ^ 3 := hpow
            _ = Ppref (2 * j - 1) * (Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) ^ 3) ^ 2 := by ring
        have hP_pow : Ppref (2 * (j + 1) - 1) ^ 3 <
            (D ^ (1 - (1 / 3 : ℝ) ^ (j - 1)) * z ^ ((1 / 3 : ℝ) ^ (j - 1))) * D ^ 2 := by
          have hsq : (Ppref (2 * j - 1) * (L.getD (2 * j - 1) 0 : ℝ) ^ 3) ^ 2 < D ^ 2 :=
            pow_lt_pow_left₀ hcube_cond (by positivity) (by norm_num)
          exact hP_lt.trans (mul_lt_mul' ih'.le hsq (by positivity) (by positivity))
        have hrhs_eq : (D ^ (1 - (1 / 3 : ℝ) ^ (j - 1)) * z ^ ((1 / 3 : ℝ) ^ (j - 1))) * D ^ 2 =
            (D ^ (1 - (1 / 3 : ℝ) ^ j) * z ^ ((1 / 3 : ℝ) ^ j)) ^ 3 := by
          rw [mul_pow, ← Real.rpow_natCast D 2,
            ← Real.rpow_natCast (D ^ _), ← Real.rpow_natCast (z ^ _),
            ← Real.rpow_mul hD_pos.le, ← Real.rpow_mul hz_pos.le]
          have heqD : D ^ (1 - (1 / 3 : ℝ) ^ (j - 1)) * D ^ ((2 : ℕ) : ℝ) =
              D ^ ((1 - (1 / 3 : ℝ) ^ j) * ((3 : ℕ) : ℝ)) := by
            rw [← Real.rpow_add hD_pos]
            congr 1
            have hj1' : j = (j - 1) + 1 := (Nat.sub_add_cancel hj1).symm
            conv_rhs => rw [hj1', pow_succ]
            push_cast; ring
          have heqz : z ^ ((1 / 3 : ℝ) ^ (j - 1)) = z ^ (((1 / 3 : ℝ) ^ j) * ((3 : ℕ) : ℝ)) := by
            congr 1
            have hj1' : j = (j - 1) + 1 := (Nat.sub_add_cancel hj1).symm
            conv_rhs => rw [hj1', pow_succ]
            push_cast; ring
          rw [← heqz]
          calc D ^ (1 - (1 / 3 : ℝ) ^ (j - 1)) * z ^ ((1 / 3 : ℝ) ^ (j - 1)) * D ^ ((2 : ℕ) : ℝ)
              = (D ^ (1 - (1 / 3 : ℝ) ^ (j - 1)) * D ^ ((2 : ℕ) : ℝ)) * z ^ ((1 / 3 : ℝ) ^ (j - 1)) := by ring
            _ = D ^ ((1 - (1 / 3 : ℝ) ^ j) * ((3 : ℕ) : ℝ)) * z ^ ((1 / 3 : ℝ) ^ (j - 1)) := by rw [heqD]
        rw [hrhs_eq] at hP_pow
        have hbase_nn : 0 ≤ D ^ (1 - (1 / 3 : ℝ) ^ j) * z ^ ((1 / 3 : ℝ) ^ j) := by positivity
        exact lt_of_pow_lt_pow_left₀ 3 hbase_nn hP_pow
    have hpref_k := hstep_pref k hk.2 le_rfl
    have hn1_eq : n - 1 = 2 * k - 1 := by omega
    rw [← hn1_eq] at hpref_k
    have hcube_gt : (D / z) ^ ((1 / 3 : ℝ) ^ (k - 1)) < (L.getD (n - 1) 0 : ℝ) ^ 3 := by
      have h1 : D / (D ^ (1 - (1 / 3 : ℝ) ^ (k - 1)) * z ^ ((1 / 3 : ℝ) ^ (k - 1))) =
          (D / z) ^ ((1 / 3 : ℝ) ^ (k - 1)) := by
        rw [Real.div_rpow hD_pos.le hz_pos.le]
        have hD_split : D = D ^ (1 - (1 / 3 : ℝ) ^ (k - 1)) * D ^ ((1 / 3 : ℝ) ^ (k - 1)) := by
          rw [← Real.rpow_add hD_pos]
          simp
        conv_lhs => lhs; rw [hD_split]
        have hne : D ^ (1 - (1 / 3 : ℝ) ^ (k - 1)) ≠ 0 := (Real.rpow_pos_of_pos hD_pos _).ne'
        field_simp [hne]
      have h2 : D / (D ^ (1 - (1 / 3 : ℝ) ^ (k - 1)) * z ^ ((1 / 3 : ℝ) ^ (k - 1))) <
          D / Ppref (n - 1) :=
        div_lt_div_of_pos_left hD_pos (hPpref_pos _ (by omega)) hpref_k
      have h3 : D / Ppref (n - 1) ≤ (L.getD (n - 1) 0 : ℝ) ^ 3 :=
        (div_le_iff₀ (hPpref_pos _ (by omega))).mpr (by linarith)
      linarith
    have hrhs_pow := rpow_one_third_lt_of_lt_cube (Real.rpow_pos_of_pos (div_pos hD_pos hz_pos) _)
      (hL_pos (n - 1) (by omega)).le hcube_gt
    have heq_exp : ((D / z) ^ ((1 / 3 : ℝ) ^ (k - 1))) ^ (1 / 3 : ℝ) =
        (D / z) ^ ((1 / 3 : ℝ) ^ k) := by
      rw [← Real.rpow_mul (div_pos hD_pos hz_pos).le]
      congr 1
      have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk.2).symm
      conv_rhs => rw [hk1, pow_succ]
    rw [← heq_exp]
    exact hrhs_pow.le
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have hdiv_eq : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have hu_eq : u_bjs n D z = D ^ ((1 / 3 : ℝ) ^ (k + 1)) := by
      simp [u_bjs, hk, hdiv_eq]
    rw [hu_eq]
    have hstep_pref : ∀ j, j ≤ k →
        Ppref (2 * j) ≤ D ^ (1 - (1 / 3 : ℝ) ^ j) := by
      intro j hjk
      induction j with
      | zero =>
        simp [Ppref]
      | succ j ih =>
        have ih' := ih (Nat.le_of_succ_le hjk)
        have h2j_lt : 2 * j < L.length - 1 := by omega
        have h2j_par : (2 * j) % 2 = (L.length - 1) % 2 := by rw [hlen]; omega
        have hcond := hfor.1 (2 * j) h2j_lt h2j_par
        rw [one_mul] at hcond
        have hpref_split : ∏ r ∈ Finset.range (2 * j + 1), (L.getD r 0 : ℝ) =
            Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) := by
          rw [Finset.prod_range_succ]
        rw [hpref_split] at hcond
        have hcube_cond : Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) ^ 3 < D := by linarith
        have hdec : (L.getD (2 * j + 1) 0 : ℝ) < (L.getD (2 * j) 0 : ℝ) :=
          hL_dec (2 * j) (by omega)
        have hP_next : Ppref (2 * (j + 1)) =
            Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) * (L.getD (2 * j + 1) 0 : ℝ) := by
          rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
          simp only [Ppref, Finset.prod_range_succ]
        have hP_lt : Ppref (2 * (j + 1)) ^ 3 <
            Ppref (2 * j) * (Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) ^ 3) ^ 2 := by
          have hmul : Ppref (2 * (j + 1)) < Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) ^ 2 := by
            rw [hP_next]
            have h1 : 0 < Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) :=
              mul_pos (hPpref_pos _ (by omega)) (hL_pos _ (by omega))
            nlinarith
          have hpow := pow_lt_pow_left₀ hmul (hPpref_pos _ (by omega)).le (by norm_num : 3 ≠ 0)
          calc Ppref (2 * (j + 1)) ^ 3
              < (Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) ^ 2) ^ 3 := hpow
            _ = Ppref (2 * j) * (Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) ^ 3) ^ 2 := by ring
        have hP_pow : Ppref (2 * (j + 1)) ^ 3 < D ^ (1 - (1 / 3 : ℝ) ^ j) * D ^ 2 := by
          have hsq : (Ppref (2 * j) * (L.getD (2 * j) 0 : ℝ) ^ 3) ^ 2 < D ^ 2 :=
            pow_lt_pow_left₀ hcube_cond (by positivity) (by norm_num)
          exact hP_lt.trans (mul_lt_mul' ih' hsq (by positivity) (by positivity))
        have hrhs_eq : D ^ (1 - (1 / 3 : ℝ) ^ j) * D ^ 2 =
            (D ^ (1 - (1 / 3 : ℝ) ^ (j + 1))) ^ 3 := by
          rw [← Real.rpow_natCast D 2, ← Real.rpow_natCast (D ^ _), ← Real.rpow_add hD_pos,
            ← Real.rpow_mul hD_pos.le]
          congr 1
          rw [pow_succ]
          push_cast; ring
        rw [hrhs_eq] at hP_pow
        exact (lt_of_pow_lt_pow_left₀ 3 (Real.rpow_nonneg hD_pos.le _) hP_pow).le
    have hpref_k := hstep_pref k le_rfl
    have hn1_eq : n - 1 = 2 * k := by omega
    rw [← hn1_eq] at hpref_k
    have hcube_ge : D ^ ((1 / 3 : ℝ) ^ k) ≤ (L.getD (n - 1) 0 : ℝ) ^ 3 := by
      have h1 : D / D ^ (1 - (1 / 3 : ℝ) ^ k) = D ^ ((1 / 3 : ℝ) ^ k) := by
        have hD_split : D = D ^ (1 - (1 / 3 : ℝ) ^ k) * D ^ ((1 / 3 : ℝ) ^ k) := by
          rw [← Real.rpow_add hD_pos]; simp
        conv_lhs => lhs; rw [hD_split]
        have hne : D ^ (1 - (1 / 3 : ℝ) ^ k) ≠ 0 := (Real.rpow_pos_of_pos hD_pos _).ne'
        field_simp [hne]
      have h2 : D / D ^ (1 - (1 / 3 : ℝ) ^ k) ≤ D / Ppref (n - 1) :=
        div_le_div_of_nonneg_left hD_pos.le (hPpref_pos _ (by omega)) hpref_k
      have h3 : D / Ppref (n - 1) ≤ (L.getD (n - 1) 0 : ℝ) ^ 3 :=
        (div_le_iff₀ (hPpref_pos _ (by omega))).mpr (by linarith)
      linarith
    have hrhs_pow := rpow_one_third_le_of_le_cube (Real.rpow_pos_of_pos hD_pos _).le
      (hL_pos (n - 1) (by omega)).le hcube_ge
    have heq_exp : (D ^ ((1 / 3 : ℝ) ^ k)) ^ (1 / 3 : ℝ) = D ^ ((1 / 3 : ℝ) ^ (k + 1)) := by
      rw [← Real.rpow_mul hD_pos.le, pow_succ]
    rwa [← heq_exp]

end

end BuchstabSwitching
