import BuchstabSwitching.Sieve.Regime2SlabBridge.Decomposition
import BuchstabSwitching.Sieve.BonferroniEstimates
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge
import Mathlib.Tactic

namespace BuchstabSwitching

noncomputable section

/-! ### 2. Prime-Omission Monotonicity, Analytic Bonferroni Tails, and `bonfDivisors` Bounds -/

section BonferroniHelpers

/-- Prime-omission ratio monotonicity (Note §2 Lemma 2): for even `N` and `z_sub ≤ z`,
`External.VN N z_sub / External.VN 2 z_sub ≤ External.VN N z / External.VN 2 z`. -/
theorem V2_ratio_shifted_le {N : ℕ} (hN : Even N) {z_sub z : ℕ} (hsub : z_sub ≤ z) :
    External.VN N z_sub / External.VN 2 z_sub ≤ External.VN N z / External.VN 2 z := by
  let T : Finset ℕ := fullOddPrimesBelow z
  let T' : Finset ℕ := fullOddPrimesBelow z_sub
  let A : Finset ℕ := T.filter (fun p => ¬ p ∣ N)
  have hAT : A ⊆ T := Finset.filter_subset _ _
  have hT'T : T' ⊆ T := by
    intro p hp
    rw [fullOddPrimesBelow_mem_iff] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hsub, hp.2⟩
  have hw : ∀ p ∈ T, 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
    gTot_prime_bounds (fullOddPrimesBelow_mem_iff.mp hp).2.1
      (fullOddPrimesBelow_mem_iff.mp hp).2.2
  have hratio := V2_ratio_mono hAT hT'T hw
  have hTA : T ∩ A = shiftedPrimesBelow N z := by
    rw [Finset.inter_eq_right.mpr hAT]
    exact (shiftedPrimesBelow_eq_filter_full hN).symm
  have hT'A : T' ∩ A = shiftedPrimesBelow N z_sub := by
    ext p
    simp only [T', A, T, Finset.mem_inter, Finset.mem_filter, fullOddPrimesBelow_mem_iff]
    rw [shiftedPrimesBelow_eq_filter_full hN]
    simp only [Finset.mem_filter, fullOddPrimesBelow_mem_iff]
    constructor
    · rintro ⟨⟨hpz', hp_pr, hp2⟩, ⟨_, hpN⟩⟩
      exact ⟨⟨hpz', hp_pr, hp2⟩, hpN⟩
    · rintro ⟨⟨hpz', hp_pr, hp2⟩, hpN⟩
      exact ⟨⟨hpz', hp_pr, hp2⟩, ⟨⟨lt_of_lt_of_le hpz' hsub, hp_pr, hp2⟩, hpN⟩⟩
  rw [hTA, hT'A] at hratio
  simpa [T, T', V2_gTot_shiftedPrimesBelow_eq_VN, V2_gTot_fullOddPrimesBelow_eq_VN_two] using hratio

/-- Product-scaling corollary of `V2_ratio_shifted_le`:
`External.VN N z_sub * R ≤ (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * R)`
for any `R ≥ 0`. -/
theorem VN_sub_mul_le_ratio {N : ℕ} (hN : Even N) {z_sub z : ℕ} (hsub : z_sub ≤ z)
    {R : ℝ} (hR : 0 ≤ R) :
    External.VN N z_sub * R ≤ (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * R) := by
  have hV2_pos : 0 < External.VN 2 z_sub := External.VN_pos_of_even z_sub (by decide)
  have hratio := V2_ratio_shifted_le hN hsub
  have hVN_le : External.VN N z_sub ≤ (External.VN N z / External.VN 2 z) * External.VN 2 z_sub := by
    calc External.VN N z_sub
        = (External.VN N z_sub / External.VN 2 z_sub) * External.VN 2 z_sub := by
            field_simp [hV2_pos.ne']
      _ ≤ (External.VN N z / External.VN 2 z) * External.VN 2 z_sub :=
            mul_le_mul_of_nonneg_right hratio hV2_pos.le
  calc External.VN N z_sub * R
      ≤ ((External.VN N z / External.VN 2 z) * External.VN 2 z_sub) * R :=
          mul_le_mul_of_nonneg_right hVN_le hR
    _ = (External.VN N z / External.VN 2 z) * (External.VN 2 z_sub * R) := by ring

lemma bonfDivisors_subset_of_subset {Q₁' Q₁ P₂' P₂ : Finset ℕ}
    (hQ : Q₁' ⊆ Q₁) (hP : P₂' ⊆ P₂) (k : ℕ) :
    bonfDivisors Q₁' P₂' k ⊆ bonfDivisors Q₁ P₂ k := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
  rcases Finset.mem_filter.mp hS₂ with ⟨hS₂p, hS₂c⟩
  refine Finset.mem_image.mpr ⟨(S₁, S₂), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS₁).trans hQ)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS₂p).trans hP), hS₂c⟩

lemma bonfDivisors_pos_and_coprime {Q₁ P₂ : Finset ℕ} {k N d : ℕ}
    (hQ₁ : ∀ p ∈ Q₁, p.Prime ∧ ¬ p ∣ N) (hP₂ : ∀ p ∈ P₂, p.Prime ∧ ¬ p ∣ N)
    (hd : d ∈ bonfDivisors Q₁ P₂ k) :
    1 ≤ d ∧ Nat.Coprime d N := by
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
  have hS₁_sub := Finset.mem_powerset.mp hS₁
  have hS₂_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
  have h1 : 1 ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := by
    refine Nat.mul_pos ?_ ?_
    · exact Finset.prod_pos fun p hp => (hQ₁ p (hS₁_sub hp)).1.pos
    · exact Finset.prod_pos fun p hp => (hP₂ p (hS₂_sub hp)).1.pos
  have hcop1 : Nat.Coprime (∏ p ∈ S₁, p) N := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    exact (hQ₁ p (hS₁_sub hp)).1.coprime_iff_not_dvd.mpr (hQ₁ p (hS₁_sub hp)).2
  have hcop2 : Nat.Coprime (∏ p ∈ S₂, p) N := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    exact (hP₂ p (hS₂_sub hp)).1.coprime_iff_not_dvd.mpr (hP₂ p (hS₂_sub hp)).2
  exact ⟨h1, hcop1.mul_left hcop2⟩

lemma bonfDivisors_odd_of_gt_two {Q₁ P₂ : Finset ℕ} {k d : ℕ}
    (hQ₁ : ∀ p ∈ Q₁, p.Prime ∧ 2 < p) (hP₂ : ∀ p ∈ P₂, p.Prime ∧ 2 < p)
    (hd : d ∈ bonfDivisors Q₁ P₂ k) :
    Odd d := by
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
  have hS₁_sub := Finset.mem_powerset.mp hS₁
  have hS₂_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
  refine Odd.mul ?_ ?_
  · exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp =>
      (hQ₁ p (hS₁_sub hp)).1.odd_of_ne_two (by have := (hQ₁ p (hS₁_sub hp)).2; omega)
  · exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun p hp =>
      (hP₂ p (hS₂_sub hp)).1.odd_of_ne_two (by have := (hP₂ p (hS₂_sub hp)).2; omega)

lemma bonfDivisors_le_prod_mul_pow_of_pos {Q₁ P₂ : Finset ℕ} {k z_sub d : ℕ}
    (hz : 1 ≤ z_sub) (hQ₁ : ∀ p ∈ Q₁, 1 ≤ p) (hP₂ : ∀ p ∈ P₂, p ≤ z_sub)
    (hd : d ∈ bonfDivisors Q₁ P₂ k) :
    d ≤ (∏ p ∈ Q₁, p) * z_sub ^ k := by
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
  have hS₁_sub := Finset.mem_powerset.mp hS₁
  have hS₂_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
  have hS₂_card := (Finset.mem_filter.mp hS₂).2
  have h1 : ∏ p ∈ S₁, p ≤ ∏ p ∈ Q₁, p :=
    Finset.prod_le_prod_of_subset_of_one_le hS₁_sub fun p hp _ => hQ₁ p hp
  have h2 : ∏ p ∈ S₂, p ≤ z_sub ^ k := by
    calc ∏ p ∈ S₂, p
        ≤ ∏ _p ∈ S₂, z_sub := Finset.prod_le_prod (fun p hp => hP₂ p (hS₂_sub hp))
      _ = z_sub ^ S₂.card := by simp
      _ ≤ z_sub ^ k := Nat.pow_le_pow_right hz hS₂_card
  exact Nat.mul_le_mul h1 h2

private lemma sublist_prod_le_take_prod :
    ∀ {L Ls : List ℕ} (k : ℕ), Ls.Sublist L → L.Pairwise (· ≥ ·) → Ls.length ≤ k →
      (∀ x ∈ L, 1 ≤ x) → Ls.prod ≤ (L.take k).prod := by
  intro L Ls k hsub
  induction hsub generalizing k with
  | slnil =>
    intro _ _ hpos
    simp only [List.prod_nil]
    exact List.one_le_prod_of_one_le fun x hx => hpos x (List.mem_of_mem_take hx)
  | @cons L₁ L₂ a _ ih =>
    intro hpair hlen hpos
    have hpair' : L₂.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hpair).2
    have hpos' : ∀ x ∈ L₂, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
    have ha_ge : ∀ x ∈ L₂, x ≤ a := (List.pairwise_cons.mp hpair).1
    have ha1 : 1 ≤ a := hpos a List.mem_cons_self
    cases k with
    | zero =>
      have hLs0 : L₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hLs0
      simp
    | succ k' =>
      have ih_le : L₁.prod ≤ (L₂.take (k' + 1)).prod := ih (k' + 1) hpair' hlen hpos'
      have htake_le : (L₂.take (k' + 1)).prod ≤ ((a :: L₂).take (k' + 1)).prod := by
        rw [List.take_succ_cons]
        simp only [List.prod_cons]
        by_cases hk : k' < L₂.length
        · have hsplit : L₂.take (k' + 1) = L₂.take k' ++ [L₂[k']] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
          have hlk_le_a : L₂[k'] ≤ a := ha_ge L₂[k'] (List.getElem_mem hk)
          rw [hsplit, List.prod_append, List.prod_singleton, mul_comm]
          exact Nat.mul_le_mul_right _ hlk_le_a
        · have hge : L₂.length ≤ k' := Nat.le_of_not_lt hk
          rw [List.take_of_length_le hge, List.take_of_length_le (by omega)]
          exact Nat.le_mul_of_pos_left L₂.prod ha1
      exact ih_le.trans htake_le
  | @cons_cons L₁ L₂ a _ ih =>
    intro hpair hlen hpos
    have hpair' : L₂.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hpair).2
    have hpos' : ∀ x ∈ L₂, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
    cases k with
    | zero =>
      simp only [List.length_cons] at hlen
      omega
    | succ k' =>
      simp only [List.length_cons] at hlen
      rw [List.take_succ_cons, List.prod_cons, List.prod_cons]
      exact Nat.mul_le_mul_left a (ih k' hpair' (by omega) hpos')

/-- Product of `S₂ ⊆ P₂` with `S₂.card ≤ k` is at most the product of the `k` largest elements of `P₂`. -/
lemma prod_subset_card_le_top_k {P₂ S₂ : Finset ℕ} {k : ℕ}
    (hS₂ : S₂ ⊆ P₂) (hcard : S₂.card ≤ k) (hP₂ : ∀ p ∈ P₂, 1 ≤ p) :
    ∏ p ∈ S₂, p ≤ ∏ p ∈ ((P₂.sort (· ≥ ·)).take k).toFinset, p := by
  set L := P₂.sort (· ≥ ·)
  set Ls := S₂.sort (· ≥ ·)
  have hLs_toFinset : Ls.toFinset = S₂ := by
    ext x
    simp [Ls]
  have hLs_nodup : Ls.Nodup := S₂.sort_nodup (· ≥ ·)
  have hprod_S : ∏ p ∈ S₂, p = Ls.prod := by
    rw [← hLs_toFinset]
    simpa using List.prod_toFinset id hLs_nodup
  have hsub_list : Ls.Sublist L := by
    have hfilt : L.filter (fun x => decide (x ∈ S₂)) = Ls := by
      have hnodup : (L.filter (fun x => decide (x ∈ S₂))).Nodup :=
        (P₂.sort_nodup (· ≥ ·)).filter _
      have hsort : (L.filter (fun x => decide (x ∈ S₂))).Pairwise (· ≥ ·) :=
        (P₂.pairwise_sort (· ≥ ·)).filter _
      have htoFin : (L.filter (fun x => decide (x ∈ S₂))).toFinset = S₂ := by
        ext x
        simp only [L, List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨hS₂ h, h⟩⟩
      have hres := (List.toFinset_sort (· ≥ ·) hnodup).mpr hsort
      rw [htoFin] at hres
      exact hres.symm
    rw [← hfilt]
    exact List.filter_sublist
  have hLs_len : Ls.length ≤ k := by
    simpa [Ls, Finset.length_sort] using hcard
  have htake_nodup : (L.take k).Nodup := (P₂.sort_nodup (· ≥ ·)).take
  have hprod_take : ∏ p ∈ (L.take k).toFinset, p = (L.take k).prod := by
    simpa using List.prod_toFinset id htake_nodup
  have hL_pos : ∀ x ∈ L, 1 ≤ x := fun x hx => hP₂ x ((P₂.mem_sort (· ≥ ·)).mp hx)
  rw [hprod_S, hprod_take]
  exact sublist_prod_le_take_prod k hsub_list (P₂.pairwise_sort (· ≥ ·)) hLs_len hL_pos

lemma bonfDivisors_le_prod_mul_top_k {Q₁ P₂ : Finset ℕ} {k d : ℕ}
    (hQ₁ : ∀ p ∈ Q₁, 1 ≤ p) (hP₂ : ∀ p ∈ P₂, 1 ≤ p)
    (hd : d ∈ bonfDivisors Q₁ P₂ k) :
    d ≤ (∏ p ∈ Q₁, p) * ∏ p ∈ ((P₂.sort (· ≥ ·)).take k).toFinset, p := by
  rcases Finset.mem_image.mp hd with ⟨⟨S₁, S₂⟩, hS, rfl⟩
  rcases Finset.mem_product.mp hS with ⟨hS₁, hS₂⟩
  have hS₁_sub := Finset.mem_powerset.mp hS₁
  have hS₂_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₂).1
  have hS₂_card := (Finset.mem_filter.mp hS₂).2
  have h1 : ∏ p ∈ S₁, p ≤ ∏ p ∈ Q₁, p :=
    Finset.prod_le_prod_of_subset_of_one_le hS₁_sub fun p hp _ => hQ₁ p hp
  have h2 := prod_subset_card_le_top_k hS₂_sub hS₂_card hP₂
  exact Nat.mul_le_mul h1 h2

/-- Analytic `V2` lower bound with safe `c_log2` for all `3 ≤ p_min` (fixing Finding §0.5:
when `a = 0` (`p_a = 2`), `p_min = 3` gives `c_log2 = 1 / (2 * (1 - 1 / 2)) = 1`). -/
theorem analytic_bonf_V2_lb {P₂ : Finset ℕ} {p_min : ℕ} (hp_min : 3 ≤ p_min)
    (hP₂ : ∀ p ∈ P₂, p.Prime ∧ p_min ≤ p) {S₁ S₂ : ℝ}
    (hS₁ : ∑ p ∈ P₂, gTot p ≤ S₁) (hS₂ : ∑ p ∈ P₂, (gTot p) ^ 2 ≤ S₂) :
    let c_log2 : ℝ := 1 / (2 * (1 - 1 / ((p_min : ℝ) - 1)))
    Real.exp (-(S₁ + c_log2 * S₂)) ≤ V2 gTot P₂ := by
  dsimp only
  have hp_min_real : (3 : ℝ) ≤ (p_min : ℝ) := by exact_mod_cast hp_min
  set w_max : ℝ := 1 / ((p_min : ℝ) - 1)
  have hwmax_lt : w_max < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hw_bd : ∀ p ∈ P₂, 0 ≤ gTot p ∧ gTot p ≤ w_max := by
    intro p hp
    have hpp := hP₂ p hp
    rw [gTot_prime hpp.1]
    have hp_real : (p_min : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.2
    refine ⟨div_nonneg zero_le_one (by linarith), ?_⟩
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hV2 := V2_ge_exp_neg_sum hwmax_lt hw_bd
  have hc_nn : 0 ≤ 1 / (2 * (1 - w_max)) := by
    have : 0 < 1 - w_max := sub_pos.mpr hwmax_lt
    positivity
  have harg : ∑ p ∈ P₂, gTot p + 1 / (2 * (1 - w_max)) * ∑ p ∈ P₂, (gTot p) ^ 2 ≤
      S₁ + 1 / (2 * (1 - w_max)) * S₂ := by
    have hmul := mul_le_mul_of_nonneg_left hS₂ hc_nn
    linarith
  exact (Real.exp_le_exp.mpr (by linarith)).trans hV2

theorem analytic_bonf_RTrunc_odd_lb {P₂ : Finset ℕ}
    (hP₂ : ∀ p ∈ P₂, p.Prime ∧ 2 < p) (m : ℕ) {S₁ g_lb : ℝ}
    (hg_pos : 0 < g_lb) (hg_le : g_lb ≤ V2 gTot P₂) (hS₁ : ∑ p ∈ P₂, gTot p ≤ S₁) :
    1 - S₁ ^ (2 * m + 2) / ((Nat.factorial (2 * m + 2) : ℝ) * g_lb) ≤
      RTrunc gTot P₂ (2 * m + 1) := by
  have hw : ∀ p ∈ P₂, 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
    gTot_prime_bounds (hP₂ p hp).1 (hP₂ p hp).2
  have h1 := RTrunc_odd_analytic_lb (w := gTot) (T := P₂) (m := 2 * m + 1) ⟨m, rfl⟩ hw
  have hS_nn : 0 ≤ ∑ p ∈ P₂, gTot p := Finset.sum_nonneg fun p hp => (hw p hp).1
  have hpow : (∑ p ∈ P₂, gTot p) ^ (2 * m + 2) ≤ S₁ ^ (2 * m + 2) :=
    pow_le_pow_left₀ hS_nn hS₁ _
  have hfact_pos : (0 : ℝ) < (Nat.factorial (2 * m + 2) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hden : (Nat.factorial (2 * m + 2) : ℝ) * g_lb ≤
      (Nat.factorial (2 * m + 2) : ℝ) * V2 gTot P₂ :=
    mul_le_mul_of_nonneg_left hg_le hfact_pos.le
  have hfrac : (∑ p ∈ P₂, gTot p) ^ (2 * m + 2) /
      ((Nat.factorial (2 * m + 2) : ℝ) * V2 gTot P₂) ≤
      S₁ ^ (2 * m + 2) / ((Nat.factorial (2 * m + 2) : ℝ) * g_lb) :=
    div_le_div₀ (pow_nonneg (hS_nn.trans hS₁) _) hpow (mul_pos hfact_pos hg_pos) hden
  have hidx : 2 * m + 1 + 1 = 2 * m + 2 := by ring
  rw [hidx] at h1
  linarith

theorem analytic_bonf_RTrunc_even_ub {P₂ : Finset ℕ}
    (hP₂ : ∀ p ∈ P₂, p.Prime ∧ 2 < p) (m : ℕ) {S₁ g_lb : ℝ}
    (hg_pos : 0 < g_lb) (hg_le : g_lb ≤ V2 gTot P₂) (hS₁ : ∑ p ∈ P₂, gTot p ≤ S₁) :
    RTrunc gTot P₂ (2 * m) ≤
      1 + S₁ ^ (2 * m + 1) / ((Nat.factorial (2 * m + 1) : ℝ) * g_lb) := by
  have hw : ∀ p ∈ P₂, 0 ≤ gTot p ∧ gTot p < 1 := fun p hp =>
    gTot_prime_bounds (hP₂ p hp).1 (hP₂ p hp).2
  have h1 := RTrunc_even_analytic_ub (w := gTot) (T := P₂) (m := 2 * m) (even_two_mul m) hw
  have hS_nn : 0 ≤ ∑ p ∈ P₂, gTot p := Finset.sum_nonneg fun p hp => (hw p hp).1
  have hpow : (∑ p ∈ P₂, gTot p) ^ (2 * m + 1) ≤ S₁ ^ (2 * m + 1) :=
    pow_le_pow_left₀ hS_nn hS₁ _
  have hfact_pos : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hden : (Nat.factorial (2 * m + 1) : ℝ) * g_lb ≤
      (Nat.factorial (2 * m + 1) : ℝ) * V2 gTot P₂ :=
    mul_le_mul_of_nonneg_left hg_le hfact_pos.le
  have hfrac : (∑ p ∈ P₂, gTot p) ^ (2 * m + 1) /
      ((Nat.factorial (2 * m + 1) : ℝ) * V2 gTot P₂) ≤
      S₁ ^ (2 * m + 1) / ((Nat.factorial (2 * m + 1) : ℝ) * g_lb) :=
    div_le_div₀ (pow_nonneg (hS_nn.trans hS₁) _) hpow (mul_pos hfact_pos hg_pos) hden
  linarith

lemma card_bonfDivisors_le_factorial_sum {Q₁ P₂ : Finset ℕ}
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime) (hP₂ : ∀ p ∈ P₂, p.Prime)
    (k : ℕ) {pi_ub : ℝ} (hpi : (P₂.card : ℝ) ≤ pi_ub) :
    ((bonfDivisors Q₁ P₂ k).card : ℝ) ≤
      (2 : ℝ) ^ Q₁.card * ∑ j ∈ Finset.range (k + 1), pi_ub ^ j / (Nat.factorial j : ℝ) := by
  have hcard := card_bonfDivisors hdisj hQ₁ hP₂ (k := k)
  have hcast : ((bonfDivisors Q₁ P₂ k).card : ℝ) =
      (2 : ℝ) ^ Q₁.card * ∑ j ∈ Finset.range (k + 1), (P₂.card.choose j : ℝ) := by
    exact_mod_cast hcard
  rw [hcast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (sum_choose_le_pow_div_factorial P₂.card k).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  have hpow : (P₂.card : ℝ) ^ j ≤ pi_ub ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hpi j
  exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)

lemma sum_bonfDivisors_gTot_le_exp {Q₁ P₂ : Finset ℕ}
    (hdisj : Disjoint Q₁ P₂) (hQ₁ : ∀ p ∈ Q₁, p.Prime ∧ 2 < p) (hP₂ : ∀ p ∈ P₂, p.Prime ∧ 2 < p)
    (k : ℕ) {S₁ : ℝ} (hS₁ : ∑ p ∈ P₂, gTot p ≤ S₁) :
    ∑ d ∈ bonfDivisors Q₁ P₂ k, gTot d ≤
      (∏ p ∈ Q₁, (p : ℝ) / ((p : ℝ) - 1)) * Real.exp S₁ := by
  rw [sum_bonfDivisors_density Q₁ P₂ gTot k hdisj (fun p hp => (hQ₁ p hp).1)
    (fun p hp => (hP₂ p hp).1) (fun S₁ hS₁ Q₂ hQ₂ =>
      gTot_prod_disjoint_primes (hdisj.mono hS₁ hQ₂)
        (fun p hp => (hQ₁ p (hS₁ hp)).1) (fun p hp => (hP₂ p (hQ₂ hp)).1))]
  have hQ_eq : ∏ p ∈ Q₁, (1 + gTot p) = ∏ p ∈ Q₁, (p : ℝ) / ((p : ℝ) - 1) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [gTot_prime (hQ₁ p hp).1]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hQ₁ p hp).2
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hQ_nn : 0 ≤ ∏ p ∈ Q₁, (p : ℝ) / ((p : ℝ) - 1) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hQ₁ p hp).2
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hP_le := (sum_elemSym_le_exp (w := gTot) (T := P₂)
    (fun p hp => gTot_nonneg p) k).trans (Real.exp_le_exp.mpr hS₁)
  rw [hQ_eq]
  exact mul_le_mul_of_nonneg_left hP_le hQ_nn

end BonferroniHelpers

end

end BuchstabSwitching
