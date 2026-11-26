import BuchstabSwitching.Sieve.OddSquarefreeBounds.OddHarmonic
import BuchstabSwitching.Sieve.OddSquarefreeBounds.InvTotient
import Mathlib.Tactic

/-!
# Explicit Constant Bounds for `alpha0` and `H_tilde`

Provides rigorous unconditional upper bounds (zero `sorry`/axioms/`native_decide`) on:
- `alpha0 = (γ + log 2) / 2 ≤ 636 / 1000` (and `≤ 64 / 100`), via
  `harmonic_sub_log_sub_eulerMascheroni_bounds 16` and `Real.log_two_gt_d9`;
- `H_tilde = ∑' b, kappa b ≤ 13 / 10`, via finite Euler product truncation at `2 * J = 160` and
  odd-integer telescoping tail bound `∑_{j ≥ J} 1/((2j+1)(2j)) ≤ 1/(2(2J-1))` with
  `exp(x) ≤ (1 - x)⁻¹`.
-/

namespace BuchstabSwitching

section ConstantBounds

/-- Tight upper bound `alpha0 ≤ 636 / 1000` from `harmonic 16` and `Real.log_two_gt_d9`. -/
theorem alpha0_le_636_div_1000 : alpha0 ≤ (636 / 1000 : ℝ) := by
  have h16 := (harmonic_sub_log_sub_eulerMascheroni_bounds 16 (by norm_num)).1
  have hh16 : (harmonic 16 : ℝ) = (2436559 / 720720 : ℝ) := by
    norm_num [harmonic]
  have hlog16 : Real.log (16 : ℕ) = 4 * Real.log 2 := by
    have : ((16 : ℕ) : ℝ) = (2 : ℝ) ^ 4 := by norm_num
    rw [this, Real.log_pow]
    ring
  have hgam : Real.eulerMascheroniConstant <
      (2436559 / 720720 : ℝ) - 4 * Real.log 2 - 1 / 34 := by
    rw [hh16, hlog16] at h16
    push_cast at h16
    linarith
  have hlog2_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  unfold alpha0
  linarith

/-- Certified upper bound `alpha0 ≤ 64 / 100`. -/
theorem alpha0_le_64_div_100 : alpha0 ≤ (64 / 100 : ℝ) :=
  alpha0_le_636_div_1000.trans (by norm_num)

private lemma sum_range_kappa_le_partial (N : ℕ) :
    ∑ b ∈ Finset.range N, kappa b ≤ H_tilde_partial N := by
  set P : Finset ℕ := (Finset.range N).filter (fun p => p.Prime ∧ 2 < p)
  have hsub : (Finset.range N).filter (fun b => Odd b ∧ Squarefree b) ⊆
      P.powerset.image (fun T => ∏ p ∈ T, p) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_powerset] at hb ⊢
    rcases hb with ⟨hbN, hb_odd, hb_sqf⟩
    refine ⟨b.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hb_sqf⟩
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    have hp_ne2 : p ≠ 2 := by
      intro h2; subst h2
      exact Nat.not_even_iff_odd.mpr hb_odd (even_iff_two_dvd.mpr hp_dvd)
    have hp_le := Nat.le_of_dvd hb_sqf.ne_zero.bot_lt hp_dvd
    have hp_ge2 := hp_prime.two_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, by omega⟩
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (P.powerset : Set (Finset ℕ)) := by
    intro T₁ hT₁ T₂ hT₂ heq
    dsimp only at heq
    simp only [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
    have h1 := primeFactors_prod_of_prime fun p hp => (Finset.mem_filter.mp (hT₁ hp)).2.1
    have h2 := primeFactors_prod_of_prime fun p hp => (Finset.mem_filter.mp (hT₂ hp)).2.1
    rw [← h1, ← h2, heq]
  have hsum_eq : ∑ b ∈ Finset.range N, kappa b =
      ∑ b ∈ (Finset.range N).filter (fun b => Odd b ∧ Squarefree b), kappa b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold kappa
    split_ifs <;> rfl
  calc ∑ b ∈ Finset.range N, kappa b
      = ∑ b ∈ (Finset.range N).filter (fun b => Odd b ∧ Squarefree b), kappa b := hsum_eq
    _ ≤ ∑ b ∈ P.powerset.image (fun T => ∏ p ∈ T, p), kappa b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => kappa_nonneg _)
    _ = ∑ T ∈ P.powerset, kappa (∏ p ∈ T, p) := Finset.sum_image hinj
    _ = ∑ T ∈ P.powerset, ∏ p ∈ T, (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        refine Finset.sum_congr rfl fun T hT => kappa_prod_of_primes fun p hp =>
          (Finset.mem_filter.mp (Finset.mem_powerset.mp hT hp)).2
    _ = H_tilde_partial N := by
        unfold H_tilde_partial
        exact (Finset.prod_one_add P).symm

/-- Tail-product bound `H_tilde ≤ H_tilde_partial (2 * J) * exp (1 / (2 * (2 * J - 1)))`
for all `J ≥ 2`. -/
theorem H_tilde_le_partial_two_mul_exp {J : ℕ} (hJ : 2 ≤ J) :
    H_tilde ≤ H_tilde_partial (2 * J) * Real.exp (1 / (2 * (2 * (J : ℝ) - 1))) := by
  have htend : Filter.Tendsto (fun N : ℕ => ∑ b ∈ Finset.range N, kappa b)
      Filter.atTop (nhds H_tilde) :=
    summable_kappa.hasSum.tendsto_sum_nat
  refine le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨2 * J, fun N hMN => ?_⟩)
  refine (sum_range_kappa_le_partial N).trans ?_
  set P_M : Finset ℕ := (Finset.range (2 * J)).filter (fun p => p.Prime ∧ 2 < p)
  set P_tail : Finset ℕ := (Finset.Ico (2 * J) N).filter (fun p => p.Prime ∧ 2 < p)
  have hdisj : Disjoint P_M P_tail := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
    have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hp2).1
    omega
  have hunion : (Finset.range N).filter (fun p => p.Prime ∧ 2 < p) = P_M ∪ P_tail := by
    ext p
    simp only [P_M, P_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hpN, hpr, hp2⟩
      by_cases hpM : p < 2 * J
      · exact Or.inl ⟨hpM, hpr, hp2⟩
      · exact Or.inr ⟨⟨Nat.le_of_not_lt hpM, hpN⟩, hpr, hp2⟩
    · rintro (⟨hpM, hpr, hp2⟩ | ⟨⟨_, hpN⟩, hpr, hp2⟩)
      · exact ⟨lt_of_lt_of_le hpM hMN, hpr, hp2⟩
      · exact ⟨hpN, hpr, hp2⟩
  have hsplit : H_tilde_partial N =
      H_tilde_partial (2 * J) * ∏ p ∈ P_tail, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    unfold H_tilde_partial
    rw [hunion, Finset.prod_union hdisj]
  rw [hsplit]
  have hHM_nn : 0 ≤ H_tilde_partial (2 * J) := by
    unfold H_tilde_partial
    refine Finset.prod_nonneg fun p hp => ?_
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hHM_nn
  have hprod_le : ∏ p ∈ P_tail, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      ∏ p ∈ P_tail, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p _ => ?_)
    · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · rw [add_comm]; exact Real.add_one_le_exp _
  rw [← Real.exp_sum] at hprod_le
  refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
  have hsub_img : P_tail ⊆ (Finset.Ico J N).image (fun j => 2 * j + 1) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIco, hpr, hp2⟩
    rw [Finset.mem_Ico] at hpIco
    have hp_odd : Odd p := hpr.odd_of_ne_two (by omega)
    rcases hp_odd with ⟨j, rfl⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  have hsum_img : ∑ p ∈ P_tail, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ j ∈ Finset.Ico J N,
        (1 / 2 : ℝ) * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) := by
    calc ∑ p ∈ P_tail, 1 / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ p ∈ ((Finset.Ico J N).image (fun j => 2 * j + 1) : Finset ℕ),
            1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun p hp _ => ?_
          rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
          have hjJ : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJ.trans (Finset.mem_Ico.mp hj).1
          have : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
          positivity
      _ = ∑ j ∈ Finset.Ico J N,
            1 / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) - 1)) := by
          rw [Finset.sum_image (f := fun p : ℕ => 1 / ((p : ℝ) * ((p : ℝ) - 1)))
            (fun a _ b _ h => by omega)]
      _ ≤ ∑ j ∈ Finset.Ico J N,
            (1 / 2 : ℝ) * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjJ : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hJ.trans (Finset.mem_Ico.mp hj).1
          have h1 : (0 : ℝ) < 2 * (j : ℝ) - 1 := by linarith
          have h2 : (0 : ℝ) < 2 * (j : ℝ) := by linarith
          have h3 : (0 : ℝ) < 2 * (j : ℝ) + 1 := by linarith
          have hcast : ((2 * j + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          have hid : (1 / 2 : ℝ) * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) =
              1 / ((2 * (j : ℝ) + 1) * (2 * (j : ℝ) - 1)) := by
            field_simp; ring
          rw [hid]
          refine one_div_le_one_div_of_le (mul_pos h3 h1) ?_
          exact mul_le_mul_of_nonneg_left (by linarith) h3.le
  have hJN : J ≤ N := by omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJN
  have htel : ∀ k : ℕ, ∑ j ∈ Finset.Ico J (J + k),
      (1 / 2 : ℝ) * (1 / (2 * (j : ℝ) - 1) - 1 / (2 * (j : ℝ) + 1)) =
      (1 / 2 : ℝ) * (1 / (2 * (J : ℝ) - 1) - 1 / (2 * ((J + k : ℕ) : ℝ) - 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show J + (k + 1) = (J + k) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
      push_cast
      ring
  refine hsum_img.trans ?_
  rw [htel d]
  have hJd : (2 : ℝ) ≤ ((J + d : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ J + d)
  have hpos : (0 : ℝ) < 2 * ((J + d : ℕ) : ℝ) - 1 := by linarith
  have hle : 1 / (2 * (J : ℝ) - 1) - 1 / (2 * ((J + d : ℕ) : ℝ) - 1) ≤ 1 / (2 * (J : ℝ) - 1) :=
    sub_le_self _ (div_nonneg zero_le_one hpos.le)
  have hmul := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have heq : (1 / 2 : ℝ) * (1 / (2 * (J : ℝ) - 1)) = 1 / (2 * (2 * (J : ℝ) - 1)) := by
    rw [one_div_mul_one_div]
  linarith

private def oddPrimesLt160_1 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29]
private def oddPrimesLt160_2 : List ℕ := [31, 37, 41, 43, 47, 53, 59, 61, 67]
private def oddPrimesLt160_3 : List ℕ := [71, 73, 79, 83, 89, 97, 101, 103, 107]
private def oddPrimesLt160_4 : List ℕ := [109, 113, 127, 131, 137, 139, 149, 151, 157]
private def oddPrimesLt160 : List ℕ :=
  oddPrimesLt160_1 ++ oddPrimesLt160_2 ++ oddPrimesLt160_3 ++ oddPrimesLt160_4

private lemma oddPrimesLt160_nodup : oddPrimesLt160.Nodup := by decide

private lemma oddPrimesLt160_ge3 : ∀ p ∈ oddPrimesLt160, 3 ≤ p := by decide

private def checkSieve160 : ℕ → Bool
  | 0 => true
  | n + 1 =>
    (if 3 ≤ n ∧ n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0
     then n ∈ oddPrimesLt160 else true) && checkSieve160 n

private lemma checkSieve160_ok : checkSieve160 160 = true := by decide

private lemma checkSieve160_sound {n p : ℕ} (h : checkSieve160 n = true) (hp : p < n)
    (h3 : 3 ≤ p) (hnd : p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧ p % 11 ≠ 0) :
    p ∈ oddPrimesLt160 := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [checkSieve160, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hlt | rfl
    · exact ih h.2 hlt
    · have h1 := h.1
      simp only [h3, hnd.1, hnd.2.1, hnd.2.2.1, hnd.2.2.2.1, hnd.2.2.2.2,
        ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h1
      exact decide_eq_true_eq.mp h1

private lemma oddPrimesLt160_subset :
    (Finset.range 160).filter (fun p => p.Prime ∧ 2 < p) ⊆ oddPrimesLt160.toFinset := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp160, hpr, hp2⟩
  rw [Finset.mem_range] at hp160
  rw [List.mem_toFinset]
  by_cases hsmall : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11
  · rcases hsmall with rfl | rfl | rfl | rfl <;> decide
  · refine checkSieve160_sound checkSieve160_ok hp160 hp2 ?_
    have hnd : ∀ q : ℕ, q.Prime → q ≠ p → p % q ≠ 0 := fun q hq hqp hmod =>
      hqp ((Nat.prime_dvd_prime_iff_eq hq hpr).mp (Nat.dvd_of_mod_eq_zero hmod))
    refine ⟨hnd 2 Nat.prime_two (by omega), hnd 3 (by decide) ?_, hnd 5 (by decide) ?_,
      hnd 7 (by decide) ?_, hnd 11 (by decide) ?_⟩ <;> tauto

private lemma H_tilde_partial_160_le : H_tilde_partial 160 ≤ (12959 / 10000 : ℝ) := by
  let f : ℕ → ℝ := fun p => 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))
  have h1_le : ∀ p ∈ oddPrimesLt160.toFinset, 1 ≤ f p := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast oddPrimesLt160_ge3 p (List.mem_toFinset.mp hp)
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    dsimp [f]
    have : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
    linarith
  have hsub : H_tilde_partial 160 ≤ ∏ p ∈ oddPrimesLt160.toFinset, f p := by
    unfold H_tilde_partial
    exact Finset.prod_le_prod_of_subset_of_one_le₀ oddPrimesLt160_subset
      (fun p hp => by linarith [h1_le p (oddPrimesLt160_subset hp)])
      (fun p hp _ => h1_le p hp)
  have hprod_eq : ∏ p ∈ oddPrimesLt160.toFinset, f p =
      (oddPrimesLt160_1.map f).prod * (oddPrimesLt160_2.map f).prod *
        (oddPrimesLt160_3.map f).prod * (oddPrimesLt160_4.map f).prod := by
    rw [List.prod_toFinset _ oddPrimesLt160_nodup]
    dsimp only [oddPrimesLt160]
    simp only [List.map_append, List.prod_append]
  have hb1 : (oddPrimesLt160_1.map f).prod ≤ (12863 / 10000 : ℝ) := by
    simp only [oddPrimesLt160_1, f, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    norm_num
  have hb2 : (oddPrimesLt160_2.map f).prod ≤ (10055 / 10000 : ℝ) := by
    simp only [oddPrimesLt160_2, f, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    norm_num
  have hb3 : (oddPrimesLt160_3.map f).prod ≤ (10013 / 10000 : ℝ) := by
    simp only [oddPrimesLt160_3, f, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    norm_num
  have hb4 : (oddPrimesLt160_4.map f).prod ≤ (10006 / 10000 : ℝ) := by
    simp only [oddPrimesLt160_4, f, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    norm_num
  have hnn1 : 0 ≤ (oddPrimesLt160_1.map f).prod := by
    refine List.prod_nonneg ?_
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro p hp; exact by linarith [h1_le p (List.mem_toFinset.mpr (by simp [oddPrimesLt160, hp]))]
  have hnn2 : 0 ≤ (oddPrimesLt160_2.map f).prod := by
    refine List.prod_nonneg ?_
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro p hp; exact by linarith [h1_le p (List.mem_toFinset.mpr (by simp [oddPrimesLt160, hp]))]
  have hnn3 : 0 ≤ (oddPrimesLt160_3.map f).prod := by
    refine List.prod_nonneg ?_
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro p hp; exact by linarith [h1_le p (List.mem_toFinset.mpr (by simp [oddPrimesLt160, hp]))]
  have hnn4 : 0 ≤ (oddPrimesLt160_4.map f).prod := by
    refine List.prod_nonneg ?_
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro p hp; exact by linarith [h1_le p (List.mem_toFinset.mpr (by simp [oddPrimesLt160, hp]))]
  rw [hprod_eq] at hsub
  have h12 : (oddPrimesLt160_1.map f).prod * (oddPrimesLt160_2.map f).prod ≤
      (12863 / 10000 : ℝ) * (10055 / 10000 : ℝ) :=
    mul_le_mul hb1 hb2 hnn2 (by norm_num)
  have h123 : (oddPrimesLt160_1.map f).prod * (oddPrimesLt160_2.map f).prod *
      (oddPrimesLt160_3.map f).prod ≤
      (12863 / 10000 : ℝ) * (10055 / 10000 : ℝ) * (10013 / 10000 : ℝ) :=
    mul_le_mul h12 hb3 hnn3 (by norm_num)
  have h1234 : (oddPrimesLt160_1.map f).prod * (oddPrimesLt160_2.map f).prod *
      (oddPrimesLt160_3.map f).prod * (oddPrimesLt160_4.map f).prod ≤
      (12863 / 10000 : ℝ) * (10055 / 10000 : ℝ) * (10013 / 10000 : ℝ) * (10006 / 10000 : ℝ) :=
    mul_le_mul h123 hb4 hnn4 (by norm_num)
  linarith

/-- Certified upper bound `H_tilde ≤ 13 / 10`. -/
theorem H_tilde_le_cert : H_tilde ≤ (13 / 10 : ℝ) := by
  have h1 := H_tilde_le_partial_two_mul_exp (J := 80) (by norm_num)
  rw [show 2 * 80 = 160 by norm_num] at h1
  have hexp : Real.exp (1 / (2 * (2 * (80 : ℝ) - 1))) ≤ (318 / 317 : ℝ) := by
    have h2 : (317 / 318 : ℝ) ≤ Real.exp (-(1 / (2 * (2 * (80 : ℝ) - 1)))) := by
      have := Real.add_one_le_exp (-(1 / (2 * (2 * (80 : ℝ) - 1))))
      linarith
    rw [Real.exp_neg] at h2
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 317 / 318) h2
    simpa using hinv
  have hpart := H_tilde_partial_160_le
  have hmul : H_tilde_partial 160 * Real.exp (1 / (2 * (2 * (80 : ℝ) - 1))) ≤
      (12959 / 10000 : ℝ) * (318 / 317 : ℝ) :=
    mul_le_mul hpart hexp (Real.exp_pos _).le (by norm_num)
  linarith

end ConstantBounds

end BuchstabSwitching
