import BuchstabSwitching.Sieve.LinearSieveBJS.CertifiedC2Grid

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 5b. Certified `ValidDecaySeq` and Concrete `C2_bjs` Upper Bound (`≤ 494`) -/

section CertifiedC2

def C2_certified_ub : ℝ := 494

def certifiedDecaySeq (n : ℕ) : ℝ := (cNum n : ℝ) / 10000

private lemma fHat_contraction_step {n : ℕ} (hn : 1 ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hprev : ∀ s, (if Even n then (2 : ℝ) else 1) ≤ s → fHat n s ≤ 2 * Real.exp 2 * A * h_bjs s) :
    ∀ s, (if Even (n + 1) then (2 : ℝ) else 1) ≤ s →
      fHat (n + 1) s ≤
        2 * Real.exp 2 * (A * (if (n + 1) % 2 = 0 then (9607 / 10000 : ℝ) else 9214 / 10000)) * h_bjs s := by
  intro s hs
  by_cases hs_supp : (n : ℝ) + 3 ≤ s
  · rw [fHat_support (n + 1) (by omega) (by push_cast; linarith)]
    have : 0 ≤ (if (n + 1) % 2 = 0 then (9607 / 10000 : ℝ) else 9214 / 10000) := by
      split_ifs <;> norm_num
    exact mul_nonneg (by positivity) (h_bjs_nonneg s)
  · have hs_lt : s < (n : ℝ) + 3 := lt_of_not_ge hs_supp
    have hcont : Continuous (fun t => h_bjs (t - 1)) :=
      h_bjs_continuous.comp (continuous_id.sub continuous_const)
    have hf_cont : ContinuousOn (fun t => fHat n (t - 1)) (Set.Ici 2) :=
      (fHat_continuousOn n hn).comp (continuousOn_id.sub continuousOn_const) fun t ht => by
        simp only [Set.mem_Ici] at ht ⊢; linarith
    set C : ℝ := 2 * Real.exp 2 * A
    have hC_nn : 0 ≤ C := by positivity
    have hint_bound : ∀ u : ℝ, (if Even n then (2 : ℝ) else 1) ≤ u - 1 → u ≤ (n : ℝ) + 3 →
        ∫ t in u..((n : ℝ) + 3), fHat n (t - 1) ≤ C * ∫ t in u..((n : ℝ) + 3), h_bjs (t - 1) := by
      intro u hu_dom hu_le
      have hu2 : 2 ≤ u := by split_ifs at hu_dom <;> linarith
      have hi1 : IntervalIntegrable (fun t => fHat n (t - 1)) volume u ((n : ℝ) + 3) := by
        refine (hf_cont.mono fun t ht => ?_).intervalIntegrable
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [Set.mem_Ici] <;> linarith
      have hi2 : IntervalIntegrable (fun t => C * h_bjs (t - 1)) volume u ((n : ℝ) + 3) :=
        (continuous_const.mul hcont).intervalIntegrable _ _
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hu_le hi1 hi2 fun t ht => ?_
      exact hprev (t - 1) (by linarith [ht.1])
    by_cases hsucc_ev : Even (n + 1)
    · have hmod : (n + 1) % 2 = 0 := Nat.even_iff.mp hsucc_ev
      have hn_odd : ¬Even n := Nat.even_add_one.mp hsucc_ev
      have hs2 : 2 ≤ s := by simpa [hsucc_ev] using hs
      have htail := (fHat_tail_integral n hn (s := s) (M := (n : ℝ) + 3) le_rfl).1 hsucc_ev hs2
      rw [htail]
      have hI := hint_bound s (by simp [hn_odd]; linarith) hs_lt.le
      have hH := H_bjs_le_two hs2 hs_lt.le
      have hs0 : 0 < s := by linarith
      calc (1 / s) * ∫ t in s..((n : ℝ) + 3), fHat n (t - 1)
          ≤ (1 / s) * (C * ∫ t in s..((n : ℝ) + 3), h_bjs (t - 1)) :=
            mul_le_mul_of_nonneg_left hI (by positivity)
        _ ≤ (1 / s) * (C * (kappa2 * s * h_bjs s)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hC_nn) (by positivity)
        _ = 2 * Real.exp 2 * (A * (9607 / 10000 : ℝ)) * h_bjs s := by
            dsimp [C]; unfold kappa2; field_simp [hs0.ne']
        _ = _ := by simp only [hmod, ↓reduceIte]
    · have hmod : (n + 1) % 2 ≠ 0 := fun h0 => hsucc_ev (Nat.even_iff.mpr h0)
      have hn_ev : Even n := not_not.mp (mt Nat.even_add_one.mpr hsucc_ev)
      have hsucc_odd : Odd (n + 1) := Nat.not_even_iff_odd.mp hsucc_ev
      have hs1 : 1 ≤ s := by simpa [hsucc_ev] using hs
      have hnot1 : ¬ s < 1 := not_lt.mpr hs1
      have hs0 : 0 < s := by linarith
      by_cases hs3 : 3 ≤ s
      · have htail := (fHat_tail_integral n hn (s := s) (M := (n : ℝ) + 3) le_rfl).2 hsucc_odd hs3
        rw [htail]
        have hI := hint_bound s (by simp [hn_ev]; linarith) hs_lt.le
        have hH := H_bjs_le_three hs3 hs_lt.le
        have hk3 : kappa3 ≤ (9214 / 10000 : ℝ) := by unfold kappa3; norm_num
        calc (1 / s) * ∫ t in s..((n : ℝ) + 3), fHat n (t - 1)
            ≤ (1 / s) * (C * ∫ t in s..((n : ℝ) + 3), h_bjs (t - 1)) :=
              mul_le_mul_of_nonneg_left hI (by positivity)
          _ ≤ (1 / s) * (C * (kappa3 * s * h_bjs s)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hC_nn) (by positivity)
          _ = C * kappa3 * h_bjs s := by field_simp [hs0.ne']
          _ ≤ C * (9214 / 10000 : ℝ) * h_bjs s :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk3 hC_nn) (h_bjs_nonneg s)
          _ = _ := by dsimp [C]; simp only [hmod, ↓reduceIte]; ring
      · have hs3' : s ≤ 3 := le_of_not_ge hs3
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hmod' : (m + 2) % 2 ≠ 0 := hmod
        have hmax : max 3 s = 3 := max_eq_left hs3'
        have hdef : fHat (m + 2) s = (1 / s) * ∫ t in (3 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1) := by
          rw [fHat]; simp only [hnot1, ↓reduceIte, hmod', hmax]
        have hcast3 : ((m + 1 : ℕ) : ℝ) + 3 = (m : ℝ) + 4 := by push_cast; ring
        have hk3_le : (3 : ℝ) ≤ (m : ℝ) + 4 := by linarith
        have hI := hint_bound 3 (by simp only [hn_ev, ↓reduceIte]; norm_num) (by push_cast; linarith)
        rw [hcast3] at hI
        have hH := H_bjs_three_le_tilde hs1 hs3' (M := (m : ℝ) + 4) hk3_le
        calc fHat (m + 1 + 1) s
            = (1 / s) * ∫ t in (3 : ℝ)..((m : ℝ) + 4), fHat (m + 1) (t - 1) := hdef
          _ ≤ (1 / s) * (C * ∫ t in (3 : ℝ)..((m : ℝ) + 4), h_bjs (t - 1)) :=
              mul_le_mul_of_nonneg_left hI (by positivity)
          _ ≤ (1 / s) * (C * (kappaTilde * s * h_bjs s)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hC_nn) (by positivity)
          _ = C * kappaTilde * h_bjs s := by field_simp [hs0.ne']
          _ = _ := by dsimp [C]; unfold kappaTilde; simp only [hmod, ↓reduceIte]; ring

private lemma tailList_sound (n prevT prevP : ℕ) (xs : List (ℕ × ℕ)) (hn : 2 ≤ n)
    (hchk : checkTailList n prevT prevP xs = true)
    (hf_prev : ∀ s, (if Even (n - 1) then (2 : ℝ) else 1) ≤ s →
      fHat (n - 1) s ≤ 2 * Real.exp 2 * ((prevT : ℝ) / (scaleF : ℝ)) * h_bjs s)
    (hp_prev : (prevP : ℝ) / (scaleF : ℝ) ≤ (certifiedDecaySeq (n - 1)) ^ (n - 2)) :
    ∀ k, k < xs.length →
      (∀ s, (if Even (n + k) then (2 : ℝ) else 1) ≤ s →
        fHat (n + k) s ≤ 2 * Real.exp 2 * (((xs.getD k (0, 0)).1 : ℝ) / (scaleF : ℝ)) * h_bjs s) ∧
      (xs.getD k (0, 0)).1 ≤ (xs.getD k (0, 0)).2 ∧
      (((xs.getD k (0, 0)).2 : ℝ) / (scaleF : ℝ) ≤ (certifiedDecaySeq (n + k)) ^ (n + k - 1)) := by
  induction xs generalizing n prevT prevP with
  | nil => intro k hk; simp at hk
  | cons hd tl ih =>
    rcases hd with ⟨t, p⟩
    dsimp only [checkTailList, tailStepCheck] at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨ht_step, htp⟩, hp_step⟩, htl⟩
    have hsf : (0 : ℝ) < (scaleF : ℝ) := by unfold scaleF; norm_num
    have ht_real : ∀ s, (if Even n then (2 : ℝ) else 1) ≤ s →
        fHat n s ≤ 2 * Real.exp 2 * ((t : ℝ) / (scaleF : ℝ)) * h_bjs s := by
      intro s hs
      have h1 := fHat_contraction_step (n := n - 1) (by omega) (by positivity) hf_prev s
        (by simpa [show n - 1 + 1 = n by omega] using hs)
      rw [show n - 1 + 1 = n by omega] at h1
      have hceil := le_ceilDiv_real (prevT * (if n % 2 = 0 then 9607 else 9214)) 10000 (by norm_num)
      have hkap : (prevT : ℝ) / (scaleF : ℝ) * (if n % 2 = 0 then (9607 / 10000 : ℝ) else 9214 / 10000) ≤
          (t : ℝ) / (scaleF : ℝ) := by
        have h2 : (ceilDiv (prevT * (if n % 2 = 0 then 9607 else 9214)) 10000 : ℝ) ≤ (t : ℝ) := by
          exact_mod_cast ht_step
        have h3 : (prevT : ℝ) * (if n % 2 = 0 then (9607 : ℝ) else 9214) / 10000 ≤ (t : ℝ) := by
          refine le_trans ?_ h2
          simpa [Nat.cast_mul, apply_ite Nat.cast] using hceil
        calc (prevT : ℝ) / (scaleF : ℝ) * (if n % 2 = 0 then (9607 / 10000 : ℝ) else 9214 / 10000)
            = ((prevT : ℝ) * (if n % 2 = 0 then (9607 : ℝ) else 9214) / 10000) / (scaleF : ℝ) := by
              split_ifs <;> ring
          _ ≤ (t : ℝ) / (scaleF : ℝ) := div_le_div_of_nonneg_right h3 hsf.le
      have hmult : 2 * Real.exp 2 *
            ((prevT : ℝ) / (scaleF : ℝ) * (if n % 2 = 0 then (9607 / 10000 : ℝ) else 9214 / 10000)) * h_bjs s ≤
          2 * Real.exp 2 * ((t : ℝ) / (scaleF : ℝ)) * h_bjs s := by
        gcongr; exact h_bjs_nonneg s
      exact h1.trans hmult
    have hp_real : (p : ℝ) / (scaleF : ℝ) ≤ (certifiedDecaySeq n) ^ (n - 1) := by
      by_cases heq : cNum n = cNum (n - 1)
      · simp only [heq, ↓reduceIte, decide_eq_true_eq] at hp_step
        have hstep' : p ≤ (prevP * cNum n) / 10000 := by simpa [heq] using hp_step
        have hdiv : (p : ℝ) ≤ ((prevP : ℝ) * (cNum n : ℝ)) / 10000 := by
          have h2 : ((prevP * cNum n / 10000 : ℕ) : ℝ) ≤ ((prevP * cNum n : ℕ) : ℝ) / 10000 := by
            rw [le_div_iff₀ (by norm_num)]
            exact_mod_cast Nat.div_mul_le_self (prevP * cNum n) 10000
          exact (by exact_mod_cast hstep' : (p : ℝ) ≤ ((prevP * cNum n / 10000 : ℕ) : ℝ)).trans
            (by simpa [Nat.cast_mul] using h2)
        have hceq : certifiedDecaySeq n = certifiedDecaySeq (n - 1) := by
          unfold certifiedDecaySeq; rw [heq]
        rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, hceq]
        calc (p : ℝ) / (scaleF : ℝ)
            ≤ (((prevP : ℝ) * (cNum n : ℝ)) / 10000) / (scaleF : ℝ) :=
              div_le_div_of_nonneg_right hdiv hsf.le
          _ = ((prevP : ℝ) / (scaleF : ℝ)) * ((cNum n : ℝ) / 10000) := by ring
          _ = ((prevP : ℝ) / (scaleF : ℝ)) * certifiedDecaySeq (n - 1) := by
              rw [← hceq]; rfl
          _ ≤ (certifiedDecaySeq (n - 1)) ^ (n - 2) * certifiedDecaySeq (n - 1) := by
              gcongr; unfold certifiedDecaySeq; positivity
      · simp only [heq, ↓reduceIte, decide_eq_true_eq] at hp_step
        have hnat : (p : ℝ) * (10000 : ℝ) ^ (n - 1) ≤ (scaleF : ℝ) * (cNum n : ℝ) ^ (n - 1) := by
          exact_mod_cast hp_step
        unfold certifiedDecaySeq
        rw [div_pow, div_le_div_iff₀ hsf (by positivity)]
        linarith
    intro k hk
    rcases k with _ | k
    · exact ⟨fun s hs => ht_real s hs, htp, hp_real⟩
    · have ih' := ih (n + 1) t p (by omega) htl (fun s hs => ht_real s hs)
        hp_real k (Nat.lt_of_succ_lt_succ hk)
      simpa only [List.getD_cons_succ, show n + (k + 1) = n + 1 + k by omega] using ih'

theorem certifiedDecaySeq_fHat_bound :
    ∀ n s, 1 ≤ n → (if Even n then (2 : ℝ) else 1) ≤ s →
      fHat n s ≤ 2 * Real.exp 2 * (certifiedDecaySeq n) ^ (n - 1) * h_bjs s := by
  have h10 : ∀ s, (if Even 10 then (2 : ℝ) else 1) ≤ s →
      fHat 10 s ≤ 2 * Real.exp 2 * ((mCertVal 10 : ℝ) / (scaleF : ℝ)) * h_bjs s :=
    fun s hs => fHat_le_mCertVal (by decide) (by decide) hs
  have hp10 : ((0 : ℕ) : ℝ) / (scaleF : ℝ) ≤ (certifiedDecaySeq 10) ^ 9 := by
    rw [Nat.cast_zero, zero_div]; unfold certifiedDecaySeq; positivity
  have htail := tailList_sound 11 (mCertVal 10) 0 tailTab (by decide) tailCheck_ok h10 hp10
  have h305 : ∀ s, (if Even 305 then (2 : ℝ) else 1) ≤ s →
      fHat 305 s ≤ 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ 304 * h_bjs s := by
    intro s hs
    rcases htail 294 (by rw [tailTab_length]; omega) with ⟨hf, htp, hp⟩
    have hc305 : certifiedDecaySeq 305 ≤ 9607 / 10000 := by
      unfold certifiedDecaySeq
      have : (cNum 305 : ℝ) ≤ 9607 := by exact_mod_cast (cNum_bounds 305).2
      linarith
    have hpow : (certifiedDecaySeq 305) ^ 304 ≤ (9607 / 10000 : ℝ) ^ 304 :=
      pow_le_pow_left₀ (by unfold certifiedDecaySeq; positivity) hc305 304
    have ht_le_p : (((tailTab.getD 294 (0, 0)).1 : ℝ) / (scaleF : ℝ)) ≤
        (((tailTab.getD 294 (0, 0)).2 : ℝ) / (scaleF : ℝ)) :=
      div_le_div_of_nonneg_right (by exact_mod_cast htp) (by unfold scaleF; norm_num)
    calc fHat 305 s
        ≤ 2 * Real.exp 2 * (((tailTab.getD 294 (0, 0)).1 : ℝ) / (scaleF : ℝ)) * h_bjs s := hf s hs
      _ ≤ 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ 304 * h_bjs s :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (ht_le_p.trans (hp.trans hpow)) (by positivity))
            (h_bjs_nonneg s)
  have hge305 : ∀ m s, (if Even (305 + m) then (2 : ℝ) else 1) ≤ s →
      fHat (305 + m) s ≤ 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (304 + m) * h_bjs s := by
    intro m; induction m with
    | zero => exact h305
    | succ m ih =>
      intro s hs
      have hstep := fHat_contraction_step (n := 305 + m) (by omega) (by positivity) ih s
        (by rw [Nat.add_assoc]; exact hs)
      have hkap : (if (305 + m + 1) % 2 = 0 then (9607 / 10000 : ℝ) else 9214 / 10000) ≤ 9607 / 10000 := by
        split_ifs <;> norm_num
      have hpow : (9607 / 10000 : ℝ) ^ (304 + m) * (9607 / 10000) = (9607 / 10000) ^ (304 + (m + 1)) := by
        rw [show 304 + (m + 1) = (304 + m) + 1 by omega, pow_succ]
      calc fHat (305 + (m + 1)) s = fHat (305 + m + 1) s := rfl
        _ ≤ 2 * Real.exp 2 * ((9607 / 10000 : ℝ) ^ (304 + m) *
              (if (305 + m + 1) % 2 = 0 then (9607 / 10000 : ℝ) else 9214 / 10000)) * h_bjs s := hstep
        _ ≤ 2 * Real.exp 2 * (9607 / 10000 : ℝ) ^ (304 + (m + 1)) * h_bjs s := by
            rw [← hpow]; gcongr; exact h_bjs_nonneg s
  intro n s hn hs
  by_cases hn1 : n = 1
  · subst hn1; simp only [Nat.sub_self, pow_zero, mul_one]
    exact fHat_one_le_h_bjs (by simpa only [Nat.not_even_one, ↓reduceIte] using hs)
  · by_cases hn10 : n ≤ 10
    · have hf := fHat_le_mCertVal (by omega) hn10 hs
      have hpre := mCertVal_prefix_check; rw [List.all_eq_true] at hpre
      have hk := hpre (n - 2) (by rw [List.mem_range]; omega)
      simp only [decide_eq_true_eq, show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at hk
      have hrat : (mCertVal n : ℝ) / (scaleF : ℝ) ≤ (certifiedDecaySeq n) ^ (n - 1) := by
        have h1 : (mCertVal n : ℝ) * (10000 : ℝ) ^ (n - 1) ≤ (scaleF : ℝ) * (cNum n : ℝ) ^ (n - 1) := by
          exact_mod_cast hk
        unfold certifiedDecaySeq; rw [div_pow, div_le_div_iff₀ (by unfold scaleF; norm_num) (by positivity)]
        linarith
      exact hf.trans (by gcongr; exact h_bjs_nonneg s)
    · by_cases hn305 : n ≤ 305
      · have hk := htail (n - 11) (by rw [tailTab_length]; omega)
        rcases hk with ⟨hf, htp, hp⟩
        have ht_le_p : (((tailTab.getD (n - 11) (0, 0)).1 : ℝ) / (scaleF : ℝ)) ≤
            (((tailTab.getD (n - 11) (0, 0)).2 : ℝ) / (scaleF : ℝ)) :=
          div_le_div_of_nonneg_right (by exact_mod_cast htp) (by unfold scaleF; norm_num)
        have h1 : fHat n s ≤ 2 * Real.exp 2 * (((tailTab.getD (n - 11) (0, 0)).1 : ℝ) / (scaleF : ℝ)) * h_bjs s := by
          have hs' : (if Even (11 + (n - 11)) then (2 : ℝ) else 1) ≤ s := by
            rwa [show 11 + (n - 11) = n by omega]
          have hfn := hf s hs'
          rwa [show 11 + (n - 11) = n by omega] at hfn
        have h2 : (((tailTab.getD (n - 11) (0, 0)).2 : ℝ) / (scaleF : ℝ)) ≤ (certifiedDecaySeq n) ^ (n - 1) := by
          rwa [show 11 + (n - 11) = n by omega] at hp
        calc fHat n s
            ≤ 2 * Real.exp 2 * (((tailTab.getD (n - 11) (0, 0)).1 : ℝ) / (scaleF : ℝ)) * h_bjs s := h1
          _ ≤ 2 * Real.exp 2 * (certifiedDecaySeq n) ^ (n - 1) * h_bjs s := by
              gcongr; exact h_bjs_nonneg s; exact ht_le_p.trans h2
      · obtain ⟨m, rfl⟩ : ∃ m, n = 305 + m := ⟨n - 305, by omega⟩
        have hc9607 : cNum (305 + m) = 9607 := by
          unfold cNum
          have h1 : ¬ (305 + m ≤ 1) := by omega
          have h2 : ¬ (305 + m ≤ 10) := by omega
          have h3 : ¬ (305 + m ≤ 15) := by omega
          have h4 : ¬ (305 + m ≤ 20) := by omega
          have h5 : ¬ (305 + m ≤ 30) := by omega
          have h6 : ¬ (305 + m ≤ 60) := by omega
          have h7 : ¬ (305 + m ≤ 150) := by omega
          have h8 : ¬ (305 + m ≤ 305) := by omega
          simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]
        have hseq : certifiedDecaySeq (305 + m) = 9607 / 10000 := by
          unfold certifiedDecaySeq; rw [hc9607]; norm_num
        rw [hseq, show 305 + m - 1 = 304 + m by omega]
        exact hge305 m s hs

theorem validDecaySeq_certified : ValidDecaySeq certifiedDecaySeq := by
  constructor
  · intro n _
    unfold certifiedDecaySeq
    obtain ⟨hpos, hle⟩ := cNum_bounds n
    constructor
    · have : (0 : ℝ) < (cNum n : ℝ) := by exact_mod_cast hpos
      linarith
    · have : (cNum n : ℝ) ≤ 9607 := by exact_mod_cast hle
      linarith
  · exact certifiedDecaySeq_fHat_bound

/-! #### Part D: `tauTab` Soundness, `J_bjs 302`, and `C2_bjs` Upper Bound -/

private lemma xiUB_sound {aC bC prev a b : ℕ} {κ γ τ_prev A B : ℝ}
    (hτ : τ_prev ≤ (prev : ℝ) / (scaleT : ℝ))
    (hA : A ≤ (a : ℝ) / (scaleT : ℝ)) (hA_nn : 0 ≤ A)
    (hB : B ≤ (b : ℝ) / (scaleT : ℝ))
    (haC : κ + (γ + κ) * (1 / 100 : ℝ) ≤ (aC : ℝ) / (scaleT : ℝ))
    (hbC : 2 * γ ≤ (bC : ℝ) / (scaleT : ℝ))
    (hκ : 0 ≤ κ + (γ + κ) * (1 / 100 : ℝ)) :
    τ_prev * (κ + (γ + κ) * (1 / 100 : ℝ)) + 2 * γ * A + 2 * B ≤
      (xiUB aC bC prev a b : ℝ) / (scaleT : ℝ) := by
  have hst : (0 : ℝ) < (scaleT : ℝ) := by unfold scaleT; norm_num
  have hc1 := le_ceilDiv_real (prev * aC) scaleT (by unfold scaleT; norm_num)
  have hc2 := le_ceilDiv_real (bC * a) scaleT (by unfold scaleT; norm_num)
  have h1 : τ_prev * (κ + (γ + κ) * (1 / 100 : ℝ)) ≤
      (ceilDiv (prev * aC) scaleT : ℝ) / (scaleT : ℝ) := by
    calc τ_prev * (κ + (γ + κ) * (1 / 100 : ℝ))
        ≤ ((prev : ℝ) / (scaleT : ℝ)) * ((aC : ℝ) / (scaleT : ℝ)) :=
          mul_le_mul hτ haC hκ (by positivity)
      _ = ((prev * aC : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
      _ ≤ (ceilDiv (prev * aC) scaleT : ℝ) / (scaleT : ℝ) :=
          div_le_div_of_nonneg_right hc1 hst.le
  have h2 : 2 * γ * A ≤ (ceilDiv (bC * a) scaleT : ℝ) / (scaleT : ℝ) := by
    calc 2 * γ * A
        ≤ ((bC : ℝ) / (scaleT : ℝ)) * ((a : ℝ) / (scaleT : ℝ)) :=
          mul_le_mul hbC hA hA_nn (by positivity)
      _ = ((bC * a : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
      _ ≤ (ceilDiv (bC * a) scaleT : ℝ) / (scaleT : ℝ) :=
          div_le_div_of_nonneg_right hc2 hst.le
  have h3 : 2 * B ≤ (2 * (b : ℝ)) / (scaleT : ℝ) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hB (by norm_num)
  unfold xiUB
  push_cast
  rw [add_div, add_div]
  linarith

private lemma tauList_sound (n tP tpP aP : ℕ) (xs : List (ℕ × ℕ × ℕ)) (hn : 2 ≤ n)
    (hchk : checkTauList n tP tpP aP xs = true)
    (ht_prev : tauBJS certifiedDecaySeq (1 / 100) (n - 1) ≤ (tP : ℝ) / (scaleT : ℝ))
    (htp_prev : tauPrimeBJS certifiedDecaySeq (1 / 100) (n - 1) ≤ (tpP : ℝ) / (scaleT : ℝ))
    (ha_prev : (certifiedDecaySeq (n - 1)) ^ (n - 2) ≤ (aP : ℝ) / (scaleT : ℝ)) :
    (∀ k, k < xs.length →
      tauBJS certifiedDecaySeq (1 / 100) (n + k) ≤ ((xs.getD k (0, 0, 0)).1 : ℝ) / (scaleT : ℝ) ∧
      tauPrimeBJS certifiedDecaySeq (1 / 100) (n + k) ≤ ((xs.getD k (0, 0, 0)).2.1 : ℝ) / (scaleT : ℝ)) ∧
    (∑ k ∈ Finset.range xs.length,
      (if (n + k) % 2 = 0 ∧ n + k ≤ 2 * keTail then (xs.getD k (0, 0, 0)).1 else 0)) =
      sumEvenTau n xs := by
  have hst : (0 : ℝ) < (scaleT : ℝ) := by unfold scaleT; norm_num
  have hg2_lt : gammaBJS 2 < (12214028 / 10000000 : ℝ) := by rw [gammaBJS_two]; exact exp_one_fifth_lt
  have hg22_lt : gammaBJS (22 / 10) < (12214028 / 10000000 : ℝ) ^ 2 := by
    have hle : (22 / 10 : ℝ) ≤ 14 / 5 := by norm_num
    simp only [gammaBJS, hle, ↓reduceIte]
    rw [show (22 / 10 : ℝ) + 1 / 5 - 2 = 2 / 5 by norm_num]; exact exp_two_fifths_lt
  have hg24_lt : gammaBJS (24 / 10) < (12214028 / 10000000 : ℝ) ^ 3 := by
    have hle : (24 / 10 : ℝ) ≤ 14 / 5 := by norm_num
    simp only [gammaBJS, hle, ↓reduceIte]
    rw [show (24 / 10 : ℝ) + 1 / 5 - 2 = 3 / 5 by norm_num]; exact exp_three_fifths_lt
  have hg26_lt : gammaBJS (26 / 10) < (12214028 / 10000000 : ℝ) ^ 4 := by
    have hle : (26 / 10 : ℝ) ≤ 14 / 5 := by norm_num
    simp only [gammaBJS, hle, ↓reduceIte]
    rw [show (26 / 10 : ℝ) + 1 / 5 - 2 = 4 / 5 by norm_num]; exact exp_four_fifths_lt
  have hg28_lt : gammaBJS (28 / 10) < (27182818286 / 10000000000 : ℝ) := by
    have hle : (28 / 10 : ℝ) ≤ 14 / 5 := by norm_num
    simp only [gammaBJS, hle, ↓reduceIte]
    rw [show (28 / 10 : ℝ) + 1 / 5 - 2 = 1 by norm_num]; exact exp_one_lt_d9'
  have hg3_lt : gammaBJS 3 < 4 * (27182818286 / 10000000000 : ℝ) / 3 := by
    rw [gammaBJS_three]; linarith [exp_one_lt_d9']
  have he1_lt : Real.exp 1 < (27182818286 / 10000000000 : ℝ) := exp_one_lt_d9'
  induction xs generalizing n tP tpP aP with
  | nil =>
    refine ⟨fun k hk => by simp at hk, by simp [sumEvenTau]⟩
  | cons hd tl ih =>
    rcases hd with ⟨t, tp, b⟩
    dsimp only [checkTauList] at hchk
    simp only [Bool.and_eq_true] at hchk
    rcases hchk with ⟨hstep_chk, htl⟩
    dsimp only [tauStepCheck] at hstep_chk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep_chk
    rcases hstep_chk with ⟨⟨hb_chk, ht_chk⟩, htp_chk⟩
    have hb_real : (certifiedDecaySeq n) ^ (n - 1) ≤ (b : ℝ) / (scaleT : ℝ) := by
      by_cases hn10 : n ≤ 10
      · simp only [hn10, ↓reduceIte, decide_eq_true_eq] at hb_chk
        have hnat : (scaleT : ℝ) * (cNum n : ℝ) ^ (n - 1) ≤ (b : ℝ) * (10000 : ℝ) ^ (n - 1) := by
          exact_mod_cast hb_chk
        unfold certifiedDecaySeq
        rw [div_pow, div_le_div_iff₀ (by positivity) hst]
        linarith
      · by_cases heq : cNum n = cNum (n - 1)
        · simp only [hn10, ↓reduceIte, heq, decide_eq_true_eq] at hb_chk
          have hceil := le_ceilDiv_real (aP * cNum n) 10000 (by norm_num)
          have h1 : (aP : ℝ) / (scaleT : ℝ) * ((cNum n : ℝ) / 10000) ≤ (b : ℝ) / (scaleT : ℝ) := by
            have h2 : (ceilDiv (aP * cNum n) 10000 : ℝ) ≤ (b : ℝ) := by
              have hb' : ceilDiv (aP * cNum n) 10000 ≤ b := by simpa [heq] using hb_chk
              exact_mod_cast hb'
            have h3 : ((aP * cNum n : ℕ) : ℝ) / 10000 ≤ (b : ℝ) := hceil.trans h2
            calc (aP : ℝ) / (scaleT : ℝ) * ((cNum n : ℝ) / 10000)
                = (((aP * cNum n : ℕ) : ℝ) / 10000) / (scaleT : ℝ) := by push_cast; ring
              _ ≤ (b : ℝ) / (scaleT : ℝ) := div_le_div_of_nonneg_right h3 hst.le
          have hceq : certifiedDecaySeq n = certifiedDecaySeq (n - 1) := by
            unfold certifiedDecaySeq; rw [heq]
          rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, hceq]
          calc (certifiedDecaySeq (n - 1)) ^ (n - 2) * certifiedDecaySeq (n - 1)
              ≤ ((aP : ℝ) / (scaleT : ℝ)) * certifiedDecaySeq (n - 1) := by
                gcongr; unfold certifiedDecaySeq; positivity
            _ = (aP : ℝ) / (scaleT : ℝ) * ((cNum n : ℝ) / 10000) := by
                rw [← hceq]; rfl
            _ ≤ (b : ℝ) / (scaleT : ℝ) := h1
        · simp only [hn10, ↓reduceIte, heq, decide_eq_true_eq] at hb_chk
          have hnat : (scaleT : ℝ) * (cNum n : ℝ) ^ (n - 1) ≤ (b : ℝ) * (10000 : ℝ) ^ (n - 1) := by
            exact_mod_cast hb_chk
          unfold certifiedDecaySeq
          rw [div_pow, div_le_div_iff₀ (by positivity) hst]
          linarith
    have hc_nn : ∀ k, 0 ≤ certifiedDecaySeq k := fun k => by
      unfold certifiedDecaySeq; positivity
    have hA_nn : 0 ≤ (certifiedDecaySeq (n - 1)) ^ (n - 2) := pow_nonneg (hc_nn _) _
    have hB_nn : 0 ≤ (certifiedDecaySeq n) ^ (n - 1) := pow_nonneg (hc_nn _) _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hm_sub1 : m + 2 - 1 = m + 1 := by omega
    have hm_sub2 : m + 2 - 2 = m := by omega
    have hmax_le : ∀ {A B : ℝ} {x y : ℕ},
        A ≤ (x : ℝ) / (scaleT : ℝ) → B ≤ (y : ℝ) / (scaleT : ℝ) →
        max A B ≤ ((max x y : ℕ) : ℝ) / (scaleT : ℝ) := fun hA hB =>
      max_le (hA.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hst.le))
        (hB.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hst.le))
    have hg_nn : ∀ s0 : ℝ, 0 ≤ gammaBJS s0 := fun s0 => by
      unfold gammaBJS; split_ifs; exact (Real.exp_pos _).le; positivity
    have ht_cur : tauBJS certifiedDecaySeq (1 / 100) (m + 2) ≤ (t : ℝ) / (scaleT : ℝ) := by
      have hstep_le : (tauStepVal (m + 2) tP aP b : ℝ) / (scaleT : ℝ) ≤ (t : ℝ) / (scaleT : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast ht_chk) hst.le
      refine le_trans ?_ hstep_le
      rw [tauBJS]
      by_cases hev : Even (m + 2)
      · have hmod : (m + 2) % 2 = 0 := Nat.even_iff.mp hev
        simp only [hev, ↓reduceIte, tauStepVal, hmod]
        have hx2 := xiUB_sound (κ := kappa2) (γ := gammaBJS 2) (aC := aCoef2) (bC := bCoef2)
          ht_prev ha_prev hA_nn hb_real
          (by unfold kappa2 aCoef2 scaleT; linarith) (by unfold bCoef2 scaleT; linarith)
          (by unfold kappa2; have := hg_nn 2; positivity)
        have hx22 := xiUB_sound (κ := kappa22) (γ := gammaBJS (22 / 10)) (aC := aCoef22) (bC := bCoef22)
          ht_prev ha_prev hA_nn hb_real
          (by unfold kappa22 aCoef22 scaleT; norm_num at hg22_lt ⊢; linarith)
          (by unfold bCoef22 scaleT; norm_num at hg22_lt ⊢; linarith)
          (by unfold kappa22; have := hg_nn (22 / 10); positivity)
        have hx24 := xiUB_sound (κ := kappa24) (γ := gammaBJS (24 / 10)) (aC := aCoef24) (bC := bCoef24)
          ht_prev ha_prev hA_nn hb_real
          (by unfold kappa24 aCoef24 scaleT; norm_num at hg24_lt ⊢; linarith)
          (by unfold bCoef24 scaleT; norm_num at hg24_lt ⊢; linarith)
          (by unfold kappa24; have := hg_nn (24 / 10); positivity)
        have hx26 := xiUB_sound (κ := kappa26) (γ := gammaBJS (26 / 10)) (aC := aCoef26) (bC := bCoef26)
          ht_prev ha_prev hA_nn hb_real
          (by unfold kappa26 aCoef26 scaleT; norm_num at hg26_lt ⊢; linarith)
          (by unfold bCoef26 scaleT; norm_num at hg26_lt ⊢; linarith)
          (by unfold kappa26; have := hg_nn (26 / 10); positivity)
        have hx28 := xiUB_sound (κ := kappa28) (γ := gammaBJS (28 / 10)) (aC := aCoef28) (bC := bCoef28)
          ht_prev ha_prev hA_nn hb_real
          (by unfold kappa28 aCoef28 scaleT; linarith) (by unfold bCoef28 scaleT; linarith)
          (by unfold kappa28; have := hg_nn (28 / 10); positivity)
        have hx3 := xiUB_sound (κ := kappa3) (γ := gammaBJS 3) (aC := aCoef3) (bC := bCoef3)
          ht_prev ha_prev hA_nn hb_real
          (by unfold kappa3 aCoef3 scaleT; linarith) (by unfold bCoef3 scaleT; linarith)
          (by unfold kappa3; have := hg_nn 3; positivity)
        unfold xiTermBJS
        rw [hm_sub1, hm_sub2]
        exact hmax_le hx2 (hmax_le hx22 (hmax_le hx24 (hmax_le hx26 (hmax_le hx28 hx3))))
      · have hmod : (m + 2) % 2 ≠ 0 := fun h0 => hev (Nat.even_iff.mpr h0)
        simp only [hev, ↓reduceIte, tauStepVal, hmod]
        have hx3 := xiUB_sound (κ := kappa3) (γ := gammaBJS 3) (aC := aCoef3) (bC := bCoef3)
          ht_prev ha_prev hA_nn hb_real
          (by unfold kappa3 aCoef3 scaleT; linarith) (by unfold bCoef3 scaleT; linarith)
          (by unfold kappa3; have := hg_nn 3; positivity)
        have hxt : xiTildeTermBJS certifiedDecaySeq (1 / 100) (m + 2)
              (tauBJS certifiedDecaySeq (1 / 100) (m + 1)) ≤
            (xiTildeUB tP aP b : ℝ) / (scaleT : ℝ) := by
          unfold xiTildeTermBJS xiTildeUB
          rw [hm_sub1, hm_sub2]
          have hc1 := le_ceilDiv_real (tP * aCoefT) scaleT (by unfold scaleT; norm_num)
          have hc2 := le_ceilDiv_real (bCoefT * aP) scaleT (by unfold scaleT; norm_num)
          have hc3 := le_ceilDiv_real (cCoef2 * b) scaleT (by unfold scaleT; norm_num)
          have h1 : tauBJS certifiedDecaySeq (1 / 100) (m + 1) * (kappaTilde + (5 + 4 * (1 / 100)) * (1 / 100)) ≤
              (ceilDiv (tP * aCoefT) scaleT : ℝ) / (scaleT : ℝ) := by
            calc _ ≤ ((tP : ℝ) / (scaleT : ℝ)) * ((aCoefT : ℝ) / (scaleT : ℝ)) :=
                  mul_le_mul ht_prev (by unfold kappaTilde aCoefT scaleT; norm_num) (by unfold kappaTilde; norm_num) (by positivity)
              _ = ((tP * aCoefT : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
              _ ≤ _ := div_le_div_of_nonneg_right hc1 hst.le
          have h2 : 6 * (1 + (1 / 100 : ℝ)) * (certifiedDecaySeq (m + 1)) ^ m ≤
              (ceilDiv (bCoefT * aP) scaleT : ℝ) / (scaleT : ℝ) := by
            calc _ ≤ ((bCoefT : ℝ) / (scaleT : ℝ)) * ((aP : ℝ) / (scaleT : ℝ)) :=
                  mul_le_mul (by unfold bCoefT scaleT; norm_num) ha_prev hA_nn (by positivity)
              _ = ((bCoefT * aP : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
              _ ≤ _ := div_le_div_of_nonneg_right hc2 hst.le
          have h3 : 2 * (2 + (1 / 100 : ℝ)) * (certifiedDecaySeq (m + 2)) ^ (m + 1) ≤
              (ceilDiv (cCoef2 * b) scaleT : ℝ) / (scaleT : ℝ) := by
            calc _ ≤ ((cCoef2 : ℝ) / (scaleT : ℝ)) * ((b : ℝ) / (scaleT : ℝ)) :=
                  mul_le_mul (by unfold cCoef2 scaleT; norm_num) hb_real hB_nn
                    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              _ = ((cCoef2 * b : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
              _ ≤ _ := div_le_div_of_nonneg_right hc3 hst.le
          push_cast; rw [add_div, add_div]; linarith
        unfold xiTermBJS
        rw [hm_sub1, hm_sub2]
        exact hmax_le hx3 hxt
    have htp_cur : tauPrimeBJS certifiedDecaySeq (1 / 100) (m + 2) ≤ (tp : ℝ) / (scaleT : ℝ) := by
      have hstep_le : (taupStepVal tpP aP b : ℝ) / (scaleT : ℝ) ≤ (tp : ℝ) / (scaleT : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast htp_chk) hst.le
      refine le_trans ?_ hstep_le
      rw [tauPrimeBJS]; unfold taupStepVal
      have hc1 := le_ceilDiv_real (tpP * aCoef2) scaleT (by unfold scaleT; norm_num)
      have hc2 := le_ceilDiv_real (bCoefPrime * aP) scaleT (by unfold scaleT; norm_num)
      have hc3 := le_ceilDiv_real (cCoef2 * b) scaleT (by unfold scaleT; norm_num)
      have h1 : tauPrimeBJS certifiedDecaySeq (1 / 100) (m + 1) * (kappa2 + (gammaBJS 2 + kappa2) * (1 / 100)) ≤
          (ceilDiv (tpP * aCoef2) scaleT : ℝ) / (scaleT : ℝ) := by
        calc _ ≤ ((tpP : ℝ) / (scaleT : ℝ)) * ((aCoef2 : ℝ) / (scaleT : ℝ)) :=
              mul_le_mul htp_prev (by unfold kappa2 aCoef2 scaleT; linarith)
                (by unfold kappa2; have := hg_nn 2; positivity) (by positivity)
          _ = ((tpP * aCoef2 : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
          _ ≤ _ := div_le_div_of_nonneg_right hc1 hst.le
      have h2 : (8 * Real.exp 1 / 3) * (certifiedDecaySeq (m + 1)) ^ m ≤
          (ceilDiv (bCoefPrime * aP) scaleT : ℝ) / (scaleT : ℝ) := by
        calc _ ≤ ((bCoefPrime : ℝ) / (scaleT : ℝ)) * ((aP : ℝ) / (scaleT : ℝ)) :=
              mul_le_mul (by unfold bCoefPrime scaleT; linarith) ha_prev hA_nn
                (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          _ = ((bCoefPrime * aP : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
          _ ≤ _ := div_le_div_of_nonneg_right hc2 hst.le
      have h3 : 2 * (2 + (1 / 100 : ℝ)) * (certifiedDecaySeq (m + 2)) ^ (m + 1) ≤
          (ceilDiv (cCoef2 * b) scaleT : ℝ) / (scaleT : ℝ) := by
        calc _ ≤ ((cCoef2 : ℝ) / (scaleT : ℝ)) * ((b : ℝ) / (scaleT : ℝ)) :=
              mul_le_mul (by unfold cCoef2 scaleT; norm_num) hb_real hB_nn
                (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          _ = ((cCoef2 * b : ℕ) : ℝ) / (scaleT : ℝ) / (scaleT : ℝ) := by push_cast; ring
          _ ≤ _ := div_le_div_of_nonneg_right hc3 hst.le
      push_cast; rw [add_div, add_div]; linarith
    have ih' := ih (m + 3) t tp b (by omega) htl (by exact ht_cur)
      (by exact htp_cur) (by exact hb_real)
    refine ⟨fun k hk => ?_, ?_⟩
    · rcases k with _ | k
      · exact ⟨ht_cur, htp_cur⟩
      · simpa [show m + 2 + (k + 1) = m + 3 + k by omega] using ih'.1 k (by simpa using hk)
    · rw [List.length_cons, Finset.sum_range_succ']
      dsimp only [sumEvenTau]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      have hid := ih'.2
      have hsum_eq : (∑ k ∈ Finset.range tl.length,
            if (m + 2 + (k + 1)) % 2 = 0 ∧ m + 2 + (k + 1) ≤ 2 * keTail
            then (tl.getD k (0, 0, 0)).1 else 0) = sumEvenTau (m + 3) tl := by
        convert hid using 2 with k
        simp [show m + 2 + (k + 1) = m + 3 + k by omega]
      rw [hsum_eq]
      ring

private lemma j_pow300_ub_aux (n150 n300 : ℕ) (hmul : n300 = n150 * 2)
    (hj_check : 18418926643 * (960700000 ^ n150) ^ 2 * scaleT ≤
      3750000000 * (jUbNum - 982521028) * (982521027 ^ n150) ^ 2) :
    (982521028 / 1000000000 : ℝ) +
      (8 * (27182818286 / 10000000000 : ℝ) / 6 + 2 * (2 + 1 / 100 : ℝ) / 3 * (9607 / 10000 : ℝ)) *
        ((9607 / 10000 : ℝ) / (982521027 / 1000000000 : ℝ)) ^ n300 ≤
      (jUbNum : ℝ) / (scaleT : ℝ) := by
  have hscale : (scaleT : ℝ) = 1000000000 := by unfold scaleT; norm_num
  set p150 : ℝ := ((960700000 : ℝ) ^ n150) ^ 2
  set q150 : ℝ := ((982521027 : ℝ) ^ n150) ^ 2
  have hpow300 : ((9607 / 10000 : ℝ) / (982521027 / 1000000000 : ℝ)) ^ n300 = p150 / q150 := by
    have h0 : (9607 / 10000 : ℝ) / (982521027 / 1000000000 : ℝ) = 960700000 / 982521027 := by norm_num
    rw [h0, div_pow, hmul, pow_mul, pow_mul]
  have hj_nat : (18418926643 : ℝ) * p150 * 1000000000 ≤
      3750000000 * ((jUbNum : ℝ) - 982521028) * q150 := by
    have hsub : 982521028 ≤ jUbNum := by unfold jUbNum; norm_num
    have h0 : ((18418926643 * (960700000 ^ n150) ^ 2 * scaleT : ℕ) : ℝ) ≤
        ((3750000000 * (jUbNum - 982521028) * (982521027 ^ n150) ^ 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hj_check
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hsub, Nat.cast_ofNat, hscale, p150, q150] using h0
  have hq_pos : 0 < q150 := by dsimp [q150]; positivity
  have hden : 0 < (3750000000 : ℝ) * q150 * 1000000000 := by positivity
  rw [hpow300, hscale, ← sub_nonneg]
  have hdiff : (jUbNum : ℝ) / 1000000000 -
        (982521028 / 1000000000 +
          (8 * (27182818286 / 10000000000) / 6 + 2 * (2 + 1 / 100) / 3 * (9607 / 10000)) *
            (p150 / q150)) =
      (3750000000 * ((jUbNum : ℝ) - 982521028) * q150 -
        18418926643 * p150 * 1000000000) /
        (3750000000 * q150 * 1000000000) := by
    field_simp [hq_pos.ne']; ring
  rw [hdiff]
  exact div_nonneg (sub_nonneg.mpr hj_nat) hden.le

private lemma J_bjs_302_le_aux (n150 n300 : ℕ) (hmul : n300 = n150 * 2) (hn300 : n300 = 300)
    (hj_check : 18418926643 * (960700000 ^ n150) ^ 2 * scaleT ≤
      3750000000 * (jUbNum - 982521028) * (982521027 ^ n150) ^ 2) :
    J_bjs (1 / 100 : ℝ) 302 ≤ (jUbNum : ℝ) / (scaleT : ℝ) := by
  have hg2_gt : (12214027 / 10000000 : ℝ) < gammaBJS 2 := by rw [gammaBJS_two]; exact exp_one_fifth_gt
  have hr_lb : (982521027 / 1000000000 : ℝ) < kappa2 + (gammaBJS 2 + kappa2) * (1 / 100 : ℝ) := by
    unfold kappa2; linarith
  have hr_ub : kappa2 + (gammaBJS 2 + kappa2) * (1 / 100 : ℝ) < (982521028 / 1000000000 : ℝ) := by
    unfold kappa2; linarith [gammaBJS_two ▸ exp_one_fifth_lt]
  set r := kappa2 + (gammaBJS 2 + kappa2) * (1 / 100 : ℝ)
  have hratio_le : kappa2 / r ≤ (9607 / 10000 : ℝ) / (982521027 / 1000000000 : ℝ) := by
    unfold kappa2
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr_lb.le
  have hpow : (kappa2 / r) ^ n300 ≤ ((9607 / 10000 : ℝ) / (982521027 / 1000000000 : ℝ)) ^ n300 :=
    pow_le_pow_left₀ (by unfold kappa2; positivity) hratio_le n300
  have hrew : kappa2 ^ (n300 + 1) / r ^ n300 = kappa2 * (kappa2 / r) ^ n300 := by
    rw [pow_succ', div_pow, mul_div_assoc]
  unfold J_bjs
  dsimp only [r]
  rw [show (302 : ℕ) - 2 = n300 by omega, show (302 : ℕ) - 1 = n300 + 1 by omega, hrew]
  have he1 := exp_one_lt_d9'
  have hnum_ub := j_pow300_ub_aux n150 n300 hmul hj_check
  set K : ℝ := (kappa2 / r) ^ n300
  have hK_nn : 0 ≤ K := by dsimp [K]; unfold kappa2; positivity
  calc r + 8 * Real.exp 1 / 6 * K + 2 * (2 + 1 / 100) / 3 * (kappa2 * K)
      = r + (8 * Real.exp 1 / 6 + 2 * (2 + 1 / 100) / 3 * kappa2) * K := by
        rw [add_assoc, ← mul_assoc, ← add_mul]
    _ ≤ (982521028 / 1000000000 : ℝ) +
          (8 * (27182818286 / 10000000000 : ℝ) / 6 + 2 * (2 + 1 / 100 : ℝ) / 3 * (9607 / 10000 : ℝ)) *
            ((9607 / 10000 : ℝ) / (982521027 / 1000000000 : ℝ)) ^ n300 := by
        unfold kappa2
        refine add_le_add hr_ub.le (mul_le_mul ?_ hpow hK_nn ?_)
        · linarith
        · norm_num
    _ ≤ (jUbNum : ℝ) / (scaleT : ℝ) := hnum_ub

private lemma J_bjs_302_le : J_bjs (1 / 100 : ℝ) 302 ≤ (jUbNum : ℝ) / (scaleT : ℝ) :=
  J_bjs_302_le_aux 150 300 rfl rfl jPow300_check

theorem C2_bjs_certified_nonneg : 0 ≤ C2_bjs certifiedDecaySeq (1 / 100 : ℝ) := by
  have hc_nn : ∀ n, 1 ≤ n → 0 ≤ certifiedDecaySeq n := fun n _ => by
    unfold certifiedDecaySeq; positivity
  exact tsum_nonneg fun k => tauBJS_nonneg (by norm_num) hc_nn _

private lemma sum_even_tau_range (xs : List (ℕ × ℕ × ℕ)) (hlen : xs.length = 300)
    (htau : ∀ k, k < xs.length →
      tauBJS certifiedDecaySeq (1 / 100) (2 + k) ≤ ((xs.getD k (0, 0, 0)).1 : ℝ) / (scaleT : ℝ))
    (hsum : (∑ k ∈ Finset.range xs.length,
      (if (2 + k) % 2 = 0 ∧ 2 + k ≤ 2 * keTail then (xs.getD k (0, 0, 0)).1 else 0)) =
      sumEvenTau 2 xs) :
    (∑ k ∈ Finset.range keTail, tauBJS certifiedDecaySeq (1 / 100) (2 * (k + 1))) ≤
      (sumEvenTau 2 xs : ℝ) / (scaleT : ℝ) := by
  have hst : (0 : ℝ) < (scaleT : ℝ) := by unfold scaleT; norm_num
  have hle_sum : ∑ k ∈ Finset.range keTail, tauBJS certifiedDecaySeq (1 / 100) (2 * (k + 1)) ≤
      ∑ k ∈ Finset.range 150, ((xs.getD (2 * k) (0, 0, 0)).1 : ℝ) / (scaleT : ℝ) := by
    unfold keTail
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_range] at hk
    have h2k := htau (2 * k) (by rw [hlen]; omega)
    rwa [show 2 + 2 * k = 2 * (k + 1) by omega] at h2k
  have hsplit : (∑ k ∈ Finset.range 150, ((xs.getD (2 * k) (0, 0, 0)).1 : ℝ) / (scaleT : ℝ)) =
      ∑ k ∈ (Finset.range 300).filter (fun k => (2 + k) % 2 = 0 ∧ 2 + k ≤ 2 * keTail),
        ((xs.getD k (0, 0, 0)).1 : ℝ) / (scaleT : ℝ) := by
    refine Finset.sum_bij (fun j _ => 2 * j) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range]; rw [Finset.mem_range] at hj
      unfold keTail; exact ⟨by omega, by omega, by omega⟩
    · intro a _ b _ hab; omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk; unfold keTail at hk
      exact ⟨k / 2, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j _; rfl
  have hcast : (∑ k ∈ (Finset.range 300).filter (fun k => (2 + k) % 2 = 0 ∧ 2 + k ≤ 2 * keTail),
        ((xs.getD k (0, 0, 0)).1 : ℝ) / (scaleT : ℝ)) =
      (sumEvenTau 2 xs : ℝ) / (scaleT : ℝ) := by
    rw [Finset.sum_filter]
    have hite : (∑ k ∈ Finset.range 300,
          (if (2 + k) % 2 = 0 ∧ 2 + k ≤ 2 * keTail then ((xs.getD k (0, 0, 0)).1 : ℝ) / (scaleT : ℝ) else 0)) =
        ∑ k ∈ Finset.range 300,
          ((if (2 + k) % 2 = 0 ∧ 2 + k ≤ 2 * keTail then (xs.getD k (0, 0, 0)).1 else 0 : ℕ) : ℝ) / (scaleT : ℝ) :=
      Finset.sum_congr rfl fun k _ => by split_ifs <;> [rfl; simp only [Nat.cast_zero, zero_div]]
    rw [hite, ← Finset.sum_div, ← Nat.cast_sum, ← hlen, hsum]
  exact hle_sum.trans (hsplit.trans hcast).le

private lemma C2_bjs_certified_le_aux (hc : ValidDecaySeq certifiedDecaySeq)
    (xs : List (ℕ × ℕ × ℕ)) (hlen : xs.length = 300)
    (hchk : checkTauList 2 (3 * scaleT) (3 * scaleT) scaleT xs = true)
    (htot_nat : sumEvenTau 2 xs * (scaleT ^ 2 - jUbNum ^ 2) +
      (xs.getD 299 (0, 0, 0)).2.1 * jUbNum * scaleT ≤
      494 * scaleT * (scaleT ^ 2 - jUbNum ^ 2))
    (J : ℝ) (hJ_eq : J = J_bjs (1 / 100 : ℝ) 302) (hJ_nn : 0 ≤ J)
    (hJ_ub : J ≤ (jUbNum : ℝ) / (scaleT : ℝ)) :
    C2_bjs certifiedDecaySeq (1 / 100 : ℝ) ≤ C2_certified_ub := by
  have hε0 : (0 : ℝ) < (1 / 100 : ℝ) := by norm_num
  have hε : (1 / 100 : ℝ) ≤ 1 / 74 := by norm_num
  have hJu : (jUbNum : ℝ) / (scaleT : ℝ) < 1 := by unfold jUbNum scaleT; norm_num
  have hJ_lt : J < 1 := lt_of_le_of_lt hJ_ub hJu
  have htail := C2_bjs_le_tail hε0 hε hc (k_e := keTail) (by unfold keTail; norm_num)
    (by rw [show 2 * keTail + 2 = 302 by unfold keTail; norm_num, ← hJ_eq]; exact hJ_lt)
  rw [show 2 * keTail + 2 = 302 by unfold keTail; norm_num, ← hJ_eq] at htail
  have htau := tauList_sound 2 (3 * scaleT) (3 * scaleT) scaleT xs (by norm_num) hchk
    (by unfold scaleT; rw [tauBJS_one]; norm_num) (by unfold scaleT; rw [tauPrimeBJS_one]; norm_num)
    (by unfold scaleT; norm_num)
  have hst : (0 : ℝ) < (scaleT : ℝ) := by unfold scaleT; norm_num
  have hsum_le : (∑ k ∈ Finset.range keTail, tauBJS certifiedDecaySeq (1 / 100) (2 * (k + 1))) ≤
      (sumEvenTau 2 xs : ℝ) / (scaleT : ℝ) :=
    sum_even_tau_range xs hlen (fun k hk => (htau.1 k hk).1) htau.2
  have htp_le : tauPrimeBJS certifiedDecaySeq (1 / 100) (2 * keTail + 1) ≤
      ((xs.getD 299 (0, 0, 0)).2.1 : ℝ) / (scaleT : ℝ) := by
    have h299 := (htau.1 299 (by rw [hlen]; omega)).2
    rwa [show 2 + 299 = 2 * keTail + 1 by unfold keTail; norm_num] at h299
  have hJ2_lt : J ^ 2 < 1 := by
    have hmul : J * J ≤ J := by simpa using mul_le_mul_of_nonneg_right hJ_lt.le hJ_nn
    rw [sq]; linarith
  have h1mJ2_pos : 0 < 1 - J ^ 2 := sub_pos.mpr hJ2_lt
  have hgeom : ∑' n : ℕ, J ^ (2 * n + 1) = J / (1 - J ^ 2) := by
    have hrew : (fun n : ℕ => J ^ (2 * n + 1)) = fun n : ℕ => J * (J ^ 2) ^ n := by
      ext n; rw [pow_add, pow_one, pow_mul]; ring
    rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg J) hJ2_lt, div_eq_mul_inv]
  have hJ_div : J / (1 - J ^ 2) ≤ ((jUbNum : ℝ) * (scaleT : ℝ)) / ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2) := by
    have hJu2_lt : ((jUbNum : ℝ) / (scaleT : ℝ)) ^ 2 < 1 := by unfold jUbNum scaleT; norm_num
    have h1mJu2_pos : 0 < 1 - ((jUbNum : ℝ) / (scaleT : ℝ)) ^ 2 := sub_pos.mpr hJu2_lt
    have hJ2_le : J ^ 2 ≤ ((jUbNum : ℝ) / (scaleT : ℝ)) ^ 2 := pow_le_pow_left₀ hJ_nn hJ_ub 2
    have hmono : J / (1 - J ^ 2) ≤ ((jUbNum : ℝ) / (scaleT : ℝ)) / (1 - ((jUbNum : ℝ) / (scaleT : ℝ)) ^ 2) :=
      div_le_div₀ (div_nonneg (Nat.cast_nonneg _) hst.le) hJ_ub h1mJu2_pos (sub_le_sub_left hJ2_le 1)
    have heq : ((jUbNum : ℝ) / (scaleT : ℝ)) / (1 - ((jUbNum : ℝ) / (scaleT : ℝ)) ^ 2) =
        ((jUbNum : ℝ) * (scaleT : ℝ)) / ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2) := by
      have hden2 : (scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2 ≠ 0 := by unfold scaleT jUbNum; norm_num
      field_simp [hst.ne', hden2]
    exact hmono.trans_eq heq
  have hden_pos : 0 < (scaleT : ℝ) * ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2) := by
    unfold scaleT jUbNum; norm_num
  have htot : (sumEvenTau 2 xs : ℝ) / (scaleT : ℝ) +
      ((xs.getD 299 (0, 0, 0)).2.1 : ℝ) / (scaleT : ℝ) *
        (((jUbNum : ℝ) * (scaleT : ℝ)) / ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2)) ≤ C2_certified_ub := by
    have hsq : jUbNum ^ 2 ≤ scaleT ^ 2 := by unfold jUbNum scaleT; norm_num
    have hnat : (sumEvenTau 2 xs : ℝ) * ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2) +
        ((xs.getD 299 (0, 0, 0)).2.1 : ℝ) * (jUbNum : ℝ) * (scaleT : ℝ) ≤
        494 * (scaleT : ℝ) * ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2) := by
      have hle : ((sumEvenTau 2 xs * (scaleT ^ 2 - jUbNum ^ 2) +
          (xs.getD 299 (0, 0, 0)).2.1 * jUbNum * scaleT : ℕ) : ℝ) ≤
          ((494 * scaleT * (scaleT ^ 2 - jUbNum ^ 2) : ℕ) : ℝ) := Nat.cast_le.mpr htot_nat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsq, Nat.cast_pow, Nat.cast_ofNat] using hle
    unfold C2_certified_ub; rw [← sub_nonneg]
    have hdiff : (494 : ℝ) - ((sumEvenTau 2 xs : ℝ) / (scaleT : ℝ) +
          ((xs.getD 299 (0, 0, 0)).2.1 : ℝ) / (scaleT : ℝ) *
            (((jUbNum : ℝ) * (scaleT : ℝ)) / ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2))) =
        (494 * (scaleT : ℝ) * ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2) -
          ((sumEvenTau 2 xs : ℝ) * ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2) +
            ((xs.getD 299 (0, 0, 0)).2.1 : ℝ) * (jUbNum : ℝ) * (scaleT : ℝ))) /
          ((scaleT : ℝ) * ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2)) := by
      have hden2 : (scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2 ≠ 0 := by unfold scaleT jUbNum; norm_num
      field_simp [hst.ne', hden2]
    rw [hdiff]; exact div_nonneg (sub_nonneg.mpr hnat) hden_pos.le
  calc C2_bjs certifiedDecaySeq (1 / 100)
      ≤ (∑ k ∈ Finset.range keTail, tauBJS certifiedDecaySeq (1 / 100) (2 * (k + 1))) +
          tauPrimeBJS certifiedDecaySeq (1 / 100) (2 * keTail + 1) * ∑' n : ℕ, J ^ (2 * n + 1) := htail
    _ = (∑ k ∈ Finset.range keTail, tauBJS certifiedDecaySeq (1 / 100) (2 * (k + 1))) +
          tauPrimeBJS certifiedDecaySeq (1 / 100) (2 * keTail + 1) * (J / (1 - J ^ 2)) := by rw [hgeom]
    _ ≤ (sumEvenTau 2 xs : ℝ) / (scaleT : ℝ) +
          ((xs.getD 299 (0, 0, 0)).2.1 : ℝ) / (scaleT : ℝ) *
            (((jUbNum : ℝ) * (scaleT : ℝ)) / ((scaleT : ℝ) ^ 2 - (jUbNum : ℝ) ^ 2)) :=
        add_le_add hsum_le (mul_le_mul htp_le hJ_div (div_nonneg hJ_nn h1mJ2_pos.le)
          (div_nonneg (Nat.cast_nonneg _) hst.le))
    _ ≤ C2_certified_ub := htot

theorem C2_bjs_certified_le : C2_bjs certifiedDecaySeq (1 / 100 : ℝ) ≤ C2_certified_ub :=
  C2_bjs_certified_le_aux validDecaySeq_certified tauTab tauTab_length tauTab_check_ok
    tauTab_total_check (J_bjs (1 / 100 : ℝ) 302) rfl
    (J_bjs_nonneg (by norm_num) (by norm_num) _) J_bjs_302_le

end CertifiedC2

end

end BuchstabSwitching
