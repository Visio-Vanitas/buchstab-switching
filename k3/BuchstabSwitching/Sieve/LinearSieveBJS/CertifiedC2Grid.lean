import BuchstabSwitching.Sieve.LinearSieveBJS.TailConstants
import BuchstabSwitching.Sieve.LinearSieveBJS.CertifiedC2Data

namespace BuchstabSwitching

open MeasureTheory intervalIntegral Set Filter

noncomputable section

/-! ### 5a. Grid Table Soundness and `fHat` Enclosures for `n = 2..10` -/

section CertifiedC2Grid

private lemma listGetD_cons_zero (x : ℕ) (xs : List ℕ) (d : ℕ) : listGetD (x :: xs) 0 d = x := rfl
private lemma listGetD_cons_succ (x : ℕ) (xs : List ℕ) (i d : ℕ) :
    listGetD (x :: xs) (i + 1) d = listGetD xs i d := rfl
private lemma listGetD_nil (i d : ℕ) : listGetD [] i d = d := by cases i <;> rfl

private lemma listGetD_append_left (xs ys : List ℕ) (i d : ℕ) (hi : i < xs.length) :
    listGetD (xs ++ ys) i d = listGetD xs i d := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rcases i with _ | i
    · rfl
    · exact ih i (by simpa using hi)

private lemma listGetD_append_right (xs ys : List ℕ) (i d : ℕ) (hi : xs.length ≤ i) :
    listGetD (xs ++ ys) i d = listGetD ys (i - xs.length) d := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    rcases i with _ | i
    · simp at hi
    · rw [List.cons_append, listGetD_cons_succ, List.length_cons, Nat.add_sub_add_right]
      exact ih i (by simpa using hi)

private lemma listGetD_replicate (n a i d : ℕ) (hi : i < n) :
    listGetD (List.replicate n a) i d = a := by
  induction n generalizing i with
  | zero => omega
  | succ n ih => cases i with | zero => rfl | succ i => exact ih i (by omega)

private lemma listGetD_map_range (n : ℕ) (f : ℕ → ℕ) (i d : ℕ) (hi : i < n) :
    listGetD ((List.range n).map f) i d = f i := by
  have h1 : i < ((List.range n).map f).length := by simp; omega
  have h2 : ∀ (xs : List ℕ) (j : ℕ) (hj : j < xs.length), listGetD xs j d = xs[j] := by
    intro xs
    induction xs with
    | nil => intro j hj; simp at hj
    | cons x xs ih => intro j hj; cases j with | zero => rfl | succ j => exact ih j (by simpa using hj)
  rw [h2 _ i h1, List.getElem_map, List.getElem_range]

private lemma listGetD_drop (xs : List ℕ) (off i d : ℕ) :
    listGetD (xs.drop off) i d = listGetD xs (off + i) d := by
  induction xs generalizing off with
  | nil => simp [listGetD_nil]
  | cons x xs ih =>
    rcases off with _ | off
    · simp
    · simp only [List.drop_succ_cons, Nat.succ_add, listGetD_cons_succ]; exact ih off

private lemma buildPwListAux_length (m k : ℕ) : (buildPwListAux m k).length = m := by
  induction m generalizing k <;> simp [buildPwListAux, *]

private lemma buildPwListAux_getD (m p i : ℕ) (hi : i < m) :
    listGetD (buildPwListAux m p) i 0 = pwVal (p + i + 1) := by
  induction m generalizing p i with
  | zero => omega
  | succ m ih =>
    rcases i with _ | i
    · dsimp only [buildPwListAux]; rw [listGetD_cons_zero]
    · dsimp only [buildPwListAux]
      rw [listGetD_cons_succ, ih (p + 1) i (by omega), show p + 1 + i + 1 = p + (i + 1) + 1 by omega]

private lemma buildPwFast_eq_aux (m p : ℕ) :
    buildPwFast m (pwVal p) = buildPwListAux m p := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    dsimp only [buildPwFast, buildPwListAux]
    have h1 : pwStep (pwVal p) = pwVal (p + 1) := rfl
    rw [h1, ih (p + 1)]

private lemma uNextR_length (j : ℕ) (xs : List ℕ) : (uNextR j xs).length = xs.length := by
  induction xs generalizing j <;> simp [uNextR, *]

private lemma uNextR_getD (j : ℕ) (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    listGetD (uNextR j xs) k 0 =
      (if j + k ≤ 2 * gridG then ceilDiv (listGetD xs k 0) 2
       else ceilDiv (listGetD xs k 0 * (gridG + (j + k))) (6 * gridG)) := by
  induction xs generalizing j k with
  | nil => simp at hk
  | cons x xs ih =>
    rcases k with _ | k
    · dsimp only [uNextR]; rw [listGetD_cons_zero, listGetD_cons_zero]; rfl
    · dsimp only [uNextR]
      rw [listGetD_cons_succ, listGetD_cons_succ, ih (j + 1) k (by simpa using hk),
        show j + 1 + k = j + (k + 1) by omega]

private lemma buildRList_length (jmax : ℕ) (hj : gridG ≤ jmax) : (buildRList jmax).length = jmax + 1 := by
  unfold buildRList
  rw [List.length_append, List.length_replicate, uNextR_length,
    show buildPwFast (jmax - gridG) scaleF = buildPwListAux (jmax - gridG) 0 from
      buildPwFast_eq_aux (jmax - gridG) 0, buildPwListAux_length]
  omega

private lemma buildRList_getD (jmax j : ℕ) (hj : j ≤ jmax) :
    listGetD (buildRList jmax) j 0 = rVal j := by
  unfold buildRList rVal
  by_cases hjG : j ≤ gridG
  · simp only [hjG, ↓reduceIte]
    rw [listGetD_append_left _ _ j 0 (by rw [List.length_replicate]; omega),
      listGetD_replicate _ _ j 0 (by omega)]
  · have hj_gt : gridG < j := Nat.lt_of_not_le hjG
    simp only [hjG, ↓reduceIte]
    rw [listGetD_append_right _ _ j 0 (by rw [List.length_replicate]; omega),
      List.length_replicate,
      show buildPwFast (jmax - gridG) scaleF = buildPwListAux (jmax - gridG) 0 from
        buildPwFast_eq_aux (jmax - gridG) 0]
    have hk_lt : j - (gridG + 1) < (buildPwListAux (jmax - gridG) 0).length := by
      rw [buildPwListAux_length]; omega
    rw [uNextR_getD (gridG + 1) _ (j - (gridG + 1)) hk_lt,
      buildPwListAux_getD (jmax - gridG) 0 (j - (gridG + 1)) (by omega)]
    have hid1 : gridG + 1 + (j - (gridG + 1)) = j := by omega
    have hid2 : 0 + (j - (gridG + 1)) + 1 = j - gridG := by omega
    rw [hid1, hid2]

private lemma suffixSums_length (xs : List ℕ) : (suffixSums xs).length = xs.length := by
  induction xs <;> simp [suffixSums, *]

private lemma suffixSums_headD (xs : List ℕ) : (suffixSums xs).headD 0 = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [suffixSums]
    rw [List.headD_cons, ih, List.sum_cons]

private lemma suffixSums_getD (xs : List ℕ) (i : ℕ) :
    listGetD (suffixSums xs) i 0 = (xs.drop i).sum := by
  induction xs generalizing i with
  | nil => simp [suffixSums, listGetD_nil]
  | cons x xs ih =>
    rcases i with _ | i
    · dsimp only [suffixSums]
      rw [listGetD_cons_zero, suffixSums_headD, List.drop_zero, List.sum_cons]
    · dsimp only [suffixSums]
      rw [listGetD_cons_succ, List.drop_succ_cons]
      exact ih i

private lemma uNextEvenAux_length (k : ℕ) (xs : List ℕ) :
    (uNextEvenAux k xs).length = xs.length := by
  induction xs generalizing k <;> simp [uNextEvenAux, *]

private lemma uNextEvenAux_getD (k : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    listGetD (uNextEvenAux k xs) i 0 = ceilDiv (listGetD xs i 0) (k + i) := by
  induction xs generalizing k i with
  | nil => simp at hi
  | cons x xs ih =>
    rcases i with _ | i
    · dsimp only [uNextEvenAux]
      rw [listGetD_cons_zero, listGetD_cons_zero, Nat.add_zero]
    · dsimp only [uNextEvenAux]
      rw [listGetD_cons_succ, listGetD_cons_succ, ih (k + 1) i (by simpa using hi),
        show k + 1 + i = k + (i + 1) by omega]

private lemma ceilDiv_getD_le_zipMaxScaled (us rs : List ℕ) (i : ℕ)
    (hu : i < us.length) (hr : i < rs.length) :
    ceilDiv (listGetD us i 0 * listGetD rs i 0) scaleF ≤ zipMaxScaled us rs := by
  induction us generalizing rs i with
  | nil => simp at hu
  | cons u us ih =>
    rcases rs with _ | ⟨r, rs⟩
    · simp at hr
    · rcases i with _ | i
      · simp [zipMaxScaled, listGetD_cons_zero]
      · exact (ih rs i (by simpa using hu) (by simpa using hr)).trans (le_max_right _ _)

private lemma uListSeq_length : ∀ n, 1 ≤ n → (uListSeq n).length = gridG * (n + 2 - aBase n) + 1
  | 0, hn => by omega
  | 1, _ => by simp [uListSeq, uInit, aBase]; ring
  | n + 2, _ => by
    have ih := uListSeq_length (n + 1) (by omega)
    rw [uListSeq, uNext_eq]
    by_cases hmod : (n + 2) % 2 = 0
    · have hnot : (n + 1) % 2 ≠ 0 := by omega
      simp only [hmod, ↓reduceIte, uNextEvenAux_length, suffixSums_length, ih, aBase, hnot]
      have hid : n + 1 + 2 - 1 = n + 2 + 2 - 2 := by omega
      rw [hid]
    · have hprev : (n + 1) % 2 = 0 := by omega
      simp only [hmod, ↓reduceIte, List.length_append, List.length_map, List.length_range,
        uNextEvenAux_length, suffixSums_length, ih, aBase, hprev]
      have hid1 : n + 1 + 2 - 2 = n + 1 := by omega
      have hid2 : n + 2 + 2 - 1 = n + 3 := by omega
      rw [hid1, hid2]
      ring

private lemma mCertGo_getD (rList : List ℕ) (rem nCur : ℕ) (uCur : List ℕ) (k : ℕ) (hk : k < rem)
    (hu : uCur = uListSeq nCur) (hn : 1 ≤ nCur) :
    listGetD (mCertGo rList rem nCur uCur) k 0 =
      zipMaxScaled (uListSeq (nCur + k + 1))
        (rList.drop (if (nCur + k + 1) % 2 = 0 then gridG + 1 else 1)) := by
  induction rem generalizing nCur uCur k with
  | zero => omega
  | succ rem ih =>
    rcases k with _ | k
    · dsimp only [mCertGo]
      rw [listGetD_cons_zero, Nat.add_zero, hu]
      obtain ⟨m0, rfl⟩ : ∃ m0, nCur = m0 + 1 := ⟨nCur - 1, by omega⟩
      rfl
    · dsimp only [mCertGo]
      rw [listGetD_cons_succ]
      have hnext : uNext (nCur + 1) uCur = uListSeq (nCur + 1) := by
        rw [hu]
        obtain ⟨m0, rfl⟩ : ∃ m0, nCur = m0 + 1 := ⟨nCur - 1, by omega⟩
        rfl
      rw [ih (nCur + 1) (uNext (nCur + 1) uCur) k (by omega) hnext (by omega),
        show nCur + 1 + k + 1 = nCur + (k + 1) + 1 by omega]

lemma le_ceilDiv_real (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (ceilDiv a b : ℝ) := by
  have hnat : a ≤ b * ceilDiv a b := by
    unfold ceilDiv
    have hdm := Nat.div_add_mod (a + b - 1) b
    have hml := Nat.mod_lt (a + b - 1) hb
    omega
  rw [div_le_iff₀ (Nat.cast_pos.mpr hb)]
  exact_mod_cast hnat.trans_eq (mul_comm b _)

private lemma exp_one_div_16_lt : Real.exp (1 / 16 : ℝ) < (expStepNum : ℝ) / (scaleF : ℝ) := by
  have hpow : (Real.exp (1 / 16 : ℝ)) ^ 16 < ((expStepNum : ℝ) / (scaleF : ℝ)) ^ 16 := by
    rw [← Real.exp_nat_mul]
    have h1 : ((16 : ℕ) : ℝ) * (1 / 16 : ℝ) = 1 := by norm_num
    rw [h1]
    have hexp : Real.exp 1 < (27182818286 / 10000000000 : ℝ) := exp_one_lt_d9'
    have hnum : (27182818286 / 10000000000 : ℝ) < ((expStepNum : ℝ) / (scaleF : ℝ)) ^ 16 := by
      unfold expStepNum scaleF
      norm_num
    linarith
  exact lt_of_pow_lt_pow_left₀ 16 (by unfold expStepNum scaleF; positivity) hpow

private lemma pwVal_spec (k : ℕ) :
    Real.exp ((k : ℝ) / (gridG : ℝ)) ≤ (pwVal k : ℝ) / (scaleF : ℝ) := by
  induction k with
  | zero => simp [pwVal, scaleF]
  | succ k ih =>
    have hexp : Real.exp (((k + 1 : ℕ) : ℝ) / (gridG : ℝ)) =
        Real.exp ((k : ℝ) / (gridG : ℝ)) * Real.exp (1 / 16 : ℝ) := by
      rw [← Real.exp_add]; congr 1; unfold gridG; push_cast; ring
    have hstep : (pwVal k : ℝ) / (scaleF : ℝ) * ((expStepNum : ℝ) / (scaleF : ℝ)) ≤
        (pwVal (k + 1) : ℝ) / (scaleF : ℝ) := by
      have hceil := le_ceilDiv_real (pwVal k * expStepNum) scaleF (by unfold scaleF; norm_num)
      have hmul : (pwVal k : ℝ) / (scaleF : ℝ) * ((expStepNum : ℝ) / (scaleF : ℝ)) =
          ((pwVal k * expStepNum : ℕ) : ℝ) / (scaleF : ℝ) / (scaleF : ℝ) := by
        push_cast; ring
      rw [hmul]
      have hsf : (0 : ℝ) < (scaleF : ℝ) := by unfold scaleF; norm_num
      exact div_le_div_of_nonneg_right hceil hsf.le
    calc Real.exp (((k + 1 : ℕ) : ℝ) / (gridG : ℝ))
        = Real.exp ((k : ℝ) / (gridG : ℝ)) * Real.exp (1 / 16 : ℝ) := hexp
      _ ≤ (pwVal k : ℝ) / (scaleF : ℝ) * ((expStepNum : ℝ) / (scaleF : ℝ)) :=
          mul_le_mul ih exp_one_div_16_lt.le (Real.exp_pos _).le (by positivity)
      _ ≤ (pwVal (k + 1) : ℝ) / (scaleF : ℝ) := hstep

private lemma rVal_spec (j : ℕ) (hj1 : 1 ≤ j) {s : ℝ}
    (hs_lo : 1 + ((j - 1 : ℕ) : ℝ) / (gridG : ℝ) ≤ s)
    (hs_hi : s ≤ 1 + (j : ℝ) / (gridG : ℝ)) :
    1 / (2 * Real.exp 2 * h_bjs s) ≤ (rVal j : ℝ) / (scaleF : ℝ) := by
  have hsf : (0 : ℝ) < (scaleF : ℝ) := by unfold scaleF; norm_num
  by_cases hjG : j ≤ gridG
  · have hs2 : s ≤ 2 := by
      have : 1 + (j : ℝ) / (gridG : ℝ) ≤ 2 := by
        unfold gridG
        have : (j : ℝ) ≤ 16 := by exact_mod_cast hjG
        linarith
      linarith
    rw [h_bjs_of_le_two hs2]
    have hlhs : 1 / (2 * Real.exp 2 * Real.exp (-2)) = (1 / 2 : ℝ) := by
      have : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
      rw [mul_assoc, this, mul_one]
    rw [hlhs, rVal]
    simp only [hjG, ↓reduceIte]
    unfold scaleF
    norm_num
  · have hj_gt : gridG < j := Nat.lt_of_not_le hjG
    have hs2 : 2 ≤ s := by
      have h1 : (2 : ℝ) ≤ 1 + ((j - 1 : ℕ) : ℝ) / (gridG : ℝ) := by
        unfold gridG
        have : (16 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show gridG ≤ j - 1 by unfold gridG at hj_gt ⊢; omega)
        linarith
      linarith
    have hexp_s : Real.exp (s - 2) ≤ (pwVal (j - gridG) : ℝ) / (scaleF : ℝ) := by
      have hs_sub : s - 2 ≤ ((j - gridG : ℕ) : ℝ) / (gridG : ℝ) := by
        have hj_cast : ((j - gridG : ℕ) : ℝ) = (j : ℝ) - (gridG : ℝ) := by
          rw [Nat.cast_sub hj_gt.le]
        rw [hj_cast]
        unfold gridG at *
        linarith
      exact (Real.exp_le_exp.mpr hs_sub).trans (pwVal_spec (j - gridG))
    by_cases hj2G : j ≤ 2 * gridG
    · have hs3 : s ≤ 3 := by
        have : 1 + (j : ℝ) / (gridG : ℝ) ≤ 3 := by
          unfold gridG at *
          have : (j : ℝ) ≤ 32 := by exact_mod_cast hj2G
          linarith
        linarith
      rw [h_bjs_of_two_to_three hs2 hs3]
      have hlhs : 1 / (2 * Real.exp 2 * Real.exp (-s)) = Real.exp (s - 2) / 2 := by
        have h : Real.exp 2 * Real.exp (-s) = (Real.exp (s - 2))⁻¹ := by
          rw [← Real.exp_add, ← Real.exp_neg]; congr 1; ring
        rw [mul_assoc, h, div_eq_mul_inv, mul_inv, inv_inv, one_mul, mul_comm, ← div_eq_mul_inv]
      rw [hlhs, rVal]
      simp only [hjG, hj2G, ↓reduceIte]
      have hceil := le_ceilDiv_real (pwVal (j - gridG)) 2 (by norm_num)
      calc Real.exp (s - 2) / 2
          ≤ ((pwVal (j - gridG) : ℝ) / (scaleF : ℝ)) / 2 := by linarith
        _ = ((pwVal (j - gridG) : ℝ) / 2) / (scaleF : ℝ) := by ring
        _ ≤ (ceilDiv (pwVal (j - gridG)) 2 : ℝ) / (scaleF : ℝ) :=
            div_le_div_of_nonneg_right hceil hsf.le
    · have hj_gt2 : 2 * gridG < j := Nat.lt_of_not_le hj2G
      have hs3 : 3 ≤ s := by
        have : (3 : ℝ) ≤ 1 + ((j - 1 : ℕ) : ℝ) / (gridG : ℝ) := by
          unfold gridG at *
          have : (32 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (show 32 ≤ j - 1 by omega)
          linarith
        linarith
      rw [h_bjs_of_three_le hs3]
      have hs0 : 0 < s := by linarith
      have hlhs : 1 / (2 * Real.exp 2 * ((3 / s) * Real.exp (-s))) =
          (s / 6) * Real.exp (s - 2) := by
        have hexp : Real.exp 2 * Real.exp (-s) = (Real.exp (s - 2))⁻¹ := by
          rw [← Real.exp_add, ← Real.exp_neg]; congr 1; ring
        have he_ne : Real.exp (s - 2) ≠ 0 := (Real.exp_pos _).ne'
        calc 1 / (2 * Real.exp 2 * ((3 / s) * Real.exp (-s)))
            = 1 / (6 / s * (Real.exp 2 * Real.exp (-s))) := by ring
          _ = 1 / (6 / s * (Real.exp (s - 2))⁻¹) := by rw [hexp]
          _ = (s / 6) * Real.exp (s - 2) := by field_simp [hs0.ne', he_ne]
      rw [hlhs, rVal]
      simp only [hjG, hj2G, ↓reduceIte]
      have hs_ub : s / 6 ≤ ((gridG + j : ℕ) : ℝ) / (6 * (gridG : ℝ)) := by
        have h1 : s ≤ ((gridG + j : ℕ) : ℝ) / (gridG : ℝ) := by
          push_cast; unfold gridG at *; linarith
        calc s / 6 ≤ (((gridG + j : ℕ) : ℝ) / (gridG : ℝ)) / 6 := by linarith
          _ = ((gridG + j : ℕ) : ℝ) / (6 * (gridG : ℝ)) := by ring
      have hceil := le_ceilDiv_real (pwVal (j - gridG) * (gridG + j)) (6 * gridG)
        (by unfold gridG; norm_num)
      calc (s / 6) * Real.exp (s - 2)
          ≤ (((gridG + j : ℕ) : ℝ) / (6 * (gridG : ℝ))) * ((pwVal (j - gridG) : ℝ) / (scaleF : ℝ)) :=
            mul_le_mul hs_ub hexp_s (Real.exp_pos _).le (by positivity)
        _ = ((pwVal (j - gridG) * (gridG + j) : ℕ) : ℝ) / ((6 * gridG : ℕ) : ℝ) / (scaleF : ℝ) := by
            push_cast; ring
        _ ≤ (ceilDiv (pwVal (j - gridG) * (gridG + j)) (6 * gridG) : ℝ) / (scaleF : ℝ) :=
            div_le_div_of_nonneg_right hceil hsf.le

private lemma list_drop_sum_eq (u : List ℕ) (i : ℕ) (hi : i < u.length) :
    (u.drop i).sum = listGetD u i 0 + (u.drop (i + 1)).sum := by
  induction u generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rcases i with _ | i
    · simp [listGetD_cons_zero]
    · simp only [List.drop_succ_cons, listGetD_cons_succ]
      exact ih i (by simpa using hi)

private lemma integral_grid_le {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Set.Ici 1))
    (hf_anti : AntitoneOn f (Set.Ici 1))
    {a : ℝ} (ha1 : 1 ≤ a) (u : List ℕ) (m i : ℕ) (him : i + m ≤ u.length)
    (hgrid : ∀ k, k < i + m → f (a + (k : ℝ) / (gridG : ℝ)) ≤ (listGetD u k 0 : ℝ) / (scaleF : ℝ)) :
    ∫ t in (a + (i : ℝ) / (gridG : ℝ))..(a + ((i + m : ℕ) : ℝ) / (gridG : ℝ)), f t ≤
      ((u.drop i).sum : ℝ) / ((gridG : ℝ) * (scaleF : ℝ)) := by
  induction m generalizing i with
  | zero =>
    simp only [Nat.add_zero, intervalIntegral.integral_same]
    positivity
  | succ m ih =>
    have hg : (0 : ℝ) < (gridG : ℝ) := by unfold gridG; norm_num
    have hsf : (0 : ℝ) < (scaleF : ℝ) := by unfold scaleF; norm_num
    have hi_lt : i < u.length := by omega
    let x0 : ℝ := a + (i : ℝ) / (gridG : ℝ)
    let x1 : ℝ := a + ((i + 1 : ℕ) : ℝ) / (gridG : ℝ)
    let x2 : ℝ := a + ((i + 1 + m : ℕ) : ℝ) / (gridG : ℝ)
    have hx01 : x0 ≤ x1 := by dsimp [x0, x1]; push_cast; gcongr; norm_num
    have hx12 : x1 ≤ x2 := by
      dsimp [x1, x2]
      have h12 : ((i + 1 : ℕ) : ℝ) ≤ ((i + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ i + 1 + m)
      linarith [div_le_div_of_nonneg_right h12 hg.le]
    have hint1 : IntervalIntegrable f volume x0 x1 := by
      refine (hf_cont.mono fun t ht => ?_).intervalIntegrable
      rw [uIcc_of_le hx01] at ht
      simp only [Set.mem_Ici]
      have hx0_ge : 1 ≤ x0 := by dsimp [x0]; linarith [show (0 : ℝ) ≤ (i : ℝ) / (gridG : ℝ) by positivity]
      linarith [ht.1]
    have hint2 : IntervalIntegrable f volume x1 x2 := by
      refine (hf_cont.mono fun t ht => ?_).intervalIntegrable
      rw [uIcc_of_le hx12] at ht
      simp only [Set.mem_Ici]
      have hx1_ge : 1 ≤ x1 := by
        dsimp [x1]; linarith [show (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) / (gridG : ℝ) by positivity]
      linarith [ht.1]
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hstep1 : ∫ t in x0..x1, f t ≤ (listGetD u i 0 : ℝ) / ((gridG : ℝ) * (scaleF : ℝ)) := by
      have hconst : ∫ _ in x0..x1, ((listGetD u i 0 : ℝ) / (scaleF : ℝ)) =
          (listGetD u i 0 : ℝ) / ((gridG : ℝ) * (scaleF : ℝ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        have hdiff : x1 - x0 = 1 / (gridG : ℝ) := by dsimp [x0, x1]; push_cast; ring
        rw [hdiff]; ring
      rw [← hconst]
      refine intervalIntegral.integral_mono_on hx01 hint1 intervalIntegrable_const fun t ht => ?_
      have hx0_mem : x0 ∈ Set.Ici (1 : ℝ) := by
        simp only [Set.mem_Ici, x0]
        linarith [show (0 : ℝ) ≤ (i : ℝ) / (gridG : ℝ) by positivity]
      have ht_mem : t ∈ Set.Ici (1 : ℝ) := by
        simp only [Set.mem_Ici] at hx0_mem ⊢; linarith [ht.1]
      exact (hf_anti hx0_mem ht_mem ht.1).trans (hgrid i (by omega))
    have hstep2 : ∫ t in x1..x2, f t ≤ ((u.drop (i + 1)).sum : ℝ) / ((gridG : ℝ) * (scaleF : ℝ)) := by
      have hih := ih (i + 1) (by omega) (fun k hk => hgrid k (by omega))
      simpa only [x1, x2, show i + (m + 1) = i + 1 + m by omega, Nat.add_assoc] using hih
    have hsum_eq : (u.drop i).sum = listGetD u i 0 + (u.drop (i + 1)).sum :=
      list_drop_sum_eq u i hi_lt
    have hrew : a + ((i + (m + 1) : ℕ) : ℝ) / (gridG : ℝ) = x2 := by
      dsimp [x2]; congr 2; exact_mod_cast show i + (m + 1) = i + 1 + m by omega
    rw [show a + (i : ℝ) / (gridG : ℝ) = x0 from rfl, hrew, ← hadd, hsum_eq, Nat.cast_add, add_div]
    linarith

private lemma uListSeq_spec : ∀ n, 1 ≤ n → ∀ i, i < (uListSeq n).length →
    fHat n ((aBase n : ℝ) + (i : ℝ) / (gridG : ℝ)) ≤ (listGetD (uListSeq n) i 0 : ℝ) / (scaleF : ℝ)
  | 0, hn, _, _ => by omega
  | 1, _, i, hi => by
    have hlen : (uListSeq 1).length = 2 * gridG + 1 := by simp [uListSeq, uInit]
    rw [hlen] at hi
    have hbase : aBase 1 = 1 := by simp [aBase]
    rw [hbase, Nat.cast_one]
    have hs1 : 1 ≤ (1 : ℝ) + (i : ℝ) / (gridG : ℝ) := by
      have : (0 : ℝ) ≤ (i : ℝ) / (gridG : ℝ) := by unfold gridG; positivity
      linarith
    have hs3 : (1 : ℝ) + (i : ℝ) / (gridG : ℝ) ≤ 3 := by
      unfold gridG at hi ⊢
      have hi' : (i : ℝ) ≤ 32 := by exact_mod_cast (show i ≤ 32 by omega)
      linarith
    rw [fHat_one_of_Icc hs1 hs3, uListSeq, uInit, listGetD_map_range (2 * gridG + 1) _ i 0 hi]
    have hdiv : (3 - ((1 : ℝ) + (i : ℝ) / (gridG : ℝ))) / ((1 : ℝ) + (i : ℝ) / (gridG : ℝ)) =
        ((scaleF * (2 * gridG - i) : ℕ) : ℝ) / ((gridG + i : ℕ) : ℝ) / (scaleF : ℝ) := by
      have hi_le : i ≤ 2 * gridG := by omega
      rw [Nat.cast_mul, Nat.cast_sub hi_le]
      have hsf : (scaleF : ℝ) ≠ 0 := by unfold scaleF; norm_num
      have hg : (gridG : ℝ) ≠ 0 := by unfold gridG; norm_num
      have hgi : ((gridG + i : ℕ) : ℝ) ≠ 0 := by unfold gridG; positivity
      push_cast
      field_simp [hsf, hg, hgi]
      ring
    rw [hdiv]
    have hceil := le_ceilDiv_real (scaleF * (2 * gridG - i)) (gridG + i) (by unfold gridG; omega)
    exact div_le_div_of_nonneg_right hceil (by unfold scaleF; norm_num)
  | n + 2, _, i, hi => by
    have ih := uListSeq_spec (n + 1) (by omega)
    have hlen_prev := uListSeq_length (n + 1) (by omega)
    have hlen_cur := uListSeq_length (n + 2) (by omega)
    have hg_pos : (0 : ℝ) < (gridG : ℝ) := by unfold gridG; norm_num
    have hsf_pos : (0 : ℝ) < (scaleF : ℝ) := by unfold scaleF; norm_num
    have hcont : ContinuousOn (fHat (n + 1)) (Set.Ici 1) := fHat_continuousOn (n + 1) (by omega)
    have hanti : AntitoneOn (fHat (n + 1)) (Set.Ici 1) := fHat_antitone (n + 1) (by omega)
    by_cases hev : (n + 2) % 2 = 0
    · have hbase2 : aBase (n + 2) = 2 := by simp only [aBase, hev, ↓reduceIte]
      have hnot : (n + 1) % 2 ≠ 0 := by omega
      have hbase1 : aBase (n + 1) = 1 := by simp only [aBase, hnot, ↓reduceIte]
      rw [hbase2, show n + 2 + 2 - 2 = n + 2 by omega] at hlen_cur
      rw [hbase2, Nat.cast_ofNat]
      rw [hbase1, show n + 1 + 2 - 1 = n + 2 by omega] at hlen_prev
      rw [hbase1, Nat.cast_one] at ih
      have hi_lt : i < gridG * (n + 2) + 1 := hi.trans_eq hlen_cur
      rw [uListSeq, uNext_eq]
      simp only [hev, ↓reduceIte]
      have hsuf_len : i < (suffixSums (uListSeq (n + 1))).length := by
        rw [suffixSums_length, hlen_prev]; exact hi_lt
      rw [uNextEvenAux_getD (2 * gridG) _ i hsuf_len, suffixSums_getD]
      by_cases hi_end : i = gridG * (n + 2)
      · have hs_ge : ((n + 2 : ℕ) : ℝ) + 2 ≤ 2 + (i : ℝ) / (gridG : ℝ) := by
          rw [hi_end]; push_cast; unfold gridG; norm_num; linarith
        rw [fHat_support (n + 2) (by omega) hs_ge]
        positivity
      · have hi_strict : i < gridG * (n + 2) := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi_lt) hi_end
        have hev' : Even (n + 2) := Nat.even_iff.mpr hev
        have hs2 : 2 ≤ (2 : ℝ) + (i : ℝ) / (gridG : ℝ) := by
          linarith [show (0 : ℝ) ≤ (i : ℝ) / (gridG : ℝ) by positivity]
        have htail := (fHat_tail_integral (n + 1) (by omega) (s := 2 + (i : ℝ) / (gridG : ℝ))
          (M := ((n + 1 : ℕ) : ℝ) + 3) le_rfl).1 hev' hs2
        rw [htail]
        have hsub : ∫ t in (2 + (i : ℝ) / (gridG : ℝ))..(((n + 1 : ℕ) : ℝ) + 3),
              fHat (n + 1) (t - 1) =
            ∫ u in ((1 : ℝ) + (i : ℝ) / (gridG : ℝ))..((1 : ℝ) + ((gridG * (n + 2) : ℕ) : ℝ) / (gridG : ℝ)),
              fHat (n + 1) u := by
          have hs_eq := intervalIntegral.integral_comp_sub_right (f := fHat (n + 1)) (1 : ℝ)
            (a := 2 + (i : ℝ) / (gridG : ℝ)) (b := ((n + 1 : ℕ) : ℝ) + 3)
          rw [hs_eq]
          congr 1
          · ring
          · push_cast; unfold gridG; norm_num; ring
        rw [hsub]
        have him : i + (gridG * (n + 2) - i) ≤ (uListSeq (n + 1)).length := by
          rw [hlen_prev]; omega
        have hint_le := integral_grid_le hcont hanti (a := 1) le_rfl (uListSeq (n + 1))
          (gridG * (n + 2) - i) i him (fun k hk => ih k (by rw [hlen_prev]; omega))
        rw [show i + (gridG * (n + 2) - i) = gridG * (n + 2) by omega] at hint_le
        have hs_eq : (2 : ℝ) + (i : ℝ) / (gridG : ℝ) = ((2 * gridG + i : ℕ) : ℝ) / (gridG : ℝ) := by
          push_cast; field_simp [hg_pos.ne']
        have h1 : (1 / (2 + (i : ℝ) / (gridG : ℝ))) *
              ∫ u in ((1 : ℝ) + (i : ℝ) / (gridG : ℝ))..((1 : ℝ) + ((gridG * (n + 2) : ℕ) : ℝ) / (gridG : ℝ)),
                fHat (n + 1) u ≤
            (((uListSeq (n + 1)).drop i).sum : ℝ) / ((2 * gridG + i : ℕ) : ℝ) / (scaleF : ℝ) := by
          calc (1 / (2 + (i : ℝ) / (gridG : ℝ))) * _
              ≤ (1 / (2 + (i : ℝ) / (gridG : ℝ))) *
                  ((((uListSeq (n + 1)).drop i).sum : ℝ) / ((gridG : ℝ) * (scaleF : ℝ))) :=
                mul_le_mul_of_nonneg_left hint_le (by positivity)
            _ = (((uListSeq (n + 1)).drop i).sum : ℝ) / ((2 * gridG + i : ℕ) : ℝ) / (scaleF : ℝ) := by
                rw [hs_eq]; push_cast; field_simp [hg_pos.ne', hsf_pos.ne']
        exact h1.trans (div_le_div_of_nonneg_right
          (le_ceilDiv_real _ (2 * gridG + i) (by unfold gridG; omega)) hsf_pos.le)
    · have hbase1 : aBase (n + 2) = 1 := by simp only [aBase, hev, ↓reduceIte]
      have hprev_ev : (n + 1) % 2 = 0 := by omega
      have hbase2 : aBase (n + 1) = 2 := by simp only [aBase, hprev_ev, ↓reduceIte]
      rw [hbase1, show n + 2 + 2 - 1 = n + 3 by omega] at hlen_cur
      rw [hbase1, Nat.cast_one]
      rw [hbase2, show n + 1 + 2 - 2 = n + 1 by omega] at hlen_prev
      rw [hbase2, Nat.cast_ofNat] at ih
      have hi_lt : i < gridG * (n + 3) + 1 := hi.trans_eq hlen_cur
      have hsplitG : gridG * (n + 3) = 2 * gridG + gridG * (n + 1) := by ring
      rw [uListSeq, uNext_eq]
      simp only [hev, ↓reduceIte]
      have hint_full : ∫ t in (3 : ℝ)..(((n + 1 : ℕ) : ℝ) + 3), fHat (n + 1) (t - 1) ≤
          ((uListSeq (n + 1)).sum : ℝ) / ((gridG : ℝ) * (scaleF : ℝ)) := by
        have hsub : ∫ t in (3 : ℝ)..(((n + 1 : ℕ) : ℝ) + 3), fHat (n + 1) (t - 1) =
            ∫ u in ((2 : ℝ) + ((0 : ℕ) : ℝ) / (gridG : ℝ))..((2 : ℝ) + ((gridG * (n + 1) : ℕ) : ℝ) / (gridG : ℝ)),
              fHat (n + 1) u := by
          rw [intervalIntegral.integral_comp_sub_right (f := fHat (n + 1)) (1 : ℝ)]
          congr 1
          · push_cast; norm_num
          · push_cast; unfold gridG; norm_num; ring
        rw [hsub]
        have hle := integral_grid_le hcont hanti (a := 2) (by norm_num) (uListSeq (n + 1))
          (gridG * (n + 1)) 0 (by rw [hlen_prev]; omega) (fun k hk => ih k (by rw [hlen_prev]; omega))
        simpa using hle
      by_cases hi2G : i < 2 * gridG
      · have hleft := listGetD_append_left
          ((List.range (2 * gridG)).map (fun i => ceilDiv ((suffixSums (uListSeq (n + 1))).headD 0) (gridG + i)))
          (uNextEvenAux (3 * gridG) (suffixSums (uListSeq (n + 1)))) i 0 (by simp; exact hi2G)
        rw [hleft, listGetD_map_range (2 * gridG) _ i 0 hi2G, suffixSums_headD]
        have hs_eq : (1 : ℝ) + (i : ℝ) / (gridG : ℝ) = ((gridG + i : ℕ) : ℝ) / (gridG : ℝ) := by
          push_cast; field_simp [hg_pos.ne']
        have hnot1 : ¬ (1 : ℝ) + (i : ℝ) / (gridG : ℝ) < 1 := by
          linarith [show (0 : ℝ) ≤ (i : ℝ) / (gridG : ℝ) by positivity]
        have hmax : max 3 ((1 : ℝ) + (i : ℝ) / (gridG : ℝ)) = 3 := by
          apply max_eq_left
          unfold gridG at hi2G ⊢
          have : (i : ℝ) ≤ 32 := by exact_mod_cast hi2G.le
          linarith
        have hdef : fHat (n + 2) (1 + (i : ℝ) / (gridG : ℝ)) =
            (1 / (1 + (i : ℝ) / (gridG : ℝ))) *
              ∫ t in (3 : ℝ)..(((n + 1 : ℕ) : ℝ) + 3), fHat (n + 1) (t - 1) := by
          rw [fHat]
          simp only [hnot1, ↓reduceIte, hev, hmax]
          congr 2; push_cast; ring
        rw [hdef]
        have h1 : (1 / (1 + (i : ℝ) / (gridG : ℝ))) *
              ∫ t in (3 : ℝ)..(((n + 1 : ℕ) : ℝ) + 3), fHat (n + 1) (t - 1) ≤
            ((uListSeq (n + 1)).sum : ℝ) / ((gridG + i : ℕ) : ℝ) / (scaleF : ℝ) := by
          calc (1 / (1 + (i : ℝ) / (gridG : ℝ))) * _
              ≤ (1 / (1 + (i : ℝ) / (gridG : ℝ))) *
                  (((uListSeq (n + 1)).sum : ℝ) / ((gridG : ℝ) * (scaleF : ℝ))) :=
                mul_le_mul_of_nonneg_left hint_full (by positivity)
            _ = ((uListSeq (n + 1)).sum : ℝ) / ((gridG + i : ℕ) : ℝ) / (scaleF : ℝ) := by
                rw [hs_eq]; push_cast; field_simp [hg_pos.ne', hsf_pos.ne']
        exact h1.trans (div_le_div_of_nonneg_right
          (le_ceilDiv_real _ (gridG + i) (by unfold gridG; omega)) hsf_pos.le)
      · have hi_ge : 2 * gridG ≤ i := Nat.le_of_not_lt hi2G
        have hright := listGetD_append_right
          ((List.range (2 * gridG)).map (fun i => ceilDiv ((suffixSums (uListSeq (n + 1))).headD 0) (gridG + i)))
          (uNextEvenAux (3 * gridG) (suffixSums (uListSeq (n + 1)))) i 0 (by simp; exact hi_ge)
        rw [List.length_map, List.length_range] at hright
        set j := i - 2 * gridG
        have hj_le : j ≤ gridG * (n + 1) := by omega
        have hj_lt : j < (suffixSums (uListSeq (n + 1))).length := by
          rw [suffixSums_length, hlen_prev]; omega
        rw [hright, uNextEvenAux_getD (3 * gridG) _ j hj_lt, suffixSums_getD]
        by_cases hj_end : j = gridG * (n + 1)
        · have hs_ge : ((n + 2 : ℕ) : ℝ) + 2 ≤ 1 + (i : ℝ) / (gridG : ℝ) := by
            have : i = gridG * (n + 3) := by omega
            rw [this]; push_cast; unfold gridG; norm_num; linarith
          rw [fHat_support (n + 2) (by omega) hs_ge]
          positivity
        · have hj_strict : j < gridG * (n + 1) := Nat.lt_of_le_of_ne hj_le hj_end
          have hodd : Odd (n + 2) := Nat.not_even_iff_odd.mp (fun he => hev (Nat.even_iff.mp he))
          have hs3 : 3 ≤ (1 : ℝ) + (i : ℝ) / (gridG : ℝ) := by
            have h2G : (2 : ℝ) ≤ (i : ℝ) / (gridG : ℝ) := by
              rw [le_div_iff₀ hg_pos]
              have : (2 * gridG : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi_ge
              linarith
            linarith
          have htail := (fHat_tail_integral (n + 1) (by omega) (s := 1 + (i : ℝ) / (gridG : ℝ))
            (M := ((n + 1 : ℕ) : ℝ) + 3) le_rfl).2 hodd hs3
          rw [htail]
          have hsub : ∫ t in (1 + (i : ℝ) / (gridG : ℝ))..(((n + 1 : ℕ) : ℝ) + 3),
                fHat (n + 1) (t - 1) =
              ∫ u in ((2 : ℝ) + (j : ℝ) / (gridG : ℝ))..((2 : ℝ) + ((gridG * (n + 1) : ℕ) : ℝ) / (gridG : ℝ)),
                fHat (n + 1) u := by
            rw [intervalIntegral.integral_comp_sub_right (f := fHat (n + 1)) (1 : ℝ)]
            have hij : (i : ℝ) = (2 * gridG : ℝ) + (j : ℝ) := by
              exact_mod_cast (show i = 2 * gridG + j by omega)
            congr 1
            · rw [hij]; field_simp [hg_pos.ne']; ring
            · push_cast; unfold gridG; norm_num; ring
          rw [hsub]
          have hjm : j + (gridG * (n + 1) - j) ≤ (uListSeq (n + 1)).length := by
            rw [hlen_prev]; omega
          have hint_le := integral_grid_le hcont hanti (a := 2) (by norm_num) (uListSeq (n + 1))
            (gridG * (n + 1) - j) j hjm (fun k hk => ih k (by rw [hlen_prev]; omega))
          rw [show j + (gridG * (n + 1) - j) = gridG * (n + 1) by omega] at hint_le
          have hs_eq : (1 : ℝ) + (i : ℝ) / (gridG : ℝ) = ((3 * gridG + j : ℕ) : ℝ) / (gridG : ℝ) := by
            rw [show i = 2 * gridG + j by omega]; push_cast; field_simp [hg_pos.ne']; ring
          have h1 : (1 / (1 + (i : ℝ) / (gridG : ℝ))) *
                ∫ u in ((2 : ℝ) + (j : ℝ) / (gridG : ℝ))..((2 : ℝ) + ((gridG * (n + 1) : ℕ) : ℝ) / (gridG : ℝ)),
                  fHat (n + 1) u ≤
              (((uListSeq (n + 1)).drop j).sum : ℝ) / ((3 * gridG + j : ℕ) : ℝ) / (scaleF : ℝ) := by
            calc (1 / (1 + (i : ℝ) / (gridG : ℝ))) * _
                ≤ (1 / (1 + (i : ℝ) / (gridG : ℝ))) *
                    ((((uListSeq (n + 1)).drop j).sum : ℝ) / ((gridG : ℝ) * (scaleF : ℝ))) :=
                  mul_le_mul_of_nonneg_left hint_le (by positivity)
              _ = (((uListSeq (n + 1)).drop j).sum : ℝ) / ((3 * gridG + j : ℕ) : ℝ) / (scaleF : ℝ) := by
                  rw [hs_eq]; push_cast; field_simp [hg_pos.ne', hsf_pos.ne']
          exact h1.trans (div_le_div_of_nonneg_right
            (le_ceilDiv_real _ (3 * gridG + j) (by unfold gridG; omega)) hsf_pos.le)

lemma fHat_le_mCertVal {n : ℕ} (hn2 : 2 ≤ n) (hn10 : n ≤ 10) {s : ℝ}
    (hs : (if Even n then (2 : ℝ) else 1) ≤ s) :
    fHat n s ≤ 2 * Real.exp 2 * ((mCertVal n : ℝ) / (scaleF : ℝ)) * h_bjs s := by
  have hsf : (0 : ℝ) < (scaleF : ℝ) := by unfold scaleF; norm_num
  have hg_pos : (0 : ℝ) < (gridG : ℝ) := by unfold gridG; norm_num
  have hhb : 0 < 2 * Real.exp 2 * h_bjs s := by
    have hhs : 0 < h_bjs s := by
      rcases le_total s 2 with h2 | h2
      · rw [h_bjs_of_le_two h2]; positivity
      · rcases le_total s 3 with h3 | h3
        · rw [h_bjs_of_two_to_three h2 h3]; positivity
        · rw [h_bjs_of_three_le h3]
          exact mul_pos (div_pos (by norm_num) (by linarith)) (Real.exp_pos _)
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hhs
  by_cases hs_supp : (n : ℝ) + 2 ≤ s
  · rw [fHat_support n (by omega) hs_supp]
    exact mul_nonneg (by positivity) (h_bjs_nonneg s)
  · have hs_lt : s < (n : ℝ) + 2 := lt_of_not_ge hs_supp
    have hs_aBase : (aBase n : ℝ) ≤ s := by
      unfold aBase
      by_cases hev : Even n
      · have hmod : n % 2 = 0 := Nat.even_iff.mp hev
        simpa [hev, hmod] using hs
      · have hmod : n % 2 ≠ 0 := fun h0 => hev (Nat.even_iff.mpr h0)
        simpa [hev, hmod] using hs
    have hnonneg : 0 ≤ (gridG : ℝ) * (s - (aBase n : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hs_aBase)
    set i := Nat.floor ((gridG : ℝ) * (s - (aBase n : ℝ)))
    have hi_lo : (i : ℝ) ≤ (gridG : ℝ) * (s - (aBase n : ℝ)) := Nat.floor_le hnonneg
    have hi_hi : (gridG : ℝ) * (s - (aBase n : ℝ)) < ((i + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add] using Nat.lt_floor_add_one ((gridG : ℝ) * (s - (aBase n : ℝ)))
    have hs_lo : (aBase n : ℝ) + (i : ℝ) / (gridG : ℝ) ≤ s := by
      have hdiv : (i : ℝ) / (gridG : ℝ) ≤ s - (aBase n : ℝ) := (div_le_iff₀ hg_pos).mpr (by linarith)
      linarith
    have hs_hi : s < (aBase n : ℝ) + ((i + 1 : ℕ) : ℝ) / (gridG : ℝ) := by
      have hdiv : s - (aBase n : ℝ) < ((i + 1 : ℕ) : ℝ) / (gridG : ℝ) := (lt_div_iff₀ hg_pos).mpr (by linarith)
      linarith
    have hi_bound : i < gridG * (n + 2 - aBase n) := by
      by_contra hge
      have hge' : gridG * (n + 2 - aBase n) ≤ i := Nat.le_of_not_lt hge
      have h1 : (n : ℝ) + 2 ≤ (aBase n : ℝ) + (i : ℝ) / (gridG : ℝ) := by
        have ha_le : aBase n ≤ n + 2 := by unfold aBase; split_ifs <;> omega
        have hcast : ((gridG * (n + 2 - aBase n) : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hge'
        rw [Nat.cast_mul, Nat.cast_sub ha_le] at hcast
        push_cast at hcast
        have hdiv : (n : ℝ) + 2 - (aBase n : ℝ) ≤ (i : ℝ) / (gridG : ℝ) := (le_div_iff₀ hg_pos).mpr (by linarith)
        linarith
      linarith
    have hlen_u := uListSeq_length n (by omega)
    have hi_u : i < (uListSeq n).length := by omega
    have hs1 : 1 ≤ (aBase n : ℝ) + (i : ℝ) / (gridG : ℝ) := by
      have ha1 : (1 : ℝ) ≤ (aBase n : ℝ) := by unfold aBase; split_ifs <;> norm_num
      have hdiv_nn : 0 ≤ (i : ℝ) / (gridG : ℝ) := div_nonneg (Nat.cast_nonneg _) hg_pos.le
      linarith
    have hf_le : fHat n s ≤ (listGetD (uListSeq n) i 0 : ℝ) / (scaleF : ℝ) := by
      have hanti := fHat_antitone n (by omega) hs1 (hs1.trans hs_lo) hs_lo
      exact hanti.trans (uListSeq_spec n (by omega) i hi_u)
    set off := if n % 2 = 0 then gridG + 1 else 1
    set j := off + i
    have hj1 : 1 ≤ j := by dsimp [j, off]; split_ifs <;> omega
    have hj_max : j ≤ gridG * 12 := by
      dsimp [j, off, aBase] at hi_bound ⊢
      split_ifs at hi_bound ⊢ <;> unfold gridG at hi_bound ⊢ <;> omega
    have hjs_lo : 1 + ((j - 1 : ℕ) : ℝ) / (gridG : ℝ) ≤ s := by
      have hj_sub : j - 1 = (if n % 2 = 0 then gridG else 0) + i := by
        dsimp [j, off]; split_ifs <;> omega
      have hid : 1 + ((j - 1 : ℕ) : ℝ) / (gridG : ℝ) = (aBase n : ℝ) + (i : ℝ) / (gridG : ℝ) := by
        rw [hj_sub]; dsimp [aBase]; split_ifs <;> push_cast <;> field_simp [hg_pos.ne'] <;> ring
      linarith
    have hjs_hi : s ≤ 1 + (j : ℝ) / (gridG : ℝ) := by
      have hid : 1 + (j : ℝ) / (gridG : ℝ) = (aBase n : ℝ) + ((i + 1 : ℕ) : ℝ) / (gridG : ℝ) := by
        dsimp [j, off, aBase]; split_ifs <;> push_cast <;> field_simp [hg_pos.ne'] <;> ring
      linarith
    have hr_le : 1 / (2 * Real.exp 2 * h_bjs s) ≤ (rVal j : ℝ) / (scaleF : ℝ) :=
      rVal_spec j hj1 hjs_lo hjs_hi
    have hm_eq : mCertVal n =
        zipMaxScaled (uListSeq n) ((buildRList (gridG * 12)).drop off) := by
      unfold mCertVal mCertList
      have hget := mCertGo_getD (buildRList (gridG * 12)) 9 1 uInit (n - 2) (by omega) rfl (by omega)
      rw [show 1 + (n - 2) + 1 = n by omega] at hget
      exact hget
    have hr_drop_len : i < ((buildRList (gridG * 12)).drop off).length := by
      rw [List.length_drop, buildRList_length (gridG * 12) (by omega)]
      omega
    have hr_get : listGetD ((buildRList (gridG * 12)).drop off) i 0 = rVal j := by
      rw [listGetD_drop, buildRList_getD (gridG * 12) (off + i) hj_max]
    have hceil_le : ceilDiv (listGetD (uListSeq n) i 0 * rVal j) scaleF ≤ mCertVal n := by
      rw [hm_eq, ← hr_get]
      exact ceilDiv_getD_le_zipMaxScaled (uListSeq n) ((buildRList (gridG * 12)).drop off) i hi_u hr_drop_len
    have hf_nn : 0 ≤ fHat n s := fHat_nonneg n s
    have hprod : fHat n s * (1 / (2 * Real.exp 2 * h_bjs s)) ≤ (mCertVal n : ℝ) / (scaleF : ℝ) := by
      calc fHat n s * (1 / (2 * Real.exp 2 * h_bjs s))
          ≤ ((listGetD (uListSeq n) i 0 : ℝ) / (scaleF : ℝ)) * ((rVal j : ℝ) / (scaleF : ℝ)) :=
            mul_le_mul hf_le hr_le (by positivity) (by positivity)
        _ = ((listGetD (uListSeq n) i 0 * rVal j : ℕ) : ℝ) / (scaleF : ℝ) / (scaleF : ℝ) := by
            push_cast; ring
        _ ≤ (ceilDiv (listGetD (uListSeq n) i 0 * rVal j) scaleF : ℝ) / (scaleF : ℝ) :=
            div_le_div_of_nonneg_right (le_ceilDiv_real _ scaleF (by unfold scaleF; norm_num)) hsf.le
        _ ≤ (mCertVal n : ℝ) / (scaleF : ℝ) := by
            exact div_le_div_of_nonneg_right (by exact_mod_cast hceil_le) hsf.le
    calc fHat n s
        = fHat n s * (1 / (2 * Real.exp 2 * h_bjs s)) * (2 * Real.exp 2 * h_bjs s) := by
          rw [mul_assoc, one_div_mul_cancel hhb.ne', mul_one]
      _ ≤ ((mCertVal n : ℝ) / (scaleF : ℝ)) * (2 * Real.exp 2 * h_bjs s) :=
          mul_le_mul_of_nonneg_right hprod hhb.le
      _ = 2 * Real.exp 2 * ((mCertVal n : ℝ) / (scaleF : ℝ)) * h_bjs s := by ring

end CertifiedC2Grid

end

end BuchstabSwitching
