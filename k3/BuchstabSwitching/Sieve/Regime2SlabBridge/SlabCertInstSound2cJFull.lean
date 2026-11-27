import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2cHelpers
import Mathlib.Tactic

/-!
# Kernel-Verified Regime `2c` `J_full` Lower Bound (`checkJFullLb2c`)

Provides `checkJFullLb2c` and `checkJFullLb2c_sound`, proving `jfLb.toReal ≤ J_full z xiLb.toReal`
for `1 ≤ xiLb < z^3` (`3 ≤ z`) via `J_full_eq_J_odd_of_lt`, `J_full_mono_xi`, and
`j_full_lb_z3_ge_general` using pure binary `Dyadic` arithmetic.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

section JFullDyadicCert

private lemma blt_of_toReal_lt {a b : Dyadic} (h : a.toReal < b.toReal) : a.blt b = true := by
  cases hb : a.blt b with
  | true => rfl
  | false => exfalso; linarith [Dyadic.blt_false_le hb]

private def logRatioLb (log1Lo log0Hi : Dyadic) : Dyadic :=
  if log0Hi.m == 0 then dyZero
  else
    let r := divDyadicLb log1Lo log0Hi
    if dyOne.ble r then
      let res := dyLogBounds r; if res.1 then res.2.1 else dyZero
    else dyZero

private lemma logRatioLb_sound (consts : External.CertifiedConstants) {log1Lo log0Hi : Dyadic} {l0 l1 : ℝ}
    (hl0 : 0 < l0) (hl01 : l0 ≤ l1) (h0 : l0 ≤ log0Hi.toReal) (h1 : log1Lo.toReal ≤ l1) :
    (logRatioLb log1Lo log0Hi).toReal ≤ Real.log (l1 / l0) := by
  have hlog_nn : 0 ≤ Real.log (l1 / l0) := Real.log_nonneg ((one_le_div hl0).mpr hl01)
  unfold logRatioLb; dsimp only; split_ifs with hm0 hr1 hok
  · rw [dyZero_toReal]; exact hlog_nn
  · set r := divDyadicLb log1Lo log0Hi
    have hr_le : r.toReal ≤ l1 / l0 :=
      (divDyadicLb_le _ _).trans (div_le_div₀ (hl0.trans_le hl01).le h1 hl0 h0)
    have hr_ge1 : (1 : ℝ) ≤ r.toReal := by simpa [dyOne_toReal] using Dyadic.ble_sound hr1
    have hrl := (dyLogBounds_sound consts hok).1
    exact hrl.trans (Real.log_le_log (by linarith) hr_le)
  · rw [dyZero_toReal]; exact hlog_nn
  · rw [dyZero_toReal]; exact hlog_nn

private def jFullS1 (zLogLo zLogHi tdiffLo tdiffHi : Dyadic) (i : Fin 3) : Dyadic :=
  let a0Lo := zLogLo.add (((Dyadic.ofNat i.1).mulLb tdiffLo).divPow2Lb 3)
  let a0Hi := zLogHi.add (((Dyadic.ofNat i.1).mulUb tdiffHi).divPow2Ub 3)
  let a1Lo := zLogLo.add (((Dyadic.ofNat (i.1 + 1)).mulLb tdiffLo).divPow2Lb 3)
  (logRatioLb a1Lo a0Hi).subLb ((jsMertLoUbDyadic a1Lo).add (jsMertHiUbDyadic a0Lo))

private def jFullTerm2Inner (zLogLo zLogHi tdiffLo tdiffHi : Dyadic) (i : Fin 3) (j : Fin 4) : Dyadic :=
  let c0 := 2 * (i.1 + 1) + j.1 * (3 - i.1)
  let c1 := 2 * (i.1 + 1) + (j.1 + 1) * (3 - i.1)
  let b0Lo := zLogLo.add (((Dyadic.ofNat c0).mulLb tdiffLo).divPow2Lb 4)
  let b0Hi := zLogHi.add (((Dyadic.ofNat c0).mulUb tdiffHi).divPow2Ub 4)
  let b1Lo := zLogLo.add (((Dyadic.ofNat c1).mulLb tdiffLo).divPow2Lb 4)
  let remLo := ((Dyadic.ofNat ((3 - i.1) * (3 - j.1))).mulLb tdiffLo).divPow2Lb 4
  let s2 := (logRatioLb b1Lo b0Hi).subLb ((jsMertLoUbDyadic b1Lo).add (jsMertHiUbDyadic b0Lo))
  s2.mulLb (jOddLbDyadic remLo)

private lemma gridLogBoundsPow2 {s td : ℝ} {sLoS sHiS tdLoS tdHiS : Dyadic} (k p : ℕ)
    (hs : sLoS.toReal ≤ s ∧ s ≤ sHiS.toReal) (htd : tdLoS.toReal ≤ td ∧ td ≤ tdHiS.toReal) :
    (sLoS.add (((Dyadic.ofNat k).mulLb tdLoS).divPow2Lb p)).toReal ≤
        s + (k : ℝ) / ((2 : ℝ) ^ p) * td ∧
      s + (k : ℝ) / ((2 : ℝ) ^ p) * td ≤
        (sHiS.add (((Dyadic.ofNat k).mulUb tdHiS).divPow2Ub p)).toReal := by
  rw [Dyadic.add_toReal, Dyadic.add_toReal]
  constructor
  · have hd1 := Dyadic.divPow2Lb_le ((Dyadic.ofNat k).mulLb tdLoS) p
    have hm0 : (Dyadic.ofNat k).toReal * tdLoS.toReal ≤ (k : ℝ) * td := by
      rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left htd.1 (Nat.cast_nonneg _)
    have hm1 := (Dyadic.mulLb_le (Dyadic.ofNat k) tdLoS).trans hm0
    have h1 := hd1.trans (div_le_div_of_nonneg_right hm1 (by positivity))
    linarith [show (k : ℝ) * td / ((2 : ℝ) ^ p) = (k : ℝ) / ((2 : ℝ) ^ p) * td by ring]
  · have hd2 := Dyadic.le_divPow2Ub ((Dyadic.ofNat k).mulUb tdHiS) p
    have hm0 : (k : ℝ) * td ≤ (Dyadic.ofNat k).toReal * tdHiS.toReal := by
      rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left htd.2 (Nat.cast_nonneg _)
    have hm2 := hm0.trans (Dyadic.le_mulUb _ _)
    have h2 := (div_le_div_of_nonneg_right hm2 (by positivity)).trans hd2
    linarith [show (k : ℝ) * td / ((2 : ℝ) ^ p) = (k : ℝ) / ((2 : ℝ) ^ p) * td by ring]

private lemma jFullTerm2_sound (consts : External.CertifiedConstants) {z_nat : ℕ} {xi : ℝ}
    (_hz3 : 3 ≤ z_nat) {zLogLo zLogHi xiLogLo xiLogHi : Dyadic}
    (hz10 : dyTen.blt zLogLo = true) (h2z : (zLogHi.add zLogHi).blt xiLogLo = true)
    (hzL : zLogLo.toReal ≤ Real.log (z_nat : ℝ) ∧ Real.log (z_nat : ℝ) ≤ zLogHi.toReal)
    (hxiL : xiLogLo.toReal ≤ Real.log xi ∧ Real.log xi ≤ xiLogHi.toReal) (hxi_pos : 0 < xi) :
    let δ := Real.log xi - 2 * Real.log (z_nat : ℝ)
    let a : Fin 4 → ℝ := fun i => Real.exp (Real.log (z_nat : ℝ) + (i.1 : ℝ) / 8 * δ)
    let b : Fin 3 → Fin 5 → ℝ := fun i j =>
      Real.exp (Real.log (z_nat : ℝ) + ((2 * (i.1 + 1) + j.1 * (3 - i.1) : ℕ) : ℝ) / 16 * δ)
    let tdLo := xiLogLo.subLb (zLogHi.add zLogHi)
    let tdHi := xiLogHi.subLb (zLogLo.add zLogLo)
    ∀ (i : Fin 3) (j : Fin 4),
      (jFullS1 zLogLo zLogHi tdLo tdHi i).toReal *
        (jFullTerm2Inner zLogLo zLogHi tdLo tdHi i j).toReal ≤
      max 0 (Real.log (Real.log (a i.succ) / Real.log (a i.castSucc)) -
          External.jsMertensLoErr (a i.succ) - External.jsMertensHiErr (a i.castSucc)) *
        max 0 (Real.log (Real.log (b i j.succ) / Real.log (b i j.castSucc)) -
          External.jsMertensLoErr (b i j.succ) - External.jsMertensHiErr (b i j.castSucc)) *
        BuchstabSwitching.J_odd_lb_asym (xi / (a i.succ * b i j.succ)) := by
  intro δ a b tdLo tdHi i j
  have h10r : (10 : ℝ) < zLogLo.toReal := by simpa [dyTen_toReal] using Dyadic.blt_sound hz10
  have h2zr : 2 * zLogHi.toReal < xiLogLo.toReal := by
    have := Dyadic.blt_sound h2z; rw [Dyadic.add_toReal] at this; linarith
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith [hzL.2, hxiL.1]
  have htd : tdLo.toReal ≤ δ ∧ δ ≤ tdHi.toReal := by
    refine ⟨(Dyadic.subLb_le_max_zero hxiL.1 ?_).trans (by rw [max_eq_right hδ_pos.le]),
      le_trans ?_ (Dyadic.sub_le_subLb_toReal _ _)⟩
    · rw [Dyadic.add_toReal]; linarith [hzL.2]
    · rw [Dyadic.add_toReal]; linarith [hxiL.2, hzL.1]
  let c0 := 2 * (i.1 + 1) + j.1 * (3 - i.1)
  let c1 := 2 * (i.1 + 1) + (j.1 + 1) * (3 - i.1)
  let a0Lo := zLogLo.add (((Dyadic.ofNat i.1).mulLb tdLo).divPow2Lb 3)
  let a0Hi := zLogHi.add (((Dyadic.ofNat i.1).mulUb tdHi).divPow2Ub 3)
  let a1Lo := zLogLo.add (((Dyadic.ofNat (i.1 + 1)).mulLb tdLo).divPow2Lb 3)
  let b0Lo := zLogLo.add (((Dyadic.ofNat c0).mulLb tdLo).divPow2Lb 4)
  let b0Hi := zLogHi.add (((Dyadic.ofNat c0).mulUb tdHi).divPow2Ub 4)
  let b1Lo := zLogLo.add (((Dyadic.ofNat c1).mulLb tdLo).divPow2Lb 4)
  have ha0 := gridLogBoundsPow2 i.1 3 hzL htd
  rw [show (2 : ℝ) ^ 3 = 8 by norm_num] at ha0
  have ha1 := gridLogBoundsPow2 (i.1 + 1) 3 hzL htd
  rw [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_add, Nat.cast_one] at ha1
  have hb0 := gridLogBoundsPow2 c0 4 hzL htd
  rw [show (2 : ℝ) ^ 4 = 16 by norm_num] at hb0
  have hb1 := gridLogBoundsPow2 c1 4 hzL htd
  rw [show (2 : ℝ) ^ 4 = 16 by norm_num] at hb1
  change a0Lo.toReal ≤ _ ∧ _ ≤ a0Hi.toReal at ha0
  change a1Lo.toReal ≤ _ ∧ _ ≤ _ at ha1
  change b0Lo.toReal ≤ _ ∧ _ ≤ b0Hi.toReal at hb0
  change b1Lo.toReal ≤ _ ∧ _ ≤ _ at hb1
  have hla0 : Real.log (a i.castSucc) = Real.log (z_nat : ℝ) + (i.1 : ℝ) / 8 * δ := Real.log_exp _
  have hla1 : Real.log (a i.succ) = Real.log (z_nat : ℝ) + ((i.1 : ℝ) + 1) / 8 * δ := by
    rw [Real.log_exp, Fin.val_succ]; push_cast; rfl
  have hlb0 : Real.log (b i j.castSucc) =
      Real.log (z_nat : ℝ) + ((c0 : ℕ) : ℝ) / 16 * δ := Real.log_exp _
  have hlb1 : Real.log (b i j.succ) =
      Real.log (z_nat : ℝ) + ((c1 : ℕ) : ℝ) / 16 * δ := Real.log_exp _
  rw [← hla0] at ha0; rw [← hla1] at ha1; rw [← hlb0] at hb0; rw [← hlb1] at hb1
  have ha0_ge : zLogLo.toReal ≤ a0Lo.toReal := by
    dsimp [a0Lo]; rw [Dyadic.add_toReal]; linarith [Dyadic.toReal_nonneg (((Dyadic.ofNat i.1).mulLb tdLo).divPow2Lb 3)]
  have ha1_ge : zLogLo.toReal ≤ a1Lo.toReal := by
    dsimp [a1Lo]; rw [Dyadic.add_toReal]; linarith [Dyadic.toReal_nonneg (((Dyadic.ofNat (i.1 + 1)).mulLb tdLo).divPow2Lb 3)]
  have hb0_ge : zLogLo.toReal ≤ b0Lo.toReal := by
    dsimp [b0Lo]; rw [Dyadic.add_toReal]; linarith [Dyadic.toReal_nonneg (((Dyadic.ofNat c0).mulLb tdLo).divPow2Lb 4)]
  have hb1_ge : zLogLo.toReal ≤ b1Lo.toReal := by
    dsimp [b1Lo]; rw [Dyadic.add_toReal]; linarith [Dyadic.toReal_nonneg (((Dyadic.ofNat c1).mulLb tdLo).divPow2Lb 4)]
  have ha0_10 : dyTen.blt a0Lo = true := blt_of_toReal_lt (by rw [dyTen_toReal]; linarith)
  have hb0_10 : dyTen.blt b0Lo = true := blt_of_toReal_lt (by rw [dyTen_toReal]; linarith)
  have ha_le : Real.log (a i.castSucc) ≤ Real.log (a i.succ) := by rw [hla0, hla1]; nlinarith
  have hb_le : Real.log (b i j.castSucc) ≤ Real.log (b i j.succ) := by
    rw [hlb0, hlb1]
    have hc_le : (c0 : ℝ) ≤ (c1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
    nlinarith
  have ha0_pos : 0 < Real.log (a i.castSucc) := by linarith [ha0.1]
  have hb0_pos : 0 < Real.log (b i j.castSucc) := by linarith [hb0.1]
  have hs1_le : ((logRatioLb a1Lo a0Hi).subLb ((jsMertLoUbDyadic a1Lo).add (jsMertHiUbDyadic a0Lo))).toReal ≤
      max 0 (Real.log (Real.log (a i.succ) / Real.log (a i.castSucc)) -
        External.jsMertensLoErr (a i.succ) - External.jsMertensHiErr (a i.castSucc)) := by
    rw [sub_sub]; refine Dyadic.subLb_le_max_zero (logRatioLb_sound consts ha0_pos ha_le ha0.2 ha1.1) ?_
    rw [Dyadic.add_toReal]
    exact add_le_add (jsMertLoUbDyadic_sound (by linarith) ha1.1)
      (jsMertHiUbDyadic_sound consts (Real.exp_pos _) ha0_10 ha0.1)
  have hs2_le : ((logRatioLb b1Lo b0Hi).subLb ((jsMertLoUbDyadic b1Lo).add (jsMertHiUbDyadic b0Lo))).toReal ≤
      max 0 (Real.log (Real.log (b i j.succ) / Real.log (b i j.castSucc)) -
        External.jsMertensLoErr (b i j.succ) - External.jsMertensHiErr (b i j.castSucc)) := by
    rw [sub_sub]; refine Dyadic.subLb_le_max_zero (logRatioLb_sound consts hb0_pos hb_le hb0.2 hb1.1) ?_
    rw [Dyadic.add_toReal]
    exact add_le_add (jsMertLoUbDyadic_sound (by linarith) hb1.1)
      (jsMertHiUbDyadic_sound consts (Real.exp_pos _) hb0_10 hb0.1)
  have hrem_ge1 : 1 ≤ xi / (a i.succ * b i j.succ) := by
    refine (one_le_div (mul_pos (Real.exp_pos _) (Real.exp_pos _))).mpr ?_
    rw [← Real.exp_add, ← Real.exp_log hxi_pos, Real.exp_le_exp]
    have hcoeff : 2 * (i.1 + 1) + c1 + (3 - i.1) * (3 - j.1) = 16 := by
      have hi3 : i.1 ≤ 3 := i.isLt.le; have hj4 : j.1 ≤ 3 := Nat.le_pred_of_lt j.isLt
      dsimp [c1]; zify [hi3, hj4]; ring
    have hle16 : ((2 * (i.1 + 1) + c1 : ℕ) : ℝ) ≤ 16 := by
      have := Nat.le_add_right (2 * (i.1 + 1) + c1) ((3 - i.1) * (3 - j.1))
      rw [hcoeff] at this; exact_mod_cast this
    dsimp [a, b, δ] at *; push_cast at hle16 ⊢
    dsimp [c1] at hle16; push_cast at hle16; nlinarith [hδ_pos]
  have hrem_log : (((Dyadic.ofNat ((3 - i.1) * (3 - j.1))).mulLb tdLo).divPow2Lb 4).toReal ≤
      Real.log (xi / (a i.succ * b i j.succ)) := by
    rw [Real.log_div hxi_pos.ne' (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', hla1, hlb1]
    have hcoeff : 2 * (i.1 + 1) + c1 + (3 - i.1) * (3 - j.1) = 16 := by
      have hi3 : i.1 ≤ 3 := i.isLt.le; have hj4 : j.1 ≤ 3 := Nat.le_pred_of_lt j.isLt
      dsimp [c1]; zify [hi3, hj4]; ring
    have hlog_eq : Real.log xi - (Real.log (z_nat : ℝ) + ((i.1 : ℝ) + 1) / 8 * δ +
        (Real.log (z_nat : ℝ) + ((c1 : ℕ) : ℝ) / 16 * δ)) =
        (((3 - i.1) * (3 - j.1) : ℕ) : ℝ) / 16 * δ := by
      have h16 : 2 * ((i.1 : ℝ) + 1) + (c1 : ℝ) = 16 - (((3 - i.1) * (3 - j.1) : ℕ) : ℝ) := by
        have hcoeff_r : ((2 * (i.1 + 1) + c1 : ℕ) : ℝ) + (((3 - i.1) * (3 - j.1) : ℕ) : ℝ) = 16 := by
          exact_mod_cast hcoeff
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hcoeff_r
        linarith
      have hlin : Real.log xi - (Real.log (z_nat : ℝ) + ((i.1 : ℝ) + 1) / 8 * δ +
          (Real.log (z_nat : ℝ) + ((c1 : ℕ) : ℝ) / 16 * δ)) =
          (16 - (2 * ((i.1 : ℝ) + 1) + (c1 : ℝ))) / 16 * δ := by
        dsimp [δ]; ring
      rw [hlin, h16]; ring
    rw [hlog_eq]
    have h1 := Dyadic.divPow2Lb_le ((Dyadic.ofNat ((3 - i.1) * (3 - j.1))).mulLb tdLo) 4
    rw [show (2 : ℝ) ^ 4 = 16 by norm_num] at h1
    have hm0 : (Dyadic.ofNat ((3 - i.1) * (3 - j.1))).toReal * tdLo.toReal ≤
        (((3 - i.1) * (3 - j.1) : ℕ) : ℝ) * δ := by
      rw [Dyadic.ofNat_toReal]; exact mul_le_mul_of_nonneg_left htd.1 (Nat.cast_nonneg _)
    have hm := (Dyadic.mulLb_le _ _).trans hm0
    exact h1.trans ((div_le_div_of_nonneg_right hm (by norm_num)).trans_eq (by ring))
  have hj_le := jOddLbDyadic_sound hrem_ge1 hrem_log
  unfold jFullS1 jFullTerm2Inner; dsimp only
  have hinner := (Dyadic.mulLb_le _ _).trans
    (mul_le_mul hs2_le hj_le (Dyadic.toReal_nonneg _) (le_max_left _ _))
  rw [mul_assoc]
  exact mul_le_mul hs1_le hinner (Dyadic.toReal_nonneg _) (le_max_left _ _)

private def foldFin12 (f : Fin 12 → Bool × Dyadic) : Bool × Dyadic :=
  (List.finRange 12).foldl (fun acc k => let r := f k; (acc.1 && r.1, acc.2.add r.2)) (true, dyZero)

private lemma foldl_bool_dyadic (L : List (Fin 12)) (f : Fin 12 → Bool × Dyadic) (b0 : Bool) (s0 : Dyadic) :
    let res := L.foldl (fun acc k => let r := f k; (acc.1 && r.1, acc.2.add r.2)) (b0, s0)
    res.1 = (b0 && L.all (fun k => (f k).1)) ∧
    res.2.toReal = s0.toReal + (L.map (fun k => (f k).2.toReal)).sum := by
  induction L generalizing b0 s0 with
  | nil => simp
  | cons k tl ih =>
    have h := ih (b0 && (f k).1) (s0.add (f k).2)
    dsimp only at h ⊢
    rw [List.foldl_cons, List.all_cons, List.map_cons, List.sum_cons, h.1, h.2,
      Bool.and_assoc, Dyadic.add_toReal, add_assoc]
    exact ⟨rfl, rfl⟩

private lemma foldFin12_spec (f : Fin 12 → Bool × Dyadic) :
    (foldFin12 f).1 = (List.finRange 12).all (fun k => (f k).1) ∧
    (foldFin12 f).2.toReal = ∑ k : Fin 12, (f k).2.toReal := by
  have h := foldl_bool_dyadic (List.finRange 12) f true dyZero
  dsimp only at h
  refine ⟨by rw [foldFin12, h.1, Bool.true_and], ?_⟩
  rw [foldFin12, h.2, dyZero_toReal, zero_add, ← List.sum_toFinset _ (List.nodup_finRange 12)]
  have hfin : (List.finRange 12).toFinset = Finset.univ := by ext x; simp
  rw [hfin]

private def jFullTerm1Fold (zLogLo zLogHi xiLogLo xiLogHi xiLb : Dyadic) : Bool × Dyadic :=
  foldFin12 (jFullTerm1 zLogLo zLogHi xiLogLo xiLogHi xiLb)

private lemma jFullTerm1Fold_spec (zLogLo zLogHi xiLogLo xiLogHi xiLb : Dyadic) :
    (jFullTerm1Fold zLogLo zLogHi xiLogLo xiLogHi xiLb).1 =
      (List.finRange 12).all (fun k => (jFullTerm1 zLogLo zLogHi xiLogLo xiLogHi xiLb k).1) ∧
    (jFullTerm1Fold zLogLo zLogHi xiLogLo xiLogHi xiLb).2.toReal =
      ∑ k : Fin 12, (jFullTerm1 zLogLo zLogHi xiLogLo xiLogHi xiLb k).2.toReal :=
  foldFin12_spec (jFullTerm1 zLogLo zLogHi xiLogLo xiLogHi xiLb)

/-- Computable lower-bound verifier `jfLb ≤ J_full z xi` for `1 ≤ xi < z^3` and `3 ≤ z`. -/
def checkJFullLb2c (z : ℕ) (zLogLo zLogUb xiLb xiLogLo xiLogUb jfLb : Dyadic)
    (wXiLog : LogWitness) : Bool :=
  decide (3 ≤ z) && decide (0 < jfLb.m) && dyOne.ble xiLb &&
  checkLogDyadic xiLb wXiLog xiLogLo xiLogUb &&
  if xiLb.blt (Dyadic.ofNat z) then jfLb.ble (jOddLbDyadic xiLogLo)
  else if (Dyadic.ofNat z).blt xiLb then
    let (ok1, s1) := jFullTerm1Fold zLogLo zLogUb xiLogLo xiLogUb xiLb
    let s2 :=
      if (zLogUb.add zLogUb).blt xiLogLo then
        let tdLo := xiLogLo.subLb (zLogUb.add zLogUb)
        let tdHi := xiLogUb.subLb (zLogLo.add zLogLo)
        sumDyadicFin (fun i : Fin 3 =>
          (jFullS1 zLogLo zLogUb tdLo tdHi i).mulLb
            (sumDyadicFin (fun j : Fin 4 => jFullTerm2Inner zLogLo zLogUb tdLo tdHi i j)))
      else dyZero
    dyTen.blt zLogLo && xiLb.blt (Dyadic.ofNat (z ^ 3)) && ok1 &&
      (jfLb.add s1).ble ((jOddLbDyadic xiLogLo).add s2)
  else jfLb.ble (jOddLbDyadic (zLogLo.subLb dyOne))

lemma checkJFullLb2c_sound (consts : External.CertifiedConstants)
    (hMert : External.MertensPrimeSumPremise consts.M0)
    {z : ℕ} {zLogLo zLogUb xiLb xiLogLo xiLogUb jfLb : Dyadic} {wXiLog : LogWitness}
    (hzL : zLogLo.toReal ≤ Real.log (z : ℝ) ∧ Real.log (z : ℝ) ≤ zLogUb.toReal)
    (h : checkJFullLb2c z zLogLo zLogUb xiLb xiLogLo xiLogUb jfLb wXiLog = true) :
    3 ≤ z ∧ 1 ≤ xiLb.toReal ∧ 0 < jfLb.toReal ∧
      (xiLogLo.toReal ≤ Real.log xiLb.toReal ∧ Real.log xiLb.toReal ≤ xiLogUb.toReal) ∧
      jfLb.toReal ≤ BuchstabSwitching.J_full z xiLb.toReal := by
  unfold checkJFullLb2c at h; dsimp only at h
  cases hbase : decide (3 ≤ z) && decide (0 < jfLb.m) && dyOne.ble xiLb &&
      checkLogDyadic xiLb wXiLog xiLogLo xiLogUb with
  | false => rw [hbase] at h; simp at h
  | true =>
  rw [hbase] at h; simp only [Bool.true_and] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hbase
  rcases hbase with ⟨hz3, hjPos, hxi1, hxiLog⟩
  have hxi1r : 1 ≤ xiLb.toReal := by simpa [dyOne_toReal] using Dyadic.ble_sound hxi1
  have hjPosr : 0 < jfLb.toReal := Dyadic.toReal_pos_of_m hjPos
  have hxiL := checkLogDyadic_sound consts hxiLog
  refine ⟨hz3, hxi1r, hjPosr, hxiL, ?_⟩
  have hmid : ∀ (s2 : Dyadic)
      (hgt : (Dyadic.ofNat z).blt xiLb = true)
      (hxi3 : xiLb.blt (Dyadic.ofNat (z ^ 3)) = true)
      (hok1 : (jFullTerm1Fold zLogLo zLogUb xiLogLo xiLogUb xiLb).1 = true)
      (hble : (jfLb.add (jFullTerm1Fold zLogLo zLogUb xiLogLo xiLogUb xiLb).2).ble
        ((jOddLbDyadic xiLogLo).add s2) = true)
      (G : BuchstabSwitching.TwoPrimeDiscreteGrid z xiLb.toReal)
      (h2_sum : s2.toReal ≤ ∑ i : Fin G.m₁, ∑ j : Fin (G.m₂ i),
        max 0 (Real.log (Real.log (G.a i.succ) / Real.log (G.a i.castSucc)) -
          External.jsMertensLoErr (G.a i.succ) - External.jsMertensHiErr (G.a i.castSucc)) *
        max 0 (Real.log (Real.log (G.b i j.succ) / Real.log (G.b i j.castSucc)) -
          External.jsMertensLoErr (G.b i j.succ) - External.jsMertensHiErr (G.b i j.castSucc)) *
        BuchstabSwitching.J_odd_lb_asym (xiLb.toReal / (G.a i.succ * G.b i j.succ))),
      jfLb.toReal ≤ BuchstabSwitching.J_full z xiLb.toReal := by
    intro s2 hgt hxi3 hok1 hble G h2_sum
    clear h hxiLog
    have hfold := jFullTerm1Fold_spec zLogLo zLogUb xiLogLo xiLogUb xiLb
    rw [hfold.1, List.all_eq_true] at hok1
    have hzxi : (z : ℝ) < xiLb.toReal := by simpa [Dyadic.ofNat_toReal] using Dyadic.blt_sound hgt
    have hxi3r : xiLb.toReal < (z : ℝ) ^ 3 := by
      simpa [Dyadic.ofNat_toReal, Nat.cast_pow] using Dyadic.blt_sound hxi3
    have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
    have hs_lt_t : Real.log (z : ℝ) < Real.log xiLb.toReal := Real.log_lt_log hz_pos hzxi
    let w : Fin 13 → ℝ := fun j =>
      Real.exp (((12 - j.1 : ℕ) * Real.log (z : ℝ) + (j.1 : ℕ) * Real.log xiLb.toReal) / 12)
    have hw0 : w 0 = (z : ℝ) := by simp [w, Real.exp_log hz_pos]
    have hw_end : w ⟨12, Nat.lt_succ_self 12⟩ = xiLb.toReal := by
      simp [w, Real.exp_log (lt_of_lt_of_le zero_lt_one hxi1r)]
    have hw_mono : StrictMono w := fun i j hij => Real.exp_lt_exp.mpr (by
      have hi12 : (i.1 : ℝ) ≤ 12 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      have hj12 : (j.1 : ℝ) ≤ 12 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      have hij' : (i.1 : ℝ) < (j.1 : ℝ) := by exact_mod_cast hij
      rw [Nat.cast_sub (Nat.le_of_lt_succ i.isLt), Nat.cast_sub (Nat.le_of_lt_succ j.isLt)]
      push_cast; nlinarith only [hi12, hj12, hij', hs_lt_t])
    have h1_sum : (∑ k : Fin 12,
        let w0 := w k.castSucc
        let w1p := if k.val + 1 = 12 then w k.succ + 1 else w k.succ
        BuchstabSwitching.J_odd (xiLb.toReal / w0) *
          (max 0 (Real.log (Real.log w1p / Real.log w0) +
            External.jsMertensHiErr w1p + External.jsMertensLoErr w0) + 2 / (w0 - 2))) ≤
        (jFullTerm1Fold zLogLo zLogUb xiLogLo xiLogUb xiLb).2.toReal := by
      rw [hfold.2]
      exact Finset.sum_le_sum fun k _ =>
        jFullTerm1_sound consts hz3 hzxi hzL hxiL (lt_of_lt_of_le zero_lt_one hxi1r) le_rfl k (hok1 k (List.mem_finRange k))
    have hj_xi := jOddLbDyadic_sound hxi1r hxiL.1
    have hG := BuchstabSwitching.j_full_lb_z3_ge_general hMert.mertensSumBounds
      (fun _ hX => ⟨BuchstabSwitching.J_odd_lb_asym_nonneg _, BuchstabSwitching.J_odd_lb_asym_le hX⟩)
      (fun _ _ => le_rfl) hz3 hzxi.le hxi3r (by norm_num) w hw0 hw_end hw_mono G
    have hfin := Dyadic.ble_sound hble
    rw [Dyadic.add_toReal, Dyadic.add_toReal] at hfin
    unfold BuchstabSwitching.j_full_lb_z3 at hG; dsimp only at hG
    linarith only [h1_sum, hj_xi, hG, hfin, h2_sum]
  split_ifs at h with hlt hgt h2z
  · have hxi_lt : Nat.floor xiLb.toReal < z := by
      have : xiLb.toReal < (z : ℝ) := by simpa [Dyadic.ofNat_toReal] using Dyadic.blt_sound hlt
      exact_mod_cast (Nat.floor_le (by linarith)).trans_lt this
    rw [BuchstabSwitching.J_full_eq_J_odd_of_lt hxi_lt]
    exact (Dyadic.ble_sound h).trans ((jOddLbDyadic_sound hxi1r hxiL.1).trans (BuchstabSwitching.J_odd_lb_asym_le hxi1r))
  · simp only [Bool.and_eq_true, and_assoc] at h
    rcases h with ⟨hz10, hxi3, hok1, hble⟩
    clear hxiLog
    have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
    let δ := Real.log xiLb.toReal - 2 * Real.log (z : ℝ)
    have hδ : 0 < δ := by
      have := Dyadic.blt_sound h2z
      rw [Dyadic.add_toReal] at this
      dsimp [δ]; linarith [hzL.2, hxiL.1]
    let G : BuchstabSwitching.TwoPrimeDiscreteGrid z xiLb.toReal :=
      { m₁ := 3, a := fun i => Real.exp (Real.log (z : ℝ) + (i.1 : ℝ) / 8 * δ),
        ha_ge := by simp [Real.exp_log hz_pos],
        ha_mono := fun i j hij => Real.exp_lt_exp.mpr (by
          have : (i.1 : ℝ) < (j.1 : ℝ) := by exact_mod_cast hij
          nlinarith),
        m₂ := fun _ => 4,
        b := fun i j => Real.exp (Real.log (z : ℝ) + ((2 * (i.1 + 1) + j.1 * (3 - i.1) : ℕ) : ℝ) / 16 * δ),
        hb_ge := fun i => Real.exp_le_exp.mpr (by simp [Fin.val_succ]; ring_nf; exact le_rfl),
        hb_mono := fun i j₁ j₂ hj => Real.exp_lt_exp.mpr (by
          have : 0 < 3 - i.1 := by omega
          have hlt : 2 * (i.1 + 1) + j₁.1 * (3 - i.1) < 2 * (i.1 + 1) + j₂.1 * (3 - i.1) :=
            Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hj this) _
          have hlt' : ((2 * (i.1 + 1) + j₁.1 * (3 - i.1) : ℕ) : ℝ) <
              ((2 * (i.1 + 1) + j₂.1 * (3 - i.1) : ℕ) : ℝ) := by exact_mod_cast hlt
          nlinarith),
        hb_le := fun i j => by
          rw [← Real.exp_add, ← Real.exp_log (by linarith : 0 < xiLb.toReal), Real.exp_le_exp]
          have hi3 : i.1 ≤ 2 := Nat.le_pred_of_lt i.isLt
          have hj4 : j.succ.1 ≤ 4 := Nat.succ_le_of_lt j.isLt
          have hc : 2 * (i.1 + 1) + (2 * (i.1 + 1) + j.succ.1 * (3 - i.1)) ≤ 16 :=
            (Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_right _ hj4) _) _).trans (by omega)
          have hcr : ((2 * (i.1 + 1) + (2 * (i.1 + 1) + j.succ.1 * (3 - i.1)) : ℕ) : ℝ) ≤ 16 := by exact_mod_cast hc
          push_cast at hcr
          rw [Nat.cast_sub (by omega : i.1 ≤ 3), Fin.val_succ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hcr
          have hsub : ((i.1 : ℝ) + 1) / 8 + (2 * ((i.1 : ℝ) + 1) + ((j.1 : ℝ) + 1) * (3 - (i.1 : ℝ))) / 16 ≤ 1 := by linarith
          dsimp [δ]; push_cast
          rw [Nat.cast_sub (by omega : i.1 ≤ 3), Nat.cast_ofNat]
          nlinarith }
    refine hmid _ hgt hxi3 hok1 hble G (sumDyadicFin_le_sum_fin _ _ fun i => ?_)
    refine (Dyadic.mulLb_le _ _).trans ?_
    rw [sumDyadicFin_toReal, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => jFullTerm2_sound consts hz3 hz10 h2z hzL hxiL (by linarith) i j
  · simp only [Bool.and_eq_true, and_assoc] at h
    rcases h with ⟨_, hxi3, hok1, hble⟩
    let G : BuchstabSwitching.TwoPrimeDiscreteGrid z xiLb.toReal :=
      { m₁ := 0, a := fun _ => (z : ℝ), ha_ge := le_rfl,
        ha_mono := fun i j h => absurd h (by omega), m₂ := fun _ => 0, b := Fin.elim0,
        hb_ge := fun i => i.elim0, hb_mono := fun i => i.elim0, hb_le := fun i => i.elim0 }
    exact hmid dyZero hgt hxi3 hok1 hble G (by simp [G, dyZero_toReal])
  · have hge : (z : ℝ) ≤ xiLb.toReal := by
      simpa [Dyadic.ofNat_toReal] using Dyadic.blt_false_le (Bool.eq_false_iff.mpr hlt)
    have hz12_ge1 : 1 ≤ (z : ℝ) - 1 / 2 := by
      have : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
      linarith
    have hz12_lt : Nat.floor ((z : ℝ) - 1 / 2) < z := by
      have h1 : (Nat.floor ((z : ℝ) - 1 / 2) : ℝ) ≤ (z : ℝ) - 1 / 2 := Nat.floor_le (by linarith)
      exact_mod_cast (by linarith : (Nat.floor ((z : ℝ) - 1 / 2) : ℝ) < (z : ℝ))
    have hlog_sub : (zLogLo.subLb dyOne).toReal ≤ Real.log ((z : ℝ) - 1 / 2) := by
      have hz2 : (z : ℝ) / 2 ≤ (z : ℝ) - 1 / 2 := by
        have : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
        linarith
      have hlog_half : Real.log (z : ℝ) - 1 ≤ Real.log ((z : ℝ) / 2) := by
        have hz_pos : (0 : ℝ) < (z : ℝ) := by positivity
        rw [Real.log_div hz_pos.ne' (by norm_num)]; linarith [Real.log_two_lt_d9]
      exact (Dyadic.subLb_le_max_zero hzL.1 dyOne_toReal.symm.le).trans
        (max_le (Real.log_nonneg hz12_ge1)
          (by linarith [Real.log_le_log (by positivity : 0 < (z : ℝ) / 2) hz2]))
    have hJmono := BuchstabSwitching.J_full_mono_xi z (by linarith : (z : ℝ) - 1 / 2 ≤ xiLb.toReal)
    rw [BuchstabSwitching.J_full_eq_J_odd_of_lt hz12_lt] at hJmono
    exact (Dyadic.ble_sound h).trans ((jOddLbDyadic_sound hz12_ge1 hlog_sub).trans
      ((BuchstabSwitching.J_odd_lb_asym_le hz12_ge1).trans hJmono))

end JFullDyadicCert

end

end BuchstabSwitching.SieveInst
