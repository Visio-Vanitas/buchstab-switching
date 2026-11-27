import BuchstabSwitching.External.NumericalConstants.CanonicalDefs
import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstH0
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTable
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tight Certified Enclosures for `H_0`, `C2_twin`, `U_c`, and `M_0 - γ`

Accelerates prime products and series via `∏_p (1 - 1/p^2)⁻¹ = ζ(2) = π^2 / 6` at cutoff `M = 2000`.
-/

namespace BuchstabSwitching.External

noncomputable section

/-! ## 1. Prime Table Slice `< 2000`, Scaled Integer Helpers, and Tail Telescoping -/

private def scale20 : ℕ := 10 ^ 20
private lemma scale20_pos : (0 : ℝ) < (scale20 : ℝ) := by unfold scale20; positivity
private def ceilDivNat (a b : ℕ) : ℕ := (a + b - 1) / b

private lemma floorDivNat_le {a b : ℕ} (hb : 0 < b) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]; exact_mod_cast Nat.div_mul_le_self a b

private lemma le_ceilDivNat {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((ceilDivNat a b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]; unfold ceilDivNat
  have h1 := Nat.div_add_mod (a + b - 1) b; have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ b * ((a + b - 1) / b) := by omega
  rw [Nat.mul_comm] at h3; exact_mod_cast h3

private def opC0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]
private def opC1 : List ℕ := [127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281]
private def opC2 : List ℕ := [283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463]
private def opC3 : List ℕ := [467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659]
private def opC4 : List ℕ := [661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863]
private def opC5 : List ℕ := [877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069]
private def opC6 : List ℕ := [1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291]
private def opC7 : List ℕ := [1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511]
private def opC8 : List ℕ := [1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733]
private def opC9 : List ℕ := [1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987]
private def opC10 : List ℕ := [1993, 1997, 1999]

private def oddPrimes2000 : List ℕ :=
  opC0 ++ opC1 ++ opC2 ++ opC3 ++ opC4 ++ opC5 ++ opC6 ++ opC7 ++ opC8 ++ opC9 ++ opC10
private def primes2000 : List ℕ := 2 :: oddPrimes2000

private lemma primesLt27000_split2000 :
    ∃ rest : List ℕ, BuchstabSwitching.SieveInst.primesLt27000 = primes2000 ++ (2003 :: rest) := by
  have h5 : BuchstabSwitching.SieveInst.primeChunks.take 5 =
      [2 :: (opC0 ++ opC1), opC2 ++ opC3, opC4 ++ opC5, opC6 ++ opC7, opC8 ++ opC9] := rfl
  have hlen : 6 ≤ BuchstabSwitching.SieveInst.primeChunks.length := by decide
  have hc5_4 : ((BuchstabSwitching.SieveInst.primeChunks.drop 5).head?.getD []).take 4 =
      opC10 ++ [2003] := rfl
  have hne : BuchstabSwitching.SieveInst.primeChunks.drop 5 ≠ [] := by
    intro h; rw [List.drop_eq_nil_iff] at h; omega
  obtain ⟨c5, cs, hdrop⟩ := List.exists_cons_of_ne_nil hne
  have hc5_take : c5.take 4 = opC10 ++ [2003] := by simpa [hdrop] using hc5_4
  refine ⟨c5.drop 4 ++ cs.flatten, ?_⟩
  calc BuchstabSwitching.SieveInst.primesLt27000
      = (BuchstabSwitching.SieveInst.primeChunks.take 5 ++
          BuchstabSwitching.SieveInst.primeChunks.drop 5).flatten := by rw [List.take_append_drop]; rfl
    _ = (BuchstabSwitching.SieveInst.primeChunks.take 5).flatten ++ (c5 ++ cs.flatten) := by
          rw [List.flatten_append, hdrop, List.flatten_cons]
    _ = (2 :: (opC0 ++ opC1 ++ (opC2 ++ opC3) ++ (opC4 ++ opC5) ++ (opC6 ++ opC7) ++
          (opC8 ++ opC9))) ++ ((c5.take 4 ++ c5.drop 4) ++ cs.flatten) := by
          rw [h5, List.take_append_drop 4 c5]; simp [List.append_assoc]
    _ = primes2000 ++ (2003 :: (c5.drop 4 ++ cs.flatten)) := by
          rw [hc5_take]; simp [primes2000, oddPrimes2000, List.append_assoc]

private lemma primes2000_nodup : primes2000.Nodup := by
  obtain ⟨rest, hsp⟩ := primesLt27000_split2000
  have hnd := BuchstabSwitching.SieveInst.primesLt27000_nodup
  rw [hsp] at hnd; exact (List.nodup_append.mp hnd).1

private lemma oddPrimes2000_nodup : oddPrimes2000.Nodup := (List.nodup_cons.mp primes2000_nodup).2

private lemma oddPrimes2000_ge3 : ∀ p ∈ oddPrimes2000, 3 ≤ p := by
  obtain ⟨rest, hsp⟩ := primesLt27000_split2000
  have hpw := BuchstabSwitching.SieveInst.primesLt27000_pairwise_lt
  rw [hsp, primes2000, List.cons_append, List.pairwise_cons] at hpw
  intro p hp; have h2 := hpw.1 p (List.mem_append_left _ hp); omega

private lemma primes2000_toFinset : primes2000.toFinset = (2000 : ℕ).primesBelow := by
  obtain ⟨rest, hsp⟩ := primesLt27000_split2000
  have hpw := BuchstabSwitching.SieveInst.primesLt27000_pairwise_lt
  rw [hsp, List.pairwise_append] at hpw
  have hlt2003 : ∀ p ∈ primes2000, p < 2003 := fun p hp => hpw.2.2 p hp 2003 List.mem_cons_self
  have hgt2003 : ∀ p ∈ rest, 2003 < p := (List.pairwise_cons.mp hpw.2.1).1
  ext p; rw [List.mem_toFinset, Nat.mem_primesBelow]; constructor
  · intro hp
    have hpL : p ∈ BuchstabSwitching.SieveInst.primesLt27000 := by rw [hsp]; exact List.mem_append_left _ hp
    have hpr := (BuchstabSwitching.SieveInst.mem_primesLt27000_iff.mp hpL).2
    have h2003 := hlt2003 p hp; refine ⟨?_, hpr⟩; by_contra hge
    rcases (by omega : p = 2000 ∨ p = 2001 ∨ p = 2002) with rfl | rfl | rfl
    · rcases hpr.eq_one_or_self_of_dvd 2 ⟨1000, rfl⟩ with h | h <;> omega
    · rcases hpr.eq_one_or_self_of_dvd 3 ⟨667, rfl⟩ with h | h <;> omega
    · rcases hpr.eq_one_or_self_of_dvd 2 ⟨1001, rfl⟩ with h | h <;> omega
  · rintro ⟨hp2000, hpr⟩
    have hpL := BuchstabSwitching.SieveInst.mem_primesLt27000_iff.mpr ⟨by omega, hpr⟩
    rw [hsp, List.mem_append, List.mem_cons] at hpL
    rcases hpL with hp | rfl | htail
    · exact hp
    · omega
    · have := hgt2003 p htail; omega

private lemma oddPrimes2000_toFinset :
    oddPrimes2000.toFinset = (Finset.range 2000).filter (fun p => p.Prime ∧ 2 < p) := by
  ext p; rw [List.mem_toFinset, Finset.mem_filter, Finset.mem_range]; constructor
  · intro hp
    have hp2 : p ∈ primes2000.toFinset := List.mem_toFinset.mpr (List.mem_cons_of_mem 2 hp)
    rw [primes2000_toFinset, Nat.mem_primesBelow] at hp2
    exact ⟨hp2.1, hp2.2, oddPrimes2000_ge3 p hp⟩
  · rintro ⟨hp2000, hpr, hp2⟩
    have hp_mem : p ∈ primes2000.toFinset := by rw [primes2000_toFinset, Nat.mem_primesBelow]; exact ⟨hp2000, hpr⟩
    rw [List.mem_toFinset, primes2000, List.mem_cons] at hp_mem
    exact hp_mem.elim (fun h => by omega) id

private lemma sum_odd_primes_Ico_le {M : ℕ} (hM : 2000 ≤ M) (f g : ℕ → ℝ)
    (hf_nn : ∀ j, 1000 ≤ j → 0 ≤ f (2 * j + 1)) (hg_nn : ∀ j, 1000 ≤ j → 0 ≤ g j)
    (hfg : ∀ j, 1000 ≤ j → f (2 * j + 1) ≤ g j - g (j + 1)) :
    ∑ p ∈ (Finset.Ico 2000 M).filter (fun p => p.Prime ∧ 2 < p), f p ≤ g 1000 := by
  set P_tail := (Finset.Ico 2000 M).filter (fun p => p.Prime ∧ 2 < p)
  have hsub : P_tail ⊆ (Finset.Ico 1000 M).image (fun j => 2 * j + 1) := fun p hp => by
    rcases Finset.mem_filter.mp hp with ⟨hpIco, hpr, _⟩; rw [Finset.mem_Ico] at hpIco
    rcases hpr.odd_of_ne_two (by omega) with ⟨j, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  calc ∑ p ∈ P_tail, f p
      ≤ ∑ p ∈ (Finset.Ico 1000 M).image (fun j => 2 * j + 1), f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
          rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩; exact hf_nn j (Finset.mem_Ico.mp hj).1
    _ = ∑ j ∈ Finset.Ico 1000 M, f (2 * j + 1) := Finset.sum_image (fun a _ b _ h => by omega)
    _ ≤ ∑ j ∈ Finset.Ico 1000 M, (g j - g (j + 1)) :=
        Finset.sum_le_sum fun j hj => hfg j (Finset.mem_Ico.mp hj).1
    _ ≤ g 1000 := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1000 ≤ M)
        have htel : ∀ k : ℕ, ∑ j ∈ Finset.Ico 1000 (1000 + k), (g j - g (j + 1)) =
            g 1000 - g (1000 + k) := fun k => by
          induction k with
          | zero => simp
          | succ k ih =>
            rw [show 1000 + (k + 1) = (1000 + k) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]; ring
        rw [htel d]; linarith [hg_nn (1000 + d) (by omega)]

/-! ## 2. Euler Product for `ζ(2) = π^2 / 6` and Odd `ζ(2)` Product -/

private def invSqHom : ℕ →*₀ ℝ where
  toFun n := (1 : ℝ) / (n : ℝ) ^ 2
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by push_cast; ring

private lemma summable_norm_invSqHom : Summable (fun n : ℕ => ‖invSqHom n‖) := by
  have h_eq : (fun n : ℕ => ‖invSqHom n‖) = fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 := by
    ext n; simp only [invSqHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [h_eq]; exact hasSum_zeta_two.summable

private lemma tendsto_zeta2_euler :
    Filter.Tendsto (fun M : ℕ => ∏ p ∈ M.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹)
      Filter.atTop (nhds (Real.pi ^ 2 / 6)) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative summable_norm_invSqHom
  have htsum : (∑' n : ℕ, invSqHom n) = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  rw [htsum] at h; simpa [invSqHom] using h

private def oddZeta2Partial (M : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range M).filter (fun p => p.Prime ∧ 2 < p), (1 - 1 / (p : ℝ) ^ 2)⁻¹

private lemma tendsto_oddZeta2Partial :
    Filter.Tendsto oddZeta2Partial Filter.atTop (nhds (Real.pi ^ 2 / 8)) := by
  have hmul := tendsto_zeta2_euler.const_mul (3 / 4 : ℝ)
  rw [show (3 / 4 : ℝ) * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 8 by ring] at hmul
  refine hmul.congr' ?_; filter_upwards [Filter.eventually_ge_atTop 3] with M hM
  set S := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
  have h_ins : M.primesBelow = insert 2 S := by
    ext p; simp only [Nat.mem_primesBelow, Finset.mem_insert, S, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨hpM, hpr⟩ => (eq_or_lt_of_le hpr.two_le).elim (Or.inl ∘ Eq.symm)
      (fun hp2 => Or.inr ⟨hpM, hpr, hp2⟩),
      fun h => h.elim (fun h2 => ⟨by omega, h2 ▸ Nat.prime_two⟩) (fun ⟨hpM, hpr, _⟩ => ⟨hpM, hpr⟩)⟩
  rw [h_ins, Finset.prod_insert (by simp [S] : 2 ∉ S),
    show (1 - 1 / ((2 : ℕ) : ℝ) ^ 2)⁻¹ = (4 / 3 : ℝ) by norm_num]
  change (3 / 4 : ℝ) * ((4 / 3 : ℝ) * oddZeta2Partial M) = oddZeta2Partial M; ring

/-! ## 3. Accelerated Bounds on `H_0`, `C2_twin`, and `U_c` -/

section H0Acceleration
open BuchstabSwitching

private lemma summable_abs_h_J_ext : Summable (fun b : ℕ => |h_J b|) := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun b => ?_) summable_abs_h_J_mul_rpow
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [h_J_zero]
  · exact le_mul_of_one_le_right (abs_nonneg _)
      (Real.one_le_rpow (by exact_mod_cast Nat.pos_of_ne_zero hb0) (by norm_num))

private lemma tendsto_H0Partial_ext : Filter.Tendsto H0Partial Filter.atTop (nhds H_0) := by
  have hbound : ∀ M : ℕ, |H0Partial M - ∑ b ∈ Finset.range M, h_J b| ≤
      (∑' b : ℕ, |h_J b|) - ∑ b ∈ Finset.range M, |h_J b| := fun M => by
    set P := (Finset.range M).filter (fun p => p.Prime ∧ 2 < p)
    have hP : ∀ p ∈ P, p.Prime ∧ 2 < p := fun p hp => (Finset.mem_filter.mp hp).2
    let S_range := (Finset.range M).filter (fun b => Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2)
    have hsub_range : S_range ⊆ B_cubefree P := fun b hb => by
      simp only [S_range, Finset.mem_filter, Finset.mem_range, B_cubefree, Finset.mem_Icc] at hb ⊢
      rcases hb with ⟨hbM, hb_odd, hb_fac⟩
      have hb0 : b ≠ 0 := by rintro rfl; exact absurd hb_odd (by decide)
      have hb_pf : b.primeFactors ⊆ P := fun p hp => by
        have hp_pr := Nat.prime_of_mem_primeFactors hp; have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        have hp_ne2 : p ≠ 2 := by rintro rfl; exact Nat.not_even_iff_odd.mpr hb_odd (even_iff_two_dvd.mpr hp_dvd)
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hp_dvd; have := hp_pr.two_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_pr, by omega⟩
      have hb_le : b ≤ ∏ p ∈ P, p ^ 2 :=
        calc b = ∏ p ∈ b.primeFactors, p ^ b.factorization p := (prod_primeFactors_pow_factorization hb0).symm
          _ ≤ ∏ p ∈ b.primeFactors, p ^ 2 := Finset.prod_le_prod fun p hp =>
              Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (hb_fac p hp)
          _ ≤ ∏ p ∈ P, p ^ 2 := Finset.prod_le_prod_of_subset_of_one_le hb_pf fun p hp _ =>
              Nat.one_le_pow 2 p (hP p hp).1.pos
      exact ⟨⟨Nat.pos_of_ne_zero hb0, hb_le⟩, hb_odd, hb_pf, hb_fac⟩
    have hrange_eq : ∑ b ∈ Finset.range M, h_J b = ∑ b ∈ S_range, h_J b := by
      rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hc : Odd b ∧ ∀ p ∈ b.primeFactors, b.factorization p ≤ 2
      · exact (ite_eq_left hc).symm
      · rw [ite_eq_right hc]; unfold h_J; exact ite_eq_right hc
    have hsplit : H0Partial M = (∑ b ∈ Finset.range M, h_J b) + ∑ b ∈ B_cubefree P \ S_range, h_J b := by
      unfold H0Partial; rw [(sum_B_cubefree_h_J P hP).symm, hrange_eq, ← Finset.sum_sdiff hsub_range, add_comm]
    have hdisj : Disjoint (Finset.range M) (B_cubefree P \ S_range) := by
      rw [Finset.disjoint_left]; intro b hbM hbs; rw [Finset.mem_sdiff] at hbs
      exact hbs.2 (Finset.mem_filter.mpr ⟨hbM, (Finset.mem_filter.mp hbs.1).2.1, (Finset.mem_filter.mp hbs.1).2.2.2⟩)
    calc |H0Partial M - ∑ b ∈ Finset.range M, h_J b|
        = |∑ b ∈ B_cubefree P \ S_range, h_J b| := by rw [hsplit, add_sub_cancel_left]
      _ ≤ ∑ b ∈ B_cubefree P \ S_range, |h_J b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑' b : ℕ, |h_J b|) - ∑ b ∈ Finset.range M, |h_J b| := by
          have := summable_abs_h_J_ext.sum_le_tsum (Finset.range M ∪ (B_cubefree P \ S_range)) (fun _ _ => abs_nonneg _)
          rw [Finset.sum_union hdisj] at this; linarith
  have hdiff : Filter.Tendsto (fun M : ℕ => H0Partial M - ∑ b ∈ Finset.range M, h_J b) Filter.atTop (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
      (fun M => by simpa [Real.norm_eq_abs] using hbound M) ?_)
    have h0 : (∑' b : ℕ, |h_J b|) - (∑' b : ℕ, |h_J b|) = 0 := sub_self _
    rw [← h0]; exact tendsto_const_nhds.sub summable_abs_h_J_ext.hasSum.tendsto_sum_nat
  unfold H_0; simpa [sub_add_cancel, zero_add] using hdiff.add summable_h_J.hasSum.tendsto_sum_nat
private def h0RatioFactor (p : ℕ) : ℝ := (((p : ℝ) - 1) ^ 3 * ((p : ℝ) + 1)) / ((p : ℝ) ^ 3 * ((p : ℝ) - 2))
private def h0RatioPartial (M : ℕ) : ℝ := ∏ p ∈ (Finset.range M).filter (fun p => p.Prime ∧ 2 < p), h0RatioFactor p
private lemma h0RatioFactor_eq_div {p : ℕ} (hp : 3 ≤ p) :
    (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) / (1 - 1 / (p : ℝ) ^ 2)⁻¹ = h0RatioFactor p := by
  have hp_r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1mp : 1 - 1 / (p : ℝ) ^ 2 ≠ 0 := by
    linarith [show (1 : ℝ) / (p : ℝ) ^ 2 < 1 from (div_lt_one (by positivity)).mpr (by nlinarith)]
  unfold h0RatioFactor; field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 2 ≠ 0 by linarith, h1mp]; ring
private lemma h0RatioFactor_eq_one_add {p : ℕ} (hp : 3 ≤ p) :
    h0RatioFactor p = 1 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 3 * ((p : ℝ) - 2)) := by
  have hp_r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  unfold h0RatioFactor; field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 2 ≠ 0 by linarith]; ring
private lemma h0RatioFactor_one_le {p : ℕ} (hp : 3 ≤ p) : 1 ≤ h0RatioFactor p := by
  rw [h0RatioFactor_eq_one_add hp]; have hp_r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have : (0 : ℝ) < 2 * (p : ℝ) - 1 := by linarith
  linarith [show 0 ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 3 * ((p : ℝ) - 2)) by positivity]
private lemma tendsto_h0RatioPartial :
    Filter.Tendsto h0RatioPartial Filter.atTop (nhds (H_0 / (Real.pi ^ 2 / 8))) := by
  have hpi_ne : Real.pi ^ 2 / 8 ≠ 0 := by have := Real.pi_pos; positivity
  refine (tendsto_H0Partial_ext.div tendsto_oddZeta2Partial hpi_ne).congr fun M => ?_
  dsimp only [Pi.div_apply, H0Partial, oddZeta2Partial, h0RatioPartial]; rw [← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun p hp => h0RatioFactor_eq_div (Finset.mem_filter.mp hp).2.2

private def prodRatioIv (ps : List ℕ) (lo hi : ℕ) : ℕ × ℕ :=
  ps.foldl (fun (acc : ℕ × ℕ) p =>
    let q := p - 1; let num := q * q * q * (p + 1); let den := p * p * p * (p - 2)
    ((acc.1 * num) / den, ceilDivNat (acc.2 * num) den)) (lo, hi)

private lemma prodRatioIv_append (ps₁ ps₂ : List ℕ) (lo hi : ℕ) :
    prodRatioIv (ps₁ ++ ps₂) lo hi = prodRatioIv ps₂ (prodRatioIv ps₁ lo hi).1 (prodRatioIv ps₁ lo hi).2 := by
  simp [prodRatioIv, List.foldl_append]

private lemma prodRatioIv_sound (ps : List ℕ) (hps : ∀ p ∈ ps, 3 ≤ p) :
    ∀ (lo hi : ℕ),
      ((prodRatioIv ps lo hi).1 : ℝ) / (scale20 : ℝ) ≤ ((lo : ℝ) / (scale20 : ℝ)) * (ps.map h0RatioFactor).prod ∧
      ((hi : ℝ) / (scale20 : ℝ)) * (ps.map h0RatioFactor).prod ≤ ((prodRatioIv ps lo hi).2 : ℝ) / (scale20 : ℝ) := by
  induction ps with
  | nil => intro lo hi; simp [prodRatioIv]
  | cons p tl ih =>
    intro lo hi
    have hp3 := hps p List.mem_cons_self; have htl : ∀ q ∈ tl, 3 ≤ q := fun q hq => hps q (List.mem_cons_of_mem p hq)
    set num : ℕ := (p - 1) * (p - 1) * (p - 1) * (p + 1); set den : ℕ := p * p * p * (p - 2)
    have hden_pos : 0 < den := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
    have hfac_eq : h0RatioFactor p = (num : ℝ) / (den : ℝ) := by
      unfold h0RatioFactor; dsimp only [num, den]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)]; ring
    have hS := scale20_pos
    have hstep_lo : (((lo * num) / den : ℕ) : ℝ) / (scale20 : ℝ) ≤ ((lo : ℝ) / (scale20 : ℝ)) * ((num : ℝ) / (den : ℝ)) := by
      have h1 : (((lo * num) / den : ℕ) : ℝ) ≤ (lo : ℝ) * (num : ℝ) / (den : ℝ) := by
        simpa [Nat.cast_mul] using floorDivNat_le (a := lo * num) hden_pos
      calc (((lo * num) / den : ℕ) : ℝ) / (scale20 : ℝ)
          ≤ ((lo : ℝ) * (num : ℝ) / (den : ℝ)) / (scale20 : ℝ) := div_le_div_of_nonneg_right h1 hS.le
        _ = _ := by ring
    have hstep_hi : ((hi : ℝ) / (scale20 : ℝ)) * ((num : ℝ) / (den : ℝ)) ≤ ((ceilDivNat (hi * num) den : ℕ) : ℝ) / (scale20 : ℝ) := by
      have h1 : (hi : ℝ) * (num : ℝ) / (den : ℝ) ≤ ((ceilDivNat (hi * num) den : ℕ) : ℝ) := by
        simpa [Nat.cast_mul] using le_ceilDivNat (a := hi * num) hden_pos
      calc ((hi : ℝ) / (scale20 : ℝ)) * ((num : ℝ) / (den : ℝ))
          = ((hi : ℝ) * (num : ℝ) / (den : ℝ)) / (scale20 : ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right h1 hS.le
    have hrec := ih htl ((lo * num) / den) (ceilDivNat (hi * num) den)
    have hprod_nn : 0 ≤ (tl.map h0RatioFactor).prod := by
      refine List.prod_nonneg ?_; simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun q hq => le_trans zero_le_one (h0RatioFactor_one_le (htl q hq))
    dsimp only [prodRatioIv] at hrec ⊢; rw [List.foldl_cons, List.map_cons, List.prod_cons, hfac_eq]
    exact ⟨hrec.1.trans (by nlinarith), (by nlinarith : _ ≤ _).trans hrec.2⟩

private lemma pr_c0 : prodRatioIv opC0 scale20 scale20 = (122781972930976905528, 122781972930976905557) := by decide
private lemma pr_c1 : prodRatioIv opC1 122781972930976905528 122781972930976905557 = (122783219011230264382, 122783219011230264441) := by decide
private lemma pr_c2 : prodRatioIv opC2 122783219011230264382 122783219011230264441 = (122783371151577045565, 122783371151577045654) := by decide
private lemma pr_c3 : prodRatioIv opC3 122783371151577045565 122783371151577045654 = (122783413504557463588, 122783413504557463707) := by decide
private lemma pr_c4 : prodRatioIv opC4 122783413504557463588 122783413504557463707 = (122783430441486492287, 122783430441486492436) := by decide
private lemma pr_c5 : prodRatioIv opC5 122783430441486492287 122783430441486492436 = (122783438529500930770, 122783438529500930949) := by decide
private lemma pr_c6 : prodRatioIv opC6 122783438529500930770 122783438529500930949 = (122783443016662184785, 122783443016662184994) := by decide
private lemma pr_c7 : prodRatioIv opC7 122783443016662184785 122783443016662184994 = (122783445677621200401, 122783445677621200640) := by decide
private lemma pr_c8 : prodRatioIv opC8 122783445677621200401 122783445677621200640 = (122783447413881145795, 122783447413881146064) := by decide
private lemma pr_c9 : prodRatioIv opC9 122783447413881145795 122783447413881146064 = (122783448570829840722, 122783448570829841021) := by decide
private lemma pr_c10 : prodRatioIv opC10 122783448570829840722 122783448570829841021 = (122783448663496285151, 122783448663496285453) := by decide

private lemma h0RatioPartial_2000_bounds :
    (122783448663496285151 : ℝ) / (scale20 : ℝ) ≤ h0RatioPartial 2000 ∧
      h0RatioPartial 2000 ≤ (122783448663496285453 : ℝ) / (scale20 : ℝ) := by
  have hprod_eq : h0RatioPartial 2000 = (oddPrimes2000.map h0RatioFactor).prod := by
    unfold h0RatioPartial; rw [← oddPrimes2000_toFinset, List.prod_toFinset _ oddPrimes2000_nodup]
  have hsnd := prodRatioIv_sound oddPrimes2000 oddPrimes2000_ge3 scale20 scale20
  have hcheck : prodRatioIv oddPrimes2000 scale20 scale20 = (122783448663496285151, 122783448663496285453) := by
    simp only [oddPrimes2000, prodRatioIv_append]
    rw [pr_c0, pr_c1, pr_c2, pr_c3, pr_c4, pr_c5, pr_c6, pr_c7, pr_c8, pr_c9, pr_c10]
  rw [hcheck, div_self scale20_pos.ne', one_mul, ← hprod_eq] at hsnd; exact hsnd

private lemma h0_tail_term_le {j : ℕ} (hj : 1000 ≤ j) :
    (2 * ((2 * j + 1 : ℕ) : ℝ) - 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 3 * (((2 * j + 1 : ℕ) : ℝ) - 2)) ≤
      (1 / (8 * (((j : ℝ) - 1) * (j : ℝ))) - 1 / (8 * ((((j + 1 : ℕ) : ℝ) - 1) * ((j + 1 : ℕ) : ℝ)))) := by
  have hj_r : (4 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 4 ≤ j)
  clear hj; set x : ℝ := 2 * (j : ℝ) + 1
  rw [show ((2 * j + 1 : ℕ) : ℝ) = x by push_cast; rfl, show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; rfl]
  have hj1 : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hj2 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hxm3 : 0 < x - 3 := by dsimp [x]; linarith
  have hxm2 : 0 < x - 2 := by dsimp [x]; linarith
  have hxm1 : 0 < x - 1 := by dsimp [x]; linarith
  have hx0 : 0 < x := by linarith
  have hxp1 : 0 < x + 1 := by linarith
  have htel_id : 1 / (8 * (((j : ℝ) - 1) * (j : ℝ))) -
      1 / (8 * (((j : ℝ) + 1 - 1) * ((j : ℝ) + 1))) = 2 / ((x - 3) * (x - 1) * (x + 1)) := by
    rw [show x - 3 = 2 * ((j : ℝ) - 1) by dsimp [x]; ring, show x - 1 = 2 * (j : ℝ) by dsimp [x]; ring,
      show x + 1 = 2 * ((j : ℝ) + 1) by dsimp [x]; ring, add_sub_cancel_right]
    field_simp [hj1.ne', hj0.ne', hj2.ne']; ring
  rw [htel_id, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpoly : 2 * (x ^ 3 * (x - 2)) - (2 * x - 1) * ((x - 3) * (x - 1) * (x + 1)) =
      (x - 2) * (3 * x ^ 2 + 5 * x + 3) + 9 := by ring
  linarith [show 0 ≤ (x - 2) * (3 * x ^ 2 + 5 * x + 3) by positivity]
private lemma h0Ratio_limit_bounds :
    (122783448663496285151 : ℝ) / (scale20 : ℝ) ≤ H_0 / (Real.pi ^ 2 / 8) ∧
      H_0 / (Real.pi ^ 2 / 8) ≤ ((122783448663496285453 : ℝ) / (scale20 : ℝ)) * (7992000 / 7991999 : ℝ) := by
  constructor
  · have hle : ∀ M : ℕ, 2000 ≤ M → h0RatioPartial 2000 ≤ h0RatioPartial M := fun M hM =>
      Finset.prod_le_prod_of_subset_of_one_le₀
        (fun p hp => by simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩)
        (fun p hp => le_trans zero_le_one (h0RatioFactor_one_le (Finset.mem_filter.mp hp).2.2))
        (fun p hp _ => h0RatioFactor_one_le (Finset.mem_filter.mp hp).2.2)
    exact h0RatioPartial_2000_bounds.1.trans (le_of_tendsto_of_tendsto tendsto_const_nhds
      tendsto_h0RatioPartial (Filter.eventually_atTop.mpr ⟨2000, hle⟩))
  · have hbound : ∀ M : ℕ, 2000 ≤ M →
        h0RatioPartial M ≤ h0RatioPartial 2000 * Real.exp (1 / 7992000 : ℝ) := fun M hM => by
      set P_2000 := (Finset.range 2000).filter (fun p => p.Prime ∧ 2 < p)
      set P_tail := (Finset.Ico 2000 M).filter (fun p => p.Prime ∧ 2 < p)
      have hdisj : Disjoint P_2000 P_tail := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        have := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
        have := Finset.mem_Ico.mp (Finset.mem_filter.mp hp2).1; omega
      have hunion : (Finset.range M).filter (fun p => p.Prime ∧ 2 < p) = P_2000 ∪ P_tail := by
        ext p; simp only [P_2000, P_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        exact ⟨fun ⟨h1, h2⟩ => if h : p < 2000 then Or.inl ⟨h, h2⟩ else Or.inr ⟨⟨by omega, h1⟩, h2⟩,
          fun h => h.elim (fun ⟨h1, h2⟩ => ⟨by omega, h2⟩) (fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩)⟩
      rw [show h0RatioPartial M = h0RatioPartial 2000 * ∏ p ∈ P_tail, h0RatioFactor p by
        unfold h0RatioPartial; rw [hunion, Finset.prod_union hdisj]]
      refine mul_le_mul_of_nonneg_left ?_ (le_trans (div_nonneg (by norm_num) scale20_pos.le) h0RatioPartial_2000_bounds.1)
      have hprod_le : ∏ p ∈ P_tail, h0RatioFactor p ≤
          ∏ p ∈ P_tail, Real.exp ((2 * (p : ℝ) - 1) / ((p : ℝ) ^ 3 * ((p : ℝ) - 2))) :=
        Finset.prod_le_prod₀
          (fun p hp => le_trans zero_le_one (h0RatioFactor_one_le (Finset.mem_filter.mp hp).2.2))
          (fun p hp => by rw [h0RatioFactor_eq_one_add (Finset.mem_filter.mp hp).2.2, add_comm]; exact Real.add_one_le_exp _)
      rw [← Real.exp_sum] at hprod_le
      refine hprod_le.trans (Real.exp_le_exp.mpr ((sum_odd_primes_Ico_le hM
        (fun p => (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 3 * ((p : ℝ) - 2)))
        (fun j => 1 / (8 * (((j : ℝ) - 1) * (j : ℝ))))
        (fun j hj => by
          have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ j)
          have : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) - 2 := by push_cast; linarith
          have : (0 : ℝ) < 2 * ((2 * j + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
          positivity)
        (fun j hj => by
          have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ j)
          have : (0 : ℝ) < (j : ℝ) - 1 := by linarith
          positivity)
        (fun j hj => h0_tail_term_le hj)).trans (by norm_num)))
    have hH_le := le_of_tendsto tendsto_h0RatioPartial (Filter.eventually_atTop.mpr ⟨2000, hbound⟩)
    have hexp : Real.exp (1 / 7992000 : ℝ) ≤ (7992000 / 7991999 : ℝ) := by
      have h2 : (7991999 / 7992000 : ℝ) ≤ Real.exp (-(1 / 7992000 : ℝ)) := by
        linarith [Real.add_one_le_exp (-(1 / 7992000 : ℝ))]
      rw [Real.exp_neg] at h2; simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7991999 / 7992000) h2
    exact hH_le.trans (mul_le_mul h0RatioPartial_2000_bounds.2 hexp (Real.exp_pos _).le (by unfold scale20; positivity))

end H0Acceleration

private lemma H0_bounds_internal :
    (1.51478008 : ℝ) ≤ BuchstabSwitching.H_0 ∧ BuchstabSwitching.H_0 ≤ (1.51478028 : ℝ) := by
  have hpi_lo : (314159265358979323846 / 10 ^ 20 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hpi_hi : Real.pi < (314159265358979323847 / 10 ^ 20 : ℝ) := by linarith [Real.pi_lt_d20]
  have hpi8_pos : 0 < Real.pi ^ 2 / 8 := by positivity
  have hpi_sq_lo : (314159265358979323846 / 10 ^ 20 : ℝ) ^ 2 / 8 ≤ Real.pi ^ 2 / 8 := by
    have := sq_le_sq' (by linarith) hpi_lo.le; linarith
  have hpi_sq_hi : Real.pi ^ 2 / 8 ≤ (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 / 8 := by
    have := sq_le_sq' (by linarith [Real.pi_pos]) hpi_hi.le; linarith
  have hlim := h0Ratio_limit_bounds; constructor
  · have h1 := (le_div_iff₀ hpi8_pos).mp hlim.1
    have h2 := mul_le_mul_of_nonneg_left hpi_sq_lo
      (by unfold scale20; positivity : (0 : ℝ) ≤ (122783448663496285151 : ℝ) / (scale20 : ℝ))
    exact (by unfold scale20; norm_num : (1.51478008 : ℝ) ≤ _).trans (h2.trans h1)
  · have h1 := (div_le_iff₀ hpi8_pos).mp hlim.2
    have h2 := mul_le_mul_of_nonneg_left hpi_sq_hi (by unfold scale20; positivity : (0 : ℝ) ≤
      ((122783448663496285453 : ℝ) / (scale20 : ℝ)) * (7992000 / 7991999 : ℝ))
    exact h1.trans (h2.trans (by unfold scale20; norm_num))

theorem H0_bounds_cert_tight :
    (1.514780025472119 : ℝ) ≤ BuchstabSwitching.H_0 ∧
      BuchstabSwitching.H_0 ≤ (1.514780782862509 : ℝ) := by
  have h := H0_bounds_internal; constructor <;> linarith

theorem C2_twin_bounds_cert :
    (0.660161530508911 : ℝ) ≤ 1 / BuchstabSwitching.H_0 ∧
      1 / BuchstabSwitching.H_0 ≤ (0.660161860589840 : ℝ) := by
  have h := H0_bounds_internal; have hpos : (0 : ℝ) < BuchstabSwitching.H_0 := by linarith [h.1]
  exact ⟨(by norm_num : (0.660161530508911 : ℝ) ≤ 1 / (1.51478028 : ℝ)).trans (one_div_le_one_div_of_le hpos h.2),
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1.51478008) h.1).trans (by norm_num)⟩

theorem U_c_bounds_cert :
    (1.320323061017821 : ℝ) ≤ 2 * (1 / BuchstabSwitching.H_0) ∧
      2 * (1 / BuchstabSwitching.H_0) ≤ (1.320323721179681 : ℝ) := by
  have hC2 := C2_twin_bounds_cert; constructor <;> linarith

/-! ## 4. Accelerated Bounds on `meisselMertensConst - Real.eulerMascheroniConstant` -/

private def mmDelta (p : ℕ) : ℝ :=
  -(Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) - (1 / 2 : ℝ) * (-Real.log (1 - 1 / (p : ℝ) ^ 2))
private lemma tendsto_mmPartial :
    Filter.Tendsto (fun M : ℕ => ∑ p ∈ M.primesBelow, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))
      Filter.atTop (nhds (meisselMertensConst - Real.eulerMascheroniConstant)) := by
  let g : ℕ → ℝ := fun n => Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)
  have hhs : HasSum (g ∘ Subtype.val (p := (· ∈ {n : ℕ | n.Prime}))) (∑' p : Nat.Primes, g p.1) :=
    summable_meisselMertens_term.hasSum
  have hsub : meisselMertensConst - Real.eulerMascheroniConstant = ∑' p : Nat.Primes, g p.1 := by
    unfold meisselMertensConst g; ring
  rw [hsub]
  refine (hasSum_subtype_iff_indicator.mp hhs).tendsto_sum_nat.congr fun M => ?_
  rw [Nat.primesBelow, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime <;> simp [Set.indicator, hn, g]
private lemma tendsto_zeta2LogPartial :
    Filter.Tendsto (fun M : ℕ => ∑ p ∈ M.primesBelow, -Real.log (1 - 1 / (p : ℝ) ^ 2))
      Filter.atTop (nhds (Real.log (Real.pi ^ 2 / 6))) := by
  have hpi6_ne : Real.pi ^ 2 / 6 ≠ 0 := by have := Real.pi_pos; positivity
  refine ((Real.continuousAt_log hpi6_ne).tendsto.comp tendsto_zeta2_euler).congr fun M => ?_
  dsimp only [Function.comp_def]; rw [Real.log_prod fun p hp => ?_]
  · exact Finset.sum_congr rfl fun p _ => Real.log_inv _
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have : 0 < 1 - 1 / (p : ℝ) ^ 2 := by
      linarith [show (1 : ℝ) / (p : ℝ) ^ 2 < 1 from (div_lt_one (by positivity)).mpr (by nlinarith)]
    positivity
private lemma tendsto_mmDeltaPartial :
    Filter.Tendsto (fun M : ℕ => ∑ p ∈ M.primesBelow, mmDelta p) Filter.atTop
      (nhds (-(meisselMertensConst - Real.eulerMascheroniConstant) - (1 / 2 : ℝ) * Real.log (Real.pi ^ 2 / 6))) := by
  refine (tendsto_mmPartial.neg.sub (tendsto_zeta2LogPartial.const_mul (1 / 2 : ℝ))).congr fun M => ?_
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]; rfl

private lemma hasSum_mmDelta {p : ℕ} (hp : 2 ≤ p) :
    HasSum (fun m : ℕ => 1 / ((2 * (m : ℝ) + 3) * (p : ℝ) ^ (2 * m + 3))) (mmDelta p) := by
  have hp_r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hx_lt1 : |1 / (p : ℝ)| < 1 := by rw [abs_of_pos (by positivity)]; exact (div_lt_one hp_pos).mpr (by linarith)
  have h1mx_pos : 0 < 1 - 1 / (p : ℝ) := by linarith [(div_lt_one hp_pos).mpr (by linarith : (1 : ℝ) < p)]
  have hlog_sq : Real.log (1 - 1 / (p : ℝ) ^ 2) = Real.log (1 - 1 / (p : ℝ)) + Real.log (1 + 1 / (p : ℝ)) := by
    rw [show 1 - 1 / (p : ℝ) ^ 2 = (1 - 1 / (p : ℝ)) * (1 + 1 / (p : ℝ)) by ring, Real.log_mul h1mx_pos.ne' (by positivity)]
  have hshift := (hasSum_nat_add_iff' 1).mpr ((Real.hasSum_log_sub_log_of_abs_lt_one hx_lt1).mul_left (1 / 2 : ℝ))
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, div_one, pow_one] at hshift
  rw [show (1 / 2 : ℝ) * (Real.log (1 + 1 / (p : ℝ)) - Real.log (1 - 1 / (p : ℝ))) -
      (1 / 2 : ℝ) * (2 * 1 * (1 / (p : ℝ))) = mmDelta p by unfold mmDelta; rw [hlog_sq]; ring] at hshift
  refine hshift.congr_fun fun m => ?_
  have hm3 : (2 * ((m + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  have hm3' : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
  rw [one_div_pow]; push_cast; field_simp [hp_pos.ne', hm3, hm3']; ring

private lemma mmDelta_bounds (K : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    (∑ m ∈ Finset.range K, 1 / ((2 * (m : ℝ) + 3) * (p : ℝ) ^ (2 * m + 3))) ≤ mmDelta p ∧
      mmDelta p ≤ (∑ m ∈ Finset.range K, 1 / ((2 * (m : ℝ) + 3) * (p : ℝ) ^ (2 * m + 3))) +
        1 / ((2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 1) * ((p : ℝ) ^ 2 - 1)) := by
  have hp_r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hshift := (hasSum_nat_add_iff' K).mpr (hasSum_mmDelta hp)
  set S := ∑ m ∈ Finset.range K, 1 / ((2 * (m : ℝ) + 3) * (p : ℝ) ^ (2 * m + 3))
  constructor
  · linarith [hasSum_le (fun _ => by positivity) hasSum_zero hshift]
  · have hr_lt1 : 1 / (p : ℝ) ^ 2 < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    have hgeom := (hasSum_geometric_of_lt_one (by positivity) hr_lt1).mul_left
      (1 / ((2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 3)))
    have hle : mmDelta p - S ≤ (1 / ((2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 3))) * (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
      refine hasSum_le (fun d => ?_) hshift hgeom
      have hden_le : (2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 3) * ((p : ℝ) ^ 2) ^ d ≤
          (2 * ((d + K : ℕ) : ℝ) + 3) * (p : ℝ) ^ (2 * (d + K) + 3) := by
        rw [mul_assoc, show (p : ℝ) ^ (2 * K + 3) * ((p : ℝ) ^ 2) ^ d = (p : ℝ) ^ (2 * (d + K) + 3) by
          rw [← pow_mul, ← pow_add]; congr 1; omega]
        exact mul_le_mul_of_nonneg_right (by push_cast; linarith) (by positivity)
      calc 1 / ((2 * ((d + K : ℕ) : ℝ) + 3) * (p : ℝ) ^ (2 * (d + K) + 3))
          ≤ 1 / ((2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 3) * ((p : ℝ) ^ 2) ^ d) := one_div_le_one_div_of_le (by positivity) hden_le
        _ = (1 / ((2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 3))) * (1 / (p : ℝ) ^ 2) ^ d := by rw [one_div_pow]; field_simp
    have hp2_1 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h1mp : 1 - 1 / (p : ℝ) ^ 2 ≠ 0 := by linarith
    have hk3 : 2 * (K : ℝ) + 3 ≠ 0 := by positivity
    have hsimp : (1 / ((2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 3))) * (1 - 1 / (p : ℝ) ^ 2)⁻¹ =
        1 / ((2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 1) * ((p : ℝ) ^ 2 - 1)) := by
      rw [show (p : ℝ) ^ (2 * K + 3) = (p : ℝ) ^ (2 * K + 1) * (p : ℝ) ^ 2 by rw [← pow_add]]
      field_simp [hp_pos.ne', hp2_1, h1mp, hk3]
    rw [hsimp] at hle; linarith

private def kOfPrime (p : ℕ) : ℕ := if p < 10 then 11 else if p < 100 then 3 else 1

private def mmSumRec (p : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | k + 1 =>
    let r := mmSumRec p k; let e := 2 * k + 3; let den := e * p ^ e
    (r.1 + scale20 / den, r.2 + ceilDivNat scale20 den)

private def mmPrimeIv (p : ℕ) : ℕ × ℕ :=
  let K := kOfPrime p; let r := mmSumRec p K
  (r.1, r.2 + ceilDivNat scale20 ((2 * K + 3) * p ^ (2 * K + 1) * (p * p - 1)))

private def sumMmIv (ps : List ℕ) (lo hi : ℕ) : ℕ × ℕ :=
  ps.foldl (fun (acc : ℕ × ℕ) p => let d := mmPrimeIv p; (acc.1 + d.1, acc.2 + d.2)) (lo, hi)

private lemma sumMmIv_append (ps₁ ps₂ : List ℕ) (lo hi : ℕ) :
    sumMmIv (ps₁ ++ ps₂) lo hi = sumMmIv ps₂ (sumMmIv ps₁ lo hi).1 (sumMmIv ps₁ lo hi).2 := by
  simp [sumMmIv, List.foldl_append]

private lemma mmSumRec_sound {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    ((mmSumRec p n).1 : ℝ) / (scale20 : ℝ) ≤ ∑ m ∈ Finset.range n, 1 / ((2 * (m : ℝ) + 3) * (p : ℝ) ^ (2 * m + 3)) ∧
    ∑ m ∈ Finset.range n, 1 / ((2 * (m : ℝ) + 3) * (p : ℝ) ^ (2 * m + 3)) ≤ ((mmSumRec p n).2 : ℝ) / (scale20 : ℝ) := by
  induction n with
  | zero => simp [mmSumRec]
  | succ k ih =>
    rw [Finset.sum_range_succ]; set den : ℕ := (2 * k + 3) * p ^ (2 * k + 3)
    have hden_pos : 0 < den := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    have hden_eq : (den : ℝ) = (2 * (k : ℝ) + 3) * (p : ℝ) ^ (2 * k + 3) := by dsimp [den]; push_cast; rfl
    have hS := scale20_pos
    have hlo : ((scale20 / den : ℕ) : ℝ) / (scale20 : ℝ) ≤ 1 / (den : ℝ) := by
      calc ((scale20 / den : ℕ) : ℝ) / (scale20 : ℝ)
          ≤ ((scale20 : ℝ) / (den : ℝ)) / (scale20 : ℝ) := div_le_div_of_nonneg_right (floorDivNat_le hden_pos) hS.le
        _ = 1 / (den : ℝ) := by field_simp [hS.ne']
    have hhi : 1 / (den : ℝ) ≤ ((ceilDivNat scale20 den : ℕ) : ℝ) / (scale20 : ℝ) := by
      calc 1 / (den : ℝ) = ((scale20 : ℝ) / (den : ℝ)) / (scale20 : ℝ) := by field_simp [hS.ne']
        _ ≤ ((ceilDivNat scale20 den : ℕ) : ℝ) / (scale20 : ℝ) := div_le_div_of_nonneg_right (le_ceilDivNat hden_pos) hS.le
    rw [hden_eq] at hlo hhi; dsimp only [mmSumRec]
    constructor <;> (push_cast; rw [add_div]; linarith [ih.1, ih.2, hlo, hhi])

private lemma mmPrimeIv_sound {p : ℕ} (hp : 2 ≤ p) :
    ((mmPrimeIv p).1 : ℝ) / (scale20 : ℝ) ≤ mmDelta p ∧ mmDelta p ≤ ((mmPrimeIv p).2 : ℝ) / (scale20 : ℝ) := by
  set K := kOfPrime p; have hK := mmDelta_bounds K hp; have hr := mmSumRec_sound hp K
  set tden : ℕ := (2 * K + 3) * p ^ (2 * K + 1) * (p * p - 1)
  have htden_pos : 0 < tden := Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
    (by have := Nat.mul_le_mul hp hp; omega)
  have htden_eq : (tden : ℝ) = (2 * (K : ℝ) + 3) * (p : ℝ) ^ (2 * K + 1) * ((p : ℝ) ^ 2 - 1) := by
    dsimp [tden]; push_cast [Nat.cast_sub (by nlinarith : 1 ≤ p * p)]; ring
  have hS := scale20_pos
  have htail : 1 / (tden : ℝ) ≤ ((ceilDivNat scale20 tden : ℕ) : ℝ) / (scale20 : ℝ) := by
    calc 1 / (tden : ℝ) = ((scale20 : ℝ) / (tden : ℝ)) / (scale20 : ℝ) := by field_simp [hS.ne']
      _ ≤ ((ceilDivNat scale20 tden : ℕ) : ℝ) / (scale20 : ℝ) := div_le_div_of_nonneg_right (le_ceilDivNat htden_pos) hS.le
  rw [htden_eq] at htail
  change ((mmSumRec p K).1 : ℝ) / (scale20 : ℝ) ≤ mmDelta p ∧
    mmDelta p ≤ (((mmSumRec p K).2 + ceilDivNat scale20 tden : ℕ) : ℝ) / (scale20 : ℝ)
  exact ⟨hr.1.trans hK.1, hK.2.trans (by push_cast; rw [add_div]; linarith [hr.2, htail])⟩

private lemma sumMmIv_sound (ps : List ℕ) (hps : ∀ p ∈ ps, 2 ≤ p) :
    ∀ (lo hi : ℕ),
      ((sumMmIv ps lo hi).1 : ℝ) / (scale20 : ℝ) ≤ (lo : ℝ) / (scale20 : ℝ) + (ps.map mmDelta).sum ∧
      (hi : ℝ) / (scale20 : ℝ) + (ps.map mmDelta).sum ≤ ((sumMmIv ps lo hi).2 : ℝ) / (scale20 : ℝ) := by
  induction ps with
  | nil => intro lo hi; simp [sumMmIv]
  | cons p tl ih =>
    intro lo hi; have hp_iv := mmPrimeIv_sound (hps p List.mem_cons_self)
    have hrec := ih (fun q hq => hps q (List.mem_cons_of_mem p hq)) (lo + (mmPrimeIv p).1) (hi + (mmPrimeIv p).2)
    dsimp only [sumMmIv] at hrec ⊢; rw [List.foldl_cons, List.map_cons, List.sum_cons]
    exact ⟨hrec.1.trans (by push_cast; rw [add_div]; linarith [hp_iv.1]),
      (by push_cast; rw [add_div]; linarith [hp_iv.2] : _ ≤ _).trans hrec.2⟩

private lemma mm_p2 : mmPrimeIv 2 = (4930614278214691663, 4930614437160411075) := by decide
private lemma mm_c0 : sumMmIv opC0 4930614278214691663 4930614437160411075 = (6686630754517637761, 6686630926850390029) := by decide
private lemma mm_c1 : sumMmIv opC1 6686630754517637761 6686630926850390029 = (6686798337001061688, 6686798513281641748) := by decide
private lemma mm_c2 : sumMmIv opC2 6686798337001061688 6686798513281641748 = (6686818899983154024, 6686819076366430888) := by decide
private lemma mm_c3 : sumMmIv opC3 6686818899983154024 6686819076366430888 = (6686824633213459870, 6686824809608354687) := by decide
private lemma mm_c4 : sumMmIv opC4 6686824633213459870 6686824809608354687 = (6686826927627413784, 6686827104024782200) := by decide
private lemma mm_c5 : sumMmIv opC5 6686826927627413784 6686827104024782200 = (6686828023785457673, 6686828200183538805) := by decide
private lemma mm_c6 : sumMmIv opC6 6686828023785457673 6686828200183538805 = (6686828632095024783, 6686828808493372054) := by decide
private lemma mm_c7 : sumMmIv opC7 6686828632095024783 6686828808493372054 = (6686828992906780176, 6686829169305238554) := by decide
private lemma mm_c8 : sumMmIv opC8 6686828992906780176 6686829169305238554 = (6686829228368315557, 6686829404766828225) := by decide
private lemma mm_c9 : sumMmIv opC9 6686829228368315557 6686829404766828225 = (6686829385285441259, 6686829561683981570) := by decide
private lemma mm_c10 : sumMmIv opC10 6686829385285441259 6686829561683981570 = (6686829397854561949, 6686829574253104157) := by decide
private lemma mm_tail_term_le {j : ℕ} (hj : 1000 ≤ j) :
    1 / (3 * ((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) ^ 2 - 1)) ≤
      (1 / (12 * ((2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1))) -
        1 / (12 * ((2 * ((j + 1 : ℕ) : ℝ) - 1) * (2 * ((j + 1 : ℕ) : ℝ) + 1)))) := by
  have hj_r : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 3 ≤ j)
  clear hj; set x : ℝ := 2 * (j : ℝ) + 1
  rw [show ((2 * j + 1 : ℕ) : ℝ) = x by push_cast; rfl, show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; rfl]
  have hxm2 : 0 < x - 2 := by dsimp [x]; linarith
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hxp2 : 0 < x + 2 := by dsimp [x]; linarith
  have htel_id : 1 / (12 * ((2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1))) -
      1 / (12 * ((2 * ((j : ℝ) + 1) - 1) * (2 * ((j : ℝ) + 1) + 1))) = 1 / (3 * (x - 2) * x * (x + 2)) := by
    rw [show 2 * (j : ℝ) - 1 = x - 2 by dsimp [x]; ring, show 2 * ((j : ℝ) + 1) - 1 = x by dsimp [x]; ring,
      show 2 * ((j : ℝ) + 1) + 1 = x + 2 by dsimp [x]; ring]
    change 1 / (12 * ((x - 2) * x)) - 1 / (12 * (x * (x + 2))) = 1 / (3 * (x - 2) * x * (x + 2))
    field_simp [hxm2.ne', hx0.ne', hxp2.ne']; ring
  rw [htel_id]; refine one_div_le_one_div_of_le (by positivity) ?_
  linarith [show 3 * x * (x ^ 2 - 1) - 3 * (x - 2) * x * (x + 2) = 9 * x by ring]
private lemma mmDelta_limit_bounds :
    (6686829397854561949 : ℝ) / (scale20 : ℝ) ≤
      -(meisselMertensConst - Real.eulerMascheroniConstant) - (1 / 2 : ℝ) * Real.log (Real.pi ^ 2 / 6) ∧
    -(meisselMertensConst - Real.eulerMascheroniConstant) - (1 / 2 : ℝ) * Real.log (Real.pi ^ 2 / 6) ≤
      (6686829574253104157 : ℝ) / (scale20 : ℝ) + 1 / (12 * 1999 * 2001 : ℝ) := by
  have h2000_eq : ∑ p ∈ (2000 : ℕ).primesBelow, mmDelta p = (primes2000.map mmDelta).sum := by
    rw [← primes2000_toFinset, List.sum_toFinset _ primes2000_nodup]
  have hsnd := sumMmIv_sound primes2000 (fun p hp => (List.mem_cons.mp hp).elim (by omega)
    (fun h => le_trans (by decide : 2 ≤ 3) (oddPrimes2000_ge3 p h))) 0 0
  have hcheck : sumMmIv primes2000 0 0 = (6686829397854561949, 6686829574253104157) := by
    simp only [primes2000, oddPrimes2000, sumMmIv, List.foldl_cons, zero_add]
    change sumMmIv ((((((((((opC0 ++ opC1) ++ opC2) ++ opC3) ++ opC4) ++ opC5) ++ opC6) ++ opC7) ++ opC8) ++ opC9) ++ opC10)
      (mmPrimeIv 2).1 (mmPrimeIv 2).2 = _
    simp only [mm_p2, sumMmIv_append]
    rw [mm_c0, mm_c1, mm_c2, mm_c3, mm_c4, mm_c5, mm_c6, mm_c7, mm_c8, mm_c9, mm_c10]
  simp only [hcheck, Nat.cast_zero, zero_div, zero_add, ← h2000_eq] at hsnd; constructor
  · have hle : ∀ M : ℕ, 2000 ≤ M → ∑ p ∈ (2000 : ℕ).primesBelow, mmDelta p ≤ ∑ p ∈ M.primesBelow, mmDelta p :=
      fun M hM => Finset.sum_le_sum_of_subset_of_nonneg
        (fun p hp => by rw [Nat.mem_primesBelow] at hp ⊢; exact ⟨by omega, hp.2⟩)
        (fun p hp _ => by simpa using (mmDelta_bounds 0 (Nat.mem_primesBelow.mp hp).2.two_le).1)
    exact hsnd.1.trans (le_of_tendsto_of_tendsto tendsto_const_nhds tendsto_mmDeltaPartial
      (Filter.eventually_atTop.mpr ⟨2000, hle⟩))
  · have hub : ∀ M : ℕ, 2000 ≤ M → ∑ p ∈ M.primesBelow, mmDelta p ≤
        (∑ p ∈ (2000 : ℕ).primesBelow, mmDelta p) + 1 / (12 * 1999 * 2001 : ℝ) := fun M hM => by
      set P_tail := (Finset.Ico 2000 M).filter (fun p => p.Prime ∧ 2 < p)
      have hdisj : Disjoint (2000 : ℕ).primesBelow P_tail := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        have := (Nat.mem_primesBelow.mp hp1).1; have := Finset.mem_Ico.mp (Finset.mem_filter.mp hp2).1; omega
      have hunion : M.primesBelow = (2000 : ℕ).primesBelow ∪ P_tail := by
        ext p; simp only [Nat.mem_primesBelow, P_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨fun ⟨h1, h2⟩ => if h : p < 2000 then Or.inl ⟨h, h2⟩ else Or.inr ⟨⟨by omega, h1⟩, h2, by omega⟩,
          fun h => h.elim (fun ⟨h1, h2⟩ => ⟨by omega, h2⟩) (fun ⟨⟨_, h1⟩, h2, _⟩ => ⟨h1, h2⟩)⟩
      rw [hunion, Finset.sum_union hdisj]; refine add_le_add le_rfl ?_
      have h1 : ∑ p ∈ P_tail, mmDelta p ≤ ∑ p ∈ P_tail, 1 / (3 * (p : ℝ) * ((p : ℝ) ^ 2 - 1)) :=
        Finset.sum_le_sum fun p hp => by simpa using (mmDelta_bounds 0 (Finset.mem_filter.mp hp).2.1.two_le).2
      refine h1.trans ((sum_odd_primes_Ico_le hM
        (fun p => 1 / (3 * (p : ℝ) * ((p : ℝ) ^ 2 - 1)))
        (fun j => 1 / (12 * ((2 * (j : ℝ) - 1) * (2 * (j : ℝ) + 1))))
        (fun j hj => by
          have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ j)
          set x : ℝ := 2 * (j : ℝ) + 1; rw [show ((2 * j + 1 : ℕ) : ℝ) = x by push_cast; rfl]
          have hx0 : 0 < x := by dsimp [x]; linarith
          have hxm1 : 0 < x - 1 := by dsimp [x]; linarith
          have hxp1 : 0 < x + 1 := by dsimp [x]; linarith
          have hsq : 0 < x ^ 2 - 1 := by rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]; positivity
          positivity)
        (fun j hj => by
          have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ j)
          have : 0 < 2 * (j : ℝ) - 1 := by linarith
          positivity)
        (fun j hj => mm_tail_term_le hj)).trans (by norm_num))
    exact (le_of_tendsto tendsto_mmDeltaPartial (Filter.eventually_atTop.mpr ⟨2000, hub⟩)).trans
      (add_le_add hsnd.2 le_rfl)

private lemma log_zeta2_bounds :
    (497700300539 / 10 ^ 12 : ℝ) ≤ Real.log (Real.pi ^ 2 / 6) ∧
      Real.log (Real.pi ^ 2 / 6) ≤ (497700303198 / 10 ^ 12 : ℝ) := by
  set x : ℝ := Real.pi ^ 2 / 6
  have hpi_lo : (314159265358979323846 / 10 ^ 20 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hpi_hi : Real.pi < (314159265358979323847 / 10 ^ 20 : ℝ) := by linarith [Real.pi_lt_d20]
  have hx_lo : (314159265358979323846 / 10 ^ 20 : ℝ) ^ 2 / 6 ≤ x := by
    dsimp [x]; have := sq_le_sq' (by linarith) hpi_lo.le; linarith
  have hx_hi : x ≤ (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 / 6 := by
    dsimp [x]; have := sq_le_sq' (by linarith [Real.pi_pos]) hpi_hi.le; linarith
  set u : ℝ := (x - 1) / (x + 1)
  have hu_eq : u = 1 - 2 / (x + 1) := by dsimp [u]; field_simp [show x + 1 ≠ 0 by linarith]; ring
  have hu_lo : (2438374834 / 10 ^ 10 : ℝ) ≤ u := by
    rw [hu_eq]; linarith [div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)
      (by linarith : (314159265358979323846 / 10 ^ 20 : ℝ) ^ 2 / 6 + 1 ≤ x + 1),
      show (2438374834 / 10 ^ 10 : ℝ) ≤ 1 - 2 / ((314159265358979323846 / 10 ^ 20 : ℝ) ^ 2 / 6 + 1) by norm_num]
  have hu_hi : u ≤ (2438374835 / 10 ^ 10 : ℝ) := by
    rw [hu_eq]; linarith [div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by linarith)
      (by linarith : x + 1 ≤ (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 / 6 + 1),
      show 1 - 2 / ((314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 / 6 + 1) ≤ (2438374835 / 10 ^ 10 : ℝ) by norm_num]
  have hu_pos : 0 < u := by linarith
  have hu_lt_q : u < (1 / 4 : ℝ) := by linarith
  have hlog_eq : Real.log (1 + u) - Real.log (1 - u) = Real.log x := by
    have h1pu : 1 + u = 2 * x / (x + 1) := by dsimp [u]; field_simp [show x + 1 ≠ 0 by linarith]; ring
    have h1mu : 1 - u = 2 / (x + 1) := by dsimp [u]; field_simp [show x + 1 ≠ 0 by linarith]; ring
    have hx_gt1 : 1 < x := by linarith
    rw [h1pu, h1mu, ← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp [show x + 1 ≠ 0 by linarith]
  have hser := Real.hasSum_log_sub_log_of_abs_lt_one (by rw [abs_of_pos hu_pos]; linarith : |u| < 1)
  rw [hlog_eq] at hser; have hshift := (hasSum_nat_add_iff' 6).mpr hser
  set S6 := ∑ k ∈ Finset.range 6, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1)
  constructor
  · have hS6_le : S6 ≤ Real.log x := by linarith [hasSum_le (fun _ => by positivity) hasSum_zero hshift]
    have hmono : ∑ k ∈ Finset.range 6, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (2438374834 / 10 ^ 10 : ℝ) ^ (2 * k + 1) ≤ S6 :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hu_lo _) (by positivity)
    exact (by norm_num [Finset.sum_range_succ] : (497700300539 / 10 ^ 12 : ℝ) ≤ _).trans (hmono.trans hS6_le)
  · have hgeom := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (1 / 16 : ℝ) < 1)).mul_left ((2 / 13 : ℝ) * (1 / 4 : ℝ) ^ 13)
    have htail : Real.log x - S6 ≤ ((2 / 13 : ℝ) * (1 / 4 : ℝ) ^ 13) * (1 - (1 / 16 : ℝ))⁻¹ := by
      refine hasSum_le (fun d => ?_) hshift hgeom
      have hu_pow : u ^ (2 * (d + 6) + 1) ≤ (1 / 4 : ℝ) ^ 13 * (1 / 16 : ℝ) ^ d := by
        rw [show (1 / 4 : ℝ) ^ 13 * (1 / 16 : ℝ) ^ d = (1 / 4 : ℝ) ^ (2 * (d + 6) + 1) by
          rw [show (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega]
        exact pow_le_pow_left₀ hu_pos.le hu_lt_q.le _
      have hc_le : (2 : ℝ) * (1 / (2 * ((d + 6 : ℕ) : ℝ) + 1)) ≤ (2 / 13 : ℝ) := by
        linarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 13)
          (show (13 : ℝ) ≤ 2 * ((d + 6 : ℕ) : ℝ) + 1 by push_cast; linarith)]
      calc (2 : ℝ) * (1 / (2 * ((d + 6 : ℕ) : ℝ) + 1)) * u ^ (2 * (d + 6) + 1)
          ≤ (2 / 13 : ℝ) * ((1 / 4 : ℝ) ^ 13 * (1 / 16 : ℝ) ^ d) := mul_le_mul hc_le hu_pow (by positivity) (by norm_num)
        _ = ((2 / 13 : ℝ) * (1 / 4 : ℝ) ^ 13) * (1 / 16 : ℝ) ^ d := by ring
    have hmono : S6 ≤ ∑ k ∈ Finset.range 6, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (2438374835 / 10 ^ 10 : ℝ) ^ (2 * k + 1) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu_pos.le hu_hi _) (by positivity)
    linarith [show (∑ k ∈ Finset.range 6, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (2438374835 / 10 ^ 10 : ℝ) ^ (2 * k + 1)) +
      ((2 / 13 : ℝ) * (1 / 4 : ℝ) ^ 13) * (1 - (1 / 16 : ℝ))⁻¹ ≤ (497700303198 / 10 ^ 12 : ℝ) by
      norm_num [Finset.sum_range_succ]]

theorem meisselMertens_sub_gamma_bounds :
    (-0.31571860 : ℝ) ≤ meisselMertensConst - Real.eulerMascheroniConstant ∧
      meisselMertensConst - Real.eulerMascheroniConstant ≤ (-0.31571843 : ℝ) := by
  have hD := mmDelta_limit_bounds; have hL := log_zeta2_bounds; unfold scale20 at hD
  exact ⟨by linarith [show (-0.31571860 : ℝ) ≤ -(1 / 2 : ℝ) * (497700303198 / 10 ^ 12 : ℝ) -
      ((6686829574253104157 : ℝ) / ((10 ^ 20 : ℕ) : ℝ) + 1 / (12 * 1999 * 2001 : ℝ)) by norm_num],
    by linarith [show -(1 / 2 : ℝ) * (497700300539 / 10 ^ 12 : ℝ) -
      (6686829397854561949 : ℝ) / ((10 ^ 20 : ℕ) : ℝ) ≤ (-0.31571843 : ℝ) by norm_num]⟩

end

end BuchstabSwitching.External
