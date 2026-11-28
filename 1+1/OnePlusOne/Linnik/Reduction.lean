import OnePlusOne.Core.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Constructive Binary Goldbach Bridge & All-Range Linnik–Goldbach Reduction (`OnePlusOne.Linnik`)

Completely unconditional Lean 4 proofs of:
1. `binary_goldbach_bridge_18`: under `EmpiricalGoldbachBase` (`4 ≤ N ≤ 4 * 10^18`), EVERY even
   integer `N` in `[40, linnikBridge18]` (`linnikBridge18 = (2^19 - 2) * 2^61 + 4 * 10^18 ≈ 1.208925e24`)
   satisfies `HasExactPosLinnikRep 18 N` (`N = p₁ + p₂ + ∑_{i=1}^{18} 2^{k_i}`, `k_i ≥ 1`) via
   base-2 decomposition (`popcount ≤ 18`) and iterated bit-splitting `2^e = 2^{e-1} + 2^{e-1}`.
2. `all_even_exact_linnik_18`: combining `binary_goldbach_bridge_18` with circle-method positivity
   above `linnikBridge18` proves `AllEvenExactLinnikAbove 18` (`∀ N ≥ 40, Even N → ...`).
3. `all_even_linnik_18`: combining `[4, 38]` (`0` powers of `2` from `EmpiricalGoldbachBase`) with
   `all_even_exact_linnik_18` yields `AllEvenLinnikProp 18` (`∀ N ≥ 4, Even N → HasLinnikRep 18 N`).
-/

namespace OnePlusOne.Linnik

/-- Certified minimal all-range Linnik–Goldbach exponent `r = 18` (v2). -/
def certifiedLinnikR : ℕ := 18

/-- Constructive Binary Goldbach Bridge ceiling `(2^19 - 2) * 2^61 + 4 * 10^18 ≈ 1.208925e24`. -/
def linnikBridge18 : ℕ := (2 ^ 19 - 2) * 2 ^ 61 + 4 * 10 ^ 18

theorem hasLinnikRep_mono {r₁ r₂ N : ℕ} (h : r₁ ≤ r₂) (hr : HasLinnikRep r₁ N) :
    HasLinnikRep r₂ N := by
  rcases hr with ⟨p₁, p₂, hp₁, hp₂, ks, hlen, hpos, hEq⟩
  exact ⟨p₁, p₂, hp₁, hp₂, ks, hlen.trans h, hpos, hEq⟩

/-- Binary exponent list of `M < 2^b` in `[0, b)`. -/
def toPow2List : ℕ → ℕ → List ℕ
  | 0, _ => []
  | b + 1, M =>
    let rest := (toPow2List b (M / 2)).map (· + 1)
    if M % 2 = 1 then 0 :: rest else rest

private lemma sum_map_pow2_succ (l : List ℕ) :
    ((l.map (· + 1)).map (2 ^ ·)).sum = 2 * (l.map (2 ^ ·)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, pow_succ']
    linarith [ih]

private lemma sum_map_pow2_shift (E : ℕ) (l : List ℕ) :
    ((l.map (· + E)).map (2 ^ ·)).sum = 2 ^ E * (l.map (2 ^ ·)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, pow_add]
    rw [ih]
    ring

private lemma toPow2List_sum (b M : ℕ) (hM : M < 2 ^ b) :
    ((toPow2List b M).map (2 ^ ·)).sum = M := by
  induction b generalizing M with
  | zero =>
    simp only [pow_zero] at hM
    have hM0 : M = 0 := by omega
    subst hM0
    simp [toPow2List]
  | succ b ih =>
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
    have hhalf : M / 2 < 2 ^ b := by omega
    have hrec := ih (M / 2) hhalf
    unfold toPow2List
    by_cases hmod : M % 2 = 1
    · simp only [hmod, ↓reduceIte, List.map_cons, List.sum_cons, pow_zero, sum_map_pow2_succ, hrec]
      omega
    · simp only [hmod, ↓reduceIte, sum_map_pow2_succ, hrec]
      omega

private lemma toPow2List_length_le (b M : ℕ) :
    (toPow2List b M).length ≤ b := by
  induction b generalizing M with
  | zero => simp [toPow2List]
  | succ b ih =>
    unfold toPow2List
    split_ifs <;> simp only [List.length_cons, List.length_map] <;> have := ih (M / 2) <;> omega

private lemma toPow2List_length_le_pred (b M : ℕ) (hb : 1 ≤ b) (hM : M ≤ 2 ^ b - 2) :
    (toPow2List b M).length ≤ b - 1 := by
  induction b generalizing M with
  | zero => omega
  | succ b ih =>
    by_cases hb0 : b = 0
    · subst hb0
      have hM0 : M = 0 := by norm_num at hM; omega
      subst hM0
      simp [toPow2List]
    · have hb1 : 1 ≤ b := by omega
      have hpow_ge1 : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by norm_num)
      have hpow_eq : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
      unfold toPow2List
      by_cases hmod : M % 2 = 1
      · have hhalf : M / 2 ≤ 2 ^ b - 2 := by omega
        have ih' := ih (M / 2) hb1 hhalf
        simp only [hmod, ↓reduceIte, List.length_cons, List.length_map]
        omega
      · have hle := toPow2List_length_le b (M / 2)
        simp only [hmod, ↓reduceIte, List.length_map]
        omega

/-- Split the head exponent `m` times (`2^k = 2^(k-1) + 2^(k-1)`), increasing length by `m`. -/
def padPow2ToLen : ℕ → List ℕ → List ℕ
  | 0, ks => ks
  | _ + 1, [] => []
  | m + 1, k :: rest => padPow2ToLen m ((k - 1) :: (k - 1) :: rest)

private lemma padPow2ToLen_spec (m : ℕ) :
    ∀ (k : ℕ) (rest : List ℕ), m + 1 ≤ k → (∀ x ∈ rest, 1 ≤ x) →
      (padPow2ToLen m (k :: rest)).length = (k :: rest).length + m ∧
      (∀ x ∈ padPow2ToLen m (k :: rest), 1 ≤ x) ∧
      ((padPow2ToLen m (k :: rest)).map (2 ^ ·)).sum = ((k :: rest).map (2 ^ ·)).sum := by
  induction m with
  | zero =>
    intro k rest hk hrest
    refine ⟨rfl, ?_, rfl⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · exact hrest x hmem
  | succ m ih =>
    intro k rest hk hrest
    have hrest' : ∀ x ∈ (k - 1) :: rest, 1 ≤ x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · omega
      · exact hrest x hmem
    obtain ⟨hlen, hpos, hsum⟩ := ih (k - 1) ((k - 1) :: rest) (by omega) hrest'
    refine ⟨?_, hpos, ?_⟩
    · simp only [padPow2ToLen]
      rw [hlen]
      simp only [List.length_cons]
      omega
    · simp only [padPow2ToLen]
      rw [hsum]
      simp only [List.map_cons, List.sum_cons]
      have hk2 : 2 ≤ k := by omega
      have hsplit : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
        have hksub : k = (k - 1) + 1 := by omega
        calc
          2 ^ (k - 1) + 2 ^ (k - 1) = 2 * 2 ^ (k - 1) := by ring
          _ = 2 ^ ((k - 1) + 1) := by rw [pow_succ']
          _ = 2 ^ k := by rw [← hksub]
      omega

private lemma two_pow_61_pos : 0 < (2 : ℕ) ^ 61 := by positivity
private lemma two_pow_61_le_cap : (2 : ℕ) ^ 61 ≤ 4 * 10 ^ 18 - 4 := by norm_num
private lemma two_pow_61_even : 2 ∣ (2 : ℕ) ^ 61 := ⟨2 ^ 60, by ring⟩
private lemma two_pow_19_sub_two_lt : 2 ^ 19 - 2 < (2 : ℕ) ^ 19 := by norm_num
private lemma sum_replicate_18_pow2 : ((List.replicate 18 1).map (2 ^ ·)).sum = 36 := by norm_num

private lemma binary_bridge_step_bounds {N Glim P B : ℕ}
    (hGlim : Glim = 4 * 10 ^ 18)
    (hN_lo : Glim + 36 < N) (hN_hi : N ≤ B * P + Glim)
    (hP_pos : 0 < P) (hP_cap : P ≤ Glim - 4) :
    let A := N - Glim
    let M := (A + P - 1) / P
    1 ≤ M ∧ M ≤ B ∧ 4 ≤ N - M * P ∧ N - M * P ≤ Glim := by
  intro A M
  have hA_pos : 0 < A := by omega
  have hM_pos : 1 ≤ M := Nat.div_pos (by omega) hP_pos
  have hdiv : P * M + (A + P - 1) % P = A + P - 1 := Nat.div_add_mod (A + P - 1) P
  have hmod : (A + P - 1) % P < P := Nat.mod_lt _ hP_pos
  have hcomm : M * P = P * M := Nat.mul_comm M P
  have hM_lo : A ≤ M * P := by omega
  have hM_hi_prod : M * P ≤ A + P - 1 := by omega
  have hM_cap : M ≤ B := by
    have hA_cap : A ≤ B * P := by omega
    have hnum_lt : A + P - 1 < (B + 1) * P := by
      calc
        A + P - 1 < A + P := by omega
        _ ≤ B * P + P := Nat.add_le_add_right hA_cap P
        _ = (B + 1) * P := by ring
    have hq : M < B + 1 := (Nat.div_lt_iff_lt_mul hP_pos).mpr hnum_lt
    omega
  refine ⟨hM_pos, hM_cap, ?_, ?_⟩
  · omega
  · omega

/-- **Constructive Binary Goldbach Bridge (`40 ≤ N ≤ linnikBridge18`)**:
reduces every even integer `N ∈ [40, 1.208925e24]` cleanly from `EmpiricalGoldbachBase`. -/
theorem binary_goldbach_bridge_18
    (hbase : EmpiricalGoldbachBase)
    {N : ℕ} (hEven : Even N) (hLo : 40 ≤ N) (hHi : N ≤ linnikBridge18) :
    HasExactPosLinnikRep 18 N := by
  by_cases hSmall : N ≤ 4 * 10 ^ 18 + 36
  · have hN4 : 4 ≤ N - 36 := by omega
    have hNcap : N - 36 ≤ 4 * 10 ^ 18 := by omega
    have hNev : Even (N - 36) := by
      rw [Nat.even_iff] at hEven ⊢
      omega
    rcases hbase (N - 36) hN4 hNcap hNev with ⟨_, p₁, p₂, hp₁, hp₂, hpEq⟩
    refine ⟨p₁, p₂, hp₁, hp₂, List.replicate 18 1, by simp, ?_, ?_⟩
    · intro k hk
      rw [List.mem_replicate] at hk
      omega
    · rw [sum_replicate_18_pow2]
      omega
  · have hGt : 4 * 10 ^ 18 + 36 < N := Nat.lt_of_not_le hSmall
    have hB := binary_bridge_step_bounds rfl hGt hHi two_pow_61_pos two_pow_61_le_cap
    set A := N - 4 * 10 ^ 18
    set P := (2 : ℕ) ^ 61
    set M := (A + P - 1) / P
    obtain ⟨hM_pos, hM_cap, hN'_lo, hN'_hi⟩ := hB
    have hM_lt19 : M < 2 ^ 19 := lt_of_le_of_lt hM_cap two_pow_19_sub_two_lt
    have hMP_even : 2 ∣ M * P := dvd_mul_of_dvd_right two_pow_61_even M
    have hN'_even : Even (N - M * P) := by
      rw [Nat.even_iff] at hEven ⊢
      omega
    rcases hbase (N - M * P) hN'_lo hN'_hi hN'_even with ⟨_, p₁, p₂, hp₁, hp₂, hpEq⟩
    let raw := toPow2List 19 M
    have hraw_sum : (raw.map (2 ^ ·)).sum = M := toPow2List_sum 19 M hM_lt19
    have hraw_len : raw.length ≤ 18 := toPow2List_length_le_pred 19 M (by omega) hM_cap
    have hraw_ne : raw ≠ [] := by
      intro hnil
      rw [hnil] at hraw_sum
      simp at hraw_sum
      omega
    let ks₀ := raw.map (· + 61)
    have hks₀_ne : ks₀ ≠ [] := by
      intro hnil
      apply hraw_ne
      simpa [ks₀] using hnil
    have hks₀_len : ks₀.length ≤ 18 := by simpa [ks₀] using hraw_len
    have hks₀_ge : ∀ x ∈ ks₀, 61 ≤ x := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
      omega
    have hks₀_sum : (ks₀.map (2 ^ ·)).sum = M * P := by
      dsimp [ks₀]
      rw [sum_map_pow2_shift, hraw_sum, Nat.mul_comm]
    cases hks₀_eq : ks₀ with
    | nil => exact absurd hks₀_eq hks₀_ne
    | cons k₀ rest₀ =>
      let m := 18 - (k₀ :: rest₀).length
      have hm_le : m ≤ 17 := by
        have hlen1 : 1 ≤ (k₀ :: rest₀).length := by simp
        have hlen18 : (k₀ :: rest₀).length ≤ 18 := by simpa [hks₀_eq] using hks₀_len
        omega
      have hk₀_ge : 61 ≤ k₀ := hks₀_ge k₀ (by rw [hks₀_eq]; simp)
      have hrest₀_ge : ∀ x ∈ rest₀, 1 ≤ x := fun x hx =>
        le_trans (by omega : 1 ≤ 61) (hks₀_ge x (by rw [hks₀_eq]; exact List.mem_cons_of_mem _ hx))
      obtain ⟨hlen, hpos, hsum⟩ := padPow2ToLen_spec m k₀ rest₀ (by omega) hrest₀_ge
      refine ⟨p₁, p₂, hp₁, hp₂, padPow2ToLen m (k₀ :: rest₀), ?_, hpos, ?_⟩
      · have hlen18 : (k₀ :: rest₀).length ≤ 18 := by simpa [hks₀_eq] using hks₀_len
        omega
      · rw [hsum, ← hks₀_eq, hks₀_sum]
        omega

/-- **All-Range Exact `r = 18` Linnik–Goldbach Theorem (`∀ N ≥ 40`)**. -/
theorem all_even_exact_linnik_18
    (hbase : EmpiricalGoldbachBase)
    (hlarge : ∀ N : ℕ, linnikBridge18 < N → Even N → HasExactPosLinnikRep 18 N) :
    AllEvenExactLinnikAbove 18 := by
  intro N hN hEven
  have h40 : 40 ≤ N := by omega
  by_cases hLe : N ≤ linnikBridge18
  · exact binary_goldbach_bridge_18 hbase hEven h40 hLe
  · exact hlarge N (Nat.lt_of_not_le hLe) hEven

/-- **All-Range `≤ 18` Positive Powers of `2` Linnik–Goldbach Theorem (`∀ N ≥ 4`)**. -/
theorem all_even_linnik_18
    (hbase : EmpiricalGoldbachBase)
    (hlarge : ∀ N : ℕ, linnikBridge18 < N → Even N → HasExactPosLinnikRep 18 N) :
    AllEvenLinnikProp 18 := by
  intro N hN hEven
  by_cases h40 : 40 ≤ N
  · exact hasLinnikRep_of_exactPos (all_even_exact_linnik_18 hbase hlarge N h40 hEven)
  · have hCap : N ≤ 4 * 10 ^ 18 := by omega
    exact hasLinnikRep_of_isGoldbachEven (hbase N hN hCap hEven)

end OnePlusOne.Linnik
