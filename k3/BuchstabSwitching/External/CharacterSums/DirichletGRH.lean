import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Dirichlet `L`-Function Non-Vanishing & Explicit AP Prime Counting Interface

States the half-plane non-vanishing hypothesis for Dirichlet `L`-functions in terms
of Mathlib's `DirichletCharacter.LFunction`, along with an interface for explicit
prime-counting bounds in arithmetic progressions (Grenié–Molteni, *Ramanujan J.* **49**
(2019), 535–548; Johnston–Starichkova, `arXiv:2208.01229v3`, Lemma 5.1).
-/

namespace BuchstabSwitching.External

/-- Non-vanishing of `L(s, χ)` strictly to the right of `Re(s) = 1/2`. -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/--
Contributor target for explicit GRH prime counting in arithmetic progressions:
for `x ≥ 4 * 10^18`, `3 ≤ d ≤ √x`, and `Nat.Coprime a d`, connects `π(x; d, a)`
to `li(x) / φ(d)` with explicit error `c_π(x) √x log x`.
-/
def ExplicitPrimeInAPPremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (x d a : ℕ), 4 * 10 ^ 18 ≤ x → 3 ≤ d → d ^ 2 ≤ x → Nat.Coprime a d →
      ∃ main err : ℝ,
        0 ≤ err ∧
        |(((Finset.Icc 1 x).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℝ) - main| ≤ err

/-- `π(x; d, a)`: the number of primes `p ≤ x` with `p ≡ a (mod d)`. -/
noncomputable def primeCountingAP (x : ℝ) (d a : ℕ) : ℕ :=
  ((Finset.range (Nat.floor x + 1)).filter fun p => p.Prime ∧ Nat.ModEq d p a).card

/-- The offset logarithmic integral `Li(x) = ∫₂ˣ dt / log t`.
Using the lower limit `2` avoids the principal-value pole at `t = 1`; the finite offset
`li(2) = ∫₀² dt / log t ∈ [1.045163780117, 1.045163780118]` is absorbed via the `li2`
parameter into `c_pi`. -/
noncomputable def offsetLogIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- Explicit error coefficient `c_π(X₂)` from Grenié–Molteni (2019, *J. Number Theory*
**200**, Corollary 1) and Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 5.1),
parameterized by an upper bound `li2 ≥ li(2)` (where `li(2) ≈ 1.04516378`):
```
c_pi X₂ li2 = 3 / (8π) + (6 + 1/π) / (4 log X₂) + 6 / (log X₂)² + li2 / (√X₂ log X₂)
```
Matches `c_pi_iv` in `k3/scripts/sieve_cert/primes_and_mertens.py`. -/
noncomputable def c_pi (X₂ li2 : ℝ) : ℝ :=
  3 / (8 * Real.pi) +
  (6 + 1 / Real.pi) / (4 * Real.log X₂) +
  6 / (Real.log X₂) ^ 2 +
  li2 / (Real.sqrt X₂ * Real.log X₂)

/-- Explicit Grenié–Molteni / Johnston–Starichkova pointwise bound for primes in
arithmetic progressions with threshold `X₂` and error constant `c`:
for `x ≥ X₂`, `3 ≤ d ≤ √x`, and `Nat.Coprime a d`,
`|π(x; d, a) - Li(x) / φ(d)| ≤ c √x log x`. -/
def GrenieMolteniAPBound (X₂ c : ℝ) : Prop :=
  ∀ x : ℝ, X₂ ≤ x → ∀ d a : ℕ, 3 ≤ d → (d : ℝ) ≤ Real.sqrt x → Nat.Coprime a d →
    |(primeCountingAP x d a : ℝ) - offsetLogIntegral x / (Nat.totient d : ℝ)| ≤
      c * Real.sqrt x * Real.log x

/-- Exact Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 5.1) premise, parameterized
by `li2` (an upper bound on `li(2)`): under `DirichletLNonvanishingRightOfHalf`, for every
threshold `X₂ ≥ 4 * 10^18`, `GrenieMolteniAPBound X₂ (c_pi X₂ li2)` holds. -/
def JSLemma51Premise (li2 : ℝ) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ X₂ : ℝ, 4 * 10 ^ 18 ≤ X₂ → GrenieMolteniAPBound X₂ (c_pi X₂ li2)

/-- `c_pi X₂ li2` is non-negative on `1 < X₂` whenever `0 ≤ li2`. -/
theorem c_pi_nonneg {X₂ li2 : ℝ} (hX₂ : 1 < X₂) (hli2 : 0 ≤ li2) :
    0 ≤ c_pi X₂ li2 := by
  have hlog : 0 < Real.log X₂ := Real.log_pos hX₂
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt X₂ := Real.sqrt_pos.mpr (lt_trans zero_lt_one hX₂)
  unfold c_pi
  positivity

/-- On `(1, ∞)`, `X₂ ↦ c_pi X₂ li2` is antitone (non-increasing) whenever `0 ≤ li2`. -/
theorem c_pi_antitoneOn_Ioi_one {li2 : ℝ} (hli2 : 0 ≤ li2) :
    AntitoneOn (fun X₂ => c_pi X₂ li2) (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) < x := hx
  have hy1 : (1 : ℝ) < y := hy
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log (lt_trans zero_lt_one hx1) hxy
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (lt_trans zero_lt_one hx1)
  have hsqrt_le : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold c_pi
  have h2 : (6 + 1 / Real.pi) / (4 * Real.log y) ≤ (6 + 1 / Real.pi) / (4 * Real.log x) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  have h3 : 6 / (Real.log y) ^ 2 ≤ 6 / (Real.log x) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have h4 : li2 / (Real.sqrt y * Real.log y) ≤ li2 / (Real.sqrt x * Real.log x) := by
    apply div_le_div_of_nonneg_left hli2 (mul_pos hsqrtx hlogx)
    exact mul_le_mul hsqrt_le hlog_le hlogx.le (Real.sqrt_nonneg y)
  linarith

/-- On `[4 * 10^18, ∞)`, `X₂ ↦ c_pi X₂ li2` is antitone (decreasing) whenever `0 ≤ li2`. -/
theorem c_pi_antitoneOn {li2 : ℝ} (hli2 : 0 ≤ li2) :
    AntitoneOn (fun X₂ => c_pi X₂ li2) (Set.Ici (4 * (10 : ℝ) ^ 18)) := by
  refine (c_pi_antitoneOn_Ioi_one hli2).mono ?_
  intro x hx
  have h1 : (1 : ℝ) < 4 * (10 : ℝ) ^ 18 := by norm_num
  exact lt_of_lt_of_le h1 hx

/-- Any `JSLemma51Premise li2` with `0 ≤ li2` implies `ExplicitPrimeInAPPremise`. -/
theorem JSLemma51Premise.toExplicitPrimeInAPPremise {li2 : ℝ} (hli2 : 0 ≤ li2)
    (hJS : JSLemma51Premise li2) : ExplicitPrimeInAPPremise := by
  intro hGRH x d a hx hd hd2 hcop
  have hx_real : 4 * (10 : ℝ) ^ 18 ≤ (x : ℝ) := by exact_mod_cast hx
  have hd_real : (d : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg d) (Nat.cast_nonneg x)]
    exact_mod_cast hd2
  have hbound := hJS hGRH (x : ℝ) hx_real (x : ℝ) le_rfl d a hd hd_real hcop
  have hx1 : (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx_real
  refine ⟨offsetLogIntegral (x : ℝ) / (Nat.totient d : ℝ),
    c_pi (x : ℝ) li2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ), ?_, ?_⟩
  · have hc := c_pi_nonneg hx1 hli2
    have hlog := (Real.log_pos hx1).le
    have hsqrt := Real.sqrt_nonneg (x : ℝ)
    positivity
  · have hset :
        (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p % d = a % d) =
          (Finset.range (Nat.floor (x : ℝ) + 1)).filter
            (fun p => p.Prime ∧ Nat.ModEq d p a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.floor_natCast,
        Nat.lt_succ_iff, Nat.ModEq]
      constructor
      · rintro ⟨⟨_, hpx⟩, hp, hmod⟩
        exact ⟨hpx, hp, hmod⟩
      · rintro ⟨hpx, hp, hmod⟩
        exact ⟨⟨hp.one_lt.le, hpx⟩, hp, hmod⟩
    simpa [primeCountingAP, hset] using hbound

end BuchstabSwitching.External
