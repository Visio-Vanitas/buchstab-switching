import AllEvenOnePlusFour.Statement

/-!
# Interface with GRH: the explicit bound for `π(x; q, a)`

The only place where GRH enters the note is the explicit bound for primes in arithmetic
progressions of [JS] Johnston–Starichkova, arXiv:2208.01229v3, **Lemma 5.1**:

> Let `x ≥ X₂ ≥ 4·10¹⁸`, and `q` and `a` be integers such that `3 ≤ q ≤ √x` and `(a, q) = 1`.
> Then, assuming GRH, `|π(x; q, a) - li(x)/φ(q)| ≤ c_π(X₂) √x log x`, with `c_π(X₂) ≤ 0.16`.

(and, for `π(x)` itself, Schoenfeld's bound under RH, quoted as [BS] Lemma 1; not stated here).

This file *states* that bound as a `Prop` and records the claimed implication from the
challenge premise as a `Prop`. Nothing here is proved, and nothing here is used by
`Reduction.lean`: there the GRH consequences enter only through the hypotheses
`ConditionalInputs.regime2` and `ConditionalInputs.regime3`.

Two remarks on the interface.

* [JS] derive Lemma 5.1 from Grenié–Molteni, which assumes GRH for the Dedekind zeta function
  of `ℚ(ζ_q)`. That zeta function is the product of `L(s, χ*)` over the primitive characters
  `χ*` inducing the characters mod `q`, so its zeros with `Re s > 1/2` are zeros of Dirichlet
  `L`-functions there; `DirichletLNonvanishingRightOfHalf` rules them out, and the functional
  equation then puts all nontrivial zeros on the line.
* [JS] use `li(x) = ∫₀ˣ dt / log t` (principal value) and absorb `li(2)/φ(q)` into `c_π`.
  To avoid the principal value we state the bound with the offset integral `∫₂ˣ dt / log t`,
  which is the form Grenié–Molteni prove; by the proof of [JS] Lemma 5.1 (quoted in the
  note, §0.2) the same constant `c_π(X₂)` works in this form.
-/

namespace AllEvenOnePlusFour

open Classical in
/-- `π(x; q, a)`: the number of primes `p ≤ x` with `p ≡ a (mod q)`. -/
noncomputable def primeCountingAP (x : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.range (Nat.floor x + 1)).filter fun p => p.Prime ∧ Nat.ModEq q p a).card

/-- The offset logarithmic integral `Li(x) = ∫₂ˣ dt / log t`. -/
noncomputable def offsetLogIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- The explicit pointwise bound for primes in progressions, with threshold `X₂`
and constant `c`:
for `x ≥ X₂`, `3 ≤ q ≤ √x`, `(a, q) = 1`,
`|π(x; q, a) - Li(x)/φ(q)| ≤ c √x log x`. -/
def PrimesInAPBound (X₂ c : ℝ) : Prop :=
  ∀ x : ℝ, X₂ ≤ x → ∀ q a : ℕ, 3 ≤ q → (q : ℝ) ≤ Real.sqrt x → Nat.Coprime a q →
    |(primeCountingAP x q a : ℝ) - offsetLogIntegral x / (Nat.totient q : ℝ)| ≤
      c * Real.sqrt x * Real.log x

/-- **[JS, Lemma 5.1], as an unproved statement.** GRH for Dirichlet `L`-functions implies
the bound `PrimesInAPBound (4·10¹⁸) 0.16`.

This is a `Prop` (a definition), not a theorem: it names the cited input precisely. It is not
assumed anywhere in this project. -/
def JSLemma51 : Prop :=
  DirichletLNonvanishingRightOfHalf → PrimesInAPBound (4 * 10 ^ 18) (16 / 100)

end AllEvenOnePlusFour
