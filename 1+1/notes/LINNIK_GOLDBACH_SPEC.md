# All-Range Explicit Linnik–Goldbach Theorem (v2, $K = 18$) under GRH + Goldbach ($\le 4\cdot 10^{18}$)

## 1. Exact Theorem Statements (v2 — Zero IEEE-754 Floats, Zero Black-Box Buffers)

Let $\mathbb{P}$ denote the primes and $k_i \ge 1$ ($2^{k_i} \ge 2$ even). For any fixed $r \ge 1$, every sum $p_1 + p_2 + \sum_{i=1}^r 2^{k_i}$ with $k_i \ge 1$ satisfies $p_1 + p_2 + \sum_{i=1}^r 2^{k_i} \ge 2r + 4$.

- **Theorem 3A & 3 (v2 — All-Range Explicit $K = 18$)**: Assume the Generalized Riemann Hypothesis (`DirichletLNonvanishingRightOfHalf`) and Oliveira e Silva–Herzog–Pardi's binary Goldbach verification ($E(4\cdot 10^{18}) = 0$). Then:
  1. Every even integer $N \ge 40$ ($= 2\cdot 18 + 4$) satisfies
     $$N = p_1 + p_2 + \sum_{i=1}^{18} 2^{k_i} \qquad (p_1, p_2 \in \mathbb{P},\quad k_1, \dots, k_{18} \ge 1).$$
  2. Every even integer $N \ge 4$ satisfies `HasLinnikRep 18 N`: $N = p_1 + p_2 + \sum_{j=1}^s 2^{k_j}$ with $0 \le s \le 18$ and **strictly positive exponents** $k_j \ge 1$ (for $4 \le N \le 38$, $s = 0$ directly from $E(4\cdot 10^{18}) = 0$).
  - Compared to v1 ($K = 22$), v2 cuts **4 powers of $2$** across the entire all-range domain $\forall N \ge 4$, tightens `HasLinnikRep` to enforce $k_j \ge 1$, and eliminates ALL v1 heuristic buffers (`+4.00` in $C_{E_2}$ and `+0.06` in $\bar{\mathfrak{S}}_2$).
- **Effective Asymptotic GRH Benchmark ($K = 6$, Zero Siegel Dependence)**: Adopting the signed-polynomial circle method on $\mathcal{D}_{25/32}$ of Li–Liu (`arXiv:2610.15784v1`, Oct 2026) with an explicit 460-pair zero-float directional net (`C_net <= 2.259e3`) and self-contained odd squarefree $q \le 105$ singular series table (`T_11 <= 0.02476`), pure effective GRH (`C_1 = 8.0`, no Siegel theorem) certifies $K = 6$ for sufficiently large even $N$ with margin `>= 0.07983` (`lhs <= 0.51307 < rhs >= 0.59290`, improving v1's asymptotic `K = 7` to `K = 6`).
- **Informational Lichtman Benchmark ($K = 5$)**: Plugging Lichtman's ineffective $C_1 = 6.7814$ (which depends on Siegel's theorem) into the same zero-float directional net reproduces Li–Liu's asymptotic GRH $K = 5$ (`lhs <= 2.40181 < rhs >= 2.40625`, margin `>= 0.00444`).

---

## 2. Regime 1: Constructive Binary Goldbach Bridge $[40, N_{\mathrm{br}}(18)]$ (100% Proved in Lean 4)

Define the exact bridge threshold with $E_0 = 61$ ($2^{61} = 2{,}305{,}843{,}009{,}213{,}693{,}952 \le 4\cdot 10^{18} - 4$):
$$N_{\mathrm{br}}(18) := (2^{19} - 2)\cdot 2^{61} + 4\cdot 10^{18} = 1{,}208{,}925{,}207{,}928{,}610{,}747{,}318{,}272 \approx 1.208925 \cdot 10^{24}.$$

- For $40 \le N \le 4\cdot 10^{18} + 36$, take $k_1 = \dots = k_{18} = 1$ ($\sum 2^{k_i} = 36$), so $N - 36 \in [4, 4\cdot 10^{18}]$ is an even Goldbach sum.
- For $4\cdot 10^{18} + 36 < N \le N_{\mathrm{br}}(18)$, set $M = \lfloor (N - 4\cdot 10^{18} + 2^{61} - 1) / 2^{61} \rfloor$. Then $1 \le M \le 2^{19} - 2$ (popcount $\le 18$) and $N - M\cdot 2^{61} \in [4, 4\cdot 10^{18}]$ is even; shifting all binary exponents of $M$ by $+61$ and iteratively splitting $2^e = 2^{e-1} + 2^{e-1}$ pads to exact length $18$ with all exponents $\ge 1$.
- This entire construction is verified unconditionally in [`OnePlusOne/Linnik/Reduction.lean`](../OnePlusOne/Linnik/Reduction.lean) (`binary_goldbach_bridge_18`, `all_even_exact_linnik_18`, `all_even_linnik_18`).

---

## 3. Regime 2: Zero-Black-Box $\sin^2(\pi t/N)$ Circle Method for $N > N_{\mathrm{br}}(18)$

Fix $c = 1/8$, $L = \lfloor \log_2(N / 8) \rfloor$ ($L \ge 76$ for $N > N_{\mathrm{br}}(18)$), $K = 18 = 2k$ ($k = 9$), pure monomial $P(z) = z^9$, $Q(z) = z^8$, and the smooth compactly supported weight $w(n) = \sin^2(\pi n / N) \mathbf{1}_{1 \le n \le N}$ ($E_2 = \frac{3}{8}N$, $\|\hat\phi\|_1 \le 2.136916$, Mellin moments $(M_0, M_1, M_2) \le (0.7703, 2.0828, 10.7884)$).

### Key v2 Analytic Upgrades (Zero Heuristic Buffers)
1. **Zero-Black-Box Major-Arc $L^2$ Constant (`C_E2 <= 31.3259`, `C_row_dir <= 1.0000`)**: Derived directly from the unit-interval Bochner kernel and Hadamard expansion at $\operatorname{Re}(s) = 5/2$ (eliminating v1's `+4.00` buffer), with exact Parseval prime-power bound ($\psi(N)-\vartheta(N) \le 1.4262\sqrt{N}$, Rosser–Schoenfeld Thm 13), exact $\omega(q)(\ln N + 2\ln Q_0)$ gcd correction, and major-arc $U \le U_q$ vertical contour at $\operatorname{Re}(s) = 1/4$.
2. **Exact Single-$N$ Dirichlet Minor-Arc Sup-Norm (`convolved_sup_Sw_finite`)**: Parameterizing $Q_1 = Q_{\max} = \sqrt{Y}$ and $q = u\sqrt{Y}$ ($u \in (0, 1]$) makes $U_q \le 2\pi / u$ independent of $N$ inside every slab, eliminating all $(N_{\mathrm{hi}}/N_{\mathrm{lo}})^{3.5}$ subdivision blowup while keeping $S_{2,w}(N)$ strictly monotone via $K_{\mathrm{err}} N_{\mathrm{hi}}^{1/4} + (\text{pole} + \text{other}) N_{\mathrm{hi}}^{1/2}$.
3. **Direct Mellin 1D Selberg Sieve (`selberg_C_sin2_finite`, `selberg_C_sin2_tail`)**: Zero prime-power subtraction error, $C_{\mathrm{Sel}} \le 5.025$ at $L = 76$ ($z = 28000$) and $C_{\mathrm{Sel}} \le 9.0945$ uniformly for all $L \ge 120$.
4. **16-Direction Rational-Polygon Transfer Automaton + Exact Convex-Vertex Monomial Bound + Abel Layer-Cake Summation**:
   - Uses 16 Pythagorean rational directions (`PYTH_DIRS`) to build 20 nested exact-`Fraction` convex polygons $K_s$. Because $f(x, y) = x^2 + y^2$ is convex, $\max_{z \in K_s} |z|^{2k}$ is attained at an exact rational vertex of $K_s$ (`polygon_max_monomial_sq`), eliminating edge-discretization loss.
   - Slabs $L \in [76, 84]$ use the dyadic run-length excluded $B = 10$ automaton ($K_0 = 30, M_{\mathrm{run}} = 45$) with exact `M_dyad` $L^2$ error; slabs $L \in [85, 119]$ use the pure $B = 10$ transfer matrix (zero `M_dyad`); the infinite tail $L \ge 120$ uses pure Collatz–Wielandt spectral radius certification (`max growth/step <= 0.916314 < 1`).
5. **Self-Contained Singular-Series Table ($S_{\mathrm{ex}}$ over all 43 odd squarefree $q \le 105$, $D_1 = 2000$ tail)**: Exact rational Ramanujan sums + outward-rounded prefix sums up to $Q = 1{,}800{,}000$, eliminating v1's `+0.06` buffer.

---

## 4. Machine-Certified Coverage Summary (`data/certify_linnik_r_output.txt`)

| Range in $N$ | Method | Certified Bounds (Outward Rounded) | Status |
| :--- | :--- | :--- | :--- |
| $4 \le N \le 38$ (even) | Goldbach $\le 4\cdot 10^{18}$ | $s = 0$ (`HasLinnikRep 18 N`, $k_j \ge 1$) | **PASS** |
| $40 \le N \le 1.208925\cdot 10^{24}$ | Lean 4 Binary Goldbach Bridge | $E_0 = 61$, $M \le 2^{19}-2$, exact $r = 18$, $k_i \ge 1$ | **PASS** |
| $L = 76$ ($N > N_{\mathrm{br}}(18)$) | 2 geometric sub-slabs, $M_{\mathrm{dyad}}(30, 45)$ | `C_Sel <= 5.025`, `lhs >= 1.0000 > rhs <= 0.9883` (`margin >= 0.0117`) | **PASS** |
| $L \in [77, 84]$ | Dyadic-excluded $B = 10$ automaton | Margin rises from `0.0125` ($L=77$) to `0.1043` ($L=82$) | **PASS** |
| $L \in [85, 119]$ | Pure $B = 10$ transfer matrix (no $M_{\mathrm{dyad}}$) | Margin rises from `0.0491` ($L=85$) to `0.2765` ($L=119$) | **PASS** |
| $L \ge 120$ ($N \ge 8\cdot 2^{120}$) | Pure Collatz–Wielandt tail | `growth/step <= 0.916314 < 1`, `lhs >= 1.0000 > rhs <= 0.8886` (`margin >= 0.1114`) | **PASS** |
| Asymptotic GRH (effective, no Siegel) | Li–Liu signed poly + 460-pair net, $C_1 = 8.0$ | **`K = 6`**: `lhs <= 0.51307 < rhs >= 0.59290` (`margin >= 0.07983`) | **PASS** |
| Asymptotic GRH (informational Lichtman) | Li–Liu signed poly + 460-pair net, $C_1 = 6.7814$ | `K = 5`: `lhs <= 2.40181 < rhs >= 2.40625` (`margin >= 0.00444`) | **PASS** |
