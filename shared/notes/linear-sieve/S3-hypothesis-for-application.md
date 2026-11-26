> Errata after review: (1) the claim in Step 8 and in the trade-off section that target 1/150 is dominated by row 1/140 is wrong: C_i(ε) is monotone in ε, so any ε ≤ 1/74 may be used with constants computed at that ε. (2) The last sentence of Proposition B is not proved. (3) Proposition E certifies ε*(S_0) < 1/k; the committed script now also checks ε_hi < 1/k. (4) All N_3 figures use the printed [BJS] constants and are superseded.

## Statement

### Notation

- 𝒫_odd is the set of odd primes. For p ∈ 𝒫_odd put g(p) = 1/(p−1) and
  ℓ(p) := −log(1−g(p)) = log((p−1)/(p−2)) > 0.
  (p = 2 never occurs: N is even, so 2 ∉ 𝐏. Also g(2) = 1 would violate g < 1.)
- For S ⊆ 𝒫_odd and real 1 < u < w, put Π_S(u,w) := ∏_{p∈S, u≤p<w} (p−1)/(p−2).
- For primes a ≤ b in S, put
  F_S(a,b) := Σ_{p∈S∩[a,b]} ℓ(p) − log log b + log log a.
  This is the logarithm of Π_{S∩[a,b]} · log a / log b.
- For z > 1, put ε*_z(S) := max{ e^{F_S(a,b)} − 1 : a ≤ b < z, a,b ∈ S }. This is a maximum over a finite set; it is 0 if S∩[2,z) = ∅.
- Put ε*(S) := sup_z ε*_z(S) = sup_{a≤b in S} e^{F_S(a,b)} − 1.
- **(H_real(S,z,K))**: for all real 1 < u < w ≤ z, Π_S(u,w) ≤ K · log w / log u.

This is the "all real sub-levels" form of (prod11) and (eq:cond1). It contains:
- the fixed-z form (w = z);
- the prime levels w = p_k, with the top prime excluded;
- the real levels w = D_k^{1/3} identified by the referees.

**Interface (not proved here).** The corrected sieve theorem being written in another section is assumed to have the following form: the conclusions of [BJS] `theo:JR` at ε′ = 1/k, with the Table `tab:fF` constants, hold for g_n = g whenever some K ∈ (1, 1+1/k) satisfies H_real(𝐏∖ℚ, z, K). This section delivers exactly that hypothesis.

### Theorem A (real endpoints ↔ closed prime intervals; exactness)

Let S ⊆ 𝒫_odd and z > 1.

- (a) For all real 1 < u < w ≤ z:
  - if S∩[u,w) = ∅, then Π_S(u,w) = 1 < log w/log u;
  - otherwise Π_S(u,w) < (1+ε*_z(S)) · log w/log u (strict inequality).
- (b) For every ε > 0: there is a K ∈ (1, 1+ε) with H_real(S,z,K) **if and only if** ε*_z(S) < ε.
- (c) Hence ε*_z(S) is the exact constant for level z. The single number ε*(S) works uniformly for all z.

### Proposition B (uniformity in N)

Fix Q_0 ⊆ 𝒫_odd and let S_0 := 𝒫_odd ∖ Q_0. For even N, put 𝐏_N := {p ∤ N} and ℚ_N := Q_0 ∖ {p | N}. Then:
- ℚ_N ⊆ 𝐏_N;
- Q_N := ∏ℚ_N divides Q_0;
- 𝐏_N∖ℚ_N = S_0 ∖ {p|N} ⊆ S_0;
- ε*_z(𝐏_N∖ℚ_N) ≤ ε*(S_0) for every z.

The main term X_A = |A|·V_N(z), with V_N(z) = ∏_{p<z, p∤N}(1 − 1/(p−1)), does not depend on Q_0. If Q_0 ⊆ [3,z), then QD ≤ Q_0 D.

Conversely, every admissible fixed Q_0 must satisfy ε*(S_0) ≤ ε. Moreover, no N-dependent choice ℚ_N can beat the best fixed Q_0 at N = 2^m.

### Proposition C (what Q_0 must contain)

Let S ⊆ 𝒫_odd and k ≥ 1. Suppose ε*(S) < 1/k (strict, as Theorem A(b) requires).
- **(i) Single primes.** For every p ∈ S, ε*(S) ≥ 1/(p−2). Hence Q_0 ⊇ F_k := {odd p ≤ k+2}.
- **(ii) Twin primes.** If p and p+2 both lie in S, then
  ε*(S) ≥ (p²−1)/(p(p−2)) · log p/log(p+2) − 1 ≥ 2/p − 2/(p log p) − 4/(p² log p).
- **(iii) Hitting-set lower bound.** Let S′ := 𝒫_odd ∖ F_k. Take any family of pairwise disjoint prime intervals [a_i, b_i] with a_i, b_i ∈ S′ and F_{S′}(a_i,b_i) ≥ log(1+1/k). Then every admissible Q_0 satisfies
  log Q_0 ≥ Σ_{p∈F_k} log p + Σ_i log a_i.

### Theorem D (analytic tail; uses external inputs E1–E3 below)

Let 5 ≤ B ≤ 10^12 be an integer, S ⊆ 𝒫_odd, and M_B ≥ max{F_S(a,b) : a ≤ b ≤ B, a,b ∈ S}. Then

sup_{a≤b in S} F_S(a,b) ≤ max(M_B + δ_B, δ′_B),

where, with t_1 := 2/(√B log B), t_2 := 6.836·10⁻⁶/log 10^12 and t_3 := 2.964·10⁻⁶/log 10^12,
- δ_B := max(t_1, t_2) + 1/(B−1);
- δ′_B := max(t_1, t_2+t_3) + 2/(B−1).

### Proposition E (the certificate)

Suppose the script below prints `PASS` for target 1/k with set Q_0. Then ε*(S_0) ≤ ε_hi < 1/k, with ε_hi the printed number. Consequently, for every even N and every z > 1, H_real(𝐏_N∖ℚ_N, z, K) holds with K := 1 + ε_hi ∈ (1, 1+1/k).

This rests on:
- Theorems A and D;
- Proposition B;
- the arithmetic lemmas of Step 6;
- E1–E3;
- the correctness of Python's integer arithmetic.

### Proposition F (no pre-sieve saves Regime 3 at 10^170 in the frame note's design)

Assumptions (the frame note §4.1):
- z = N^{1/22}, y = N^{21/88};
- level D = N^{1/2−α}, with QD ≤ √N/log^{4.05}N, i.e. α ≥ (log Q + 4.05 log log N)/log N;
- D/q ≥ z required for all q < y, i.e. s_min = 5.75 − 22α ≥ 1.

Then for every Q_0 with ε*(𝒫_odd∖Q_0) < 1/74 and every N = 2^m with log N ≤ 414, the requirement s_min ≥ 1 fails. In particular it fails at N ≈ 10^170.

### External inputs (quoted, not re-proved)

Write A(x) := Σ_{p≤x} 1/p − log log x − M, with M the Meissel–Mertens constant (the same limit in all three sources).

- **E1** ([BJS] Lemma `mertencomplem`, computational). For 2 ≤ x ≤ 10^12: 0 < A(x) < 2/(√x log x).
- **E2** ([JS] v3 Lemma 3.2 (3.3), as quoted in the frame note §0.2). For x > 10^12: Σ_{p<x} 1/p ≤ log log x + M + 6.836·10⁻⁶/log x.
- **E3** ([BJS] Lemma `mertenlem`, eq. (small1p)). For x ≥ 2: A(x) ≥ −2.964·10⁻⁶/log x.

---

## Proof

**Step 1 (Theorem A(a)).**
1. Fix 1 < u < w ≤ z. If S∩[u,w) = ∅, then Π = 1. Since log w > log u > 0, we get 1 < log w/log u.
2. Otherwise let p_1 < … < p_m be the primes of S in [u,w). Then Π_S(u,w) = ∏_{i}(p_i−1)/(p_i−2).
3. We have u ≤ p_1, so 0 < log u ≤ log p_1. We have p_m < w, so log w > log p_m > 0. Hence log u/log w < log p_1/log p_m.
4. Multiply by Π > 0: Π·log u/log w < Π·log p_1/log p_m = e^{F_S(p_1,p_m)}.
5. Since p_1 ≤ p_m < w ≤ z, the pair (p_1, p_m) enters ε*_z(S). So the right side is ≤ 1 + ε*_z(S). ∎(a)

**Step 2 (Theorem A(b), A(c)).**

(⇐) Assume ε*_z(S) < ε.
- If S∩[2,z) ≠ ∅, then ε*_z(S) ≥ ℓ(p)-type value > 0 for any such p. Put K := 1 + ε*_z(S) ∈ (1, 1+ε). Step 1 gives H_real(S,z,K).
- If S∩[2,z) = ∅, every product is 1 and K := 1 + ε/2 works.

(⇒) Assume H_real(S,z,K) holds with K < 1+ε.
1. Take primes a ≤ b < z in S. Let b⁺ be the next prime of S after b (b⁺ = ∞ if there is none).
2. For real w with b < w < min(b⁺, z], and u := a, we have S∩[u,w) = S∩[a,b]. So Π_{S∩[a,b]} ≤ K·log w/log a.
3. Let w ↓ b: Π_{S∩[a,b]}·log a/log b ≤ K. Hence 1 + ε*_z(S) ≤ K < 1+ε.

For (c): ε*_z is nondecreasing in z and ε* = sup_z ε*_z. ∎

The same limiting argument with w ↓ b shows the following. Real levels just above a prime **do** force the closed interval [a,b]: this is referee v3's finding. Any proof that also uses w = D_k^{1/3} levels therefore needs ε*(S) on closed intervals, not the half-open prime-top version of this note §9.

**Step 3 (Proposition B).**
1. Since N is even, 2 ∉ 𝐏_N.
2. ℚ_N = Q_0∖{p|N} consists of primes not dividing N, so ℚ_N ⊆ 𝐏_N. Also Q_N | Q_0.
3. 𝐏_N∖ℚ_N is the set of odd p ∤ N with p ∉ Q_0 (a prime of Q_0 dividing N is not in 𝐏_N at all). This equals S_0∖{p|N}.
4. **Monotonicity.** If S′ ⊆ S, then ε*_z(S′) ≤ ε*_z(S). Take a ≤ b < z in S′. Then a, b ∈ S, and every factor (p−1)/(p−2) ≥ 1. So Π_{S′∩[a,b]} ≤ Π_{S∩[a,b]}, hence F_{S′}(a,b) ≤ F_S(a,b).
5. In [BJS] `theo:JR`, X_A = |A|∏_{p|P(z)}(1−g(p)), where P(z) runs over **all** of 𝐏_N below z, including ℚ_N. So pre-sieving changes only:
   - the remainder level, which becomes Q_N·D ≤ Q_0·D;
   - the hypothesis set 𝐏∖ℚ.

   N enters V_N(z), and this is handled uniformly by [BJS] Lemma 38 (the frame note §4.3). The theorem needs ℚ_N ⊆ {p<z}. This holds whenever max Q_0 < z, and in the frame note z ≥ 5.3·10⁷.
6. **Converse.** For N = 2^m we have 𝐏_N = 𝒫_odd, so ℚ_N = Q_0 and the hypothesis set is S_0. Any scheme, fixed or N-dependent, must therefore satisfy ε*(𝒫_odd∖ℚ_{2^m}) < ε at N = 2^m. That is precisely the fixed-set problem.

So with a fixed Q_0, "worst case over N" means N = 2^m. Removing primes dividing N only helps the hypothesis; it changes V_N, which is handled by Lemma 38, and changes Q_N, which only gets smaller. ∎

**Step 4 (Proposition C).**

(i) Take a = b = p. Then F_S(p,p) = ℓ(p), so ε*(S) ≥ (p−1)/(p−2) − 1 = 1/(p−2). The condition 1/(p−2) < 1/k is equivalent to p > k+2. So every odd p ≤ k+2 must lie in Q_0. Note that p = k+2 gives equality, which is already inadmissible because strictness is needed.

(ii) Take a = p and b = p+2.
1. (p−1)(p+1)/((p−2)p) = 1 + (2p−1)/(p(p−2)) ≥ 1 + 2/p, because (2p−1)/(p−2) ≥ 2.
2. log(p+2) = log p + log(1+2/p) ≤ log p + 2/p. Hence log p/log(p+2) ≥ 1 − (2/p)/(log p + 2/p) ≥ 1 − 2/(p log p).
3. Multiply the two positive factors: the product is ≥ 1 + 2/p − 2/(p log p) − 4/(p² log p).

(iii) Suppose some interval [a_i, b_i] is not hit, i.e. Q_0 ∩ S′∩[a_i,b_i] = ∅. Then S_0 ⊇ S′∩[a_i,b_i], and a_i, b_i ∈ S_0. By Step 3.4 (monotonicity), F_{S_0}(a_i,b_i) ≥ F_{S′}(a_i,b_i) ≥ log(1+1/k), which contradicts ε*(S_0) < 1/k.

So Q_0∖F_k hits every [a_i,b_i]. The intervals are disjoint, so the hitting primes are distinct, and each costs at least log a_i. Together with (i) this gives the bound. ∎

*Heuristic (not proved).* A cluster of j primes of S in [p, p+h] with h = o(p) gives ε ≈ (j − h/log p)/p. This is the excess over the expected prime count, divided by p.

**Step 5 (Theorem D).**

Fix a ≤ b in S with b > B.

1. Use ℓ(p) = log(1 + 1/(p−2)) ≤ 1/(p−2) = 1/p + 2/(p(p−2)).
2. **Telescoping.** For odd n, 2/(n(n−2)) = 1/(n−2) − 1/n. Hence, for any odd n_0 ≥ 3,
   Σ_{p prime, p ≥ n_0} 2/(p(p−2)) ≤ Σ_{n odd ≥ n_0} (1/(n−2) − 1/n) = 1/(n_0−2).
3. **Case (i): a ≤ B < b.** Let p_B be the largest prime of S that is ≤ B. It exists because a ∈ S and a ≤ B, and a ≤ p_B. Split:
   F_S(a,b) = [Σ_{S∩[a,B]} ℓ − log log B + log log a] + [Σ_{S∩(B,b]} ℓ − log log b + log log B].
   - First bracket: log log B ≥ log log p_B, so it is ≤ F_S(a,p_B) ≤ M_B.
   - Second bracket: since S ⊆ 𝒫_odd, by item 1 it is ≤ Σ_{B<p≤b} 1/p + Σ_{p>B} 2/(p(p−2)) − (log log b − log log B).
   - Now Σ_{B<p≤b} 1/p = log log b − log log B + A(b) − A(B).
   - Item 2 with n_0 = the least odd integer > B gives n_0 − 2 ≥ B − 1.
   - So the second bracket is ≤ A(b) − A(B) + 1/(B−1).
   - By E1 at x = B (valid since B ≤ 10^12), A(B) > 0.
   - If b ≤ 10^12: by E1, A(b) < 2/(√b log b) ≤ t_1, because √x log x is increasing.
   - If b > 10^12: E2 holds for every y > b. Its right side is continuous and Σ_{p≤b} = Σ_{p<y} for y ∈ (b, next prime). Letting y ↓ b gives A(b) ≤ 6.836·10⁻⁶/log b < t_2.
   - Hence F_S(a,b) ≤ M_B + δ_B.
4. **Case (ii): B < a ≤ b.** Since a is prime, Σ_{a≤p≤b} 1/p = log log b − log log a + A(b) − A(a) + 1/a. Item 2 with n_0 = a gives Σ_{p≥a} 2/(p(p−2)) ≤ 1/(a−2). Hence F_S(a,b) ≤ A(b) − A(a) + 1/a + 1/(a−2).
   - Since a ≥ B+1, we get 1/a + 1/(a−2) ≤ 1/(B+1) + 1/(B−1) < 2/(B−1).
   - If a ≤ 10^12: A(a) > 0 by E1, and A(b) ≤ max(t_1, t_2) as in Case (i).
   - If a > 10^12: by E3, A(a) ≥ −2.964·10⁻⁶/log a > −t_3, and A(b) ≤ t_2.
   - So F_S(a,b) ≤ δ′_B.
5. Pairs with b ≤ B satisfy F_S(a,b) ≤ M_B ≤ M_B + δ_B. ∎

Numerical values for B = 10^7:
- t_1 ≈ 3.924·10⁻⁵, t_2 ≈ 2.47·10⁻⁷, t_3 ≈ 1.07·10⁻⁷;
- δ_B ≈ 3.93·10⁻⁵ and δ′_B ≈ 3.94·10⁻⁵.

**Step 6 (arithmetic lemmas behind Proposition E).**

Fixed point: ONE = 2^160. A real x is carried as integers lo ≤ ONE·x ≤ hi.

1. **atanh.** Let 0 ≤ n and 2n ≤ d, and put x = n/d ∈ [0, ½]. Then atanh x = Σ_{k≥0} x^{2k+1}/(2k+1), and all terms are ≥ 0.
   - The sum of floor(ONE·term_k) for k ≤ K is a lower bound.
   - Let K be the first k with floor(ONE·term_K) = 0, so ONE·term_K < 1. The tail satisfies Σ_{k>K} ONE·term_k ≤ ONE·term_K·x²/(1−x²) < 1/3. So (Σ_{k≤K} ceil(ONE·term_k)) + 1 is an upper bound.
2. **Logarithm identity.** For r > 0, log r = 2 atanh((r−1)/(r+1)). This gives:
   - log 2 = 2 atanh(1/3);
   - log 3 = 2 atanh(1/2);
   - ℓ(p) = 2 atanh(1/(2p−3));
   - log p − log p′ = 2 atanh((p−p′)/(p+p′)) for consecutive odd primes p′ < p. Here p ≤ 3p′ because p < 2p′ (Bertrand), so x ≤ ½.
3. **Iterated logarithm.** With δ = log(p/p′) and L′ = log p′,
   log log p − log log p′ = 2 atanh(δ/(2L′+δ)).
   The argument δ/(2L′+δ) increases in δ and decreases in L′. So the lower (upper) bound uses δ_lo, L′_hi (respectively δ_hi, L′_lo). Each is an exact rational of scaled integers, with 2·num ≤ den because δ < log 2 < 2L′.
   - Start: log log 3 = 2 atanh((L−1)/(L+1)) with L = log 3 ∈ (1, 3).
4. **Exponential.** For 0 ≤ x ≤ ½:
   - Ceiling Taylor terms t_j = ⌈t_{j−1}x/j⌉ dominate the true terms by induction.
   - Stop at the first J ≥ 1 with t_J ≤ 1. The tail ratio is ≤ 1/4, so the tail is < 1, and "+1" bounds it.
   - Floor terms give a lower bound.
5. **Scan identity.** F_S(a,b) = X_b − Y_a, where X_b = Σ_{p∈S, p≤b} ℓ − log log b and Y_a = Σ_{p∈S, p<a} ℓ − log log a. Hence
   max_{a≤b≤B} F_S(a,b) = max_{b≤B} (X_b − min_{a≤b} Y_a).
   Replacing X by its upper bound and Y by its lower bound gives a rigorous upper bound M_B in one linear pass. The case a = b is included because Y_b is inserted before X_b is evaluated.
6. **Final comparison.** log(1+1/k) = 2 atanh(1/(2k+1)). `PASS` means T := max(M_B + δ_B, δ′_B) < lower bound of log(1+1/k). Then ε*(S_0) ≤ e^T − 1 ≤ ε_hi < 1/k by Theorem D. Proposition B then transfers this to every N. Theorem A(b) gives K = 1 + ε_hi. ∎

**Step 7 (construction of Q_0: heuristic, then certified).**

The greedy only proposes Q_0. Proposition E certifies it.
1. Start with Q_0 = F_k (forced by C(i)).
2. On the primes up to G, find the worst pair (a,b) (by upper bounds) against the threshold τ := log(1+1/k)_lo − δ_B. This threshold leaves room for the tail.
3. For each candidate r ∈ S∩[a,b], compute Φ = Σ_b max(0, val_b − τ) after adding r to Q_0. Add the r that maximises (decrease in Φ)/log r.
4. Repeat until the scan maximum is < τ.
5. **Reverse delete.** For r ∈ Q_0∖F_k in decreasing order, drop r if the set stays feasible. Infeasibility is upward closed in S (Step 3.4). Therefore the result is **inclusion-minimal**: no single extra prime can be returned to S.

Global minimality of log Q_0 is not claimed. The script prints the rigorous lower bound of C(iii), computed by weighted interval packing (dynamic programming over primes ≤ 5000, with certified violation tests F_lo ≥ log(1+1/k)_hi), so the gap to optimal is visible.

**Step 8 (forced sets and twin lower bounds by hand; the script's DP recomputes them).**

The forced set is F_k = {odd p ≤ k+2}. Sums of log p:
- θ(37) − log 2 = 28.942;
- adding primes up to 73 gives 65.184;
- up to 79: 69.553;
- up to 89: 78.461;
- up to 101: 87.650;
- up to 113: 106.377;
- up to 139: 125.950;
- up to 151: 135.972;
- up to 199: 187.870.

By C(ii), the twin pairs below are outside F_k and have ε ≥ 1/k. Each bound was evaluated by hand from the explicit inequality; borderline cases are checked at the end of this step.

| target 1/k | forced bound | forced log Q (LB) | twin pairs (p,p+2) forcing a removal | LB incl. twins |
|---|---|---|---|---|
| 1/74 | p ≤ 76 | 65.18 | (101,103), (107,109) | 74.47 |
| 1/80 | p ≤ 82 | 69.55 | (101,103), (107,109) | 78.84 |
| 1/90 | p ≤ 92 | 78.46 | (101,103), (107,109), (137,139) | 92.67 |
| 1/100 | p ≤ 102 | 87.65 | (107,109), (137,139), (149,151) | 102.25 |
| 1/120 | p ≤ 122 | 106.38 | (137,139), (149,151), (179,181), (191,193) | 126.74 |
| 1/140 | p ≤ 142 | 125.95 | (149,151), (179,181), (191,193), (197,199), (227,229) | 152.10 |
| 1/150 | p ≤ 152 | 135.97 | (179,181), (191,193), (197,199), (227,229), (239,241) | 162.59 |
| 1/200 | p ≤ 202 | 187.87 | (227,229), (239,241), (269,271), (281,283), (311,313) | 215.74 |

Borderline cases:
- (227,229) at 1/140: the bound gives 0.00717 against 0.00714.
- (311,313) at 1/200: 0.00530 against 0.005.
- Not forced by the inequality: (197,199) at 1/120 (0.00821) and (347,349) at 1/200 (0.00478).

Denser clusters force further removals. Referee v3's list for 1/100 is {103…113}, {191…199} and [223,281]. These are picked up only by the script.

Target 1/150 is **dominated**. Theorem `theo:JR` is applied at the table row below 150, which is 140. Any Q_0 admissible for 1/150 is admissible for 1/140. So target 1/150 never beats target 1/140; the same holds for every non-row target.

**Step 9 (Proposition F).**
1. By C(i), log Q_0 ≥ 65.18.
2. At N = 2^m, Q_N = Q_0.
3. The design needs α ≥ (65.18 + 4.05 log L)/L with L = log N. The right side decreases for L ≥ 10.
4. At L = 414 it equals (65.18 + 24.405)/414 = 0.21639 > 4.75/22 = 0.215909.
5. So s_min = 5.75 − 22α < 1 for all L ≤ 414. Note that 10^170 corresponds to L = 391.4, where α ≥ 0.2283 and s_min ≤ 0.73. ∎

---

## Certification script

```python
#!/usr/bin/env python3
"""
hstar_certify.py -- certified verification of hypothesis (H*) (closed prime intervals,
equivalently all real levels 1<u<w<=z) for the frame note Regime 3, g(p)=1/(p-1).

Run:  python3 hstar_certify.py [B] [G]
   B : bound for the exhaustive scan            (default 10**7; need G <= B <= 10**12)
   G : range for the greedy construction of Q0  (default 20000; need 300 <= G)

CERTIFIED (each 'PASS' line):  for the printed Q0 and S0 = odd primes minus Q0,
   eps*(S0) = sup_{a<=b primes of S0} prod_{p in S0, a<=p<=b}(p-1)/(p-2) * log a/log b - 1
   <= eps_hi < 1/k.      (note: Theorems A, D, Proposition E)
   Inputs: E1 [BJS mertencomplem], E2 [JS (3.3)], E3 [BJS small1p], used only via
   the constants t1, t2, t3 in tail_constants().
ARITHMETIC: fixed point, ONE = 2**PREC; a real x is a pair of ints lo <= ONE*x <= hi.
   Divisions are explicit floor/ceil. Logs from the atanh series with an explicit
   tail bound. No floats anywhere. decimal is used only (a) for printing with
   directed rounding, (b) in n3_estimate(), which is HEURISTIC.
NOT CERTIFIED: the greedy choice of Q0 (a candidate that the certificate then checks)
   and the N_3 estimates (hand-estimated alpha*, see note).
"""
import sys
import bisect
from fractions import Fraction
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING

PREC = 160
ONE = 1 << PREC


# ---------------------------------------------------------------- integer helpers
def ceil_div(a, b):
    """Exact ceil(a/b) for ints with b > 0."""
    if b <= 0:
        raise ValueError("ceil_div needs b > 0")
    return -((-a) // b)


def isqrt(n):
    """floor(sqrt(n)) for int n >= 0 (Newton from above; exact integer arithmetic)."""
    if n < 0:
        raise ValueError
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + 1) // 2)      # x >= sqrt(n)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


# ------------------------------------------------- certified elementary functions
def atanh_fp(num, den):
    """(lo, hi) ints with lo <= ONE*atanh(num/den) <= hi.
    Needs ints num >= 0, den > 0, 2*num <= den (x <= 1/2). Series terms x^(2k+1)/(2k+1)>=0.
    lo = sum of floors (k<=K); hi = sum of ceilings (k<=K) + 1, where K is the first k
    with floor(ONE*term_k) = 0; the tail is < ONE*term_K * x^2/(1-x^2) < 1/3."""
    if not (isinstance(num, int) and isinstance(den, int)):
        raise TypeError("atanh_fp needs ints")
    if num < 0 or den <= 0 or 2 * num > den:
        raise ValueError("atanh_fp needs 0 <= num and 2*num <= den")
    if num == 0:
        return 0, 0
    n2, d2 = num * num, den * den
    pn, pd, k = num, den, 0
    lo = hi = 0
    while True:
        q, r = divmod(pn << PREC, pd * (2 * k + 1))
        lo += q
        hi += q + (1 if r else 0)
        if q == 0:
            return lo, hi + 1
        pn *= n2
        pd *= d2
        k += 1


_a, _b = atanh_fp(1, 3)
LN2 = (2 * _a, 2 * _b)                         # log 2 = 2 atanh(1/3)


def ln_int_fp(n):
    """(lo, hi) enclosing ONE*log(n), int n >= 1: n = 2^k*m, m in [1,2),
    log n = k log 2 + 2 atanh((n-2^k)/(n+2^k)), argument <= 1/3."""
    k = n.bit_length() - 1
    lo, hi = atanh_fp(n - (1 << k), n + (1 << k))
    return k * LN2[0] + 2 * lo, k * LN2[1] + 2 * hi


def ln1p_inv_fp(k):
    """(lo, hi) enclosing ONE*log(1+1/k) = ONE*2 atanh(1/(2k+1))."""
    lo, hi = atanh_fp(1, 2 * k + 1)
    return 2 * lo, 2 * hi


def exp_hi_fp(x):
    """hi >= ONE*exp(x/ONE) for 0 <= x <= ONE/2. Ceiling Taylor terms dominate the true
    terms; stop at first J>=1 with t_J <= 1; tail < t_J*(1/4)/(3/4) < 1, hence +1."""
    if x < 0 or 2 * x > ONE:
        raise ValueError("exp_hi_fp range")
    total, t, j = 0, ONE, 0
    while True:
        total += t
        if t <= 1:
            return total + 1
        j += 1
        t = ceil_div(t * x, ONE * j)


def exp_lo_fp(x):
    """lo <= ONE*exp(x/ONE) for x >= 0: truncated Taylor sum with floored terms (all >= 0)."""
    if x < 0:
        raise ValueError("exp_lo_fp needs x >= 0")
    total, t, j = 0, ONE, 0
    while t > 0:
        total += t
        j += 1
        t = (t * x) // (ONE * j)
    return total


def fp_dec(x, up, digits=30):
    """Decimal rounding of x/ONE upward (up=True) or downward; Decimal(int) is exact."""
    with localcontext() as c:
        c.prec = digits
        c.rounding = ROUND_CEILING if up else ROUND_FLOOR
        return Decimal(x) / Decimal(ONE)


# ---------------------------------------------------------------------- primes
def odd_primes_upto(n):
    """All odd primes <= n (sieve of Eratosthenes on a bytearray)."""
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    i = 2
    while i * i <= n:
        if s[i]:
            st = i * i
            s[st::i] = bytes(len(range(st, n + 1, i)))
        i += 1
    return [p for p in range(3, n + 1, 2) if s[p]]


def prime_data(primes):
    """Yield (p, lnlo, lnhi, lamlo, lamhi, elllo, ellhi) for consecutive odd primes from 3:
    enclosures of ONE*log p, ONE*loglog p, ONE*log((p-1)/(p-2)). Recursions in note Step 6."""
    if not primes or primes[0] != 3:
        raise ValueError("primes must start at 3")
    a, b = atanh_fp(1, 2)
    L_lo, L_hi = 2 * a, 2 * b                         # log 3
    assert ONE < L_lo and L_hi <= 3 * ONE
    lam_lo = 2 * atanh_fp(L_lo - ONE, L_lo + ONE)[0]  # log log 3, increasing in L
    lam_hi = 2 * atanh_fp(L_hi - ONE, L_hi + ONE)[1]
    prev = 3
    for p in primes:
        if p != 3:
            d_lo, d_hi = atanh_fp(p - prev, p + prev)  # raises unless p <= 3*prev
            d_lo *= 2
            d_hi *= 2
            s_lo = atanh_fp(d_lo, 2 * L_hi + d_lo)[0]  # uses log(prev) before update
            s_hi = atanh_fp(d_hi, 2 * L_lo + d_hi)[1]
            L_lo += d_lo
            L_hi += d_hi
            lam_lo += 2 * s_lo
            lam_hi += 2 * s_hi
            prev = p
        e_lo, e_hi = atanh_fp(1, 2 * p - 3)
        yield p, L_lo, L_hi, lam_lo, lam_hi, 2 * e_lo, 2 * e_hi


# ------------------------------------------------------- scan / greedy / lower bound
def scan(data, excluded, tau):
    """Upper bound mx >= ONE*max_{a<=b in S} F_S(a,b), S = primes of data not in excluded,
    via F = X_b - Y_a and a running minimum of the lower bounds of Y (note Step 6.5).
    Also returns the realising pair and phi = sum_b max(0, val_b - tau) (heuristic use)."""
    Ls_lo = Ls_hi = 0
    minY = minYp = mx = pair = None
    phi = 0
    for (p, _l1, _l2, lam_lo, lam_hi, e_lo, e_hi) in data:
        if p in excluded:
            continue
        Y = Ls_lo - lam_hi
        if minY is None or Y < minY:
            minY, minYp = Y, p
        Ls_lo += e_lo
        Ls_hi += e_hi
        val = Ls_hi - lam_lo - minY
        if mx is None or val > mx:
            mx, pair = val, (minYp, p)
        if tau is not None and val > tau:
            phi += val - tau
    return mx, pair, phi


def greedy_Q(data, primes_G, lnlo, forced, tau):
    """HEURISTIC candidate Q0 (note Step 7); inclusion-minimal w.r.t. tau on primes <= G."""
    excl = set(forced)
    while True:
        mx, pair, phi = scan(data, excl, tau)
        if mx is None or mx < tau:
            break
        a, b = pair
        i0, i1 = bisect.bisect_left(primes_G, a), bisect.bisect_right(primes_G, b)
        best_r, best_gain, best_w = None, 0, 1
        for r in primes_G[i0:i1]:
            if r in excl:
                continue
            excl.add(r)
            _, _, phi_r = scan(data, excl, tau)
            excl.discard(r)
            gain, w = phi - phi_r, lnlo[r]
            if best_r is None or gain * best_w > best_gain * w:
                best_r, best_gain, best_w = r, gain, w
        if best_gain <= 0:
            best_r = b
        excl.add(best_r)
    for r in sorted(excl - forced, reverse=True):     # reverse delete
        excl.discard(r)
        mx, _, _ = scan(data, excl, tau)
        if mx is not None and mx >= tau:
            excl.add(r)
    return excl


def lower_bound_rest(data, forced, thr_hi):
    """CERTIFIED lower bound (ONE-scaled) for log of the product of Q0 \\ F_k (Prop. C(iii)):
    max-weight packing of disjoint intervals [a,b] of S' = primes of data not in forced
    with certified F_{S'}(a,b) >= log(1+1/k) (lower bound of F >= upper bound of the log);
    the weight is the lower bound of ONE*log a."""
    rest = [r for r in data if r[0] not in forced]
    n = len(rest)
    Plo = [0] * (n + 1)
    for i, r in enumerate(rest):
        Plo[i + 1] = Plo[i] + r[5]
    best = [0] * (n + 1)
    for j in range(n):
        bj, lamhi_j = best[j], rest[j][4]
        for i in range(j + 1):
            if Plo[j + 1] - Plo[i] - lamhi_j + rest[i][3] >= thr_hi:
                c = best[i] + rest[i][1]
                if c > bj:
                    bj = c
        best[j + 1] = bj
    return best[n]


def pair_bounds(data, excl, a, b):
    """(lo, hi) enclosing ONE*F_S(a,b), with a, b in S, both in data."""
    s_lo = s_hi = 0
    ra = rb = None
    for r in data:
        if a <= r[0] <= b and r[0] not in excl:
            s_lo += r[5]
            s_hi += r[6]
            if r[0] == a:
                ra = r
            if r[0] == b:
                rb = r
    return s_lo - rb[4] + ra[3], s_hi - rb[3] + ra[4]


# ------------------------------------------------------------ Theorem D constants
def tail_constants(B):
    """(d1, d2) >= ONE*(delta_B, delta'_B) of Theorem D; needs 5 <= B <= 10**12 (int).
    t1 >= 2/(sqrt B log B) [E1], t2 >= 6.836e-6/log 1e12 [E2], t3 >= 2.964e-6/log 1e12 [E3],
    t4 >= 1/(B-1)."""
    if not (5 <= B <= 10**12):
        raise ValueError("B out of range for Theorem D")
    lnB_lo = ln_int_fp(B)[0]
    ln12_lo = ln_int_fp(10**12)[0]
    t1 = ceil_div(2 * ONE * ONE, isqrt(B) * lnB_lo)
    t2 = ceil_div(6836 * ONE * ONE, 10**9 * ln12_lo)
    t3 = ceil_div(2964 * ONE * ONE, 10**9 * ln12_lo)
    t4 = ceil_div(ONE, B - 1)
    return max(t1, t2) + t4, max(t1, t2 + t3) + 2 * t4


# --------------------------------------------------- BJS Table 1, heuristic N_3
TABLE = {74: (631, 630), 76: (559, 559), 78: (504, 504), 80: (461, 461), 85: (386, 386),
         90: (336, 337), 95: (302, 302), 100: (276, 277), 120: (218, 219), 140: (189, 190),
         160: (172, 173), 180: (161, 162), 200: (153, 154), 300: (133, 134), 400: (125, 126)}


def table_row(k):
    rows = [r for r in TABLE if r <= k]
    if not rows:
        raise ValueError("k < 74 not allowed by BJS")
    return max(rows)


# HEURISTIC alpha* (largest alpha with model main term >= 0.01), note section 'Trade-off'.
ALPHA_STAR_EST = {74: "0.0957", 80: "0.110", 90: "0.1235", 100: "0.1344",
                  120: "0.1458", 140: "0.1551", 200: "0.1684"}


def n3_estimate(logQ, alpha_str):
    """HEURISTIC, NOT CERTIFIED: solve L = (logQ + 4.05 log L)/alpha (the frame note level rule)."""
    with localcontext() as c:
        c.prec = 28
        a, L = Decimal(alpha_str), Decimal(1000)
        for _ in range(200):
            L = (logQ + Decimal("4.05") * L.ln()) / a
        Lc = Decimal(170) * Decimal(10).ln()
        al170 = (logQ + Decimal("4.05") * Lc.ln()) / Lc
        return L, L / Decimal(10).ln(), al170, Decimal("5.75") - 22 * al170


# --------------------------------------------------------------- sanity checks
def sanity_checks(data):
    idx = {r[0]: r for r in data}
    L2 = Fraction("0.6931471805599453094172321214581765680755")
    assert LN2[0] <= (L2 + Fraction(1, 10**40)) * ONE and LN2[1] >= L2 * ONE, "log 2"
    print("[sanity] log 2 in [%s, %s]" % (fp_dec(LN2[0], False), fp_dec(LN2[1], True)))
    print("[sanity] loglog 3 in [%s, %s]  (expect 0.0940478276...)"
          % (fp_dec(idx[3][3], False), fp_dec(idx[3][4], True)))
    ps = (97, 101, 103, 107, 109)
    P = Fraction(1)
    for p in ps:
        P *= Fraction(p - 1, p - 2)
    assert P == Fraction(11209881600, 10672182675), "exact product"
    xl, xh = atanh_fp(P.numerator - P.denominator, P.numerator + P.denominator)
    s_lo, s_hi = sum(idx[p][5] for p in ps), sum(idx[p][6] for p in ps)
    assert s_lo <= 2 * xh and 2 * xl <= s_hi, "ell sums vs exact log of the product"
    F_lo = s_lo - idx[113][4] + idx[97][3]
    F_hi = s_hi - idx[113][3] + idx[97][4]
    e_lo, e_hi = exp_lo_fp(F_lo) - ONE, exp_hi_fp(F_hi) - ONE
    assert Fraction(16459, 10**6) * ONE <= e_lo and e_hi <= Fraction(16461, 10**6) * ONE
    print("[sanity] half-open [97,113): eps in [%s, %s]  (expect 0.0164598)"
          % (fp_dec(e_lo, False, 8), fp_dec(e_hi, True, 8)))
    lo, hi = pair_bounds(data, set(), 103, 113)
    print("[sanity] closed [103,113], all primes: eps in [%s, %s]  (expect ~0.01797)"
          % (fp_dec(exp_lo_fp(lo) - ONE, False, 8), fp_dec(exp_hi_fp(hi) - ONE, True, 8)))


class St:
    __slots__ = ("name", "k", "Q", "forced", "thr_lo", "lb", "Ls_lo", "Ls_hi",
                 "minY", "minYp", "best", "pair")


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
    G = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    targets = [74, 80, 90, 100, 120, 140, 150, 200]
    if not (300 <= G <= B <= 10**12) or max(targets) + 2 > G:
        raise ValueError("need 300 <= G <= B <= 1e12 and G >= max target + 2")
    GLB = min(5000, G)
    primes = odd_primes_upto(B)
    data_G = []
    for rec in prime_data(primes):
        if rec[0] > G:
            break
        data_G.append(rec)
    primes_G = [r[0] for r in data_G]
    lnlo = {r[0]: r[1] for r in data_G}
    lnhi = {r[0]: r[2] for r in data_G}
    data_LB = [r for r in data_G if r[0] <= GLB]
    sanity_checks(data_G)
    d1, d2 = tail_constants(B)
    print("[tail] B = %d: delta_B <= %s, delta'_B <= %s" % (B, fp_dec(d1, True, 6),
                                                        fp_dec(d2, True, 6)))
    states = []
    for k in targets:
        st = St()
        st.name, st.k = "target 1/%d" % k, k
        thr_lo, thr_hi = ln1p_inv_fp(k)
        st.thr_lo = thr_lo
        st.forced = frozenset(p for p in primes_G if p <= k + 2)
        st.Q = frozenset(greedy_Q(data_G, primes_G, lnlo, st.forced, thr_lo - d1 - 1))
        st.lb = sum(lnlo[p] for p in st.forced) + lower_bound_rest(data_LB, st.forced, thr_hi)
        states.append(st)
    st = St()
    st.name, st.k = "the frame note current (Q0 = odd primes < 41)", None
    st.Q = st.forced = frozenset(p for p in primes_G if p < 41)
    st.thr_lo = st.lb = None
    states.append(st)
    for st in states:
        st.Ls_lo = st.Ls_hi = 0
        st.minY = st.minYp = st.best = st.pair = None
    last = None
    for (p, _a, _b, lam_lo, lam_hi, e_lo, e_hi) in prime_data(primes):   # exhaustive, v <= B
        for st in states:
            if p in st.Q:
                continue
            Y = st.Ls_lo - lam_hi
            if st.minY is None or Y < st.minY:
                st.minY, st.minYp = Y, p
            st.Ls_lo += e_lo
            st.Ls_hi += e_hi
            val = st.Ls_hi - lam_lo - st.minY
            if st.best is None or val > st.best:
                st.best, st.pair = val, (st.minYp, p)
        last = p
    print("[scan] %d odd primes scanned, largest %d" % (len(primes), last))
    allpass = True
    for st in states:
        T = max(st.best + d1, d2)
        eps_hi = exp_hi_fp(T) - ONE
        print("\n== %s ==" % st.name)
        print("   worst closed pair (scan, v <= B): %s" % (st.pair,))
        logQ_hi = sum(lnhi[p] for p in st.Q)
        if st.k is None:
            print("   eps*(S) <= %s" % fp_dec(eps_hi, True, 8))
            a, b = st.pair
            if b <= G:
                lo, _ = pair_bounds(data_G, set(st.Q), a, b)
                if lo >= 0:
                    print("   eps*(S) >= %s (certified, at that pair)"
                          % fp_dec(exp_lo_fp(lo) - ONE, False, 8))
            continue
        ok = T < st.thr_lo
        allpass = allpass and ok
        extras = sorted(st.Q - st.forced)
        row = table_row(st.k)
        print("   Q0 = {odd p <= %d} U %s" % (st.k + 2, extras))
        print("   log Q0 <= %s   (certified LB for any admissible Q0: %s)"
              % (fp_dec(logQ_hi, True, 10), fp_dec(st.lb, False, 10)))
        print("   eps*(S0) <= eps_hi = %s ; 1/eps_hi >= %s ; target 1/%d : %s"
              % (fp_dec(eps_hi, True, 10),
                 fp_dec(ONE * ONE // eps_hi, False, 10), st.k, "PASS" if ok else "FAIL"))
        print("   BJS row %d: C1 = %d, C2 = %d (theorem applied at eps' = 1/%d)"
              % (row, TABLE[row][0], TABLE[row][1], row))
        if str(row) in map(str, ALPHA_STAR_EST):
            L, l10, al, sm = n3_estimate(fp_dec(logQ_hi, True, 20), ALPHA_STAR_EST[row])
            print("   HEURISTIC: alpha*~%s -> log N_3 ~ %.1f (N_3 ~ 10^%.0f); at 1e170: "
                  "alpha >= %.4f, s_min <= %.3f" % (ALPHA_STAR_EST[row], L, l10, al, sm))
    print("\nALL TARGETS PASS" if allpass else "\nSOME TARGET FAILED (enlarge G or B)")
    return 0 if allpass else 1


if __name__ == "__main__":
    sys.exit(main())
```

### Expected output (not run; how to sanity-check)

**Sanity lines.**
- log 2 ∈ [0.69314718…, 0.69314718…].
- log log 3 ≈ 0.0940478.
- Half-open [97,113): ε ∈ [0.016459, 0.016461]. This reproduces the independently computed 0.0164598, and the exact product 11209881600/10672182675 is asserted.
- Closed [103,113] with all primes: ≈ 0.01797 (referee v3).

**Tail line** for B = 10^7: δ_B ≈ 3.93·10⁻⁵ and δ′_B ≈ 3.94·10⁻⁵.

**the frame note current set.**
- Expected ε* upper bound ≈ 0.0374 at pair (41,43). This is referee v3's "≥ 0.0374 inclusive"; by hand, F = 0.049416 − 0.012744.
- A certified lower bound of the same size should also be printed.
- So the frame note's current pre-sieve is outside the theorem, as all three referees found.

**Target lines.**
- The forced part should show log sums matching Step 8 (for example, ≈ 87.650 for 1/100).
- The printed certified lower bound should be ≥ the "LB incl. twins" column, since the DP contains those disjoint twin intervals.
- For 1/100 the extras should include primes from {103…113}, {137,139}, {149,151}, {191…199} and [223,281]. This is a guess from referee v3's list; my guess is log Q_0 ≈ 115–135.

**Runtime.** I estimate 1–5 minutes, dominated by the scan up to 10^7. I could not measure it.

**Independent check.** A float scan of max_{a≤b} F_S(a,b) for the printed Q_0 should agree with the printed pair and value to about 10⁻¹².

---

## Trade-off for the frame note Regime 3 (ESTIMATES, not proofs)

### Model

Write c := 22(½ − α), so c = s for the lower sieve. For q = N^{w/22} with w ∈ [1, 5.25], s_q = c − w. Approximating the q-sum by its Mertens integral, the main coefficient (in the frame note's units, before the (1−δ_V) factor) is

net(α, row) ≈ f(4) − εC₂e²h(c) − ½∫₁^{5.25} [F(c−w) + εC₁e²h(c−w)] dw/w.

Here f(4) is the frame note's bound for the lower bracket, and εC_i are taken at the table row. I evaluated the integrals by hand with Simpson's rule, using step 0.25 in s, Cai's formulas for F on [0,4], and the delay equation on [4,5].

Calibration:
- At c = 8.0124 (the frame note's α = 0.1358, row 100), the model gives 0.0055.
- the frame note's rigorous evaluation gives 0.002683, i.e. about 0.0028 of rigour slack.
- The error terms are about 0.0012.
- I call α "workable" if net ≥ 0.01. This leaves ≈ 0.006 of real margin.

| c (α) | 9.0 (0.0909) | 8.5 (0.1136) | 8.0124 (0.1358) | 7.5 (0.1591) | 7.0 (0.1818) |
|---|---|---|---|---|---|
| f(4) − ½∫F dw/w | 0.1478 | 0.1443 | 0.1331 | 0.1109 | 0.0669 |
| I_h = ½∫e²h dw/w | 0.0134 | 0.0247 | 0.0453 | 0.0823 | 0.1406 |
| e²h(c) | 0.00030 | 0.00053 | 0.00092 | 0.00163 | 0.00289 |

### Per-row results

net ≈ (row 1) − εC₁·I_h − εC₂·e²h(c). Linear interpolation for net = 0.01 gives α*. The columns are:
- s_min = 5.75 − 22α*;
- log₁₀N_3 using the forced log Q only;
- log₁₀N_3 using forced log Q plus the twin lower bound.

The last two are lower bounds on N_3 for this design, conditional on the estimated α*.

| row (εC₁) | α* (est.) | s_min at α* | log₁₀N_3, forced LB | log₁₀N_3, forced+twins LB |
|---|---|---|---|---|
| 74 (8.53) | 0.096 | 3.64 | ≥ 422 | ≥ 466 |
| 80 (5.76) | 0.110 | 3.33 | ≥ 383 | ≥ 421 |
| 90 (3.73) | 0.1235 | 3.03 | ≥ 372 | ≥ 424 |
| 100 (2.76) | 0.134 | 2.79 | ≥ 372 | ≥ 420 |
| 120 (1.82) | 0.146 | 2.54 | ≥ 399 | ≥ 462 |
| 140 (1.35) | 0.155 | 2.34 | ≥ 431 | ≥ 506 |
| 150 → row 140 | 0.155 | 2.34 | ≥ 460 | ≥ 536 |
| 200 (0.765) | 0.168 | 2.05 | ≥ 559 | ≥ 632 |

**Uncertainty.** α* is uncertain by about ±0.005, which moves log N_3 by about ±4%. Each extra unit of log Q adds about 8 to log N, i.e. about 3.5 to log₁₀N_3. The script prints N_3 for the certified log Q_0.

### Conclusions (estimates, except where marked)

1. **Rigorous (Proposition F).** No pre-sieve satisfying (H*) at ε ≤ 1/74 lets Regime 3 start at 10^170 in the frame note's current design. The obstruction is already s_min < 1, before any main-term consideration.
2. **Estimate.** With the BJS constants, Regime 3 cannot start much below about 10^420 for any row. Rows 80, 90 and 100 are the best candidates. The constraint that binds is the main-term budget εC₁·I_h against f − ½∫F, not s_min ≥ 1: s_min stays ≥ 2 at α*.
3. **Recommendation.**
   - Run the script.
   - For rows 80, 90, 100 and 120, compute log N_3 from the **certified** log Q_0. Pick the minimum; I expect row 90 or 100 with N_3 ≈ 10^{420–480}.
   - Rerun the frame note's Regime-3 script at the corresponding α, ε′ = 1/row, and Q_0.
   - Never use non-row targets such as 1/150.
   - Regime 2 must then reach N_3. That is a 250–300 orders-of-magnitude extension, and its feasibility is unknown.
4. **Levers that would lower N_3** (not done here):
   - Use rigorous values of f(s) at s ≈ 8 instead of f(4). This adds about +0.02 to net, i.e. about +0.006 to α*, about −4% on log N_3.
   - A refined induction with a level-dependent ε. The small-prime levels only enter at large n, where τ_n is small. This attacks the real bottleneck, which is that pre-sieving small primes costs log Q ≳ 100.

---

## What is not proved here

- **The interface.** That H_real (all real levels 1 < u < w ≤ z) suffices for a corrected `theo:JR`, with the Table `tab:fF` constants (including Lemma `lem:hsm1`'s inconsistency, flagged by referee v1), is assumed from another section.
- **External inputs.** E1–E3 are quoted, not re-proved. E1 is a 15-hour computation. E2 is from [JS] (via the frame note §0.2) and is not in the attached TeX. E3 rests on Büthe and Broadbent et al.
- **The script has not been run.** No PASS or FAIL is claimed for any target. Python big-integer arithmetic is trusted.
- **Optimality of Q_0.** The greedy result is only inclusion-minimal. Global minimality of log Q_0 is not proved; only the hitting-set lower bound is.
- **Twin-table arithmetic.** The twin-pair entries in Step 8 are hand-evaluated. The script's DP is the rigorous version.
- **The trade-off section.** All of it is an estimate: hand quadrature, linear interpolation, and a calibration on a single the frame note data point. The hard-coded α* values in the script are heuristic. Decimal's `ln` there is not certified.
- **Regime 2 and the rest of the frame note.** Neither the extension of Regime 2 nor any other the frame note quantity at the new parameters is checked.

## Checks a referee should make

1. Run the script and confirm:
   - the sanity assertions pass, including the exact product 11209881600/10672182675;
   - the forced log sums match Step 8;
   - the the frame note line shows ε* ≈ 0.0374.
2. Recheck Theorem A(b): the limit w ↓ b needs b < z. This is why ε*_z runs over pairs with b < z.
3. Recheck Theorem D:
   - B ≤ 10^12 is needed for A(B) > 0;
   - the passage in E2 from Σ_{p<x} to Σ_{p≤x} by right-continuity;
   - the telescoping bound n_0 − 2 ≥ B − 1;
   - the 1/a term in Case (ii).
4. Check the atanh tail bound, which needs x ≤ ½, and the monotonicity directions in the log log recursion (δ_lo with L′_hi).
5. Check the prefix-minimum identity, including that the a = b case is covered.
6. Cross-check the certified M_B against an independent float computation of max F_S. Confirm that the printed lower bound for log Q_0 is ≥ the hand "LB incl. twins".
7. Redo the trade-off integrals numerically, and replace the model by the frame note's rigorous Regime-3 computation at the chosen (α, row, Q_0).
8. Verify the Proposition F arithmetic: at L = 414, α ≥ 0.21639 > 0.215909.