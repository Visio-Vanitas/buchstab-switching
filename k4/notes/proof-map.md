# Every even N ≥ 4 is p + η with Ω(η) ≤ 4, under GRH: the proof with final parameters

GRH for Dirichlet L-functions is used as an established theorem. This note assembles the three ranges with their final parameters. The weighted inequality and the worst case over the primes dividing `N` are in `frame-weighted-inequality.md` (§1–§2; its §3–§4 describe an earlier split and are superseded here), the corrected linear sieve in `../../shared/notes/linear-sieve/`, the block sieve in `../../shared/notes/block-sieve/`.

## 1. Theorem

**Theorem.** *Assume GRH for Dirichlet L-functions. Then every even integer N ≥ 4 is N = p + η with p prime and Ω(η) ≤ 4.*

The proof splits the even integers into three ranges with exact integer endpoints:

| Range | Method | Where proved | Certificate | Least margin |
|---|---|---|---|---|
| `4 ≤ N ≤ 4·10^18` | numerical verification of Goldbach (`Ω(η) = 1`) | quoted, frame note §0.6 | none | not applicable |
| `4·10^18 ≤ N < 10^500` | weighted inequality (1.1) with the Brun block sieve, 58 contiguous slabs | frame note §1–§2, block-sieve note | `k4/data/certificate/ladder_4e18_500_all.json`, replay log | net `> 1.6796·10^-3` (slab `[10^390, 10^400)`); relative margin smallest in slab 1 (`1.82·10^-3` of main `2.43·10^-2`) |
| `N ≥ 10^500` | weighted inequality (1.1) with the explicit linear sieve with pre-sieve | frame note §1, linear-sieve notes | `k4/data/certificate/tail/tail_at_500.json` | net `> 0.07522` (sharper recursion), `> 0.03909` (old recursion) |

## 2. The common frame

For even `N`, `A = {N − p : p ≤ N, p ∤ N}`, and parameters `z < y`. With the weight

`w(a) = 1 − ½·#{q prime, z ≤ q < y, q | a} − ½·#{q prime, z ≤ q < y, q² | a}`,

every `a ∈ A` with no prime factor below `z` and `w(a) > 0` has `Ω(a) ≤ 4`, provided `z·y⁴ ≥ N` and `y⁵ > N` (frame note §1: either no `q ∈ [z, y)` divides `a`, and then all prime factors are `≥ y` with `a < y⁵`; or exactly one does, to the first power, and `a/q < y⁴`). Since `w ≤ 1`,

`π₄(N) ≥ S(A, z) − ½ Σ_{z ≤ q < y} S(A_q, z) − ½ Σ_{z ≤ q < y} |A_{q²}|`. (1.1)

A lower-bound sieve is applied to the first term, an upper-bound sieve to each `S(A_q, z)`, and the last term is bounded directly. The remainders are bounded per modulus by GRH ([JS] Lemma 5.1, with the certified `c_π`), and the worst case over the primes dividing `N` is handled by frame note §2 and block-sieve Lemma C (deleting primes from the sifting set only helps).

## 3. Middle range: the block sieve

Blocks of primes `B_1` (largest) … `B_r`, with caps `m_1 ≤ … ≤ m_r` on the number of prime factors of `d` in `B_1 ∪ … ∪ B_i`; all caps odd give a lower-bound sieve, all even an upper-bound sieve (Theorem A). The sieve sum is `V·(1 ∓ E)` with `0 ≤ E ≤ Σ_i S_i^{m_i+1} / ((m_i+1)!·V_i)` (Lemmas B.3, D), and the level is at most `∏ z_{i−1}^{m_i − m_{i−1}}` (Lemma E). The script `k4/certificate/all_even_1p4_ext/regime2_brun.py` (`certify_brun_slab`) evaluates (1.1) on a slab `[X_lo, X_hi)` in interval arithmetic with the package's inputs and checks the level conditions as exact integers.

- Ladder: `k4/data/certificate/LADDER_TABLE.md` (58 slabs, parameters and nets).
- Replay: `k4/certificate/all_even_1p4_ext/replay.py` re-certifies each slab from the recorded parameters with no search and checks that the endpoints are contiguous from `4·10^18` to `10^500`; log in `k4/data/certificate/replay/`.
- Cross-check against the Bonferroni sieve of the frame note on `[10^200, 10^205)`: `k4/data/certificate/crosscheck_200_205.txt`.

## 4. Tail: the explicit linear sieve

The linear-sieve notes prove an explicit β = 2 linear sieve with an arbitrary pre-sieve set `Q₀`, under the hypothesis that for every closed interval of sifting primes `[u, v]` the product `∏ (1 − 1/(p−1))^{-1}` is at most `(1 + ε)·log v / log u` with `ε ≤ 1/74`: lower and upper bounds `V(z)·(f(s) − ε C₂ e² h(s))` and `V(z)·(F(s) + ε C₁ e² h(s))`, up to remainders. It replaces [BJS] Theorem 6, whose printed table is not reproduced by its own recursion (`shared/notes/linear-sieve/README.md` §2).

Final parameters, `ε = 1/80`:

- `Q₀` = odd primes `≤ 82` together with `103, 107, 191, 223`, `log ∏Q₀ ≤ 89.52005829`; the hypothesis is certified for all prime pairs (scan to `10^7` plus the analytic tail of linear-sieve S3 Theorem D): `shared/certificate/linear_sieve/hstar_certify.py`.
- Constants: `C₁ = 391.821751`, `C₂ = 390.689851` (sharper recursion, linear-sieve S4 Theorem 3); `C₁ ≤ 577.871`, `C₂ ≤ 579.660` (old recursion with certified `c_n`).
- At `N ≥ 10^500`, `B = 3.01`, `α = 0.1024`: sharper recursion `M = 22`, `s = 8.7472`, main `0.07667`, errors `0.00144`, **net `> 0.07522`**; old recursion `M = 24`, `s = 9.5424`, main `0.04042`, errors `0.00132`, **net `> 0.03909`**. With `C₁`, `C₂` raised by 5% the nets are `0.0707` and `0.0349`. The tail therefore does not depend on the sharper recursion.
- Script: `k4/certificate/all_even_1p4_ext/tail_x31.py` (reads `Q₀`, `C₁`, `C₂` from `shared/data/linear_sieve_inputs/`), `tail_at_500.py`; `F`, `f` from `sieve_fF.py` at mesh `H = 2000`.

## 5. Checks

Each part (the weighted inequality and its remainder terms, the block sieve, the corrected linear sieve and its constants, and the certificate code for both computed ranges) was read by several independent readers, each part at least twice, with no error found. Every certified number was reproduced by an independent replay from the recorded parameters with no search (`k4/data/certificate/replay/`).

## 6. What the theorem still rests on without a check at source

1. Regime 1: the numerical verification of Goldbach to `4·10^18` (Oliveira e Silva, Herzog, Pardi), quoted.
2. Nathanson, *Additive Number Theory: The Classical Bases*, Theorem 9.4 and its neighbourhood: the identification of the sieve limits with the delay-equation functions `F`, `f` (`3F(3) = 2e^γ`, `f(2) = 0`). The book has not been available to the group.
3. [JS] arXiv:2208.01229v3: Lemma 5.1 (GRH remainder with `c_π`), Lemma 3.1, (3.1)–(3.3), and the monotonicity of `F`, `f` in §2. Read as quoted; (3.3) is used second-hand in linear-sieve S3 Theorem D.
4. Schoenfeld's bound for `π(x)` under RH, Robin's bound for `ω(n)`, [BJS] Lemma 16.

## 7. Reproduce

See `k4/data/certificate/README.md` (ladder segments, cross-check, tail) and

```
cd k4/certificate
python3 -I all_even_1p4_ext/replay.py ../data/certificate/ladder_4e18_500_all.json ../data/certificate/tail/tail_at_500.json
```
