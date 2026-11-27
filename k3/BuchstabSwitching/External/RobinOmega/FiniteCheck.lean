import BuchstabSwitching.External.RobinOmega.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Pure-Kernel Finite Verification of `π(p) < 1.3841 * θ(p) / log θ(p)` for `7 ≤ p < 13000`

Certifies the finite prime range `7 ≤ p < 13000` (`1,547` primes `< 13000`) for Robin's bound
using outward-rounded Q64 (`2^64`) integer lower bounds on `Real.log` and `Real.exp` evaluated
by the Lean kernel (`by decide`), with zero infinite-series tail bounds:
1. `primesLt13000`: complete strictly increasing table of all `1,547` primes `< 13000`;
2. `q64LogNatLb` and `q64ExpLb`: unconditional partial-sum lower bounds for `log` and `exp`;
3. `robin_primeCounting_lt_of_lt_13000`: `π(p) < 1.3841 * θ(p) / log θ(p)` for `7 ≤ p < 13000`.
-/

namespace BuchstabSwitching.External

/-! ## 1. Complete Prime Table `< 13000` -/

private def smallPrimes113 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

private def hasSmallFactor113 (n : ℕ) : Bool :=
  smallPrimes113.any (fun d => d < n && n % d == 0)

private def checkGapRange13000 (lo : ℕ) : ℕ → Bool
  | 0 => true
  | c + 1 => hasSmallFactor113 lo && checkGapRange13000 (lo + 1) c

private def checkPrimesLoop13000 (prev : ℕ) : List ℕ → Bool × ℕ
  | [] => (true, prev)
  | p :: ps =>
    if prev < p && p < 13000 && !hasSmallFactor113 p &&
        checkGapRange13000 (prev + 1) (p - prev - 1) then
      checkPrimesLoop13000 p ps
    else (false, 0)

private def checkPrimesChunks13000 (prev : ℕ) : List (List ℕ) → Bool
  | [] => decide (prev < 13000) && checkGapRange13000 (prev + 1) (13000 - prev - 1)
  | c :: cs =>
    let (ok, nxt) := checkPrimesLoop13000 prev c
    ok && checkPrimesChunks13000 nxt cs

private def primeChunks13000 : List (List ℕ) := [
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
   179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281],
  [283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
   419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
   547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659],
  [661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
   811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
   947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069],
  [1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
   1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373,
   1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511],
  [1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657,
   1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
   1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987],
  [1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129,
   2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287,
   2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423],
  [2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617,
   2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
   2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903],
  [2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079,
   3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257,
   3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413],
  [3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571,
   3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727,
   3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907],
  [3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057,
   4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231,
   4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409],
  [4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583,
   4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751,
   4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937],
  [4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087,
   5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279,
   5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443],
  [5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639,
   5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791,
   5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939],
  [5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133,
   6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301,
   6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473],
  [6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673,
   6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833,
   6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997],
  [7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207,
   7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411,
   7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561],
  [7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723,
   7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919,
   7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111],
  [8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291,
   8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501,
   8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677],
  [8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831,
   8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011,
   9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199],
  [9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377,
   9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533,
   9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733],
  [9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887,
   9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099,
   10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271],
  [10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459,
   10463, 10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657,
   10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859],
  [10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059,
   11069, 11071, 11083, 11087, 11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239, 11243, 11251,
   11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399, 11411, 11423, 11437, 11443],
  [11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657,
   11677, 11681, 11689, 11699, 11701, 11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833,
   11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987, 12007, 12011],
  [12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161, 12163, 12197, 12203, 12211,
   12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289, 12301, 12323, 12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401,
   12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553],
  [12569, 12577, 12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739,
   12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899, 12907, 12911, 12917, 12919, 12923,
   12941, 12953, 12959, 12967, 12973, 12979, 12983]
]

private def primesLt13000 : List ℕ := primeChunks13000.flatten

private lemma primesLt13000_chain_ok :
    checkPrimesChunks13000 1 primeChunks13000 = true := by decide

private lemma small115_check :
    (List.range 115).all (fun q => q ∈ smallPrimes113 || q < 2 ||
      [2, 3, 5, 7].any (fun d => d < q && q % d == 0)) = true := by decide

private lemma smallPrimes113_ge2 : ∀ d ∈ smallPrimes113, 2 ≤ d := by decide

private lemma smallDivs_ge2 : ∀ d ∈ ([2, 3, 5, 7] : List ℕ), 2 ≤ d := by decide

private lemma prime_of_not_hasSmallFactor113 {n : ℕ} (hn2 : 2 ≤ n) (hn : n < 13000)
    (hsf : hasSmallFactor113 n = false) : n.Prime := by
  by_contra hnp
  have hm_pr := Nat.minFac_prime (by omega : n ≠ 1)
  have hm_lt : n.minFac < n :=
    lt_of_le_of_ne (Nat.minFac_le (by omega)) (fun h => hnp (h ▸ hm_pr))
  have hm_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hm_lt115 : n.minFac < 115 := by nlinarith
  have hall := List.all_eq_true.mp small115_check n.minFac (List.mem_range.mpr hm_lt115)
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hall
  have hm_mem : n.minFac ∈ smallPrimes113 := by
    rcases hall with (hm | h2) | ⟨d, hdm, hdl, hmod⟩
    · exact hm
    · exact absurd hm_pr.two_le (by omega)
    · have hd2 := smallDivs_ge2 d hdm
      rcases hm_pr.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with rfl | rfl <;> omega
  have hbad := List.any_eq_false.mp hsf n.minFac hm_mem
  simp [hm_lt, Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n)] at hbad

private lemma hasSmallFactor113_not_prime {n : ℕ} (hsf : hasSmallFactor113 n = true) :
    ¬ n.Prime := by
  intro hpr
  rcases List.any_eq_true.mp hsf with ⟨d, hd_mem, hd_prop⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd_prop
  have hd2 := smallPrimes113_ge2 d hd_mem
  rcases hpr.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd_prop.2) with rfl | rfl <;> omega

private lemma checkGapRange13000_sound : ∀ (c lo : ℕ), checkGapRange13000 lo c = true →
    ∀ n : ℕ, lo ≤ n → n < lo + c → ¬ n.Prime := by
  intro c
  induction c with
  | zero => intro lo _ n h1 h2; omega
  | succ c ih =>
    intro lo h n h1 h2
    simp only [checkGapRange13000, Bool.and_eq_true] at h
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact hasSmallFactor113_not_prime h.1
    · exact ih (lo + 1) h.2 n (by omega) (by omega)

private lemma checkPrimesLoop13000_sound : ∀ (ps : List ℕ) (prev : ℕ),
    1 ≤ prev → (checkPrimesLoop13000 prev ps).1 = true →
    prev ≤ (checkPrimesLoop13000 prev ps).2 ∧ ps.Pairwise (· < ·) ∧
      (∀ p ∈ ps, prev < p ∧ p ≤ (checkPrimesLoop13000 prev ps).2 ∧ p < 13000 ∧ p.Prime) ∧
      (∀ n : ℕ, prev < n → n ≤ (checkPrimesLoop13000 prev ps).2 → n ∉ ps → ¬ n.Prime) := by
  intro ps
  induction ps with
  | nil =>
    intro prev _ _
    simp only [checkPrimesLoop13000]
    exact ⟨le_rfl, List.Pairwise.nil, (fun _ h => by cases h), fun n h1 h2 _ => by omega⟩
  | cons p ps ih =>
    intro prev hprev h
    simp only [checkPrimesLoop13000] at h
    split_ifs at h with hcond
    · have hres : checkPrimesLoop13000 prev (p :: ps) = checkPrimesLoop13000 p ps := by
        simp only [checkPrimesLoop13000, hcond, ↓reduceIte]
      rw [hres]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨⟨hp_gt, hp_lt⟩, hsf⟩, hgap⟩
      have hp_pr := prime_of_not_hasSmallFactor113 (by omega) hp_lt hsf
      have hrec := ih p (by omega) h
      refine ⟨(hp_gt.le).trans hrec.1,
        List.pairwise_cons.mpr ⟨fun q hq => (hrec.2.2.1 q hq).1, hrec.2.1⟩,
        fun q hq => ?_, fun n hn1 hn2 hn_mem => ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hp_gt, hrec.1, hp_lt, hp_pr⟩
        · exact ⟨hp_gt.trans (hrec.2.2.1 q hq).1, (hrec.2.2.1 q hq).2⟩
      · simp only [List.mem_cons, not_or] at hn_mem
        rcases lt_or_gt_of_ne hn_mem.1 with hnp | hpn
        · exact checkGapRange13000_sound (p - prev - 1) (prev + 1) hgap n (by omega) (by omega)
        · exact hrec.2.2.2 n hpn hn2 hn_mem.2

private lemma checkPrimesChunks13000_sound : ∀ (cs : List (List ℕ)) (prev : ℕ),
    1 ≤ prev → checkPrimesChunks13000 prev cs = true →
    cs.flatten.Pairwise (· < ·) ∧
      (∀ p ∈ cs.flatten, prev < p ∧ p < 13000 ∧ p.Prime) ∧
      (∀ n : ℕ, prev < n → n < 13000 → n ∉ cs.flatten → ¬ n.Prime) := by
  intro cs
  induction cs with
  | nil =>
    intro prev _ h
    simp only [checkPrimesChunks13000, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨List.Pairwise.nil, (fun _ h1 => by cases h1), fun n h1 h2 _ =>
      checkGapRange13000_sound (13000 - prev - 1) (prev + 1) h.2 n (by omega) (by omega)⟩
  | cons c cs ih =>
    intro prev hprev h
    simp only [checkPrimesChunks13000, Bool.and_eq_true] at h
    have hloop := checkPrimesLoop13000_sound c prev hprev h.1
    have hrec := ih (checkPrimesLoop13000 prev c).2 (hprev.trans hloop.1) h.2
    refine ⟨?_, fun p hp => ?_, fun n h1 h2 hmem => ?_⟩
    · simp only [List.flatten_cons]
      exact List.pairwise_append.mpr ⟨hloop.2.1, hrec.1, fun a ha b hb =>
        lt_of_le_of_lt (hloop.2.2.1 a ha).2.1 (hrec.2.1 b hb).1⟩
    · simp only [List.flatten_cons, List.mem_append] at hp
      exact hp.elim (fun h => ⟨(hloop.2.2.1 p h).1, (hloop.2.2.1 p h).2.2⟩)
        (fun h => ⟨lt_of_le_of_lt hloop.1 (hrec.2.1 p h).1, (hrec.2.1 p h).2⟩)
    · simp only [List.flatten_cons, List.mem_append, not_or] at hmem
      exact (le_or_gt n (checkPrimesLoop13000 prev c).2).elim
        (fun hn => hloop.2.2.2 n h1 hn hmem.1) (fun hn => hrec.2.2 n hn h2 hmem.2)

private lemma primesLt13000_pairwise_lt : primesLt13000.Pairwise (· < ·) :=
  (checkPrimesChunks13000_sound primeChunks13000 1 le_rfl primesLt13000_chain_ok).1

private lemma primesLt13000_nodup : primesLt13000.Nodup :=
  primesLt13000_pairwise_lt.imp (fun {_ _} h => Nat.ne_of_lt h)

private lemma mem_primesLt13000_iff {p : ℕ} : p ∈ primesLt13000 ↔ p < 13000 ∧ p.Prime := by
  have hs := checkPrimesChunks13000_sound primeChunks13000 1 le_rfl primesLt13000_chain_ok
  constructor
  · intro hp
    exact (hs.2.1 p hp).2
  · rintro ⟨hp13, hp_pr⟩
    by_contra hmem
    exact hs.2.2 p hp_pr.two_le hp13 hmem hp_pr

/-! ## 2. Zero-Tail Q64 `log` and `exp` Lower Bounds -/

private def q64Scale : ℕ := 1 <<< 64

private lemma q64Scale_eq : q64Scale = 2 ^ 64 := by
  unfold q64Scale; rw [Nat.shiftLeft_eq, one_mul]

private lemma q64Scale_pos : (0 : ℝ) < (q64Scale : ℝ) := by
  rw [q64Scale_eq]; positivity

private lemma q64MulLb_le (a b : ℕ) :
    (((a * b) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤
      ((a : ℝ) / (q64Scale : ℝ)) * ((b : ℝ) / (q64Scale : ℝ)) := by
  have hq : 0 < (q64Scale : ℝ) := q64Scale_pos
  have hdiv : ((a * b) >>> 64) * q64Scale ≤ a * b := by
    rw [Nat.shiftRight_eq_div_pow, ← q64Scale_eq]
    exact Nat.div_mul_le_self (a * b) q64Scale
  have hcast : (((a * b) >>> 64 : ℕ) : ℝ) * (q64Scale : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    exact_mod_cast hdiv
  rw [div_mul_div_comm, div_le_div_iff₀ hq (mul_pos hq hq)]
  calc
    (((a * b) >>> 64 : ℕ) : ℝ) * ((q64Scale : ℝ) * (q64Scale : ℝ))
        = ((((a * b) >>> 64 : ℕ) : ℝ) * (q64Scale : ℝ)) * (q64Scale : ℝ) := by ring
    _ ≤ ((a : ℝ) * (b : ℝ)) * (q64Scale : ℝ) := mul_le_mul_of_nonneg_right hcast hq.le

private def coeffsLo10 : List ℕ := [
  36893488147419103232, 12297829382473034410, 7378697629483820646,
  5270498306774157604, 4099276460824344803, 3353953467947191202,
  2837960626724546402, 2459565876494606882, 2170205185142300190,
  1941762534074689643
]

private def checkCoeffsLo : ℕ → List ℕ → Bool
  | _, [] => true
  | j, c :: rest => decide (c * (2 * j + 1) ≤ 2 * q64Scale) && checkCoeffsLo (j + 1) rest

private lemma coeffsLo10_ok : checkCoeffsLo 0 coeffsLo10 = true := by decide

private def logLoopLb64 (u2Lo : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, sLo => sLo
  | c :: rest, tLo, sLo =>
    logLoopLb64 u2Lo rest ((tLo * u2Lo) >>> 64) (sLo + ((tLo * c) >>> 64))

private lemma logLoopLb64_sound {u : ℝ} (hu_nn : 0 ≤ u)
    {u2Lo : ℕ} (hu2Lo : (u2Lo : ℝ) / (q64Scale : ℝ) ≤ u ^ 2) :
    ∀ (cs : List ℕ) (j tLo sLo : ℕ),
      checkCoeffsLo j cs = true →
      (tLo : ℝ) / (q64Scale : ℝ) ≤ u ^ (2 * j + 1) →
      ((logLoopLb64 u2Lo cs tLo sLo : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) ≤
        ∑ m ∈ Finset.range cs.length,
          (2 : ℝ) * (1 / (2 * ((j + m : ℕ) : ℝ) + 1)) * u ^ (2 * (j + m) + 1)
  | [], _, _, sLo, _, _ => by simp [logLoopLb64]
  | c :: rest, j, tLo, sLo, hchk, htLo => by
    simp only [checkCoeffsLo, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have hd_pos : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
    have hcLo : (c : ℝ) / (q64Scale : ℝ) ≤ 2 / (2 * (j : ℝ) + 1) := by
      rw [div_le_div_iff₀ q64Scale_pos hd_pos]; exact_mod_cast hchk.1
    have hterm : (((tLo * c) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤
        (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) := by
      have h1 := (q64MulLb_le tLo c).trans
        (mul_le_mul htLo hcLo (by positivity) (pow_nonneg hu_nn _))
      linarith [show (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * u ^ (2 * j + 1) =
        u ^ (2 * j + 1) * (2 / (2 * (j : ℝ) + 1)) by ring]
    have htLo1 : (((tLo * u2Lo) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤ u ^ (2 * (j + 1) + 1) := by
      have h1 := (q64MulLb_le tLo u2Lo).trans
        (mul_le_mul htLo hu2Lo (by positivity) (pow_nonneg hu_nn _))
      rw [← pow_add, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega] at h1
      exact h1
    have hrec := logLoopLb64_sound hu_nn hu2Lo rest (j + 1)
      ((tLo * u2Lo) >>> 64) (sLo + ((tLo * c) >>> 64)) hchk.2 htLo1
    dsimp only [logLoopLb64] at hrec ⊢
    rw [List.length_cons, Finset.sum_range_succ']
    have hshift :
        ∑ x ∈ Finset.range rest.length,
          (2 : ℝ) * (1 / (2 * ((j + (x + 1) : ℕ) : ℝ) + 1)) * u ^ (2 * (j + (x + 1)) + 1) =
        ∑ m ∈ Finset.range rest.length,
          (2 : ℝ) * (1 / (2 * ((j + 1 + m : ℕ) : ℝ) + 1)) * u ^ (2 * (j + 1 + m) + 1) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show j + (m + 1) = j + 1 + m by omega]
    rw [hshift]; simp only [Nat.add_zero]
    push_cast at hrec ⊢
    set res := logLoopLb64 u2Lo rest ((tLo * u2Lo) >>> 64) (sLo + ((tLo * c) >>> 64))
    have hs1 : ((res : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) =
        ((res : ℝ) - ((sLo : ℝ) + (((tLo * c) >>> 64 : ℕ) : ℝ))) / (q64Scale : ℝ) +
          (((tLo * c) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) := by ring
    rw [hs1]; exact add_le_add hrec hterm

private def q64LogRatioLb (m p2 : ℕ) : ℕ :=
  let uLo := ((m - p2) <<< 64) / (m + p2)
  let u2Lo := (uLo * uLo) >>> 64
  logLoopLb64 u2Lo coeffsLo10 uLo 0

private lemma q64LogRatioLb_le {m p2 : ℕ} (hp2 : 0 < p2) (hlo : p2 ≤ m) :
    (q64LogRatioLb m p2 : ℝ) / (q64Scale : ℝ) ≤ Real.log ((m : ℝ) / (p2 : ℝ)) := by
  set a : ℕ := m - p2
  set d : ℕ := m + p2
  set u : ℝ := (a : ℝ) / (d : ℝ)
  have hd_pos : 0 < d := by omega
  have ha_lt_d : a < d := by omega
  have hm_pos : 0 < m := by omega
  have hd_r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hp2_r : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2
  have hm_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hu_nn : 0 ≤ u := by positivity
  have hu_lt1 : u < 1 := (div_lt_one hd_r).mpr (by exact_mod_cast ha_lt_d)
  have hu_abs : |u| < 1 := by rwa [abs_of_nonneg hu_nn]
  have hlog_eq : Real.log ((m : ℝ) / (p2 : ℝ)) = Real.log (1 + u) - Real.log (1 - u) := by
    have ha_r : (a : ℝ) = (m : ℝ) - (p2 : ℝ) := Nat.cast_sub hlo
    have hd_eq : (d : ℝ) = (m : ℝ) + (p2 : ℝ) := by push_cast [d]; rfl
    have h1pu : 1 + u = (2 * (m : ℝ)) / (d : ℝ) := by
      simp only [u]; rw [one_add_div hd_r.ne', ha_r, hd_eq]; ring
    have h1mu : 1 - u = (2 * (p2 : ℝ)) / (d : ℝ) := by
      simp only [u]; rw [one_sub_div hd_r.ne', ha_r, hd_eq]; ring
    rw [← Real.log_div (by rw [h1pu]; positivity) (by rw [h1mu]; positivity), h1pu, h1mu]
    congr 1; field_simp [hd_r.ne', hp2_r.ne']
  have hhasSum := hlog_eq ▸ Real.hasSum_log_sub_log_of_abs_lt_one hu_abs
  have hsum_le := sum_le_hasSum (Finset.range coeffsLo10.length)
    (fun j _ => by positivity) hhasSum
  set uLo : ℕ := (a <<< 64) / d
  have huLo : (uLo : ℝ) / (q64Scale : ℝ) ≤ u := by
    rw [div_le_div_iff₀ q64Scale_pos hd_r]
    have hmul : uLo * d ≤ a * q64Scale := by
      have h1 : uLo * d ≤ a <<< 64 := Nat.div_mul_le_self (a <<< 64) d
      rwa [Nat.shiftLeft_eq, ← q64Scale_eq] at h1
    exact_mod_cast hmul
  set u2Lo : ℕ := (uLo * uLo) >>> 64
  have hu2Lo : (u2Lo : ℝ) / (q64Scale : ℝ) ≤ u ^ 2 :=
    (q64MulLb_le uLo uLo).trans (sq u ▸ mul_le_mul huLo huLo (by positivity) hu_nn)
  have hloop := logLoopLb64_sound hu_nn hu2Lo coeffsLo10 0 uLo 0
    coeffsLo10_ok (by simpa using huLo)
  simp only [Nat.cast_zero, sub_zero, Nat.zero_add] at hloop
  exact hloop.trans hsum_le

private def ln2Lo64 : ℕ := 12786308645015723917

private lemma ln2Lo64_ok : decide (ln2Lo64 ≤ q64LogRatioLb 2 1) = true := by decide

private lemma ln2Lo64_le : (ln2Lo64 : ℝ) / (q64Scale : ℝ) ≤ Real.log 2 := by
  have h1 : (ln2Lo64 : ℝ) / (q64Scale : ℝ) ≤ (q64LogRatioLb 2 1 : ℝ) / (q64Scale : ℝ) := by
    gcongr
    exact_mod_cast of_decide_eq_true ln2Lo64_ok
  have h2 := q64LogRatioLb_le (m := 2) (p2 := 1) (by omega) (by omega)
  simpa using h1.trans h2

private def log2Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if 2 ≤ n then log2Aux fuel (n >>> 1) + 1 else 0

private def fastLog2 (n : ℕ) : ℕ := log2Aux 14 n

private def q64LogNatLb (n : ℕ) : ℕ :=
  let b := fastLog2 n
  let p2 := 1 <<< b
  if p2 ≤ n then b * ln2Lo64 + q64LogRatioLb n p2 else 0

private lemma q64LogNatLb_le {n : ℕ} (hn : 1 ≤ n) :
    (q64LogNatLb n : ℝ) / (q64Scale : ℝ) ≤ Real.log (n : ℝ) := by
  unfold q64LogNatLb; dsimp only
  split_ifs with hlo
  · set b := fastLog2 n
    set p2 := 1 <<< b
    have hp2_eq : p2 = 2 ^ b := by dsimp only [p2]; rw [Nat.shiftLeft_eq, one_mul]
    have hp2_pos : 0 < p2 := by rw [hp2_eq]; positivity
    have hp2_r : (0 : ℝ) < (p2 : ℝ) := by exact_mod_cast hp2_pos
    have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsplit : (n : ℝ) = (2 : ℝ) ^ b * ((n : ℝ) / (p2 : ℝ)) := by
      have hp2_cast : (p2 : ℝ) = (2 : ℝ) ^ b := by exact_mod_cast hp2_eq
      rw [← hp2_cast, mul_div_cancel₀ _ hp2_r.ne']
    have hlog : Real.log (n : ℝ) = (b : ℝ) * Real.log 2 + Real.log ((n : ℝ) / (p2 : ℝ)) := by
      conv_lhs => rw [hsplit]
      rw [Real.log_mul (by positivity) (div_pos hn_r hp2_r).ne', Real.log_pow]
    have hln2 := mul_le_mul_of_nonneg_left ln2Lo64_le (Nat.cast_nonneg b)
    have hrat := q64LogRatioLb_le hp2_pos hlo
    push_cast; rw [add_div, mul_div_assoc]; linarith
  · simp only [Nat.cast_zero, zero_div]
    exact Real.log_nonneg (by exact_mod_cast hn)

private def invFactLo13 : List ℕ := [
  18446744073709551616, 18446744073709551616, 9223372036854775808,
  3074457345618258602, 768614336404564650, 153722867280912930,
  25620477880152155, 3660068268593165, 457508533574145,
  50834281508238, 5083428150823, 462129831893, 38510819324
]

private def checkInvFactLo : ℕ → List ℕ → Bool
  | _, [] => true
  | j, c :: rest => decide (c * j.factorial ≤ q64Scale) && checkInvFactLo (j + 1) rest

private lemma invFactLo13_ok : checkInvFactLo 0 invFactLo13 = true := by decide

private def expTaylorLbLoop (z : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, sLo => sLo
  | c :: rest, pLo, sLo =>
    expTaylorLbLoop z rest ((pLo * z) >>> 64) (sLo + ((pLo * c) >>> 64))

private lemma expTaylorLbLoop_sound {w : ℝ} (hw_nn : 0 ≤ w)
    {z : ℕ} (hz : (z : ℝ) / (q64Scale : ℝ) ≤ w) :
    ∀ (cs : List ℕ) (j pLo sLo : ℕ),
      checkInvFactLo j cs = true →
      (pLo : ℝ) / (q64Scale : ℝ) ≤ w ^ j →
      ((expTaylorLbLoop z cs pLo sLo : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) ≤
        ∑ m ∈ Finset.range cs.length, w ^ (j + m) / ((j + m).factorial : ℝ)
  | [], _, _, sLo, _, _ => by simp [expTaylorLbLoop]
  | c :: rest, j, pLo, sLo, hchk, hpLo => by
    simp only [checkInvFactLo, Bool.and_eq_true, decide_eq_true_eq] at hchk
    have hf_pos : (0 : ℝ) < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
    have hc : (c : ℝ) / (q64Scale : ℝ) ≤ 1 / (j.factorial : ℝ) := by
      rw [div_le_div_iff₀ q64Scale_pos hf_pos, one_mul]; exact_mod_cast hchk.1
    have hterm : (((pLo * c) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤ w ^ j / (j.factorial : ℝ) := by
      have h1 := (q64MulLb_le pLo c).trans
        (mul_le_mul hpLo hc (by positivity) (pow_nonneg hw_nn j))
      rwa [← div_eq_mul_one_div] at h1
    have hpLo1 : (((pLo * z) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤ w ^ (j + 1) := by
      have h1 := (q64MulLb_le pLo z).trans
        (mul_le_mul hpLo hz (by positivity) (pow_nonneg hw_nn j))
      simpa [pow_succ] using h1
    have hrec := expTaylorLbLoop_sound hw_nn hz rest (j + 1)
      ((pLo * z) >>> 64) (sLo + ((pLo * c) >>> 64)) hchk.2 hpLo1
    dsimp only [expTaylorLbLoop] at hrec ⊢
    rw [List.length_cons, Finset.sum_range_succ']
    have hshift :
        ∑ x ∈ Finset.range rest.length, w ^ (j + (x + 1)) / ((j + (x + 1)).factorial : ℝ) =
        ∑ m ∈ Finset.range rest.length, w ^ (j + 1 + m) / ((j + 1 + m).factorial : ℝ) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show j + (m + 1) = j + 1 + m by omega]
    rw [hshift]; simp only [Nat.add_zero]
    push_cast at hrec ⊢
    set res := expTaylorLbLoop z rest ((pLo * z) >>> 64) (sLo + ((pLo * c) >>> 64))
    have hs1 : ((res : ℝ) - (sLo : ℝ)) / (q64Scale : ℝ) =
        ((res : ℝ) - ((sLo : ℝ) + (((pLo * c) >>> 64 : ℕ) : ℝ))) / (q64Scale : ℝ) +
          (((pLo * c) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) := by ring
    rw [hs1]; exact add_le_add hrec hterm

private def squarePow2Q64 : ℕ → ℕ → ℕ
  | 0, r => r
  | s + 1, r => squarePow2Q64 s ((r * r) >>> 64)

private lemma squarePow2Q64_sound : ∀ (s : ℕ) (r : ℕ) (y : ℝ),
    (r : ℝ) / (q64Scale : ℝ) ≤ y →
    (squarePow2Q64 s r : ℝ) / (q64Scale : ℝ) ≤ y ^ (2 ^ s)
  | 0, r, y, hy => by simpa [squarePow2Q64] using hy
  | s + 1, r, y, hy => by
    have hr_nn : 0 ≤ (r : ℝ) / (q64Scale : ℝ) := by positivity
    have hsq : (((r * r) >>> 64 : ℕ) : ℝ) / (q64Scale : ℝ) ≤ y ^ 2 :=
      (q64MulLb_le r r).trans (sq y ▸ mul_le_mul hy hy hr_nn (hr_nn.trans hy))
    rw [show y ^ (2 ^ (s + 1)) = (y ^ 2) ^ (2 ^ s) by rw [← pow_mul, pow_succ', mul_comm]]
    exact squarePow2Q64_sound s ((r * r) >>> 64) (y ^ 2) hsq

private def q64ExpLb (xQ64 : ℕ) : ℕ :=
  squarePow2Q64 4 (expTaylorLbLoop (xQ64 >>> 4) invFactLo13 q64Scale 0)

private lemma q64ExpLb_le {xQ64 : ℕ} {x : ℝ} (hx : (xQ64 : ℝ) / (q64Scale : ℝ) ≤ x) :
    (q64ExpLb xQ64 : ℝ) / (q64Scale : ℝ) ≤ Real.exp x := by
  set w : ℝ := ((xQ64 : ℝ) / (q64Scale : ℝ)) / 16
  have hw_nn : 0 ≤ w := by positivity
  have hz : (((xQ64 >>> 4 : ℕ) : ℝ) / (q64Scale : ℝ)) ≤ w := by
    dsimp only [w]
    rw [div_div, div_le_div_iff₀ q64Scale_pos (mul_pos q64Scale_pos (by norm_num))]
    have hsh : (xQ64 >>> 4) * 16 ≤ xQ64 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_mul_le_self xQ64 16
    have hcast : ((xQ64 >>> 4 : ℕ) : ℝ) * 16 ≤ (xQ64 : ℝ) := by exact_mod_cast hsh
    calc
      ((xQ64 >>> 4 : ℕ) : ℝ) * ((q64Scale : ℝ) * 16)
          = (((xQ64 >>> 4 : ℕ) : ℝ) * 16) * (q64Scale : ℝ) := by ring
      _ ≤ (xQ64 : ℝ) * (q64Scale : ℝ) := mul_le_mul_of_nonneg_right hcast q64Scale_pos.le
  have hloop := expTaylorLbLoop_sound hw_nn hz invFactLo13 0 q64Scale 0 invFactLo13_ok
    (by simp [div_self q64Scale_pos.ne'])
  simp only [Nat.cast_zero, sub_zero, Nat.zero_add] at hloop
  have hsum : ∑ m ∈ Finset.range invFactLo13.length, w ^ m / (m.factorial : ℝ) ≤ Real.exp w :=
    Real.sum_le_exp_of_nonneg hw_nn invFactLo13.length
  have hsq := squarePow2Q64_sound 4
    (expTaylorLbLoop (xQ64 >>> 4) invFactLo13 q64Scale 0) (Real.exp w) (hloop.trans hsum)
  have hexp16 : (Real.exp w) ^ (2 ^ 4) = Real.exp ((xQ64 : ℝ) / (q64Scale : ℝ)) := by
    rw [← Real.exp_natCast_mul]
    congr 1
    dsimp only [w]; push_cast; ring
  rw [hexp16] at hsq
  exact hsq.trans (Real.exp_le_exp.mpr hx)

/-! ## 3. Single-Pass Finite Verification Over `primesLt13000` -/

private def checkRobinStep (k' thetaLo' : ℕ) : Bool :=
  if 4 ≤ k' then
    decide (3 * q64Scale ≤ thetaLo') &&
      decide (thetaLo' < q64ExpLb ((13841 * thetaLo') / (10000 * k')))
  else true

private def checkRobinList (k thetaLo : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps =>
    let k' := k + 1
    let thetaLo' := thetaLo + q64LogNatLb p
    checkRobinStep k' thetaLo' && checkRobinList k' thetaLo' ps

private def checkRobinChunkLoop (k thetaLo : ℕ) : List ℕ → Bool × ℕ × ℕ
  | [] => (true, k, thetaLo)
  | p :: ps =>
    let k' := k + 1
    let thetaLo' := thetaLo + q64LogNatLb p
    if checkRobinStep k' thetaLo' then checkRobinChunkLoop k' thetaLo' ps else (false, 0, 0)

private def checkRobinChunks (k thetaLo : ℕ) : List (List ℕ) → Bool
  | [] => true
  | c :: cs =>
    let (ok, k', thetaLo') := checkRobinChunkLoop k thetaLo c
    ok && checkRobinChunks k' thetaLo' cs

private lemma robinChunks_ok : checkRobinChunks 0 0 primeChunks13000 = true := by decide

private lemma checkRobinChunkLoop_to_list :
    ∀ (c : List ℕ) (k thetaLo : ℕ) (rest : List ℕ),
      (checkRobinChunkLoop k thetaLo c).1 = true →
      checkRobinList (checkRobinChunkLoop k thetaLo c).2.1
        (checkRobinChunkLoop k thetaLo c).2.2 rest = true →
      checkRobinList k thetaLo (c ++ rest) = true
  | [], _, _, rest, _, hrest => by simpa [checkRobinChunkLoop] using hrest
  | p :: ps, k, thetaLo, rest, hc, hrest => by
    simp only [checkRobinChunkLoop] at hc hrest
    split_ifs at hc hrest with hstep
    simp only [checkRobinList, List.cons_append, Bool.and_eq_true]
    exact ⟨hstep, checkRobinChunkLoop_to_list ps (k + 1) (thetaLo + q64LogNatLb p) rest hc hrest⟩

private lemma checkRobinChunks_to_list :
    ∀ (cs : List (List ℕ)) (k thetaLo : ℕ),
      checkRobinChunks k thetaLo cs = true →
      checkRobinList k thetaLo cs.flatten = true
  | [], _, _, _ => by simp [checkRobinList]
  | c :: cs, k, thetaLo, h => by
    simp only [checkRobinChunks, Bool.and_eq_true] at h
    rw [List.flatten_cons]
    exact checkRobinChunkLoop_to_list c k thetaLo cs.flatten h.1
      (checkRobinChunks_to_list cs _ _ h.2)

private lemma robinList_ok : checkRobinList 0 0 primesLt13000 = true :=
  checkRobinChunks_to_list primeChunks13000 0 0 robinChunks_ok

private lemma checkRobinList_mem :
    ∀ (suff pref : List ℕ) (thetaLo : ℕ),
      checkRobinList pref.length thetaLo suff = true →
      (∀ q ∈ suff, 1 ≤ q) →
      (thetaLo : ℝ) / (q64Scale : ℝ) ≤ (pref.map (fun q : ℕ => Real.log (q : ℝ))).sum →
      ∀ p ∈ suff, ∃ pre2 suf2 : List ℕ,
        pref ++ suff = pre2 ++ (p :: suf2) ∧
        ∃ thetaLo' : ℕ,
          checkRobinStep (pre2 ++ [p]).length thetaLo' = true ∧
          (thetaLo' : ℝ) / (q64Scale : ℝ) ≤
            ((pre2 ++ [p]).map (fun q : ℕ => Real.log (q : ℝ))).sum
  | [], _, _, _, _, _, p, hp => by cases hp
  | q :: qs, pref, thetaLo, hchk, hq1, hth, p, hp => by
    simp only [checkRobinList, Bool.and_eq_true] at hchk
    have hq_ge1 : 1 ≤ q := hq1 q List.mem_cons_self
    have hth' : ((thetaLo + q64LogNatLb q : ℕ) : ℝ) / (q64Scale : ℝ) ≤
        ((pref ++ [q]).map (fun r : ℕ => Real.log (r : ℝ))).sum := by
      rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      push_cast; rw [add_div]
      exact add_le_add hth (q64LogNatLb_le hq_ge1)
    have hlen : (pref ++ [q]).length = pref.length + 1 := by simp
    rcases List.mem_cons.mp hp with rfl | hp_qs
    · refine ⟨pref, qs, rfl, thetaLo + q64LogNatLb p, ?_, hth'⟩
      rw [hlen]; exact hchk.1
    · have hrec := checkRobinList_mem qs (pref ++ [q]) (thetaLo + q64LogNatLb q)
        (hlen.symm ▸ hchk.2) (fun r hr => hq1 r (List.mem_cons_of_mem q hr)) hth' p hp_qs
      rcases hrec with ⟨pre2, suf2, heq, thetaLo', hst, hsum⟩
      rw [List.append_assoc, List.singleton_append] at heq
      exact ⟨pre2, suf2, heq, thetaLo', hst, hsum⟩

private lemma prefix_toFinset_eq_primesLE {pre suf : List ℕ} {p : ℕ}
    (hsplit : primesLt13000 = pre ++ (p :: suf)) :
    (pre ++ [p]).Nodup ∧ (pre ++ [p]).toFinset = Nat.primesLE p := by
  have hsplit' : primesLt13000 = (pre ++ [p]) ++ suf := by
    simpa [List.append_assoc] using hsplit
  have hnd : (pre ++ [p]).Nodup := by
    have hnd_all := primesLt13000_nodup
    rw [hsplit'] at hnd_all
    exact (List.nodup_append.mp hnd_all).1
  have hpw := primesLt13000_pairwise_lt
  rw [hsplit] at hpw
  rcases List.pairwise_append.mp hpw with ⟨_, hpw_cons, hcross⟩
  have hpw_suf := (List.pairwise_cons.mp hpw_cons).1
  refine ⟨hnd, ?_⟩
  ext q
  simp only [List.mem_toFinset, Nat.mem_primesLE]
  constructor
  · intro hq
    have hq_all : q ∈ primesLt13000 := by
      rw [hsplit']; exact List.mem_append_left suf hq
    have hq_pr := (mem_primesLt13000_iff.mp hq_all).2
    have hq_le : q ≤ p := by
      rcases List.mem_append.mp hq with hq_pre | hq_p
      · exact (hcross q hq_pre p List.mem_cons_self).le
      · simp only [List.mem_singleton] at hq_p; omega
    exact ⟨hq_le, hq_pr⟩
  · rintro ⟨hq_le, hq_pr⟩
    have hp_all : p ∈ primesLt13000 := by
      rw [hsplit]; exact List.mem_append_right pre List.mem_cons_self
    have hp_lt : p < 13000 := (mem_primesLt13000_iff.mp hp_all).1
    have hq_all : q ∈ primesLt13000 :=
      mem_primesLt13000_iff.mpr ⟨lt_of_le_of_lt hq_le hp_lt, hq_pr⟩
    rw [hsplit'] at hq_all
    rcases List.mem_append.mp hq_all with hq_pre | hq_suf
    · exact hq_pre
    · exact absurd (hpw_suf q hq_suf) (by omega)

private lemma primeCounting_seven : Nat.primeCounting 7 = 4 := by decide

/-- Pure-kernel finite verification of `π(p) < 1.3841 * θ(p) / log θ(p)` for all primes
`7 ≤ p < 13000`. -/
theorem robin_primeCounting_lt_of_lt_13000
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hp_lt : p < 13000) :
    (Nat.primeCounting p : ℝ) <
      (1.3841 : ℝ) * Chebyshev.theta (p : ℝ) / Real.log (Chebyshev.theta (p : ℝ)) := by
  have hp_mem : p ∈ primesLt13000 := mem_primesLt13000_iff.mpr ⟨hp_lt, hp⟩
  have hge1 : ∀ q ∈ primesLt13000, 1 ≤ q := fun q hq =>
    (mem_primesLt13000_iff.mp hq).2.one_le
  rcases checkRobinList_mem primesLt13000 [] 0 robinList_ok hge1 (by simp) p hp_mem with
    ⟨pre, suf, hsplit, thetaLo', hstep, hsum_le⟩
  rcases prefix_toFinset_eq_primesLE hsplit with ⟨hnd, hfin⟩
  set k' : ℕ := (pre ++ [p]).length
  have hk'_eq : k' = Nat.primeCounting p := by
    calc
      k' = (pre ++ [p]).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = (Nat.primesLE p).card := by rw [hfin]
      _ = Nat.primeCounting p := Nat.primesLE_card_eq_primeCounting p
  have hk'4 : 4 ≤ k' := by
    rw [hk'_eq, ← primeCounting_seven]
    exact Nat.monotone_primeCounting hp7
  have htheta_sum :
      ((pre ++ [p]).map (fun q : ℕ => Real.log (q : ℝ))).sum = Chebyshev.theta (p : ℝ) := by
    rw [← List.sum_toFinset _ hnd, hfin, ← Chebyshev.theta_eq_sum_primesLE_log p]
  simp only [checkRobinStep, hk'4, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hstep
  set T : ℝ := (thetaLo' : ℝ) / (q64Scale : ℝ)
  have h3_le_T : (3 : ℝ) ≤ T := by
    dsimp only [T]
    rw [le_div_iff₀ q64Scale_pos]
    exact_mod_cast hstep.1
  have hT_le_th : T ≤ Chebyshev.theta (p : ℝ) := htheta_sum ▸ hsum_le
  have hk'_pos : (0 : ℝ) < (k' : ℝ) := by exact_mod_cast (by omega : 0 < k')
  set xQ64 : ℕ := (13841 * thetaLo') / (10000 * k')
  set X : ℝ := (1.3841 : ℝ) * T / (k' : ℝ)
  have hxQ64_le : (xQ64 : ℝ) / (q64Scale : ℝ) ≤ X := by
    dsimp only [X, T]
    have hmul : xQ64 * (10000 * k') ≤ 13841 * thetaLo' :=
      Nat.div_mul_le_self (13841 * thetaLo') (10000 * k')
    have hcast : (xQ64 : ℝ) * (10000 * (k' : ℝ)) ≤ 13841 * (thetaLo' : ℝ) := by
      exact_mod_cast hmul
    have hden_pos : (0 : ℝ) < (10000 * (k' : ℝ)) * (q64Scale : ℝ) :=
      mul_pos (mul_pos (by norm_num) hk'_pos) q64Scale_pos
    have h1 : (xQ64 : ℝ) / (q64Scale : ℝ) ≤
        (13841 * (thetaLo' : ℝ)) / ((10000 * (k' : ℝ)) * (q64Scale : ℝ)) := by
      rw [div_le_div_iff₀ q64Scale_pos hden_pos]
      calc
        (xQ64 : ℝ) * ((10000 * (k' : ℝ)) * (q64Scale : ℝ))
            = ((xQ64 : ℝ) * (10000 * (k' : ℝ))) * (q64Scale : ℝ) := by ring
        _ ≤ (13841 * (thetaLo' : ℝ)) * (q64Scale : ℝ) :=
            mul_le_mul_of_nonneg_right hcast q64Scale_pos.le
    refine h1.trans_eq ?_
    field_simp [q64Scale_pos.ne', hk'_pos.ne']
    ring
  have hT_lt_exp : T < Real.exp X := by
    have hlt : T < (q64ExpLb xQ64 : ℝ) / (q64Scale : ℝ) := by
      dsimp only [T]
      exact div_lt_div_of_pos_right (by exact_mod_cast hstep.2) q64Scale_pos
    exact hlt.trans_le (q64ExpLb_le hxQ64_le)
  have hlogT_lt : Real.log T < X := by
    have h1 := Real.log_lt_log (by linarith : 0 < T) hT_lt_exp
    rwa [Real.log_exp] at h1
  have hexp1_lt_T : Real.exp 1 < T := lt_of_lt_of_le exp_one_lt_three h3_le_T
  have hlogT_pos : 0 < Real.log T := lt_trans zero_lt_one (one_lt_log_of_exp_one_lt hexp1_lt_T)
  have hk'_lt : (k' : ℝ) < (1.3841 : ℝ) * (T / Real.log T) := by
    have hmul : Real.log T * (k' : ℝ) < (1.3841 : ℝ) * T := (lt_div_iff₀ hk'_pos).mp hlogT_lt
    rw [← mul_div_assoc]
    exact (lt_div_iff₀ hlogT_pos).mpr (by linarith)
  have hmono : T / Real.log T ≤ Chebyshev.theta (p : ℝ) / Real.log (Chebyshev.theta (p : ℝ)) :=
    div_log_monoOn hexp1_lt_T.le (hexp1_lt_T.le.trans hT_le_th) hT_le_th
  rw [← hk'_eq, mul_div_assoc]
  exact lt_of_lt_of_le hk'_lt (mul_le_mul_of_nonneg_left hmono (by norm_num))

end BuchstabSwitching.External
