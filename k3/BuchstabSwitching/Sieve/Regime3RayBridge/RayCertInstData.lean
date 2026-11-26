import BuchstabSwitching.Sieve.Regime3RayBridge.RayCertInstLogExp
import Mathlib.Tactic

/-!
# Fixed-Point Integer Strip Evaluator & `L = 120` Certificate Data (`10^12` Scale)

Provides the computable `ℕ` evaluator (`evalStripJLb`, `evalStripAqUb`, `checkStripsChunk`),
the `L = 120` `(rLoNum, rHiNum)` table `stripsRData`, and kernel-verified `decide` proofs
for all `120` strips (zero `sorry`, zero axioms, zero `native_decide`).
-/

namespace BuchstabSwitching

section RayCertData

def rayRScale : ℕ := 1000000
def rayUDen : ℕ := 120000000000
def rayLogXLo : ℕ := 1381551055326000
def rayLogXHi : ℕ := 1381551121366200
def rayLLXLo : ℕ := 7230962097282
def rayLLXHi : ℕ := 7230962259345
def rayLogZLo : ℕ := 86346940957874
def rayH0Lo : ℕ := 1514236169719
def rayH0Hi : ℕ := 1516136089708
def rayCJHi : ℕ := 8030531202875
def rayUcLo : ℕ := 1320323061017
def rayENegGLo : ℕ := 561459483566
def rayOneMinusDv : ℕ := 999932938000

def rayAqLo : ℕ := (11 * rayLLXLo * scaleS) / (2 * rayLogXHi)
def rayAqHi : ℕ := hstarCeilDiv (11 * rayLLXHi * scaleS) (2 * rayLogXLo)

def stripsRData : List (ℕ × ℕ) :=
  [ (2950000, 2950000), (2950000, 2950000), (2950000, 2950000), (2950000, 2950000),
    (2950000, 2950000), (2950000, 2950000), (2950000, 2950000), (2950000, 2950000),
    (2950000, 2950000), (2950000, 2950000), (2950000, 2950000), (2950000, 2950000),
    (2950000, 2950000), (2950000, 2950000), (2950000, 2950000), (2950000, 2950000),
    (2950000, 2950000), (2950000, 2950000), (2950000, 2950000), (2936373, 2936374),
    (2919706, 2919707), (2903039, 2903040), (2886373, 2886374), (2869706, 2869707),
    (2853039, 2853040), (2836373, 2836374), (2819706, 2819707), (2803039, 2803040),
    (2786373, 2786374), (2769706, 2769707), (2753039, 2753040), (2736373, 2736374),
    (2719706, 2719707), (2703039, 2703040), (2686373, 2686374), (2669706, 2669707),
    (2653039, 2653040), (2636373, 2636374), (2619706, 2619707), (2603039, 2603040),
    (2586373, 2586374), (2569706, 2569707), (2553039, 2553040), (2536373, 2536374),
    (2519706, 2519707), (2503039, 2503040), (2486373, 2486374), (2469706, 2469707),
    (2453039, 2453040), (2436373, 2436374), (2419706, 2419707), (2403039, 2403040),
    (2386373, 2386374), (2369706, 2369707), (2353039, 2353040), (2336373, 2336374),
    (2319706, 2319707), (2303039, 2303040), (2286373, 2286374), (2269706, 2269707),
    (2253039, 2253040), (2236373, 2236374), (2219706, 2219707), (2203039, 2203040),
    (2186373, 2186374), (2169706, 2169707), (2153039, 2153040), (2136373, 2136374),
    (2119706, 2119707), (2103039, 2103040), (2086373, 2086374), (2069706, 2069707),
    (2053039, 2053040), (2036373, 2036374), (2019706, 2019707), (2003039, 2003040),
    (1986373, 1986374), (1969706, 1969707), (1953039, 1953040), (1936373, 1936374),
    (1919706, 1919707), (1903039, 1903040), (1886373, 1886374), (1869706, 1869707),
    (1853039, 1853040), (1836373, 1836374), (1819706, 1819707), (1803039, 1803040),
    (1786373, 1786374), (1769706, 1769707), (1753039, 1753040), (1736373, 1736374),
    (1719706, 1719707), (1703039, 1703040), (1686373, 1686374), (1669706, 1669707),
    (1653039, 1653040), (1636373, 1636374), (1619706, 1619707), (1603039, 1603040),
    (1586373, 1586374), (1569706, 1569707), (1553039, 1553040), (1536373, 1536374),
    (1519706, 1519707), (1503039, 1503040), (1486373, 1486374), (1469706, 1469707),
    (1453039, 1453040), (1436373, 1436374), (1419706, 1419707), (1403039, 1403040),
    (1386373, 1386374), (1369706, 1369707), (1353039, 1353040), (1336373, 1336374),
    (1319706, 1319707), (1303039, 1303040), (1286373, 1286374), (1269706, 1269707) ]

lemma stripsRData_length : stripsRData.length = 120 := by decide

def checkStripR (k : ℕ) (rLo rHi : ℕ) : Bool :=
  let uNum := 7500000000 + (k + 1) * 250000001
  let denTot := scaleS * rayUDen
  let rhsLo := 4 * scaleS * rayUDen - 8 * rayAqHi * rayUDen - 8 * uNum * scaleS
  let rhsHi := 4 * scaleS * rayUDen - 8 * rayAqLo * rayUDen - 8 * uNum * scaleS
  (rayRScale < rLo) && (rLo ≤ rHi) && (rHi ≤ 2950000) &&
    (rLo * denTot ≤ rhsLo * rayRScale) &&
    ((rHi == 2950000) || (rhsHi * rayRScale ≤ rHi * denTot)) &&
    (8 * rayAqHi * rayUDen + 8 * uNum * scaleS < 4 * scaleS * rayUDen)

def checkStripsChunk (c : ℕ) : Bool :=
  (List.range 10).all fun i =>
    let k := 10 * c + i
    let p := stripsRData.getD k (0, 0)
    checkStripR k p.1 p.2

private lemma checkStripsChunk_0 : checkStripsChunk 0 = true := by decide
private lemma checkStripsChunk_1 : checkStripsChunk 1 = true := by decide
private lemma checkStripsChunk_2 : checkStripsChunk 2 = true := by decide
private lemma checkStripsChunk_3 : checkStripsChunk 3 = true := by decide
private lemma checkStripsChunk_4 : checkStripsChunk 4 = true := by decide
private lemma checkStripsChunk_5 : checkStripsChunk 5 = true := by decide
private lemma checkStripsChunk_6 : checkStripsChunk 6 = true := by decide
private lemma checkStripsChunk_7 : checkStripsChunk 7 = true := by decide
private lemma checkStripsChunk_8 : checkStripsChunk 8 = true := by decide
private lemma checkStripsChunk_9 : checkStripsChunk 9 = true := by decide
private lemma checkStripsChunk_10 : checkStripsChunk 10 = true := by decide
private lemma checkStripsChunk_11 : checkStripsChunk 11 = true := by decide

lemma stripsRData_check_ok :
    ((List.range 120).all fun k =>
      let p := stripsRData.getD k (0, 0)
      checkStripR k p.1 p.2) = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hc : k / 10 < 12 := by omega
  have hi : k % 10 < 10 := by omega
  have hchunk : checkStripsChunk (k / 10) = true := by
    interval_cases c : k / 10
    · exact checkStripsChunk_0
    · exact checkStripsChunk_1
    · exact checkStripsChunk_2
    · exact checkStripsChunk_3
    · exact checkStripsChunk_4
    · exact checkStripsChunk_5
    · exact checkStripsChunk_6
    · exact checkStripsChunk_7
    · exact checkStripsChunk_8
    · exact checkStripsChunk_9
    · exact checkStripsChunk_10
    · exact checkStripsChunk_11
  have h1 := List.all_eq_true.mp hchunk (k % 10) (List.mem_range.mpr hi)
  simpa [Nat.div_add_mod] using h1

def tNum (rLo j : ℕ) : ℕ := 32 * rayRScale + j * (rLo - rayRScale)

def evalOnePrimePanelUb (rLo rHi j : ℕ) : ℕ :=
  let d1 := 32 * rayRScale
  let t0 := tNum rLo j
  let t1Hi := if j < 31 then tNum rLo (j + 1) else 32 * rHi
  let t1Lo := if j < 31 then tNum rLo (j + 1) else 32 * rLo
  let lHi := logRatioHi t1Hi t0
  let merrHi := hstarCeilDiv (6836000 * d1 * scaleS) (t1Lo * rayLogZLo)
  let m2964 := hstarCeilDiv (2964000 * d1 * scaleS) (t0 * rayLogZLo)
  let mertUb := lHi + merrHi + m2964 + 2
  let remHi := 32 * rHi - t0
  let remLo := 32 * rLo - t0
  let eRem := expNegUb (remLo * rayLogZLo) (4 * d1 * scaleS)
  let jremLin := hstarCeilDiv (rayH0Hi * remHi) (2 * d1)
  let jremC1 := hstarCeilDiv (rayH0Hi * 636) 1000 + hstarCeilDiv (rayCJHi * eRem) scaleS
  let jremUb := jremLin + hstarCeilDiv (jremC1 * scaleS) rayLogZLo
  hstarCeilDiv (mertUb * jremUb) scaleS

def aNum (rLo i : ℕ) : ℕ := 20 * rayRScale + i * (rLo - 2 * rayRScale)

def bNum (rLo a1 j : ℕ) : ℕ := 10 * a1 + j * (20 * rLo - 2 * a1)

def evalTwoPrimeRowLb (rLo i : ℕ) : ℕ :=
  let d2 := 20 * rayRScale
  let d3 := 200 * rayRScale
  let a0 := aNum rLo i
  let a1 := aNum rLo (i + 1)
  if 2 * a1 < 20 * rLo then
    let laLo := logRatioLo a1 a0
    let ea1 := hstarCeilDiv (2964000 * d2 * scaleS) (a1 * rayLogZLo)
    let ea2 := hstarCeilDiv (6836000 * d2 * scaleS) (a0 * rayLogZLo)
    let mlbA := if ea1 + ea2 ≤ laLo then laLo - (ea1 + ea2) else 0
    if mlbA == 0 then 0 else
      (List.range 10).foldl (fun acc j =>
        let b0 := bNum rLo a1 j
        let b1 := bNum rLo a1 (j + 1)
        let lbLo := logRatioLo b1 b0
        let eb1 := hstarCeilDiv (2964000 * d3 * scaleS) (b1 * rayLogZLo)
        let eb2 := hstarCeilDiv (6836000 * d3 * scaleS) (b0 * rayLogZLo)
        let mlbB := if eb1 + eb2 ≤ lbLo then lbLo - (eb1 + eb2) else 0
        let remT := 200 * rLo - 10 * a1 - b1
        if mlbB == 0 || remT == 0 then acc else
          let eRem2 := expNegUb (remT * rayLogZLo) (4 * d3 * scaleS)
          let jLin := (rayH0Lo * remT) / (2 * d3)
          let jErr := hstarCeilDiv (rayCJHi * eRem2) rayLogZLo
          let jLb := if jErr ≤ jLin then jLin - jErr else 0
          let pAb := (mlbA * mlbB) / scaleS
          acc + (pAb * jLb) / scaleS) 0
  else 0

def evalStripJLb (rLo rHi : ℕ) : ℕ :=
  let mainPos := (rayH0Lo * rLo) / (2 * rayRScale)
  let eMain := expNegUb (rLo * rayLogZLo) (4 * rayRScale * scaleS)
  let mainErr := hstarCeilDiv (rayCJHi * eMain) rayLogZLo
  let term1Hi := (List.range 32).foldl (fun acc j => acc + evalOnePrimePanelUb rLo rHi j) 0
  let term2Lo :=
    if 2 * rayRScale < rLo then
      (List.range 10).foldl (fun acc i => acc + evalTwoPrimeRowLb rLo i) 0
    else 0
  let totPos := mainPos + term2Lo
  let totNeg := mainErr + term1Hi
  if totNeg ≤ totPos then totPos - totNeg else 0

def evalStripAqUb (k : ℕ) : ℕ :=
  let (rLo, rHi) := stripsRData.getD k (0, 0)
  let jLb := evalStripJLb rLo rHi
  let v1 := (rayUcLo * rayENegGLo) / scaleS
  let v2 := (v1 * rayOneMinusDv) / scaleS
  let vjLb := (v2 * jLb) / scaleS
  let uk := 7500000000 + k * 250000001
  let uk1 := 7500000000 + (k + 1) * 250000001
  let lq := logRatioHi uk1 uk
  let qMert := hstarCeilDiv (9800000 * rayUDen * scaleS) (uk * rayLogXLo)
  let qSub := lq + qMert + 1 + (if k == 0 then 1 else 0)
  let numStrip := hstarCeilDiv ((scaleS + 1) * qSub) scaleS
  hstarCeilDiv (numStrip * scaleS) vjLb

def checkStripLogRatios (k : ℕ) : Bool :=
  let (rLo, rHi) := stripsRData.getD k (0, 0)
  let jLb := evalStripJLb rLo rHi
  let uk := 7500000000 + k * 250000001
  let uk1 := 7500000000 + (k + 1) * 250000001
  let okU := uk ≤ uk1 && uk1 ≤ 2 * uk
  let okT := (List.range 32).all fun j =>
    let t0 := tNum rLo j
    let t1Hi := if j < 31 then tNum rLo (j + 1) else 32 * rHi
    t0 ≤ t1Hi && t1Hi ≤ 2 * t0
  let okAB :=
    if 2 * rayRScale < rLo then
      (List.range 10).all fun i =>
        let a0 := aNum rLo i
        let a1 := aNum rLo (i + 1)
        a0 ≤ a1 && a1 ≤ 2 * a0 &&
          (if 2 * a1 < 20 * rLo then
            (List.range 10).all fun j =>
              let b0 := bNum rLo a1 j
              let b1 := bNum rLo a1 (j + 1)
              b0 ≤ b1 && b1 ≤ 2 * b0
          else true)
    else true
  (10 ≤ jLb) && okU && okT && okAB

def sumAqChunk (c : ℕ) : ℕ :=
  ((List.range 10).map fun i => evalStripAqUb (10 * c + i)).sum

def checkChunkLogRatios (c : ℕ) : Bool :=
  (List.range 10).all fun i => checkStripLogRatios (10 * c + i)

lemma checkChunkLogRatios_0 : checkChunkLogRatios 0 = true := by decide
lemma checkChunkLogRatios_1 : checkChunkLogRatios 1 = true := by decide
lemma checkChunkLogRatios_2 : checkChunkLogRatios 2 = true := by decide
lemma checkChunkLogRatios_3 : checkChunkLogRatios 3 = true := by decide
lemma checkChunkLogRatios_4 : checkChunkLogRatios 4 = true := by decide
lemma checkChunkLogRatios_5 : checkChunkLogRatios 5 = true := by decide
lemma checkChunkLogRatios_6 : checkChunkLogRatios 6 = true := by decide
lemma checkChunkLogRatios_7 : checkChunkLogRatios 7 = true := by decide
lemma checkChunkLogRatios_8 : checkChunkLogRatios 8 = true := by decide
lemma checkChunkLogRatios_9 : checkChunkLogRatios 9 = true := by decide
lemma checkChunkLogRatios_10 : checkChunkLogRatios 10 = true := by decide
lemma checkChunkLogRatios_11 : checkChunkLogRatios 11 = true := by decide

lemma sumAqChunk_0 : sumAqChunk 0 = 302573038027 := by decide
lemma sumAqChunk_1 : sumAqChunk 1 = 234692467790 := by decide
lemma sumAqChunk_2 : sumAqChunk 2 = 191778059976 := by decide
lemma sumAqChunk_3 : sumAqChunk 3 = 162564255562 := by decide
lemma sumAqChunk_4 : sumAqChunk 4 = 141722699575 := by decide
lemma sumAqChunk_5 : sumAqChunk 5 = 126402160766 := by decide
lemma sumAqChunk_6 : sumAqChunk 6 = 115003771477 := by decide
lemma sumAqChunk_7 : sumAqChunk 7 = 106609058623 := by decide
lemma sumAqChunk_8 : sumAqChunk 8 = 100697878839 := by decide
lemma sumAqChunk_9 : sumAqChunk 9 = 96966316268 := by decide
lemma sumAqChunk_10 : sumAqChunk 10 = 95341972284 := by decide
lemma sumAqChunk_11 : sumAqChunk 11 = 96031420564 := by decide

lemma checkAllLogRatios_ok :
    ∀ k : ℕ, k < 120 → checkStripLogRatios k = true := by
  intro k hk
  have hc : k / 10 < 12 := by omega
  have hi : k % 10 < 10 := by omega
  have hmem : k % 10 ∈ List.range 10 := List.mem_range.mpr hi
  have hchunk : checkChunkLogRatios (k / 10) = true := by
    interval_cases c : k / 10
    · exact checkChunkLogRatios_0
    · exact checkChunkLogRatios_1
    · exact checkChunkLogRatios_2
    · exact checkChunkLogRatios_3
    · exact checkChunkLogRatios_4
    · exact checkChunkLogRatios_5
    · exact checkChunkLogRatios_6
    · exact checkChunkLogRatios_7
    · exact checkChunkLogRatios_8
    · exact checkChunkLogRatios_9
    · exact checkChunkLogRatios_10
    · exact checkChunkLogRatios_11
  have h1 := List.all_eq_true.mp hchunk (k % 10) hmem
  simpa [Nat.div_add_mod] using h1

lemma sumAq_total_eq :
    ((List.range 120).map evalStripAqUb).sum = 1770383099751 := by
  have hsplit : ((List.range 120).map evalStripAqUb).sum =
      ((List.range 12).map sumAqChunk).sum := by
    have h12 : ∀ m : ℕ, ((List.range (10 * m)).map evalStripAqUb).sum =
        ((List.range m).map sumAqChunk).sum := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hrange : List.range (10 * (m + 1)) =
            List.range (10 * m) ++ (List.range 10).map (fun i => 10 * m + i) := by
          clear ih
          have h10 : ∀ d : ℕ, List.range (10 * m + d) =
              List.range (10 * m) ++ (List.range d).map (fun i => 10 * m + i) := by
            intro d
            induction d with
            | zero => simp
            | succ d ihd =>
              rw [show 10 * m + (d + 1) = (10 * m + d) + 1 by omega,
                List.range_succ, List.range_succ, List.map_append, List.map_singleton,
                ← List.append_assoc, ihd]
          simpa [Nat.mul_add] using h10 10
        rw [hrange, List.map_append, List.sum_append, ih]
        conv_rhs =>
          rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
            List.sum_singleton]
        rw [List.map_map]
        rfl
    exact h12 12
  rw [hsplit]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_nil, List.map_cons,
    List.sum_append, List.sum_nil, List.sum_cons, zero_add, add_zero]
  rw [sumAqChunk_0, sumAqChunk_1, sumAqChunk_2, sumAqChunk_3, sumAqChunk_4, sumAqChunk_5,
    sumAqChunk_6, sumAqChunk_7, sumAqChunk_8, sumAqChunk_9, sumAqChunk_10, sumAqChunk_11]

end RayCertData

end BuchstabSwitching
