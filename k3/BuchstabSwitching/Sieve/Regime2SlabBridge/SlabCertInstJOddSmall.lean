import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTable
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstExpProofs
import BuchstabSwitching.Sieve.OddSquarefreeBounds.JOddConvolution
import BuchstabSwitching.Sieve.OddSquarefreeBounds.ThreePowOmega
import Mathlib.Tactic

/-!
# Certified 11-Step Small-Argument Upper Bound `jOddStepMin` on `J_odd(X)`

Provides kernel-verified `SciNat` upper bounds `jOddStepUb M` at `M ∈ [1, 2, 4, 8, ..., 1024]`
via the complete table of all `415` odd squarefree integers `1 ≤ d ≤ 1024`, together with
`jOddStepMin` and `jOddStepMin_sound`.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

section OddSqf1024Table

/-- Complete list of `(d, primeFactors d)` for all `415` odd squarefree `1 ≤ d ≤ 1024`. -/
private def oddSqfChunk0 : List (ℕ × List ℕ) := [
  (1, []), (3, [3]), (5, [5]), (7, [7]), (11, [11]), (13, [13]),
  (15, [3, 5]), (17, [17]), (19, [19]), (21, [3, 7]), (23, [23]), (29, [29]),
  (31, [31]), (33, [3, 11]), (35, [5, 7]), (37, [37]), (39, [3, 13]), (41, [41]),
  (43, [43]), (47, [47]), (51, [3, 17]), (53, [53]), (55, [5, 11]), (57, [3, 19]),
  (59, [59]), (61, [61]), (65, [5, 13]), (67, [67]), (69, [3, 23]), (71, [71]),
  (73, [73]), (77, [7, 11]), (79, [79]), (83, [83]), (85, [5, 17]), (87, [3, 29]),
  (89, [89]), (91, [7, 13]), (93, [3, 31]), (95, [5, 19]), (97, [97]), (101, [101]),
  (103, [103]), (105, [3, 5, 7]), (107, [107]), (109, [109]), (111, [3, 37]), (113, [113]),
  (115, [5, 23]), (119, [7, 17])
]

private def oddSqfChunk1 : List (ℕ × List ℕ) := [
  (123, [3, 41]), (127, [127]), (129, [3, 43]), (131, [131]), (133, [7, 19]), (137, [137]),
  (139, [139]), (141, [3, 47]), (143, [11, 13]), (145, [5, 29]), (149, [149]), (151, [151]),
  (155, [5, 31]), (157, [157]), (159, [3, 53]), (161, [7, 23]), (163, [163]), (165, [3, 5, 11]),
  (167, [167]), (173, [173]), (177, [3, 59]), (179, [179]), (181, [181]), (183, [3, 61]),
  (185, [5, 37]), (187, [11, 17]), (191, [191]), (193, [193]), (195, [3, 5, 13]), (197, [197]),
  (199, [199]), (201, [3, 67]), (203, [7, 29]), (205, [5, 41]), (209, [11, 19]), (211, [211]),
  (213, [3, 71]), (215, [5, 43]), (217, [7, 31]), (219, [3, 73]), (221, [13, 17]), (223, [223]),
  (227, [227]), (229, [229]), (231, [3, 7, 11]), (233, [233]), (235, [5, 47]), (237, [3, 79]),
  (239, [239]), (241, [241])
]

private def oddSqfChunk2 : List (ℕ × List ℕ) := [
  (247, [13, 19]), (249, [3, 83]), (251, [251]), (253, [11, 23]), (255, [3, 5, 17]), (257, [257]),
  (259, [7, 37]), (263, [263]), (265, [5, 53]), (267, [3, 89]), (269, [269]), (271, [271]),
  (273, [3, 7, 13]), (277, [277]), (281, [281]), (283, [283]), (285, [3, 5, 19]), (287, [7, 41]),
  (291, [3, 97]), (293, [293]), (295, [5, 59]), (299, [13, 23]), (301, [7, 43]), (303, [3, 101]),
  (305, [5, 61]), (307, [307]), (309, [3, 103]), (311, [311]), (313, [313]), (317, [317]),
  (319, [11, 29]), (321, [3, 107]), (323, [17, 19]), (327, [3, 109]), (329, [7, 47]), (331, [331]),
  (335, [5, 67]), (337, [337]), (339, [3, 113]), (341, [11, 31]), (345, [3, 5, 23]), (347, [347]),
  (349, [349]), (353, [353]), (355, [5, 71]), (357, [3, 7, 17]), (359, [359]), (365, [5, 73]),
  (367, [367]), (371, [7, 53])
]

private def oddSqfChunk3 : List (ℕ × List ℕ) := [
  (373, [373]), (377, [13, 29]), (379, [379]), (381, [3, 127]), (383, [383]), (385, [5, 7, 11]),
  (389, [389]), (391, [17, 23]), (393, [3, 131]), (395, [5, 79]), (397, [397]), (399, [3, 7, 19]),
  (401, [401]), (403, [13, 31]), (407, [11, 37]), (409, [409]), (411, [3, 137]), (413, [7, 59]),
  (415, [5, 83]), (417, [3, 139]), (419, [419]), (421, [421]), (427, [7, 61]), (429, [3, 11, 13]),
  (431, [431]), (433, [433]), (435, [3, 5, 29]), (437, [19, 23]), (439, [439]), (443, [443]),
  (445, [5, 89]), (447, [3, 149]), (449, [449]), (451, [11, 41]), (453, [3, 151]), (455, [5, 7, 13]),
  (457, [457]), (461, [461]), (463, [463]), (465, [3, 5, 31]), (467, [467]), (469, [7, 67]),
  (471, [3, 157]), (473, [11, 43]), (479, [479]), (481, [13, 37]), (483, [3, 7, 23]), (485, [5, 97]),
  (487, [487]), (489, [3, 163])
]

private def oddSqfChunk4 : List (ℕ × List ℕ) := [
  (491, [491]), (493, [17, 29]), (497, [7, 71]), (499, [499]), (501, [3, 167]), (503, [503]),
  (505, [5, 101]), (509, [509]), (511, [7, 73]), (515, [5, 103]), (517, [11, 47]), (519, [3, 173]),
  (521, [521]), (523, [523]), (527, [17, 31]), (533, [13, 41]), (535, [5, 107]), (537, [3, 179]),
  (541, [541]), (543, [3, 181]), (545, [5, 109]), (547, [547]), (551, [19, 29]), (553, [7, 79]),
  (555, [3, 5, 37]), (557, [557]), (559, [13, 43]), (561, [3, 11, 17]), (563, [563]), (565, [5, 113]),
  (569, [569]), (571, [571]), (573, [3, 191]), (577, [577]), (579, [3, 193]), (581, [7, 83]),
  (583, [11, 53]), (587, [587]), (589, [19, 31]), (591, [3, 197]), (593, [593]), (595, [5, 7, 17]),
  (597, [3, 199]), (599, [599]), (601, [601]), (607, [607]), (609, [3, 7, 29]), (611, [13, 47]),
  (613, [613]), (615, [3, 5, 41])
]

private def oddSqfChunk5 : List (ℕ × List ℕ) := [
  (617, [617]), (619, [619]), (623, [7, 89]), (627, [3, 11, 19]), (629, [17, 37]), (631, [631]),
  (633, [3, 211]), (635, [5, 127]), (641, [641]), (643, [643]), (645, [3, 5, 43]), (647, [647]),
  (649, [11, 59]), (651, [3, 7, 31]), (653, [653]), (655, [5, 131]), (659, [659]), (661, [661]),
  (663, [3, 13, 17]), (665, [5, 7, 19]), (667, [23, 29]), (669, [3, 223]), (671, [11, 61]), (673, [673]),
  (677, [677]), (679, [7, 97]), (681, [3, 227]), (683, [683]), (685, [5, 137]), (687, [3, 229]),
  (689, [13, 53]), (691, [691]), (695, [5, 139]), (697, [17, 41]), (699, [3, 233]), (701, [701]),
  (703, [19, 37]), (705, [3, 5, 47]), (707, [7, 101]), (709, [709]), (713, [23, 31]), (715, [5, 11, 13]),
  (717, [3, 239]), (719, [719]), (721, [7, 103]), (723, [3, 241]), (727, [727]), (731, [17, 43]),
  (733, [733]), (737, [11, 67])
]

private def oddSqfChunk6 : List (ℕ × List ℕ) := [
  (739, [739]), (741, [3, 13, 19]), (743, [743]), (745, [5, 149]), (749, [7, 107]), (751, [751]),
  (753, [3, 251]), (755, [5, 151]), (757, [757]), (759, [3, 11, 23]), (761, [761]), (763, [7, 109]),
  (767, [13, 59]), (769, [769]), (771, [3, 257]), (773, [773]), (777, [3, 7, 37]), (779, [19, 41]),
  (781, [11, 71]), (785, [5, 157]), (787, [787]), (789, [3, 263]), (791, [7, 113]), (793, [13, 61]),
  (795, [3, 5, 53]), (797, [797]), (799, [17, 47]), (803, [11, 73]), (805, [5, 7, 23]), (807, [3, 269]),
  (809, [809]), (811, [811]), (813, [3, 271]), (815, [5, 163]), (817, [19, 43]), (821, [821]),
  (823, [823]), (827, [827]), (829, [829]), (831, [3, 277]), (835, [5, 167]), (839, [839]),
  (843, [3, 281]), (849, [3, 283]), (851, [23, 37]), (853, [853]), (857, [857]), (859, [859]),
  (861, [3, 7, 41]), (863, [863])
]

private def oddSqfChunk7 : List (ℕ × List ℕ) := [
  (865, [5, 173]), (869, [11, 79]), (871, [13, 67]), (877, [877]), (879, [3, 293]), (881, [881]),
  (883, [883]), (885, [3, 5, 59]), (887, [887]), (889, [7, 127]), (893, [19, 47]), (895, [5, 179]),
  (897, [3, 13, 23]), (899, [29, 31]), (901, [17, 53]), (903, [3, 7, 43]), (905, [5, 181]), (907, [907]),
  (911, [911]), (913, [11, 83]), (915, [3, 5, 61]), (917, [7, 131]), (919, [919]), (921, [3, 307]),
  (923, [13, 71]), (929, [929]), (933, [3, 311]), (935, [5, 11, 17]), (937, [937]), (939, [3, 313]),
  (941, [941]), (943, [23, 41]), (947, [947]), (949, [13, 73]), (951, [3, 317]), (953, [953]),
  (955, [5, 191]), (957, [3, 11, 29]), (959, [7, 137]), (965, [5, 193]), (967, [967]), (969, [3, 17, 19]),
  (971, [971]), (973, [7, 139]), (977, [977]), (979, [11, 89]), (983, [983]), (985, [5, 197]),
  (987, [3, 7, 47]), (989, [23, 43])
]

private def oddSqfChunk8 : List (ℕ × List ℕ) := [
  (991, [991]), (993, [3, 331]), (995, [5, 199]), (997, [997]), (1001, [7, 11, 13]), (1003, [17, 59]),
  (1005, [3, 5, 67]), (1007, [19, 53]), (1009, [1009]), (1011, [3, 337]), (1013, [1013]), (1015, [5, 7, 29]),
  (1019, [1019]), (1021, [1021]), (1023, [3, 11, 31])
]

def oddSqf1024Data : List (ℕ × List ℕ) :=
  oddSqfChunk0 ++ oddSqfChunk1 ++ oddSqfChunk2 ++ oddSqfChunk3 ++ oddSqfChunk4 ++
  oddSqfChunk5 ++ oddSqfChunk6 ++ oddSqfChunk7 ++ oddSqfChunk8

private def primesLt1024 : List ℕ := primesLt27000.filter (· < 1024)

private lemma mem_primesLt1024_iff {p : ℕ} : p ∈ primesLt1024 ↔ p < 1024 ∧ p.Prime := by
  simp only [primesLt1024, List.mem_filter, decide_eq_true_eq, mem_primesLt27000_iff]
  exact ⟨fun ⟨h, hlt⟩ => ⟨hlt, h.2⟩, fun ⟨hlt, hpr⟩ => ⟨⟨by omega, hpr⟩, hlt⟩⟩

private def checkChainLt : List ℕ → Bool
  | a :: b :: t => decide (a < b) && checkChainLt (b :: t)
  | _ => true

private lemma checkChainLt_sound : ∀ (xs : List ℕ), checkChainLt xs = true → xs.Pairwise (· < ·)
  | [] => fun _ => List.Pairwise.nil
  | [_] => fun _ => List.pairwise_singleton _ _
  | a :: b :: t => fun h => by
    simp only [checkChainLt, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := checkChainLt_sound (b :: t) h.2
    rw [List.pairwise_cons]
    refine ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.mp ih).1 x hxt)

private def checkSqfEntry (e : ℕ × List ℕ) : Bool :=
  decide (e.2.prod = e.1) && checkChainLt e.2 &&
  e.2.all (fun p => decide (3 ≤ p) && decide (p < 1024) && decide (p ∈ primesLt1024))

private lemma oddSqfChunk0_ok : oddSqfChunk0.all checkSqfEntry = true := by decide
private lemma oddSqfChunk1_ok : oddSqfChunk1.all checkSqfEntry = true := by decide
private lemma oddSqfChunk2_ok : oddSqfChunk2.all checkSqfEntry = true := by decide
private lemma oddSqfChunk3_ok : oddSqfChunk3.all checkSqfEntry = true := by decide
private lemma oddSqfChunk4_ok : oddSqfChunk4.all checkSqfEntry = true := by decide
private lemma oddSqfChunk5_ok : oddSqfChunk5.all checkSqfEntry = true := by decide
private lemma oddSqfChunk6_ok : oddSqfChunk6.all checkSqfEntry = true := by decide
private lemma oddSqfChunk7_ok : oddSqfChunk7.all checkSqfEntry = true := by decide
private lemma oddSqfChunk8_ok : oddSqfChunk8.all checkSqfEntry = true := by decide

private lemma oddSqfData_all_ok : oddSqf1024Data.all checkSqfEntry = true := by
  simp only [oddSqf1024Data, List.all_append, oddSqfChunk0_ok, oddSqfChunk1_ok, oddSqfChunk2_ok,
    oddSqfChunk3_ok, oddSqfChunk4_ok, oddSqfChunk5_ok, oddSqfChunk6_ok, oddSqfChunk7_ok,
    oddSqfChunk8_ok, Bool.and_self]

private lemma pairwise_step {xs ys : List ℕ} {a b : ℕ} (hab : a ≤ b)
    (hxs : xs.Pairwise (· < ·)) (hys : ys.Pairwise (· < ·))
    (hxa : xs.all (a ≤ ·) = true) (hxb : xs.all (· < b) = true)
    (hyb : ys.all (b ≤ ·) = true) :
    (xs ++ ys).Pairwise (· < ·) ∧ (xs ++ ys).all (a ≤ ·) = true := by
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_append]
    exact ⟨hxs, hys, fun x hx y hy => lt_of_lt_of_le
      (decide_eq_true_eq.mp (List.all_eq_true.mp hxb x hx))
      (decide_eq_true_eq.mp (List.all_eq_true.mp hyb y hy))⟩
  · rw [List.all_append, hxa, Bool.true_and, List.all_eq_true]
    intro y hy
    exact decide_eq_true (hab.trans (decide_eq_true_eq.mp (List.all_eq_true.mp hyb y hy)))

private lemma fst_lt_0 : checkChainLt (oddSqfChunk0.map Prod.fst) = true := by decide
private lemma fst_lt_1 : checkChainLt (oddSqfChunk1.map Prod.fst) = true := by decide
private lemma fst_lt_2 : checkChainLt (oddSqfChunk2.map Prod.fst) = true := by decide
private lemma fst_lt_3 : checkChainLt (oddSqfChunk3.map Prod.fst) = true := by decide
private lemma fst_lt_4 : checkChainLt (oddSqfChunk4.map Prod.fst) = true := by decide
private lemma fst_lt_5 : checkChainLt (oddSqfChunk5.map Prod.fst) = true := by decide
private lemma fst_lt_6 : checkChainLt (oddSqfChunk6.map Prod.fst) = true := by decide
private lemma fst_lt_7 : checkChainLt (oddSqfChunk7.map Prod.fst) = true := by decide
private lemma fst_lt_8 : checkChainLt (oddSqfChunk8.map Prod.fst) = true := by decide

private lemma bnd_0l : (oddSqfChunk0.map Prod.fst).all (0 ≤ ·) = true := by decide
private lemma bnd_0u : (oddSqfChunk0.map Prod.fst).all (· < 120) = true := by decide
private lemma bnd_1l : (oddSqfChunk1.map Prod.fst).all (120 ≤ ·) = true := by decide
private lemma bnd_1u : (oddSqfChunk1.map Prod.fst).all (· < 245) = true := by decide
private lemma bnd_2l : (oddSqfChunk2.map Prod.fst).all (245 ≤ ·) = true := by decide
private lemma bnd_2u : (oddSqfChunk2.map Prod.fst).all (· < 372) = true := by decide
private lemma bnd_3l : (oddSqfChunk3.map Prod.fst).all (372 ≤ ·) = true := by decide
private lemma bnd_3u : (oddSqfChunk3.map Prod.fst).all (· < 490) = true := by decide
private lemma bnd_4l : (oddSqfChunk4.map Prod.fst).all (490 ≤ ·) = true := by decide
private lemma bnd_4u : (oddSqfChunk4.map Prod.fst).all (· < 616) = true := by decide
private lemma bnd_5l : (oddSqfChunk5.map Prod.fst).all (616 ≤ ·) = true := by decide
private lemma bnd_5u : (oddSqfChunk5.map Prod.fst).all (· < 738) = true := by decide
private lemma bnd_6l : (oddSqfChunk6.map Prod.fst).all (738 ≤ ·) = true := by decide
private lemma bnd_6u : (oddSqfChunk6.map Prod.fst).all (· < 864) = true := by decide
private lemma bnd_7l : (oddSqfChunk7.map Prod.fst).all (864 ≤ ·) = true := by decide
private lemma bnd_7u : (oddSqfChunk7.map Prod.fst).all (· < 990) = true := by decide
private lemma bnd_8l : (oddSqfChunk8.map Prod.fst).all (990 ≤ ·) = true := by decide

private lemma oddSqfData_fst_pairwise_lt : (oddSqf1024Data.map Prod.fst).Pairwise (· < ·) := by
  have p78 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_7) (checkChainLt_sound _ fst_lt_8) bnd_7l bnd_7u bnd_8l
  have p68 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_6) p78.1 bnd_6l bnd_6u p78.2
  have p58 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_5) p68.1 bnd_5l bnd_5u p68.2
  have p48 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_4) p58.1 bnd_4l bnd_4u p58.2
  have p38 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_3) p48.1 bnd_3l bnd_3u p48.2
  have p28 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_2) p38.1 bnd_2l bnd_2u p38.2
  have p18 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_1) p28.1 bnd_1l bnd_1u p28.2
  have p08 := pairwise_step (by norm_num) (checkChainLt_sound _ fst_lt_0) p18.1 bnd_0l bnd_0u p18.2
  simpa [oddSqf1024Data, List.map_append, List.append_assoc] using p08.1

private def smallSqPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

private def covHalf (lo n : ℕ) (ch : List (ℕ × List ℕ)) : Bool :=
  (List.range n).all fun j =>
    let d := lo + 2 * j
    ch.any (fun e => e.1 == d) || smallSqPrimes.any (fun p => d % (p * p) == 0)

private lemma covH0a : covHalf 1 30 oddSqfChunk0 = true := by decide
private lemma covH0b : covHalf 61 30 oddSqfChunk0 = true := by decide
private lemma covH1a : covHalf 121 31 oddSqfChunk1 = true := by decide
private lemma covH1b : covHalf 183 31 oddSqfChunk1 = true := by decide
private lemma covH2a : covHalf 245 32 oddSqfChunk2 = true := by decide
private lemma covH2b : covHalf 309 32 oddSqfChunk2 = true := by decide
private lemma covH3a : covHalf 373 29 oddSqfChunk3 = true := by decide
private lemma covH3b : covHalf 431 30 oddSqfChunk3 = true := by decide
private lemma covH4a : covHalf 491 31 oddSqfChunk4 = true := by decide
private lemma covH4b : covHalf 553 32 oddSqfChunk4 = true := by decide
private lemma covH5a : covHalf 617 30 oddSqfChunk5 = true := by decide
private lemma covH5b : covHalf 677 31 oddSqfChunk5 = true := by decide
private lemma covH6a : covHalf 739 31 oddSqfChunk6 = true := by decide
private lemma covH6b : covHalf 801 32 oddSqfChunk6 = true := by decide
private lemma covH7a : covHalf 865 31 oddSqfChunk7 = true := by decide
private lemma covH7b : covHalf 927 32 oddSqfChunk7 = true := by decide
private lemma covH8  : covHalf 991 17 oddSqfChunk8 = true := by decide

private lemma smallSqPrimes_ge3 : ∀ p ∈ smallSqPrimes, 3 ≤ p := by
  intro p hp; simp only [smallSqPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp; omega

private lemma mem_chunk_of_covHalf {lo n d : ℕ} {ch : List (ℕ × List ℕ)}
    (hcov : covHalf lo n ch = true) (hsub : ∀ e ∈ ch, e ∈ oddSqf1024Data)
    (hge : lo ≤ d) (hlt : d < lo + 2 * n) (hodd_par : (d - lo) % 2 = 0)
    (hsqf : Squarefree d) : d ∈ oddSqf1024Data.map Prod.fst := by
  set j : ℕ := (d - lo) / 2
  have hj : j < n := by omega
  have hd_eq : lo + 2 * j = d := by omega
  have hj_ok := List.all_eq_true.mp hcov j (List.mem_range.mpr hj)
  dsimp only at hj_ok; rw [hd_eq] at hj_ok
  rcases Bool.or_eq_true _ _ |>.mp hj_ok with hmem | hdiv
  · rcases List.any_eq_true.mp hmem with ⟨e, he, hed⟩
    exact List.mem_map.mpr ⟨e, hsub e he, beq_iff_eq.mp hed⟩
  · rcases List.any_eq_true.mp hdiv with ⟨p, hp_mem, hp_mod⟩
    have hdvd : p * p ∣ d := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hp_mod)
    have hunit := Nat.isUnit_iff.mp (hsqf p hdvd)
    have hp3 := smallSqPrimes_ge3 p hp_mem
    omega

private lemma odd_sqf_mem_data {d : ℕ} (hd1 : 1 ≤ d) (hd1024 : d ≤ 1024)
    (hodd : Odd d) (hsqf : Squarefree d) : d ∈ oddSqf1024Data.map Prod.fst := by
  have hd_mod : d % 2 = 1 := Nat.odd_iff.mp hodd
  have hsub0 : ∀ e ∈ oddSqfChunk0, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub1 : ∀ e ∈ oddSqfChunk1, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub2 : ∀ e ∈ oddSqfChunk2, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub3 : ∀ e ∈ oddSqfChunk3, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub4 : ∀ e ∈ oddSqfChunk4, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub5 : ∀ e ∈ oddSqfChunk5, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub6 : ∀ e ∈ oddSqfChunk6, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub7 : ∀ e ∈ oddSqfChunk7, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  have hsub8 : ∀ e ∈ oddSqfChunk8, e ∈ oddSqf1024Data := by intro e he; simp [oddSqf1024Data, he]
  by_cases h0a : d < 61
  · exact mem_chunk_of_covHalf covH0a hsub0 (by omega) h0a (by omega) hsqf
  · by_cases h0b : d < 121
    · exact mem_chunk_of_covHalf covH0b hsub0 (by omega) h0b (by omega) hsqf
    · by_cases h1a : d < 183
      · exact mem_chunk_of_covHalf covH1a hsub1 (by omega) h1a (by omega) hsqf
      · by_cases h1b : d < 245
        · exact mem_chunk_of_covHalf covH1b hsub1 (by omega) h1b (by omega) hsqf
        · by_cases h2a : d < 309
          · exact mem_chunk_of_covHalf covH2a hsub2 (by omega) h2a (by omega) hsqf
          · by_cases h2b : d < 373
            · exact mem_chunk_of_covHalf covH2b hsub2 (by omega) h2b (by omega) hsqf
            · by_cases h3a : d < 431
              · exact mem_chunk_of_covHalf covH3a hsub3 (by omega) h3a (by omega) hsqf
              · by_cases h3b : d < 491
                · exact mem_chunk_of_covHalf covH3b hsub3 (by omega) h3b (by omega) hsqf
                · by_cases h4a : d < 553
                  · exact mem_chunk_of_covHalf covH4a hsub4 (by omega) h4a (by omega) hsqf
                  · by_cases h4b : d < 617
                    · exact mem_chunk_of_covHalf covH4b hsub4 (by omega) h4b (by omega) hsqf
                    · by_cases h5a : d < 677
                      · exact mem_chunk_of_covHalf covH5a hsub5 (by omega) h5a (by omega) hsqf
                      · by_cases h5b : d < 739
                        · exact mem_chunk_of_covHalf covH5b hsub5 (by omega) h5b (by omega) hsqf
                        · by_cases h6a : d < 801
                          · exact mem_chunk_of_covHalf covH6a hsub6 (by omega) h6a (by omega) hsqf
                          · by_cases h6b : d < 865
                            · exact mem_chunk_of_covHalf covH6b hsub6 (by omega) h6b (by omega) hsqf
                            · by_cases h7a : d < 927
                              · exact mem_chunk_of_covHalf covH7a hsub7 (by omega) h7a (by omega) hsqf
                              · by_cases h7b : d < 991
                                · exact mem_chunk_of_covHalf covH7b hsub7 (by omega) h7b (by omega) hsqf
                                · exact mem_chunk_of_covHalf covH8 hsub8 (by omega) (by omega) (by omega) hsqf

end OddSqf1024Table

section JOddStaircase

/-- Staircase exponents `k ∈ {0, 1, ..., 10}` (`M = 2^k ∈ {1, 2, 4, ..., 1024}`). -/
def jOddStepK : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- Single odd-squarefree term Q64 upper bound `⌈2^64 / ∏_{p ∈ ps} (p - 2)⌉`. -/
def jOddTermUb64 (ps : List ℕ) : ℕ :=
  let den := (ps.map (· - 2)).prod
  (q64Scale + den - 1) / den

/-- Certified Q64 `Dyadic` sum `∑_{d ≤ M, d odd sqf} ⌈2^64 / ∏(p - 2)⌉ / 2^64`. -/
def jOddStepUb (M : ℕ) : Dyadic :=
  Dyadic.ofQ64 (((oddSqf1024Data.filter (·.1 ≤ M)).map (fun e => jOddTermUb64 e.2)).sum)

private lemma prod_map_inv_sub_two : ∀ (ps : List ℕ), (∀ p ∈ ps, 3 ≤ p) →
    (ps.map (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 2))).prod = 1 / (((ps.map (· - 2)).prod : ℕ) : ℝ)
  | [] => fun _ => by simp
  | p :: tl => fun hp => by
    have hp3 := hp p List.mem_cons_self
    have ih := prod_map_inv_sub_two tl fun q hq => hp q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.prod_cons]
    have htl : (((tl.map (· - 2)).prod : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (List.prod_pos fun x hx => by
        rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩
        have := hp q (List.mem_cons_of_mem _ hq); omega).ne'
    have hp0 : (p : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    rw [ih, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ p)]
    push_cast; field_simp

private lemma entry_term_le {d : ℕ} {ps : List ℕ} (h : checkSqfEntry (d, ps) = true) :
    ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2)) ≤ (jOddTermUb64 ps : ℝ) / (q64Scale : ℝ) := by
  simp only [checkSqfEntry, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hprod, hlt⟩, hps⟩
  have hnd : ps.Nodup := (checkChainLt_sound ps hlt).imp fun h => h.ne
  have hpr : ∀ p ∈ ps, 3 ≤ p ∧ p.Prime := fun p hp =>
    let hp' := hps p hp; ⟨hp'.1.1, (mem_primesLt1024_iff.mp hp'.2).2⟩
  have hd_eq : ∏ p ∈ ps.toFinset, p = d := by
    rw [List.prod_toFinset (fun x : ℕ => x) hnd]
    exact (congrArg List.prod (List.map_id' ps)).trans hprod
  have hpf : d.primeFactors = ps.toFinset := by
    rw [← hd_eq]; exact BuchstabSwitching.primeFactors_prod_of_prime fun p hp => (hpr p (List.mem_toFinset.mp hp)).2
  have hprod_fin : ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 2) =
      (ps.map (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 2))).prod := by
    rw [hpf, ← List.prod_toFinset (fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 2)) hnd]
  rw [hprod_fin, prod_map_inv_sub_two ps fun p hp => (hpr p hp).1]
  set den := (ps.map (· - 2)).prod
  have hden_pos : 0 < den := List.prod_pos fun x hx => by
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩; have := (hpr p hp).1; omega
  rw [div_le_div_iff₀ (by exact_mod_cast hden_pos) q64Scale_pos, one_mul]
  have hmul : q64Scale ≤ jOddTermUb64 ps * den := by
    unfold jOddTermUb64
    change q64Scale ≤ ((q64Scale + den - 1) / den) * den
    have hd := Nat.div_add_mod (q64Scale + den - 1) den
    have hm := Nat.mod_lt (q64Scale + den - 1) hden_pos
    rw [Nat.mul_comm] at hd; omega
  exact_mod_cast hmul

private lemma sum_toFinset_le_sum_ub : ∀ (L : List (ℕ × List ℕ)),
    (L.map Prod.fst).Nodup → (∀ e ∈ L, checkSqfEntry e = true) →
    ∑ d ∈ (L.map Prod.fst).toFinset, ∏ p ∈ d.primeFactors, ((1 : ℝ) / ((p : ℝ) - 2)) ≤
      ((L.map (fun e => jOddTermUb64 e.2)).sum : ℝ) / (q64Scale : ℝ)
  | [] => fun _ _ => by simp
  | (d, ps) :: tl => fun hnd he => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnot : d ∉ (tl.map Prod.fst).toFinset := by simpa [List.mem_toFinset] using hnd.1
    have ih := sum_toFinset_le_sum_ub tl hnd.2 fun x hx => he x (List.mem_cons_of_mem _ hx)
    have hterm := entry_term_le (he (d, ps) List.mem_cons_self)
    simp only [List.map_cons, List.toFinset_cons, Finset.sum_insert hnot, List.sum_cons, Nat.cast_add]
    rw [add_div]; exact add_le_add hterm ih

theorem jOddStepUb_sound {M : ℕ} (hM : M ≤ 1024) {X : ℝ} (hXM : X ≤ (M : ℝ)) :
    BuchstabSwitching.J_odd X ≤ (jOddStepUb M).toReal := by
  unfold BuchstabSwitching.J_odd jOddStepUb
  rw [Dyadic.ofQ64_toReal]
  set S := (Finset.Icc 1 (Nat.floor X)).filter (fun d => Odd d ∧ Squarefree d)
  set L := oddSqf1024Data.filter (·.1 ≤ M)
  have hsub : S ⊆ (L.map Prod.fst).toFinset := by
    intro d hd
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hd
    have hdM : d ≤ M := by
      have hfl : Nat.floor X ≤ M := by
        by_cases hX0 : 0 ≤ X
        · exact_mod_cast (Nat.floor_le hX0).trans hXM
        · rw [Nat.floor_of_nonpos (le_of_not_ge hX0)]; exact Nat.zero_le M
      exact hd.1.2.trans hfl
    have hmem := odd_sqf_mem_data hd.1.1 (hdM.trans hM) hd.2.1 hd.2.2
    rcases List.mem_map.mp hmem with ⟨e, he, rfl⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true hdM⟩, rfl⟩)
  have hnn : ∀ d ∈ (L.map Prod.fst).toFinset, 0 ≤ ∏ p ∈ d.primeFactors, ((1 : ℝ) / ((p : ℝ) - 2)) :=
    fun d _ => Finset.prod_nonneg fun p hp => by
      by_cases hp2 : 2 < p
      · have hp_r : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        positivity
      · have hle2 := (Nat.prime_of_mem_primeFactors hp).two_le
        have : p = 2 := by omega
        subst this; norm_num
  have hnd : (L.map Prod.fst).Nodup := by
    have hsub_nd : ∀ {α : Type} (p : α → Bool) (xs : List α) (f : α → ℕ),
        (xs.map f).Pairwise (· < ·) → ((xs.filter p).map f).Nodup := by
      intro α p xs f hp
      induction xs with
      | nil => simp
      | cons a t ih =>
        simp only [List.map_cons, List.pairwise_cons] at hp
        rw [List.filter_cons]; split_ifs
        · simp only [List.map_cons, List.nodup_cons]; refine ⟨fun hm => ?_, ih hp.2⟩
          rcases List.mem_map.mp hm with ⟨x, hx, hfx⟩
          exact (hp.1 _ (List.mem_map_of_mem (List.mem_of_mem_filter hx))).ne hfx.symm
        · exact ih hp.2
    exact hsub_nd _ oddSqf1024Data Prod.fst oddSqfData_fst_pairwise_lt
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ => hnn d hd).trans ?_
  simpa using sum_toFinset_le_sum_ub L hnd fun e he =>
    List.all_eq_true.mp oddSqfData_all_ok e (List.mem_of_mem_filter he)

private def minDyadic (a b : Dyadic) : Dyadic := if a.ble b then a else b

private lemma minDyadic_sound {a b : Dyadic} {x : ℝ} (ha : x ≤ a.toReal) (hb : x ≤ b.toReal) :
    x ≤ (minDyadic a b).toReal := by unfold minDyadic; split_ifs; exacts [ha, hb]

private lemma ln2Lo64_nat_ok : ln2Lo64 * 10 ^ 15 ≤ 693147180559945 * q64Scale := by decide

private lemma pow2_log_lb (consts : External.CertifiedConstants) (k : ℕ) :
    (Dyadic.ofQ64 (k * ln2Lo64)).toReal ≤ Real.log ((2 ^ k : ℕ) : ℝ) := by
  have hln2 : (ln2Lo64 : ℝ) / (q64Scale : ℝ) ≤ Real.log 2 := by
    have h1 : (ln2Lo64 : ℝ) / (q64Scale : ℝ) ≤ (0.693147180559945 : ℝ) := by
      rw [show (0.693147180559945 : ℝ) = (693147180559945 : ℝ) / (10 ^ 15 : ℝ) by norm_num,
        div_le_div_iff₀ q64Scale_pos (by norm_num)]
      exact_mod_cast ln2Lo64_nat_ok
    exact h1.trans consts.ln2_bounds.1
  rw [Dyadic.ofQ64_toReal, Nat.cast_mul, mul_div_assoc, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  exact mul_le_mul_of_nonneg_left hln2 (Nat.cast_nonneg k)

/-- Precomputed `(2^k, lmLo, stepUb)` table for the 11 staircase cutoffs `2^k ∈ {1, ..., 1024}`. -/
def jOddStepTable : List (ℕ × Dyadic × Dyadic) :=
  jOddStepK.map fun k => (2 ^ k, Dyadic.ofQ64 (k * ln2Lo64), jOddStepUb (2 ^ k))

/-- Literal-folded copy of `jOddStepTable` avoiding repeated 415-entry filter/div in the kernel. -/
def jOddStepTableFast : List (ℕ × Dyadic × Dyadic) := [
  (1, Dyadic.ofQ64 0, Dyadic.ofQ64 18446744073709551616),
  (2, Dyadic.ofQ64 12786308645202649952, Dyadic.ofQ64 18446744073709551616),
  (4, Dyadic.ofQ64 25572617290405299904, Dyadic.ofQ64 36893488147419103232),
  (8, Dyadic.ofQ64 38358925935607949856, Dyadic.ofQ64 46731751653397530762),
  (16, Dyadic.ofQ64 51145234580810599808, Dyadic.ofQ64 56607281309019815972),
  (32, Dyadic.ofQ64 63931543226013249760, Dyadic.ofQ64 64809239405744627418),
  (64, Dyadic.ofQ64 76717851871215899712, Dyadic.ofQ64 75621611716796046550),
  (128, Dyadic.ofQ64 89504160516418549664, Dyadic.ofQ64 85379149797613331761),
  (256, Dyadic.ofQ64 102290469161621199616, Dyadic.ofQ64 95395656791707058146),
  (512, Dyadic.ofQ64 115076777806823849568, Dyadic.ofQ64 104989327878886119960),
  (1024, Dyadic.ofQ64 127863086452026499520, Dyadic.ofQ64 114545877051222834619)
]

private def chunkStepSum (L : List (ℕ × List ℕ)) (M : ℕ) : ℕ :=
  ((L.filter (·.1 ≤ M)).map (fun e => jOddTermUb64 e.2)).sum

private lemma jOddStepUb_eq_chunks (M : ℕ) :
    jOddStepUb M = Dyadic.ofQ64 (chunkStepSum oddSqfChunk0 M + chunkStepSum oddSqfChunk1 M +
      chunkStepSum oddSqfChunk2 M + chunkStepSum oddSqfChunk3 M + chunkStepSum oddSqfChunk4 M +
      chunkStepSum oddSqfChunk5 M + chunkStepSum oddSqfChunk6 M + chunkStepSum oddSqfChunk7 M +
      chunkStepSum oddSqfChunk8 M) := by
  simp only [jOddStepUb, chunkStepSum, oddSqf1024Data, List.filter_append, List.map_append,
    List.sum_append, Nat.add_assoc]

set_option maxRecDepth 200000 in
private lemma jOddStepTableFast_eq : jOddStepTableFast = jOddStepTable := by
  simp only [jOddStepTable, jOddStepUb_eq_chunks]; decide

private lemma jOddStepK_ok : jOddStepK.all (fun k => decide (2 ^ k ≤ 1024)) = true := by decide

/-- Staircase minimum of `jOddStepUb (2^k)` over the first matching `logHi ≤ lmLo(2^k)` and `asymUb`. -/
def jOddStepMin (logHi asymUb : Dyadic) : Dyadic :=
  let rec go : List (ℕ × Dyadic × Dyadic) → Dyadic
    | [] => asymUb
    | (_, lmLo, stepUb) :: rest => if logHi.ble lmLo then minDyadic stepUb asymUb else go rest
  go jOddStepTableFast

theorem jOddStepMin_sound (consts : External.CertifiedConstants) {logHi asymUb : Dyadic} {X : ℝ}
    (hX1 : 1 ≤ X) (hhi : Real.log X ≤ logHi.toReal) (hasym : BuchstabSwitching.J_odd X ≤ asymUb.toReal) :
    BuchstabSwitching.J_odd X ≤ (jOddStepMin logHi asymUb).toReal := by
  have hXpos : 0 < X := by linarith
  have hgo : ∀ (L : List ℕ), (∀ k ∈ L, 2 ^ k ≤ 1024) →
      BuchstabSwitching.J_odd X ≤
        (jOddStepMin.go logHi asymUb
          (L.map fun k => (2 ^ k, Dyadic.ofQ64 (k * ln2Lo64), jOddStepUb (2 ^ k)))).toReal := by
    intro L hL; induction L with
    | nil => simpa [jOddStepMin.go] using hasym
    | cons k rest ih =>
      have hk := hL k List.mem_cons_self
      simp only [List.map_cons, jOddStepMin.go]
      split_ifs with hble
      · have hlogM : Real.log X ≤ Real.log ((2 ^ k : ℕ) : ℝ) :=
          hhi.trans ((Dyadic.ble_sound hble).trans (pow2_log_lb consts k))
        have hXM : X ≤ ((2 ^ k : ℕ) : ℝ) := by
          have hMp : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast (Nat.two_pow_pos k)
          rwa [← Real.exp_log hXpos, ← Real.exp_log hMp, Real.exp_le_exp]
        exact minDyadic_sound (jOddStepUb_sound hk hXM) hasym
      · exact ih fun m hm => hL m (List.mem_cons_of_mem _ hm)
  unfold jOddStepMin; rw [jOddStepTableFast_eq]; unfold jOddStepTable
  exact hgo jOddStepK fun k hk => decide_eq_true_eq.mp (List.all_eq_true.mp jOddStepK_ok k hk)

end JOddStaircase

end

end BuchstabSwitching.SieveInst
