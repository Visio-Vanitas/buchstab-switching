import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstDefs
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstPrimeTable
import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstSound2abLower
import Mathlib.Tactic

set_option maxRecDepth 200000

/-!
# Fast Precomputed Prime-Chunk Tables & Evaluators for Regime `2c`

Provides `oddPrimesLt27000`, `smallOddPrimes2c`, chunk-summarized exact evaluators
(`fastExactMertens2c`, `fastV2LbExact2c`, `fastV2UbExact2c`, `fastOddPrimesList2c`), and their
soundness theorems so `by decide` in Regime `2c` avoids re-folding all `2,961` primes `< 27000`.
-/

namespace BuchstabSwitching.SieveInst

noncomputable section

private abbrev sn (m e : ℕ) : SciNat := ⟨m, e⟩

section OddPrimesSplit27000

/-- Exact sorted list of odd primes `< 27000` (`2,960` primes). -/
def oddPrimesLt27000 : List ℕ := primesLt27000.filter (3 ≤ ·)

lemma oddPrimesLt27000_pairwise_lt : oddPrimesLt27000.Pairwise (· < ·) :=
  primesLt27000_pairwise_lt.filter _

lemma oddPrimesLt27000_nodup : oddPrimesLt27000.Nodup :=
  pairwise_lt_nodup oddPrimesLt27000_pairwise_lt

lemma mem_oddPrimesLt27000_iff {p : ℕ} :
    p ∈ oddPrimesLt27000 ↔ 3 ≤ p ∧ p < 27000 ∧ p.Prime := by
  simp only [oddPrimesLt27000, List.mem_filter, decide_eq_true_eq, mem_primesLt27000_iff]; tauto

lemma oddPrimesLt27000_split_props {a z bLast : ℕ}
    (ha : a < oddPrimesLt27000.length) (hbz : bLast ≤ z)
    (hpa : (if a = 0 then 2 else oddPrimesLt27000[a - 1]'(by omega)) < bLast)
    (hb_le : bLast ≤ oddPrimesLt27000[a]) :
    let Q₁ : Finset ℕ := (oddPrimesLt27000.take a).toFinset
    let P₂ : Finset ℕ := (Finset.Ico bLast z).filter Nat.Prime
    Disjoint Q₁ P₂ ∧ Q₁ ∪ P₂ = BuchstabSwitching.fullOddPrimesBelow z ∧ Q₁.card = a ∧
      (∀ p ∈ Q₁, p.Prime ∧ 2 < p ∧ p < bLast) ∧
      (∀ p ∈ P₂, p.Prime ∧ bLast ≤ p ∧ oddPrimesLt27000[a] ≤ p) := by
  intro Q₁ P₂
  have hQ_lt : ∀ p ∈ Q₁, p.Prime ∧ 2 < p ∧ p < bLast := by
    intro p hp; have hp_mem := List.mem_toFinset.mp hp
    have hp_full := mem_oddPrimesLt27000_iff.mp (List.mem_of_mem_take hp_mem)
    rcases List.mem_iff_getElem.mp hp_mem with ⟨j, hj, rfl⟩
    rw [List.length_take, Nat.min_eq_left ha.le] at hj
    have ha0 : a ≠ 0 := by omega
    simp only [ha0, ↓reduceIte] at hpa
    have hle_last : oddPrimesLt27000[j] ≤ oddPrimesLt27000[a - 1]'(by omega) := by
      rcases eq_or_lt_of_le (by omega : j ≤ a - 1) with rfl | hlt
      · exact le_rfl
      · exact ((List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt) j (a - 1) (by omega) (by omega) hlt).le
    have hp_eq : (oddPrimesLt27000.take a)[j] = oddPrimesLt27000[j] := List.getElem_take
    rw [hp_eq] at hp_full ⊢
    exact ⟨hp_full.2.2, by omega, lt_of_le_of_lt hle_last hpa⟩
  have hidx_lt : ∀ p, p.Prime → 3 ≤ p → p < oddPrimesLt27000[a] → p ∈ oddPrimesLt27000.take a := by
    intro p hp_pr hp3 hplt
    have ha_mem := mem_oddPrimesLt27000_iff.mp (List.getElem_mem ha)
    rcases List.mem_iff_getElem.mp (mem_oddPrimesLt27000_iff.mpr ⟨hp3, hplt.trans ha_mem.2.1, hp_pr⟩)
      with ⟨j, hj, rfl⟩
    have hj_lt : j < a := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · exact absurd hplt (lt_irrefl _)
      · exact absurd ((List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt) a j ha hj hgt) (by omega)
    exact List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take, Nat.min_eq_left ha.le]; exact hj_lt, by simp [List.getElem_take]⟩
  have h3_b : 3 ≤ bLast := by
    split_ifs at hpa with ha0
    · omega
    · exact (mem_oddPrimesLt27000_iff.mp (List.getElem_mem (by omega : a - 1 < oddPrimesLt27000.length))).1.trans hpa.le
  have hP_ge : ∀ p ∈ P₂, p.Prime ∧ bLast ≤ p ∧ oddPrimesLt27000[a] ≤ p := by
    intro p hp; rcases Finset.mem_filter.mp hp with ⟨hpIco, hp_pr⟩; rw [Finset.mem_Ico] at hpIco
    refine ⟨hp_pr, hpIco.1, ?_⟩; by_contra hlt; push Not at hlt
    exact absurd (hQ_lt p (List.mem_toFinset.mpr (hidx_lt p hp_pr (by omega) hlt))).2.2 (by omega)
  refine ⟨Finset.disjoint_left.mpr fun p h1 h2 => by linarith [(hQ_lt p h1).2.2, (hP_ge p h2).2.1], ?_,
    by rw [List.toFinset_card_of_nodup oddPrimesLt27000_nodup.take, List.length_take, Nat.min_eq_left ha.le],
    hQ_lt, hP_ge⟩
  ext p; simp only [Finset.mem_union, BuchstabSwitching.fullOddPrimesBelow_mem_iff]
  constructor
  · rintro (h1 | h2)
    · exact ⟨lt_of_lt_of_le (hQ_lt p h1).2.2 hbz, (hQ_lt p h1).1, (hQ_lt p h1).2.1⟩
    · exact ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).2, (hP_ge p h2).1, by have := (hP_ge p h2).2.1; omega⟩
  · rintro ⟨hpz, hp_pr, hp2⟩
    by_cases hpb : p < bLast
    · exact Or.inl (List.mem_toFinset.mpr (hidx_lt p hp_pr (by omega) (lt_of_lt_of_le hpb hb_le)))
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hpz⟩, hp_pr⟩)

/-- First 12 odd primes `[3..41]` (`max a = 8`, `max aQ = 10` across all 66 Regime `2c` slabs). -/
def smallOddPrimes2c : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

lemma smallOddPrimes2c_eq_take : smallOddPrimes2c = oddPrimesLt27000.take 12 := by
  have hhead : primeChunks = (primeChunks.headD []) :: primeChunks.tail := rfl
  have hlen : 12 ≤ ((primeChunks.headD []).filter (3 ≤ ·)).length := by decide
  have htake : oddPrimesLt27000.take 12 = ((primeChunks.headD []).filter (3 ≤ ·)).take 12 := by
    unfold oddPrimesLt27000 primesLt27000
    conv_lhs => rw [hhead]
    rw [List.flatten_cons, List.filter_append, List.take_append_of_le_length hlen]
  rw [htake]; decide

lemma smallOddPrimes2c_len_le : smallOddPrimes2c.length ≤ oddPrimesLt27000.length := by
  have h := congrArg List.length smallOddPrimes2c_eq_take
  rw [List.length_take] at h; omega

lemma smallOddPrimes2c_getElem {i : ℕ} (hi : i < smallOddPrimes2c.length) :
    smallOddPrimes2c[i] = oddPrimesLt27000[i]'(lt_of_lt_of_le hi smallOddPrimes2c_len_le) := by
  simp [smallOddPrimes2c_eq_take]

lemma smallOddPrimes2c_take {i : ℕ} (hi : i ≤ smallOddPrimes2c.length) :
    smallOddPrimes2c.take i = oddPrimesLt27000.take i := by
  have hi12 : i ≤ 12 := hi
  rw [smallOddPrimes2c_eq_take, List.take_take, Nat.min_eq_left hi12]

private lemma oddPrimesLt27000_get12 :
    ∃ h12 : 12 < oddPrimesLt27000.length, oddPrimesLt27000[12]'h12 = 43 := by
  have hhead : primeChunks = (primeChunks.headD []) :: primeChunks.tail := rfl
  have hlen : 13 ≤ ((primeChunks.headD []).filter (3 ≤ ·)).length := by decide
  have htake : oddPrimesLt27000.take 13 = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] := by
    have h1 : oddPrimesLt27000.take 13 = ((primeChunks.headD []).filter (3 ≤ ·)).take 13 := by
      unfold oddPrimesLt27000 primesLt27000
      conv_lhs => rw [hhead]
      rw [List.flatten_cons, List.filter_append, List.take_append_of_le_length hlen]
    rw [h1]; decide
  have h12 : 12 < oddPrimesLt27000.length := by
    have := congrArg List.length htake; rw [List.length_take] at this; simp at this; omega
  refine ⟨h12, ?_⟩
  have hget : (oddPrimesLt27000.take 13)[12]'(by rw [htake]; decide) = oddPrimesLt27000[12]'h12 :=
    List.getElem_take
  rw [← hget]; simp [htake]

lemma smallOddPrimes2c_mem_iff {p : ℕ} : p ∈ smallOddPrimes2c ↔ 3 ≤ p ∧ p < 43 ∧ p.Prime := by
  have hlt43 : ∀ q ∈ smallOddPrimes2c, q < 43 := by decide
  constructor
  · intro hp
    have hmem := mem_oddPrimesLt27000_iff.mp (List.mem_of_mem_take (smallOddPrimes2c_eq_take ▸ hp))
    exact ⟨hmem.1, hlt43 p hp, hmem.2.2⟩
  · rintro ⟨hp3, hp43, hp_pr⟩
    obtain ⟨h12, h43⟩ := oddPrimesLt27000_get12
    rcases List.mem_iff_getElem.mp (mem_oddPrimesLt27000_iff.mpr ⟨hp3, by omega, hp_pr⟩) with ⟨j, hj, rfl⟩
    have hj12 : j < 12 := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · omega
      · exact absurd ((List.pairwise_iff_getElem.mp oddPrimesLt27000_pairwise_lt) 12 j h12 hj hgt) (by omega)
    rw [smallOddPrimes2c_eq_take]
    exact List.mem_iff_getElem.mpr ⟨j, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩

end OddPrimesSplit27000

section PrimeChunksFast2c

/-- Precomputed exact bounds for one chunk of `primeChunks` (restricted to odd primes `p ≥ 3`). -/
structure ChunkStat2c where
  lo : ℕ
  hi : ℕ
  s1 : SciNat
  s2 : SciNat
  cnt : ℕ
  vLb : SciNat
  vUb : SciNat
  deriving DecidableEq

private def chunkS1 (c : List ℕ) : SciNat :=
  c.foldl (fun a q => a.add (SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat (q - 1)) 24)) (sn 0 24)

private def chunkS2 (c : List ℕ) : SciNat :=
  c.foldl (fun a q => a.add (SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat ((q - 1) ^ 2)) 24)) (sn 0 24)

private def chunkVLb (c : List ℕ) : SciNat :=
  c.foldl (fun a p => (a.mul (SciNat.divLb (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24)).trimLb 24) (sn 1 0)

private def chunkVUb (c : List ℕ) : SciNat :=
  c.foldl (fun a p => (a.mul (SciNat.divUb (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24)).trimUb 24) (sn 1 0)

private def checkOneChunk2c (p : List ℕ × ChunkStat2c) : Bool :=
  let ps := p.1.filter (3 ≤ ·)
  decide (3 ≤ p.2.lo) && ps.all (fun q => decide (p.2.lo ≤ q ∧ q ≤ p.2.hi)) &&
  decide (chunkS1 ps = p.2.s1) && decide (chunkS2 ps = p.2.s2) &&
  decide (ps.length = p.2.cnt) && decide (chunkVLb ps = p.2.vLb) && decide (chunkVUb ps = p.2.vUb)

private def chunkStats2c : List ChunkStat2c := [
  ⟨3, 281, sn 1778549563909457237980067 24, sn 374548067635774659835293 24, 59, sn 129642361798372000529717 24, sn 129642361798372000529770 24⟩,
  ⟨283, 659, sn 133923952828949461273764 24, sn 317144389044288920992 24, 60, sn 874517659764578202079254 24, sn 874517659764578202079365 24⟩,
  ⟨661, 1069, sn 70210320547920329868834 24, sn 83825451913923629038 24, 60, sn 932158637064958539506811 24, sn 932158637064958539506922 24⟩,
  ⟨1087, 1511, sn 46683665926336315843664 24, sn 36697707308239162148 24, 60, sn 954371734619968738360349 24, sn 954371734619968738360463 24⟩,
  ⟨1523, 1987, sn 34675817891750293789643 24, sn 20161319901818410733 24, 60, sn 965908758157076839443188 24, sn 965908758157076839443303 24⟩,
  ⟨1993, 2423, sn 27271125666173829800087 24, sn 12440719360874903758 24, 60, sn 973091319236443644269102 24, sn 973091319236443644269219 24⟩,
  ⟨2437, 2903, sn 22463736733226781630671 24, sn 8430987123058604835 24, 60, sn 977782571411181419067383 24, sn 977782571411181419067500 24⟩,
  ⟨2909, 3413, sn 18970455929087096789733 24, sn 6011493634083658395 24, 60, sn 981205400819621618889002 24, sn 981205400819621618889121 24⟩,
  ⟨3433, 3907, sn 16423633389831661845707 24, sn 4501761439075145513 24, 60, sn 983708284540768862755756 24, sn 983708284540768862755875 24⟩,
  ⟨3911, 4409, sn 14481305351118001853756 24, sn 3499463264836924317 24, 60, sn 985621319584359629912933 24, sn 985621319584359629913050 24⟩,
  ⟨4421, 4937, sn 12859771460641053149973 24, sn 2759168335950774628 24, 60, sn 987221199941523811088592 24, sn 987221199941523811088711 24⟩,
  ⟨4943, 5443, sn 11573452068642546532110 24, sn 2234470671587475028 24, 60, sn 988492158185016342873651 24, sn 988492158185016342873769 24⟩,
  ⟨5449, 5939, sn 10534370241246270499571 24, sn 1850707692461844867 24, 60, sn 989520006146728857894746 24, sn 989520006146728857894863 24⟩,
  ⟨5953, 6473, sn 9648912745809300456913 24, sn 1552495971957587001 24, 60, sn 990396719775567127223175 24, sn 990396719775567127223293 24⟩,
  ⟨6481, 6997, sn 8887856268882184629141 24, sn 1317214074804832730 24, 60, sn 991150871126960769041726 24, sn 991150871126960769041845 24⟩,
  ⟨7001, 7561, sn 8226130185667067898725 24, sn 1128455748053490808 24, 60, sn 991807052181212037604137 24, sn 991807052181212037604256 24⟩,
  ⟨7573, 8111, sn 7664276380561717536489 24, sn 979448326321378234 24, 60, sn 992364533268060690888429 24, sn 992364533268060690888548 24⟩,
  ⟨8117, 8677, sn 7147665831193811437652 24, sn 851814900664508502 24, 60, sn 992877395071904975548286 24, sn 992877395071904975548405 24⟩,
  ⟨8681, 9199, sn 6722770040137209168181 24, sn 753491648771364171 24, 60, sn 993299402973940114908348 24, sn 993299402973940114908467 24⟩,
  ⟨9203, 9733, sn 6343791148404890806404 24, sn 670900466631083252 24, 60, sn 993675954860072367104177 24, sn 993675954860072367104295 24⟩,
  ⟨9739, 10271, sn 6000883546994830469444 24, sn 600337103408474802 24, 60, sn 994016787400207519449698 24, sn 994016787400207519449816 24⟩,
  ⟨10273, 10859, sn 5681808936968637536397 24, sn 538191042791063424 24, 60, sn 994334034424102811067762 24, sn 994334034424102811067881 24⟩,
  ⟨10861, 11443, sn 5382715743049453664495 24, sn 483005490925158987 24, 60, sn 994631504892832819170053 24, sn 994631504892832819170171 24⟩,
  ⟨11447, 12011, sn 5109594373469969918484 24, sn 435222432297634995 24, 60, sn 994903220884302268658213 24, sn 994903220884302268658332 24⟩,
  ⟨12037, 12553, sn 4878039611125677003699 24, sn 396653797498021875 24, 60, sn 995133641329465694598476 24, sn 995133641329465694598595 24⟩,
  ⟨12569, 13109, sn 4675193380001987926745 24, sn 364348483362620391 24, 60, sn 995335536991232049465522 24, sn 995335536991232049465641 24⟩,
  ⟨13121, 13697, sn 4474590582504022312236 24, sn 333757859531879209 24, 60, sn 995535239340812949442549 24, sn 995535239340812949442668 24⟩,
  ⟨13709, 14323, sn 4289461960440986140881 24, sn 306709802165982817 24, 60, sn 995719571935858049304148 24, sn 995719571935858049304267 24⟩,
  ⟨14327, 14851, sn 4110187295356658955185 24, sn 281591386934815473 24, 60, sn 995898107739076121546157 24, sn 995898107739076121546276 24⟩,
  ⟨14867, 15401, sn 3961499529954290000547 24, sn 261587744707806951 24, 60, sn 996046206575459557952329 24, sn 996046206575459557952448 24⟩,
  ⟨15413, 15971, sn 3824115294232698548002 24, sn 243755775322359080 24, 60, sn 996183065905154626262579 24, sn 996183065905154626262698 24⟩,
  ⟨15973, 16603, sn 3685618568872402233474 24, sn 226424312356843311 24, 60, sn 996321052186538508498326 24, sn 996321052186538508498444 24⟩,
  ⟨16607, 17191, sn 3550801394022350295920 24, sn 210158570734192776 24, 60, sn 996455390535378431034366 24, sn 996455390535378431034485 24⟩,
  ⟨17203, 17783, sn 3431701568962633750982 24, sn 196293041015414827 24, 60, sn 996574082175012041871376 24, sn 996574082175012041871495 24⟩,
  ⟨17789, 18313, sn 3322007180134319079564 24, sn 183942414154191310 24, 60, sn 996683412911094301808384 24, sn 996683412911094301808503 24⟩,
  ⟨18329, 19009, sn 3217959101813087500921 24, sn 172607780549320074 24, 60, sn 996787126949554264824086 24, sn 996787126949554264824204 24⟩,
  ⟨19013, 19571, sn 3106799322530355038813 24, sn 160881328594208777 24, 60, sn 996897941590550647907445 24, sn 996897941590550647907564 24⟩,
  ⟨19577, 20149, sn 3016965782734507516731 24, sn 151712089046081368 24, 60, sn 996987505055136840247490 24, sn 996987505055136840247608 24⟩,
  ⟨20161, 20771, sn 2931442422557668167328 24, sn 143233958250602991 24, 60, sn 997072778649699174589284 24, sn 997072778649699174589402 24⟩,
  ⟨20773, 21383, sn 2846016339589273163268 24, sn 135005567883761091 24, 60, sn 997157962412544284512182 24, sn 997157962412544284512301 24⟩,
  ⟨21391, 21943, sn 2770309955269228951937 24, sn 127917215546516147 24, 60, sn 997233460028666946117941 24, sn 997233460028666946118060 24⟩,
  ⟨21961, 22543, sn 2698475196038492171015 24, sn 121370006092596739 24, 60, sn 997305101892136367545379 24, sn 997305101892136367545498 24⟩,
  ⟨22549, 23099, sn 2627314902703304836590 24, sn 115052421861600986 24, 60, sn 997376076091505617968754 24, sn 997376076091505617968873 24⟩,
  ⟨23117, 23743, sn 2560148820037205475556 24, sn 109246188912430456 24, 60, sn 997443071081073226030305 24, sn 997443071081073226030423 24⟩,
  ⟨23747, 24281, sn 2499785998485209860750 24, sn 104152936897263062 24, 60, sn 997503283916769529008509 24, sn 997503283916769529008628 24⟩,
  ⟨24317, 24977, sn 2434377067218123301946 24, sn 98776424017734889 24, 60, sn 997568534356205984181174 24, sn 997568534356205984181293 24⟩,
  ⟨24979, 25603, sn 2371861623051659261152 24, sn 93766874219204993 24, 60, sn 997630902244538423761876 24, sn 997630902244538423761993 24⟩,
  ⟨25609, 26203, sn 2316235514566834075599 24, sn 89419919490183757 24, 60, sn 997686400281363322254103 24, sn 997686400281363322254222 24⟩,
  ⟨26209, 26801, sn 2263545559066166883351 24, sn 85397775213139035 24, 60, sn 997738971724927893605353 24, sn 997738971724927893605472 24⟩,
  ⟨26813, 26993, sn 780639235797103788611 24, sn 29019055152038971 24, 21, sn 999219650885175490755523 24, sn 999219650885175490755564 24⟩
]

private lemma chunkStats2c_len : chunkStats2c.length = primeChunks.length := by decide
private lemma chunkStats2c_ok0 : ((primeChunks.zip chunkStats2c).take 10).all checkOneChunk2c = true := by decide
private lemma chunkStats2c_ok1 : (((primeChunks.zip chunkStats2c).drop 10).take 10).all checkOneChunk2c = true := by decide
private lemma chunkStats2c_ok2 : (((primeChunks.zip chunkStats2c).drop 20).take 10).all checkOneChunk2c = true := by decide
private lemma chunkStats2c_ok3 : (((primeChunks.zip chunkStats2c).drop 30).take 10).all checkOneChunk2c = true := by decide
private lemma chunkStats2c_ok4 : ((primeChunks.zip chunkStats2c).drop 40).all checkOneChunk2c = true := by decide

private lemma chunkStats2c_all_ok : ∀ p ∈ primeChunks.zip chunkStats2c, checkOneChunk2c p = true := by
  intro p hp
  have h10 : p ∈ (primeChunks.zip chunkStats2c).take 10 ∨ p ∈ (primeChunks.zip chunkStats2c).drop 10 := by
    rwa [← List.mem_append, List.take_append_drop]
  rcases h10 with h | h
  · exact List.all_eq_true.mp chunkStats2c_ok0 p h
  have h20 : p ∈ ((primeChunks.zip chunkStats2c).drop 10).take 10 ∨ p ∈ (primeChunks.zip chunkStats2c).drop 20 := by
    rw [show (20 : ℕ) = 10 + 10 by norm_num, ← List.drop_drop]; rwa [← List.mem_append, List.take_append_drop]
  rcases h20 with h | h
  · exact List.all_eq_true.mp chunkStats2c_ok1 p h
  have h30 : p ∈ ((primeChunks.zip chunkStats2c).drop 20).take 10 ∨ p ∈ (primeChunks.zip chunkStats2c).drop 30 := by
    rw [show (30 : ℕ) = 20 + 10 by norm_num, ← List.drop_drop]; rwa [← List.mem_append, List.take_append_drop]
  rcases h30 with h | h
  · exact List.all_eq_true.mp chunkStats2c_ok2 p h
  have h40 : p ∈ ((primeChunks.zip chunkStats2c).drop 30).take 10 ∨ p ∈ (primeChunks.zip chunkStats2c).drop 40 := by
    rw [show (40 : ℕ) = 30 + 10 by norm_num, ← List.drop_drop]; rwa [← List.mem_append, List.take_append_drop]
  rcases h40 with h | h
  · exact List.all_eq_true.mp chunkStats2c_ok3 p h
  exact List.all_eq_true.mp chunkStats2c_ok4 p h

private def fastMertensLoop (u v : ℕ) : List (List ℕ × ChunkStat2c) → SciNat × SciNat × ℕ
  | [] => (sn 0 24, sn 0 24, 0)
  | (c, st) :: rest =>
    let r := fastMertensLoop u v rest
    if st.hi < u || v ≤ st.lo then r
    else if u ≤ st.lo && st.hi < v then (st.s1.add r.1, st.s2.add r.2.1, st.cnt + r.2.2)
    else
      let ps := c.filter (fun q => decide (u ≤ q ∧ q < v))
      ((chunkS1 ps).add r.1, (chunkS2 ps).add r.2.1, ps.length + r.2.2)

private def fastV2LbLoop (u v : ℕ) : List (List ℕ × ChunkStat2c) → SciNat
  | [] => sn 1 0
  | (c, st) :: rest =>
    let r := fastV2LbLoop u v rest
    if st.hi < u || v ≤ st.lo then r
    else if u ≤ st.lo && st.hi < v then (st.vLb.mul r).trimLb 24
    else ((chunkVLb (c.filter (fun q => decide (u ≤ q ∧ q < v)))).mul r).trimLb 24

private def fastV2UbLoop (u v : ℕ) : List (List ℕ × ChunkStat2c) → SciNat
  | [] => sn 1 0
  | (c, st) :: rest =>
    let r := fastV2UbLoop u v rest
    if st.hi < u || v ≤ st.lo then r
    else if u ≤ st.lo && st.hi < v then (st.vUb.mul r).trimUb 24
    else ((chunkVUb (c.filter (fun q => decide (u ≤ q ∧ q < v)))).mul r).trimUb 24

private def fastOddPrimesLoop (z : ℕ) : List (List ℕ × ChunkStat2c) → List ℕ
  | [] => []
  | (c, st) :: rest =>
    if z ≤ st.lo then []
    else if st.hi < z then (c.filter (3 ≤ ·)) ++ fastOddPrimesLoop z rest
    else (c.filter (fun q => decide (3 ≤ q ∧ q < z))) ++ fastOddPrimesLoop z rest

private def tail43S1 : SciNat := sn 972747172517088365122869 24
private def tail43S2 : SciNat := sn 4997444704148667157075 24
private def tail43Cnt : ℕ := 2948
private def tail43VLb : SciNat := sn 377091136510217510212866 24

private lemma tail43_mert_eq :
    fastMertensLoop 43 27000 (primeChunks.zip chunkStats2c) = (tail43S1, tail43S2, tail43Cnt) := by decide
private lemma tail43_vLb_eq :
    fastV2LbLoop 43 27000 (primeChunks.zip chunkStats2c) = tail43VLb := by decide

/-- O(1)-fast exact Mertens sums/count on `[u, v)` (`v ≤ 27000`, O(1) on `[u, 27000)` for `3 ≤ u ≤ 43`). -/
def fastExactMertens2c (u v : ℕ) : SciNat × SciNat × ℕ :=
  if 3 ≤ u && u ≤ 43 && v == 27000 then
    let ps := smallOddPrimes2c.filter (u ≤ ·)
    ((chunkS1 ps).add tail43S1, (chunkS2 ps).add tail43S2, ps.length + tail43Cnt)
  else if 3 ≤ u then fastMertensLoop u v (primeChunks.zip chunkStats2c)
  else (exactInvSubOneSumUb u v 24, exactInvPredSqSumUb u v 24, exactPrimeCount u v)

/-- O(1)-fast exact lower bound on `∏_{p ∈ [u, v)} (1 - 1/(p-1))` (`v ≤ 27000`). -/
def fastV2LbExact2c (u v : ℕ) : SciNat :=
  if 3 ≤ u && u ≤ 43 && v == 27000 then
    ((chunkVLb (smallOddPrimes2c.filter (u ≤ ·))).mul tail43VLb).trimLb 24
  else if 3 ≤ u then fastV2LbLoop u v (primeChunks.zip chunkStats2c)
  else exactProdOneSubInvPredLb u v 24

/-- Chunk-skipping exact upper bound on `∏_{p ∈ [u, v)} (1 - 1/(p-1))` (`3 ≤ u, v ≤ 27000`). -/
def fastV2UbExact2c (u v : ℕ) : SciNat :=
  if 3 ≤ u then fastV2UbLoop u v (primeChunks.zip chunkStats2c) else exactProdOneSubInvPredUb u v 24

/-- Chunk-skipping sorted odd primes `< z` (`z ≤ 27000`), equal to `oddPrimesList z`. -/
def fastOddPrimesList2c (z : ℕ) : List ℕ :=
  fastOddPrimesLoop z (primeChunks.zip chunkStats2c)

private lemma foldl_add_sci_le (ps : List ℕ) (f : ℕ → ℝ) (g : ℕ → SciNat)
    (hg : ∀ q ∈ ps, f q ≤ (g q).toReal) (acc : SciNat) :
    acc.toReal + (ps.map f).sum ≤ (ps.foldl (fun a q => a.add (g q)) acc).toReal := by
  induction ps generalizing acc with
  | nil => simp
  | cons p tl ih =>
    have hrec := ih (fun q hq => hg q (List.mem_cons_of_mem _ hq)) (acc.add (g p))
    rw [List.foldl_cons, List.map_cons, List.sum_cons]; rw [SciProofs.add_toReal] at hrec
    linarith [hg p List.mem_cons_self]

private lemma foldl_mul_trimLb_sci_le (ps : List ℕ) (f : ℕ → ℝ) (g : ℕ → SciNat)
    (hf : ∀ q ∈ ps, 0 ≤ f q) (hg : ∀ q ∈ ps, (g q).toReal ≤ f q) (acc : SciNat) :
    (ps.foldl (fun a q => (a.mul (g q)).trimLb 24) acc).toReal ≤ acc.toReal * (ps.map f).prod := by
  induction ps generalizing acc with
  | nil => simp
  | cons p tl ih =>
    have hrec := ih (fun q hq => hf q (List.mem_cons_of_mem _ hq))
      (fun q hq => hg q (List.mem_cons_of_mem _ hq)) ((acc.mul (g p)).trimLb 24)
    have hstep : ((acc.mul (g p)).trimLb 24).toReal ≤ acc.toReal * f p :=
      (SciProofs.trimLb_le _ 24).trans (by rw [SciProofs.mul_toReal]; exact mul_le_mul_of_nonneg_left (hg p List.mem_cons_self) acc.toReal_nonneg)
    have hnn : 0 ≤ (tl.map f).prod := List.prod_nonneg fun x hx => by
      rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩; exact hf q (List.mem_cons_of_mem _ hq)
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    calc _ ≤ ((acc.mul (g p)).trimLb 24).toReal * (tl.map f).prod := hrec
      _ ≤ (acc.toReal * f p) * (tl.map f).prod := mul_le_mul_of_nonneg_right hstep hnn
      _ = acc.toReal * (f p * (tl.map f).prod) := by ring

private lemma foldl_mul_trimUb_sci_le (ps : List ℕ) (f : ℕ → ℝ) (g : ℕ → SciNat)
    (hf : ∀ q ∈ ps, 0 ≤ f q) (hg : ∀ q ∈ ps, f q ≤ (g q).toReal) (acc : SciNat) :
    acc.toReal * (ps.map f).prod ≤ (ps.foldl (fun a q => (a.mul (g q)).trimUb 24) acc).toReal := by
  induction ps generalizing acc with
  | nil => simp
  | cons p tl ih =>
    have hrec := ih (fun q hq => hf q (List.mem_cons_of_mem _ hq))
      (fun q hq => hg q (List.mem_cons_of_mem _ hq)) ((acc.mul (g p)).trimUb 24)
    have hstep : acc.toReal * f p ≤ ((acc.mul (g p)).trimUb 24).toReal :=
      (mul_le_mul_of_nonneg_left (hg p List.mem_cons_self) acc.toReal_nonneg).trans
        ((SciProofs.mul_toReal _ _).symm.trans_le (SciProofs.trimUb_le _ 24))
    have hnn : 0 ≤ (tl.map f).prod := List.prod_nonneg fun x hx => by
      rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩; exact hf q (List.mem_cons_of_mem _ hq)
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    calc acc.toReal * (f p * (tl.map f).prod) = (acc.toReal * f p) * (tl.map f).prod := by ring
      _ ≤ ((acc.mul (g p)).trimUb 24).toReal * (tl.map f).prod := mul_le_mul_of_nonneg_right hstep hnn
      _ ≤ _ := hrec

private lemma one_sub_inv_pred_2c {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 : ℝ) - 1 / ((p : ℝ) - 1) ∧
      (1 : ℝ) - 1 / ((p : ℝ) - 1) = ((p - 2 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  refine ⟨by have : 1 / ((p : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
             linarith, ?_⟩
  rw [Nat.cast_sub hp.two_le, Nat.cast_sub (by have := hp.two_le; omega)]; push_cast; field_simp [hden]; ring

private lemma chunkS1_sound {ps : List ℕ} (hpr : ∀ q ∈ ps, q.Prime) :
    (ps.map (fun q : ℕ => (1 : ℝ) / ((q : ℝ) - 1))).sum ≤ (chunkS1 ps).toReal := by
  have h := foldl_add_sci_le ps (fun q : ℕ => (1 : ℝ) / ((q : ℝ) - 1))
    (fun q => SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat (q - 1)) 24) (fun q hq => by
      have hd := SciNat.divUb_le (SciNat.ofNat 1) (SciNat.ofNat (q - 1)) 24
      rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, Nat.cast_sub (hpr q hq).one_lt.le] at hd
      simpa using hd) (sn 0 24)
  simpa [chunkS1, SciNat.toReal] using h

private lemma chunkS2_sound {ps : List ℕ} (hpr : ∀ q ∈ ps, q.Prime) :
    (ps.map (fun q : ℕ => (1 : ℝ) / ((q : ℝ) - 1) ^ 2)).sum ≤ (chunkS2 ps).toReal := by
  have h := foldl_add_sci_le ps (fun q : ℕ => (1 : ℝ) / ((q : ℝ) - 1) ^ 2)
    (fun q => SciNat.divUb (SciNat.ofNat 1) (SciNat.ofNat ((q - 1) ^ 2)) 24) (fun q hq => by
      have hd := SciNat.divUb_le (SciNat.ofNat 1) (SciNat.ofNat ((q - 1) ^ 2)) 24
      rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, Nat.cast_pow, Nat.cast_sub (hpr q hq).one_lt.le] at hd
      simpa using hd) (sn 0 24)
  simpa [chunkS2, SciNat.toReal] using h

private lemma chunkVLb_sound {ps : List ℕ} (hpr : ∀ p ∈ ps, p.Prime) :
    (chunkVLb ps).toReal ≤ (ps.map (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod := by
  have h := foldl_mul_trimLb_sci_le ps (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))
    (fun p => SciNat.divLb (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24)
    (fun p hp => (one_sub_inv_pred_2c (hpr p hp)).1) (fun p hp => by
      have hd := SciNat.divLb_le (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24
      rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, ← (one_sub_inv_pred_2c (hpr p hp)).2] at hd; exact hd) (sn 1 0)
  simpa [chunkVLb, SciNat.toReal] using h

private lemma chunkVUb_sound {ps : List ℕ} (hpr : ∀ p ∈ ps, p.Prime) :
    (ps.map (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod ≤ (chunkVUb ps).toReal := by
  have h := foldl_mul_trimUb_sci_le ps (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))
    (fun p => SciNat.divUb (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24)
    (fun p hp => (one_sub_inv_pred_2c (hpr p hp)).1) (fun p hp => by
      have hd := SciNat.divUb_le (SciNat.ofNat (p - 2)) (SciNat.ofNat (p - 1)) 24
      rw [SciProofs.ofNat_toReal, SciProofs.ofNat_toReal, ← (one_sub_inv_pred_2c (hpr p hp)).2] at hd; exact hd) (sn 1 0)
  simpa [chunkVUb, SciNat.toReal] using h

private lemma chunk_filter_cases {c : List ℕ} {st : ChunkStat2c} {u v : ℕ} (hu : 3 ≤ u)
    (hok : checkOneChunk2c (c, st) = true) :
    (st.hi < u ∨ v ≤ st.lo → c.filter (fun q => decide (u ≤ q ∧ q < v)) = []) ∧
    (u ≤ st.lo ∧ st.hi < v → c.filter (fun q => decide (u ≤ q ∧ q < v)) = c.filter (3 ≤ ·)) ∧
    chunkS1 (c.filter (3 ≤ ·)) = st.s1 ∧ chunkS2 (c.filter (3 ≤ ·)) = st.s2 ∧
    (c.filter (3 ≤ ·)).length = st.cnt ∧ chunkVLb (c.filter (3 ≤ ·)) = st.vLb ∧
    chunkVUb (c.filter (3 ≤ ·)) = st.vUb := by
  simp only [checkOneChunk2c, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨_, hbd⟩, hs1⟩, hs2⟩, hcnt⟩, hvl⟩, hvu⟩
  refine ⟨fun hskip => List.filter_eq_nil_iff.mpr fun q hq => by
      simp only [decide_eq_true_eq]; intro huv
      have hb := hbd q (List.mem_filter.mpr ⟨hq, decide_eq_true (by omega)⟩); omega,
    fun hfull => List.filter_congr fun q hq => by
      simp only [decide_eq_decide]
      exact ⟨fun huv => by omega, fun h3 => by
        have hb := hbd q (List.mem_filter.mpr ⟨hq, decide_eq_true h3⟩); omega⟩,
    hs1, hs2, hcnt, hvl, hvu⟩

private lemma fastMertensLoop_sound (u v : ℕ) (hu : 3 ≤ u) :
    ∀ (pairs : List (List ℕ × ChunkStat2c)),
      (∀ p ∈ pairs, checkOneChunk2c p = true ∧ ∀ q ∈ p.1, q.Prime) →
      let flat := (pairs.map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v))
      let res := fastMertensLoop u v pairs
      (flat.map (fun q : ℕ => (1 : ℝ) / ((q : ℝ) - 1))).sum ≤ res.1.toReal ∧
      (flat.map (fun q : ℕ => (1 : ℝ) / ((q : ℝ) - 1) ^ 2)).sum ≤ res.2.1.toReal ∧
      flat.length = res.2.2
  | [], _ => by simp [fastMertensLoop, SciNat.toReal]
  | (c, st) :: rest, hall => by
    have h0 := hall (c, st) List.mem_cons_self
    have ih := fastMertensLoop_sound u v hu rest fun p hp => hall p (List.mem_cons_of_mem _ hp)
    have hcc := chunk_filter_cases (v := v) hu h0.1
    set ps := c.filter (fun q => decide (u ≤ q ∧ q < v))
    have hpr_ps : ∀ q ∈ ps, q.Prime := fun q hq => h0.2 q (List.mem_of_mem_filter hq)
    have hflat : (((c, st) :: rest).map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v)) =
        ps ++ (rest.map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v)) := by
      simp [ps, List.filter_append]
    dsimp only; rw [hflat, List.map_append, List.map_append, List.sum_append, List.sum_append, List.length_append]
    unfold fastMertensLoop; dsimp only; split_ifs with hskip hfull
    · have hnil : ps = [] := hcc.1 (by simpa [Bool.or_eq_true, decide_eq_true_eq] using hskip)
      simpa [hnil] using ih
    · have heq : ps = c.filter (3 ≤ ·) := hcc.2.1 (by simpa [Bool.and_eq_true, decide_eq_true_eq] using hfull)
      rw [← hcc.2.2.1, ← hcc.2.2.2.1, ← hcc.2.2.2.2.1, ← heq, SciProofs.add_toReal, SciProofs.add_toReal]
      exact ⟨add_le_add (chunkS1_sound hpr_ps) ih.1, add_le_add (chunkS2_sound hpr_ps) ih.2.1, by dsimp only; exact congrArg (ps.length + ·) ih.2.2⟩
    · rw [SciProofs.add_toReal, SciProofs.add_toReal]
      exact ⟨add_le_add (chunkS1_sound hpr_ps) ih.1, add_le_add (chunkS2_sound hpr_ps) ih.2.1, by dsimp only [ps]; exact congrArg (_ + ·) ih.2.2⟩

private lemma fastV2LbLoop_sound (u v : ℕ) (hu : 3 ≤ u) :
    ∀ (pairs : List (List ℕ × ChunkStat2c)),
      (∀ p ∈ pairs, checkOneChunk2c p = true ∧ ∀ q ∈ p.1, q.Prime) →
      (fastV2LbLoop u v pairs).toReal ≤
        (((pairs.map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v))).map
          (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod
  | [], _ => by simp [fastV2LbLoop, SciNat.toReal]
  | (c, st) :: rest, hall => by
    have h0 := hall (c, st) List.mem_cons_self
    have ih := fastV2LbLoop_sound u v hu rest fun p hp => hall p (List.mem_cons_of_mem _ hp)
    have hcc := chunk_filter_cases (v := v) hu h0.1
    set ps := c.filter (fun q => decide (u ≤ q ∧ q < v))
    have hpr_ps : ∀ q ∈ ps, q.Prime := fun q hq => h0.2 q (List.mem_of_mem_filter hq)
    have hnn_ps : 0 ≤ (ps.map (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod :=
      List.prod_nonneg fun x hx => by rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩; exact (one_sub_inv_pred_2c (hpr_ps q hq)).1
    have hflat : (((c, st) :: rest).map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v)) =
        ps ++ (rest.map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v)) := by
      simp [ps, List.filter_append]
    rw [hflat, List.map_append, List.prod_append]; unfold fastV2LbLoop; dsimp only; split_ifs with hskip hfull
    · have hnil : ps = [] := hcc.1 (by simpa [Bool.or_eq_true, decide_eq_true_eq] using hskip)
      simpa [hnil] using ih
    · have heq : ps = c.filter (3 ≤ ·) := hcc.2.1 (by simpa [Bool.and_eq_true, decide_eq_true_eq] using hfull)
      rw [← hcc.2.2.2.2.2.1, ← heq]
      exact (SciProofs.trimLb_le _ 24).trans (by rw [SciProofs.mul_toReal]; exact mul_le_mul (chunkVLb_sound hpr_ps) ih (SciNat.toReal_nonneg _) hnn_ps)
    · exact (SciProofs.trimLb_le _ 24).trans (by rw [SciProofs.mul_toReal]; exact mul_le_mul (chunkVLb_sound hpr_ps) ih (SciNat.toReal_nonneg _) hnn_ps)

private lemma fastV2UbLoop_sound (u v : ℕ) (hu : 3 ≤ u) :
    ∀ (pairs : List (List ℕ × ChunkStat2c)),
      (∀ p ∈ pairs, checkOneChunk2c p = true ∧ ∀ q ∈ p.1, q.Prime) →
      (((pairs.map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v))).map
          (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod ≤
        (fastV2UbLoop u v pairs).toReal
  | [], _ => by simp [fastV2UbLoop, SciNat.toReal]
  | (c, st) :: rest, hall => by
    have h0 := hall (c, st) List.mem_cons_self
    have ih := fastV2UbLoop_sound u v hu rest fun p hp => hall p (List.mem_cons_of_mem _ hp)
    have hcc := chunk_filter_cases (v := v) hu h0.1
    set ps := c.filter (fun q => decide (u ≤ q ∧ q < v))
    have hpr_ps : ∀ q ∈ ps, q.Prime := fun q hq => h0.2 q (List.mem_of_mem_filter hq)
    have hnn_rest : 0 ≤ (((rest.map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v))).map
        (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod :=
      List.prod_nonneg fun x hx => by
        rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩
        rcases List.mem_flatten.mp (List.mem_of_mem_filter hq) with ⟨c', hc', hqc'⟩
        rcases List.mem_map.mp hc' with ⟨p', hp', rfl⟩
        exact (one_sub_inv_pred_2c ((hall p' (List.mem_cons_of_mem _ hp')).2 q hqc')).1
    have hflat : (((c, st) :: rest).map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v)) =
        ps ++ (rest.map Prod.fst).flatten.filter (fun q => decide (u ≤ q ∧ q < v)) := by
      simp [ps, List.filter_append]
    rw [hflat, List.map_append, List.prod_append]; unfold fastV2UbLoop; dsimp only; split_ifs with hskip hfull
    · have hnil : ps = [] := hcc.1 (by simpa [Bool.or_eq_true, decide_eq_true_eq] using hskip)
      simpa [hnil] using ih
    · have heq : ps = c.filter (3 ≤ ·) := hcc.2.1 (by simpa [Bool.and_eq_true, decide_eq_true_eq] using hfull)
      rw [← hcc.2.2.2.2.2.2, ← heq]
      exact (mul_le_mul (chunkVUb_sound hpr_ps) ih hnn_rest (SciNat.toReal_nonneg _)).trans
        ((SciProofs.mul_toReal _ _).symm.trans_le (SciProofs.trimUb_le _ 24))
    · exact (mul_le_mul (chunkVUb_sound hpr_ps) ih hnn_rest (SciNat.toReal_nonneg _)).trans
        ((SciProofs.mul_toReal _ _).symm.trans_le (SciProofs.trimUb_le _ 24))

private lemma zip_chunks_props :
    ((primeChunks.zip chunkStats2c).map Prod.fst).flatten = primesLt27000 ∧
    (∀ p ∈ primeChunks.zip chunkStats2c, checkOneChunk2c p = true ∧ ∀ q ∈ p.1, q.Prime) := by
  have hfst : (primeChunks.zip chunkStats2c).map Prod.fst = primeChunks :=
    List.map_fst_zip (le_of_eq chunkStats2c_len.symm)
  refine ⟨by rw [hfst]; rfl, fun p hp => ⟨chunkStats2c_all_ok p hp, fun q hq => ?_⟩⟩
  have hmem : p.1 ∈ primeChunks := hfst ▸ List.mem_map_of_mem hp
  exact (mem_primesLt27000_iff.mp (List.mem_flatten.mpr ⟨p.1, hmem, hq⟩)).2

private lemma filter_ico_eq_2c {u v : ℕ} (hv : v ≤ 27000) :
    (Finset.Ico u v).filter Nat.Prime =
      (primesLt27000.filter (fun q => decide (u ≤ q ∧ q < v))).toFinset := by
  ext q; simp only [Finset.mem_filter, Finset.mem_Ico, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq, mem_primesLt27000_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, hp⟩ => ⟨⟨lt_of_lt_of_le h2 hv, hp⟩, h1, h2⟩, fun ⟨⟨_, hp⟩, h1, h2⟩ => ⟨⟨h1, h2⟩, hp⟩⟩

lemma fastExactMertens2c_sound {u v : ℕ} (hv : v ≤ 27000) :
    ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, BuchstabSwitching.gTot p ≤ (fastExactMertens2c u v).1.toReal ∧
    ∑ p ∈ (Finset.Ico u v).filter Nat.Prime, (BuchstabSwitching.gTot p) ^ 2 ≤ (fastExactMertens2c u v).2.1.toReal ∧
    (((Finset.Ico u v).filter Nat.Prime).card : ℝ) ≤ ((fastExactMertens2c u v).2.2 : ℝ) := by
  have hconv : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      (∑ p ∈ S, BuchstabSwitching.gTot p = ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1)) ∧
      (∑ p ∈ S, (BuchstabSwitching.gTot p) ^ 2 = ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ^ 2) := fun S hS =>
    ⟨Finset.sum_congr rfl fun p hp => BuchstabSwitching.gTot_prime (hS p hp),
     Finset.sum_congr rfl fun p hp => by rw [BuchstabSwitching.gTot_prime (hS p hp), one_div_pow]⟩
  have hloop : ∀ a b, 3 ≤ a → b ≤ 27000 →
      ∑ p ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ≤
        (fastMertensLoop a b (primeChunks.zip chunkStats2c)).1.toReal ∧
      ∑ p ∈ (Finset.Ico a b).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤
        (fastMertensLoop a b (primeChunks.zip chunkStats2c)).2.1.toReal ∧
      ((Finset.Ico a b).filter Nat.Prime).card =
        (fastMertensLoop a b (primeChunks.zip chunkStats2c)).2.2 := by
    intro a b ha hb
    have h1 := fastMertensLoop_sound a b ha (primeChunks.zip chunkStats2c) zip_chunks_props.2
    dsimp only at h1; rw [zip_chunks_props.1] at h1
    have hnd := primesLt27000_nodup.filter (fun q => decide (a ≤ q ∧ q < b))
    rw [filter_ico_eq_2c hb, List.sum_toFinset _ hnd, List.sum_toFinset _ hnd, List.toFinset_card_of_nodup hnd]
    exact h1
  have hpr := fun p (hp : p ∈ (Finset.Ico u v).filter Nat.Prime) => (Finset.mem_filter.mp hp).2
  rw [(hconv _ hpr).1, (hconv _ hpr).2]
  unfold fastExactMertens2c; split_ifs with hsm hu3
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsm
    rcases hsm with ⟨⟨hu3', hu43⟩, rfl⟩
    have hsplit : (Finset.Ico u 27000).filter Nat.Prime =
        (Finset.Ico u 43).filter Nat.Prime ∪ (Finset.Ico 43 27000).filter Nat.Prime := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨fun ⟨⟨h1, h2⟩, hp⟩ => if h : p < 43 then Or.inl ⟨⟨h1, h⟩, hp⟩ else Or.inr ⟨⟨by omega, h2⟩, hp⟩,
        by rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩⟩
    have hdisj : Disjoint ((Finset.Ico u 43).filter Nat.Prime) ((Finset.Ico 43 27000).filter Nat.Prime) :=
      Finset.disjoint_left.mpr fun p h1 h2 => by
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1).2
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega
    have hsm_eq : (Finset.Ico u 43).filter Nat.Prime = (smallOddPrimes2c.filter (u ≤ ·)).toFinset := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Ico, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq, smallOddPrimes2c_mem_iff]
      exact ⟨fun ⟨⟨h1, h2⟩, hp⟩ => ⟨⟨by omega, h2, hp⟩, h1⟩, fun ⟨⟨_, h2, hp⟩, h1⟩ => ⟨⟨h1, h2⟩, hp⟩⟩
    have hnd_sm : (smallOddPrimes2c.filter (u ≤ ·)).Nodup :=
      (by decide : smallOddPrimes2c.Nodup).filter _
    have hpr_sm : ∀ q ∈ smallOddPrimes2c.filter (u ≤ ·), q.Prime := fun q hq =>
      (smallOddPrimes2c_mem_iff.mp (List.mem_of_mem_filter hq)).2.2
    have htail := hloop 43 27000 (by norm_num) le_rfl; rw [tail43_mert_eq] at htail; dsimp only at htail
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj,
      hsm_eq, List.sum_toFinset _ hnd_sm, List.sum_toFinset _ hnd_sm, List.toFinset_card_of_nodup hnd_sm,
      SciProofs.add_toReal, SciProofs.add_toReal]
    exact ⟨add_le_add (chunkS1_sound hpr_sm) htail.1, add_le_add (chunkS2_sound hpr_sm) htail.2.1,
      by exact_mod_cast (by omega : (smallOddPrimes2c.filter (u ≤ ·)).length + ((Finset.Ico 43 27000).filter Nat.Prime).card ≤ (smallOddPrimes2c.filter (u ≤ ·)).length + tail43Cnt)⟩
  · have h := hloop u v hu3 hv; exact ⟨h.1, h.2.1, by exact_mod_cast h.2.2.le⟩
  · exact ⟨sum_inv_sub_one_le_exact hv 24, sum_inv_pred_sq_le_exact hv 24,
      by rw [card_ico_primes_eq_exact hv]⟩

lemma fastV2LbExact2c_sound {u v : ℕ} (hv : v ≤ 27000) :
    (fastV2LbExact2c u v).toReal ≤
      ∏ p ∈ (Finset.Ico u v).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) := by
  have hloop : ∀ a b, 3 ≤ a → b ≤ 27000 →
      (fastV2LbLoop a b (primeChunks.zip chunkStats2c)).toReal ≤
        ∏ p ∈ (Finset.Ico a b).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) := by
    intro a b ha hb
    have h1 := fastV2LbLoop_sound a b ha (primeChunks.zip chunkStats2c) zip_chunks_props.2
    rw [zip_chunks_props.1] at h1
    rw [filter_ico_eq_2c hb, List.prod_toFinset _ (primesLt27000_nodup.filter _)]; exact h1
  unfold fastV2LbExact2c; split_ifs with hsm hu3
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsm
    rcases hsm with ⟨⟨hu3', hu43⟩, rfl⟩
    have hsplit : (Finset.Ico u 27000).filter Nat.Prime =
        (Finset.Ico u 43).filter Nat.Prime ∪ (Finset.Ico 43 27000).filter Nat.Prime := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨fun ⟨⟨h1, h2⟩, hp⟩ => if h : p < 43 then Or.inl ⟨⟨h1, h⟩, hp⟩ else Or.inr ⟨⟨by omega, h2⟩, hp⟩,
        by rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩⟩
    have hdisj : Disjoint ((Finset.Ico u 43).filter Nat.Prime) ((Finset.Ico 43 27000).filter Nat.Prime) :=
      Finset.disjoint_left.mpr fun p h1 h2 => by
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h1).1).2
        have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h2).1).1; omega
    have hsm_eq : (Finset.Ico u 43).filter Nat.Prime = (smallOddPrimes2c.filter (u ≤ ·)).toFinset := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Ico, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq, smallOddPrimes2c_mem_iff]
      exact ⟨fun ⟨⟨h1, h2⟩, hp⟩ => ⟨⟨by omega, h2, hp⟩, h1⟩, fun ⟨⟨_, h2, hp⟩, h1⟩ => ⟨⟨h1, h2⟩, hp⟩⟩
    have hnd_sm : (smallOddPrimes2c.filter (u ≤ ·)).Nodup :=
      (by decide : smallOddPrimes2c.Nodup).filter _
    have hpr_sm : ∀ q ∈ smallOddPrimes2c.filter (u ≤ ·), q.Prime := fun q hq =>
      (smallOddPrimes2c_mem_iff.mp (List.mem_of_mem_filter hq)).2.2
    have htail := hloop 43 27000 (by norm_num) le_rfl; rw [tail43_vLb_eq] at htail
    have hnn_sm : 0 ≤ ((smallOddPrimes2c.filter (u ≤ ·)).map (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).prod :=
      List.prod_nonneg fun x hx => by rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩; exact (one_sub_inv_pred_2c (hpr_sm q hq)).1
    rw [hsplit, Finset.prod_union hdisj, hsm_eq, List.prod_toFinset _ hnd_sm]
    exact (SciProofs.trimLb_le _ 24).trans (by rw [SciProofs.mul_toReal]; exact mul_le_mul (chunkVLb_sound hpr_sm) htail (SciNat.toReal_nonneg _) hnn_sm)
  · exact hloop u v hu3 hv
  · exact exactProdOneSubInvPredLb_le hv 24

lemma fastV2UbExact2c_sound {u v : ℕ} (hv : v ≤ 27000) :
    ∏ p ∈ (Finset.Ico u v).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1)) ≤
      (fastV2UbExact2c u v).toReal := by
  unfold fastV2UbExact2c; split_ifs with hu3
  · have h1 := fastV2UbLoop_sound u v hu3 (primeChunks.zip chunkStats2c) zip_chunks_props.2
    rw [zip_chunks_props.1] at h1
    rw [filter_ico_eq_2c hv, List.prod_toFinset _ (primesLt27000_nodup.filter _)]; exact h1
  · exact le_exactProdOneSubInvPredUb hv 24

private lemma fastOddPrimesLoop_eq (z : ℕ) :
    ∀ (pairs : List (List ℕ × ChunkStat2c)),
      (∀ p ∈ pairs, checkOneChunk2c p = true) →
      (pairs.Pairwise (fun a b => a.2.lo ≤ b.2.lo)) →
      fastOddPrimesLoop z pairs =
        (pairs.map Prod.fst).flatten.filter (fun q => decide (3 ≤ q ∧ q < z))
  | [], _, _ => rfl
  | (c, st) :: rest, hall, hmono => by
    have h0 := hall (c, st) List.mem_cons_self
    have hcc := chunk_filter_cases (u := 3) (v := z) le_rfl h0
    have hpair := List.pairwise_cons.mp hmono
    have ih := fastOddPrimesLoop_eq z rest (fun p hp => hall p (List.mem_cons_of_mem _ hp)) hpair.2
    simp only [fastOddPrimesLoop, List.map_cons, List.flatten_cons, List.filter_append]
    split_ifs with hskip hfull
    · have hnil1 : c.filter (fun q => decide (3 ≤ q ∧ q < z)) = [] := hcc.1 (Or.inr hskip)
      have hnil2 : (rest.map Prod.fst).flatten.filter (fun q => decide (3 ≤ q ∧ q < z)) = [] :=
        List.filter_eq_nil_iff.mpr fun q hq => by
          rcases List.mem_flatten.mp hq with ⟨c', hc', hqc'⟩
          rcases List.mem_map.mp hc' with ⟨p', hp', rfl⟩
          have hlo : st.lo ≤ p'.2.lo := hpair.1 p' hp'
          have hcc' := chunk_filter_cases (u := 3) (v := z) le_rfl (hall p' (List.mem_cons_of_mem _ hp'))
          have hnil' := hcc'.1 (Or.inr (le_trans hskip hlo))
          have hnot := List.filter_eq_nil_iff.mp hnil' q hqc'
          simpa using hnot
      rw [hnil1, hnil2, List.nil_append]
    · have heq : c.filter (fun q => decide (3 ≤ q ∧ q < z)) = c.filter (3 ≤ ·) :=
        hcc.2.1 ⟨by simp only [checkOneChunk2c, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h0; omega, hfull⟩
      rw [heq, ih]
    · rw [ih]

private lemma chunkStats2c_lo_mono :
    (primeChunks.zip chunkStats2c).Pairwise (fun a b => a.2.lo ≤ b.2.lo) := by decide

lemma fastOddPrimesList2c_eq (z : ℕ) : fastOddPrimesList2c z = oddPrimesList z := by
  unfold fastOddPrimesList2c oddPrimesList
  rw [fastOddPrimesLoop_eq z (primeChunks.zip chunkStats2c) chunkStats2c_all_ok chunkStats2c_lo_mono,
    zip_chunks_props.1]

end PrimeChunksFast2c


end

end BuchstabSwitching.SieveInst
