import Divseq2.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace divseq2
namespace extendedStar

/-- Rational-state formalization of the extended star conversions in `Extension.egi`. -/
structure State where
  value : ℚ
  sequence : List ℤ
deriving DecidableEq, Repr

def starA : State → Option State
  | ⟨x, y :: ys⟩ => some ⟨4 * x / 3 - 7, 6 :: (y - 4) :: ys⟩
  | _ => none

def starB : State → Option State
  | ⟨x, y :: ys⟩ => some ⟨x / 6 - 1 / 2, 1 :: (y - 2) :: ys⟩
  | _ => none

def starC : State → Option State
  | ⟨x, y :: ys⟩ => some ⟨x / 3 - 2, 4 :: (y - 4) :: ys⟩
  | _ => none

def starD : State → Option State
  | ⟨x, y :: ys⟩ => some ⟨2 * x / 3 - 1, 3 :: (y - 2) :: ys⟩
  | _ => none

def starE : State → Option State
  | ⟨x, y :: ys⟩ => some ⟨x / 12 - 3 / 4, 2 :: (y - 4) :: ys⟩
  | _ => none

def starF : State → Option State
  | ⟨x, y :: ys⟩ => some ⟨8 * x / 3 - 3, 5 :: (y - 2) :: ys⟩
  | _ => none

def starDE (s : State) : Option State := (starE s).bind starD
def starAE (s : State) : Option State := (starE s).bind starA
def starFE (s : State) : Option State := (starE s).bind starF
def starCF (s : State) : Option State := (starF s).bind starC
def starBF (s : State) : Option State := (starF s).bind starB
def starEF (s : State) : Option State := (starF s).bind starE
def starDB (s : State) : Option State := (starB s).bind starD
def starAB (s : State) : Option State := (starB s).bind starA
def starFB (s : State) : Option State := (starB s).bind starF

def extCollatz (s : State) : Option State :=
  match s.sequence with
  | [] => none
  | k :: ks => some ⟨(3 * s.value + 1) / (2 : ℚ) ^ k, ks⟩

def iterateExt : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (extCollatz s).bind (iterateExt n)

theorem extCollatz_of_factorization (n k m : Nat) (ys : List ℤ)
    (hfactor : 3 * n + 1 = 2 ^ k * m) :
    extCollatz ⟨(n : ℚ), Int.ofNat k :: ys⟩ = some ⟨(m : ℚ), ys⟩ := by
  simp only [extCollatz]
  congr 1
  simp only [State.mk.injEq]
  constructor
  · have hfactorQ : 3 * (n : ℚ) + 1 = (2 : ℚ) ^ k * m := by
      exact_mod_cast hfactor
    rw [show (2 : ℚ) ^ (Int.ofNat k) = (2 : ℚ) ^ k by simp]
    rw [hfactorQ]
    field_simp
  · trivial

theorem extCollatz_of_factorization_matches_col (n k m : Nat) (ys : List ℤ)
    (hne : n ≠ 1) (hodd : n % 2 ≠ 0)
    (hfactor : 3 * n + 1 = 2 ^ k * m) :
    extCollatz ⟨(n : ℚ), Int.ofNat k :: ys⟩ = some ⟨(m : ℚ), ys⟩ ∧
      col^[k + 1] n = m := by
  exact ⟨extCollatz_of_factorization n k m ys hfactor,
    col_iterate_odd_factorization n k m hne hodd hfactor⟩

/-- Two states are equivalent when finite extended continuations reach a common state. -/
def ExtContinuationEq (s t : State) : Prop :=
  ∃ i j u, iterateExt i s = some u ∧ iterateExt j t = some u

lemma iterateExt_add (m n : Nat) (s : State) :
    iterateExt (m + n) s = (iterateExt m s).bind (iterateExt n) := by
  induction m generalizing s with
  | zero => simp [iterateExt]
  | succ m ih =>
    simp only [Nat.succ_add, iterateExt]
    cases h : extCollatz s with
    | none => simp [h]
    | some t => simp [h, ih t]

inductive CanonicalRun : Nat → List ℤ → Nat → Nat → Prop where
  | nil (n : Nat) : CanonicalRun n [] n 0
  | cons {n m q k : Nat} {ks : List ℤ} {steps : Nat}
      (hne : n ≠ 1) (hodd : n % 2 ≠ 0)
      (hfactor : 3 * n + 1 = 2 ^ k * m) (hm : m % 2 ≠ 0)
      (tail : CanonicalRun m ks q steps) :
      CanonicalRun n (Int.ofNat k :: ks) q (k + 1 + steps)

theorem canonicalRun_iterateExt {n : Nat} {ks : List ℤ} {q steps : Nat}
    (h : CanonicalRun n ks q steps) :
    iterateExt ks.length ⟨(n : ℚ), ks⟩ = some ⟨(q : ℚ), []⟩ := by
  induction h with
  | nil n => simp [iterateExt]
  | @cons n m q k ks steps hne hodd hfactor hm tail ih =>
      rw [show (Int.ofNat k :: ks).length = 1 + ks.length by simp; omega]
      rw [iterateExt_add]
      have hstep :
          iterateExt 1 ⟨(n : ℚ), Int.ofNat k :: ks⟩ =
            some ⟨(m : ℚ), ks⟩ := by
        change
          (extCollatz ⟨(n : ℚ), Int.ofNat k :: ks⟩).bind (iterateExt 0) =
            some ⟨(m : ℚ), ks⟩
        rw [extCollatz_of_factorization n k m ks hfactor]
        simp [iterateExt]
      rw [hstep]
      simpa using ih

theorem canonicalRun_col {n : Nat} {ks : List ℤ} {q steps : Nat}
    (h : CanonicalRun n ks q steps) : col^[steps] n = q := by
  induction h with
  | nil n => simp
  | @cons n m q k ks steps hne hodd hfactor hm tail ih =>
      have hfirst :=
        col_iterate_odd_factorization n k m hne hodd hfactor
      have hadd : k + 1 + steps = steps + (k + 1) := by omega
      calc
        col^[k + 1 + steps] n =
            col^[steps] (col^[k + 1] n) := by
              rw [hadd, Function.iterate_add_apply]
        _ = q := by rw [hfirst, ih]

theorem canonicalRuns_orbitEq {n m q : Nat} {ks ls : List ℤ}
    {i j : Nat} (hn : CanonicalRun n ks q i) (hm : CanonicalRun m ls q j) :
    ∃ a b : Nat, col^[a] n = col^[b] m :=
  ⟨i, j, by rw [canonicalRun_col hn, canonicalRun_col hm]⟩

theorem SEis02CanonicalRuns_mod4_one (k r z : Nat)
    (hq : 27 * k + 11 = 2 ^ r * z) (hz : z % 2 ≠ 0) :
    ∃ i j : Nat,
      CanonicalRun (24 * k + 9) [Int.ofNat 2, Int.ofNat (r + 1)] z i ∧
      CanonicalRun (288 * k + 117) [Int.ofNat (r + 5)] z j := by
  have hlow1 : 3 * (24 * k + 9) + 1 = 2 ^ 2 * (18 * k + 7) := by omega
  have hlow2 : 3 * (18 * k + 7) + 1 = 2 ^ (r + 1) * z := by
    calc
      3 * (18 * k + 7) + 1 = 2 * (27 * k + 11) := by omega
      _ = 2 ^ (r + 1) * z := by rw [pow_succ, hq]; ring
  have hhigh : 3 * (288 * k + 117) + 1 = 2 ^ (r + 5) * z := by
    calc
      3 * (288 * k + 117) + 1 = 32 * (27 * k + 11) := by omega
      _ = 2 ^ 5 * (2 ^ r * z) := by rw [hq]; norm_num
      _ = 2 ^ (r + 5) * z := by rw [pow_add]; norm_num; ring
  refine ⟨(2 + 1) + ((r + 1) + 1), (r + 5) + 1, ?_, ?_⟩
  · apply CanonicalRun.cons
    · omega
    · omega
    · exact hlow1
    · omega
    · refine CanonicalRun.cons
        (n := 18 * k + 7) (m := z) (q := z) (k := r + 1)
        (ks := []) (steps := 0) ?_ ?_ ?_ ?_ (CanonicalRun.nil z)
      · omega
      · omega
      · exact hlow2
      · exact hz
  · refine CanonicalRun.cons
      (n := 288 * k + 117) (m := z) (q := z) (k := r + 5)
      (ks := []) (steps := 0) ?_ ?_ ?_ ?_ (CanonicalRun.nil z)
    · omega
    · omega
    · exact hhigh
    · exact hz

theorem SEis02Orbit_mod4_one_canonical (k : Nat) :
    ∃ i j : Nat,
      col^[i] (24 * k + 9) = col^[j] (288 * k + 117) := by
  have hn : 27 * k + 11 ≠ 0 := by omega
  obtain ⟨r, z, hzOdd, hq⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hz : z % 2 ≠ 0 := by
    rcases hzOdd with ⟨a, ha⟩
    omega
  obtain ⟨i, j, hL, hH⟩ := SEis02CanonicalRuns_mod4_one k r z hq hz
  exact canonicalRuns_orbitEq hL hH

theorem SEis02CanonicalRuns_mod4_three (k r z : Nat)
    (hq : 9 * k + 8 = 2 ^ r * z) (hz : z % 2 ≠ 0) :
    CanonicalRun (24 * k + 21) [Int.ofNat (r + 3)] z (r + 4) ∧
      CanonicalRun (4 * k + 3) [1, Int.ofNat (r + 1)] z (r + 4) := by
  have hlow : 3 * (24 * k + 21) + 1 = 2 ^ (r + 3) * z := by
    calc
      3 * (24 * k + 21) + 1 = 8 * (9 * k + 8) := by omega
      _ = 2 ^ (r + 3) * z := by rw [hq]; norm_num [pow_add]; ring
  have hfirst : 3 * (4 * k + 3) + 1 = 2 * (6 * k + 5) := by omega
  have hsecond : 3 * (6 * k + 5) + 1 = 2 ^ (r + 1) * z := by
    calc
      3 * (6 * k + 5) + 1 = 2 * (9 * k + 8) := by omega
      _ = 2 ^ (r + 1) * z := by rw [hq, pow_succ]; ring
  constructor
  · refine CanonicalRun.cons
      (n := 24 * k + 21) (m := z) (q := z) (k := r + 3)
      (ks := []) (steps := 0) ?_ ?_ ?_ ?_ (CanonicalRun.nil z)
    · omega
    · omega
    · exact hlow
    · exact hz
  · have hsteps : 1 + 1 + (r + 2) = r + 4 := by omega
    rw [← hsteps]
    refine CanonicalRun.cons
      (n := 4 * k + 3) (m := 6 * k + 5) (q := z) (k := 1)
      (ks := [Int.ofNat (r + 1)]) (steps := r + 2) ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · exact hfirst
    · omega
    · refine CanonicalRun.cons
        (n := 6 * k + 5) (m := z) (q := z) (k := r + 1)
        (ks := []) (steps := 0) ?_ ?_ ?_ ?_ (CanonicalRun.nil z)
      · omega
      · omega
      · exact hsecond
      · exact hz

theorem SEis02LowSeedOrbit_mod4_three (k : Nat) :
    ∃ i j : Nat, col^[i] (6 * (4 * k + 3) + 3) = col^[j] (4 * k + 3) := by
  have hpos : 9 * k + 8 ≠ 0 := by omega
  obtain ⟨r, z, hzOdd, hq⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hz : z % 2 ≠ 0 := by
    rcases hzOdd with ⟨a, ha⟩
    omega
  obtain ⟨hL, hParam⟩ := SEis02CanonicalRuns_mod4_three k r z hq hz
  have horbit := canonicalRuns_orbitEq hL hParam
  simpa only [show 6 * (4 * k + 3) + 3 = 24 * k + 21 by omega] using horbit

theorem canonicalRuns_extContinuationEq {n m q : Nat} {ks ls : List ℤ}
    {i j : Nat} (hn : CanonicalRun n ks q i) (hm : CanonicalRun m ls q j) :
    ExtContinuationEq ⟨(n : ℚ), ks⟩ ⟨(m : ℚ), ls⟩ := by
  exact ⟨ks.length, ls.length, ⟨(q : ℚ), []⟩,
    canonicalRun_iterateExt hn, canonicalRun_iterateExt hm⟩

theorem extContinuationEq_equivalence : Equivalence ExtContinuationEq where
  refl s := ⟨0, 0, s, rfl, rfl⟩
  symm := by
    rintro s t ⟨i, j, u, hs, ht⟩
    exact ⟨j, i, u, ht, hs⟩
  trans := by
    rintro s t v ⟨i, j, u, hs, htu⟩ ⟨k, l, w, htw, hv⟩
    rcases Nat.le_total j k with hjk | hkj
    · let d := k - j
      have hju : iterateExt d u = some w := by
        have h := iterateExt_add j d t
        rw [show j + d = k by simp [d, Nat.add_sub_of_le hjk], htu] at h
        simpa [htw] using h.symm
      have hs' : iterateExt (i + d) s = some w := by
        rw [iterateExt_add, hs]
        simpa using hju
      exact ⟨i + d, l, w, hs', hv⟩
    · let d := j - k
      have hwu : iterateExt d w = some u := by
        have h := iterateExt_add k d t
        rw [show k + d = j by simp [d, Nat.add_sub_of_le hkj], htw] at h
        simpa [htu] using h.symm
      have hv' : iterateExt (l + d) v = some u := by
        rw [iterateExt_add, hv]
        simpa using hwu
      exact ⟨i, l + d, u, hs, hv'⟩

lemma twoZpowAdd (a b : ℤ) :
    (2 : ℚ) ^ (a + b) = (2 : ℚ) ^ a * (2 : ℚ) ^ b :=
  zpow_add₀ (by norm_num) a b

theorem starE_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starE ⟨x, y :: ys⟩).bind (iterateExt 2) := by
  simp [iterateExt, extCollatz, starE]
  rw [show y = (-4 + y) + 4 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starC_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starC ⟨x, y :: ys⟩).bind (iterateExt 2) := by
  simp [iterateExt, extCollatz, starC]
  rw [show y = (-4 + y) + 4 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starB_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starB ⟨x, y :: ys⟩).bind (iterateExt 2) := by
  simp [iterateExt, extCollatz, starB]
  rw [show y = (-2 + y) + 2 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starDE_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starDE ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starDE, starE, starD]
  rw [show y = (-4 + y) + 4 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starAE_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starAE ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starAE, starE, starA]
  rw [show y = (-4 + y) + 4 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starFE_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starFE ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starFE, starE, starF]
  rw [show y = (-4 + y) + 4 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starCF_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starCF ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starCF, starF, starC]
  rw [show y = (-2 + y) + 2 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starBF_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starBF ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starBF, starF, starB]
  rw [show y = (-2 + y) + 2 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starEF_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starEF ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starEF, starF, starE]
  rw [show y = (-2 + y) + 2 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starDB_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starDB ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starDB, starB, starD]
  rw [show y = (-2 + y) + 2 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starAB_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starAB ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starAB, starB, starA]
  rw [show y = (-2 + y) + 2 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

theorem starFB_orbit (x : ℚ) (y : ℤ) (ys : List ℤ) :
    iterateExt 1 ⟨x, y :: ys⟩ =
      (starFB ⟨x, y :: ys⟩).bind (iterateExt 3) := by
  simp [iterateExt, extCollatz, starFB, starB, starF]
  rw [show y = (-2 + y) + 2 by omega, twoZpowAdd]
  norm_num
  field_simp
  ring

lemma iterateExt_one_success {s : State} (hne : s.sequence ≠ []) :
    ∃ u, iterateExt 1 s = some u := by
  cases s with
  | mk x sequence =>
    cases sequence with
    | nil => contradiction
    | cons k ks =>
      exact ⟨⟨(3 * x + 1) / (2 : ℚ) ^ k, ks⟩, by
        simp [iterateExt, extCollatz]⟩

lemma extContinuationEq_of_one_eq {s t : State} {n : Nat}
    (hne : s.sequence ≠ [])
    (h : iterateExt 1 s = iterateExt n t) :
    ExtContinuationEq s t := by
  obtain ⟨u, hu⟩ := iterateExt_one_success hne
  exact ⟨1, n, u, hu, h.symm.trans hu⟩

theorem starE_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starE ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starE_orbit x y ys

theorem starC_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starC ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starC_orbit x y ys

theorem starB_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starB ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starB_orbit x y ys

theorem starDE_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starDE ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starDE_orbit x y ys

theorem starAE_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starAE ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starAE_orbit x y ys

theorem starFE_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starFE ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starFE_orbit x y ys

theorem starCF_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starCF ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starCF_orbit x y ys

theorem starBF_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starBF ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starBF_orbit x y ys

theorem starEF_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starEF ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starEF_orbit x y ys

theorem starDB_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starDB ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starDB_orbit x y ys

theorem starAB_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starAB ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starAB_orbit x y ys

theorem starFB_preserves_continuation (x : ℚ) (y : ℤ) (ys : List ℤ)
    (t : State) (ht : starFB ⟨x, y :: ys⟩ = some t) :
    ExtContinuationEq ⟨x, y :: ys⟩ t := by
  apply extContinuationEq_of_one_eq (by simp)
  simpa [ht] using starFB_orbit x y ys

/-- One of the extended star conversions from the paper, or an identity step. -/
inductive ExtendedStarStep : State → State → Prop where
  | refl (s : State) : ExtendedStarStep s s
  | e (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starE ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | c (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starC ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | b (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starB ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | de (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starDE ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | ae (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starAE ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | fe (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starFE ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | cf (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starCF ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | bf (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starBF ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | ef (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starEF ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | db (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starDB ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | ab (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starAB ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t
  | fb (x : ℚ) (y : ℤ) (ys : List ℤ) (t : State)
      (h : starFB ⟨x, y :: ys⟩ = some t) :
      ExtendedStarStep ⟨x, y :: ys⟩ t

theorem extendedStar_preserves_continuation {s t : State}
    (h : ExtendedStarStep s t) : ExtContinuationEq s t := by
  cases h with
  | refl s => exact extContinuationEq_equivalence.1 s
  | e x y ys t ht => exact starE_preserves_continuation x y ys t ht
  | c x y ys t ht => exact starC_preserves_continuation x y ys t ht
  | b x y ys t ht => exact starB_preserves_continuation x y ys t ht
  | de x y ys t ht => exact starDE_preserves_continuation x y ys t ht
  | ae x y ys t ht => exact starAE_preserves_continuation x y ys t ht
  | fe x y ys t ht => exact starFE_preserves_continuation x y ys t ht
  | cf x y ys t ht => exact starCF_preserves_continuation x y ys t ht
  | bf x y ys t ht => exact starBF_preserves_continuation x y ys t ht
  | ef x y ys t ht => exact starEF_preserves_continuation x y ys t ht
  | db x y ys t ht => exact starDB_preserves_continuation x y ys t ht
  | ab x y ys t ht => exact starAB_preserves_continuation x y ys t ht
  | fb x y ys t ht => exact starFB_preserves_continuation x y ys t ht

theorem starB_connects_SEis02_mod4_three (k r : Nat) :
    ExtendedStarStep
      ⟨24 * (k : ℚ) + 21, [Int.ofNat (r + 3)]⟩
      ⟨4 * (k : ℚ) + 3, [1, Int.ofNat (r + 1)]⟩ := by
  apply ExtendedStarStep.b
  simp only [starB, Option.some.injEq, State.mk.injEq]
  constructor
  · norm_num
    ring
  · simp only [List.cons.injEq]
    constructor
    · trivial
    · constructor
      · have h : r + 3 = (r + 1) + 2 := by omega
        change ((r + 3 : Nat) : Int) - 2 = ((r + 1 : Nat) : Int)
        rw [h]
        simp only [Int.natCast_add]
        norm_num
      · trivial

theorem SEis02StarBBranch_mod4_three (k r z : Nat)
    (hq : 9 * k + 8 = 2 ^ r * z) (hz : z % 2 ≠ 0) :
    ExtendedStarStep
        ⟨24 * (k : ℚ) + 21, [Int.ofNat (r + 3)]⟩
        ⟨4 * (k : ℚ) + 3, [1, Int.ofNat (r + 1)]⟩ ∧
      ∃ i j : Nat,
        col^[i] (24 * k + 21) = col^[j] (4 * k + 3) := by
  obtain ⟨hL, hParam⟩ := SEis02CanonicalRuns_mod4_three k r z hq hz
  exact ⟨starB_connects_SEis02_mod4_three k r,
    canonicalRuns_orbitEq hL hParam⟩

theorem SEis02Orbit_mod4_three_of_intermediateOrbit (k : Nat)
    (h : ∃ i j : Nat,
      col^[i] (9 * k + 8) = col^[j] (54 * k + 49)) :
    ∃ i j : Nat,
      col^[i] (24 * k + 21) = col^[j] (288 * k + 261) := by
  have hlow : col^[4] (24 * k + 21) = 9 * k + 8 :=
    col_iterate_odd_factorization _ 3 _ (by omega) (by omega) (by omega)
  have hhigh : col^[5] (288 * k + 261) = 54 * k + 49 :=
    col_iterate_odd_factorization _ 4 _ (by omega) (by omega) (by omega)
  obtain ⟨i, j, hij⟩ := h
  refine ⟨i + 4, j + 5, ?_⟩
  calc
    col^[i + 4] (24 * k + 21) =
        col^[i] (col^[4] (24 * k + 21)) := by
          rw [Function.iterate_add_apply]
    _ = col^[i] (9 * k + 8) := by rw [hlow]
    _ = col^[j] (54 * k + 49) := hij
    _ = col^[j] (col^[5] (288 * k + 261)) := by rw [hhigh]
    _ = col^[j + 5] (288 * k + 261) := by
          rw [Function.iterate_add_apply]

theorem SEis02Orbit_mod4_two_of_residualOrbit (k : Nat)
    (h : ∃ i j : Nat,
      col^[i] (36 * k + 23) = col^[j] (108 * k + 71)) :
    ∃ i j : Nat,
      col^[i] (24 * k + 15) = col^[j] (288 * k + 189) := by
  have hlow : col^[2] (24 * k + 15) = 36 * k + 23 := by
    have hfirst : col (24 * k + 15) = 72 * k + 46 := by
      simp [col, show 24 * k + 15 ≠ 1 by omega,
        show (24 * k + 15) % 2 ≠ 0 by omega]
      omega
    have hsecond : col (72 * k + 46) = 36 * k + 23 := by
      simp [col, show 72 * k + 46 ≠ 1 by omega,
        show (72 * k + 46) % 2 = 0 by omega]
      omega
    calc
      col^[2] (24 * k + 15) =
          col (col (24 * k + 15)) := by
            rw [Function.iterate_succ_apply]
            simp
      _ = col (72 * k + 46) := by rw [hfirst]
      _ = 36 * k + 23 := hsecond
  have hhigh : col^[4] (288 * k + 189) = 108 * k + 71 := by
    have h1 : col (288 * k + 189) = 864 * k + 568 := by
      simp [col, show 288 * k + 189 ≠ 1 by omega,
        show (288 * k + 189) % 2 ≠ 0 by omega]
      omega
    have h2 : col (864 * k + 568) = 432 * k + 284 := by
      simp [col, show 864 * k + 568 ≠ 1 by omega,
        show (864 * k + 568) % 2 = 0 by omega]
      omega
    have h3 : col (432 * k + 284) = 216 * k + 142 := by
      simp [col, show 432 * k + 284 ≠ 1 by omega,
        show (432 * k + 284) % 2 = 0 by omega]
      omega
    have h4 : col (216 * k + 142) = 108 * k + 71 := by
      simp [col, show 216 * k + 142 ≠ 1 by omega,
        show (216 * k + 142) % 2 = 0 by omega]
      omega
    calc
      col^[4] (288 * k + 189) =
          col^[3] (864 * k + 568) := by
            rw [Function.iterate_succ_apply, h1]
      _ = col^[2] (432 * k + 284) := by
            rw [Function.iterate_succ_apply, h2]
      _ = col (216 * k + 142) := by
            rw [Function.iterate_succ_apply, h3]
            simp
      _ = 108 * k + 71 := h4
  obtain ⟨i, j, hij⟩ := h
  refine ⟨i + 2, j + 4, ?_⟩
  calc
    col^[i + 2] (24 * k + 15) =
        col^[i] (col^[2] (24 * k + 15)) := by
          rw [Function.iterate_add_apply]
    _ = col^[i] (36 * k + 23) := by rw [hlow]
    _ = col^[j] (108 * k + 71) := hij
    _ = col^[j] (col^[4] (288 * k + 189)) := by rw [hhigh]
    _ = col^[j + 4] (288 * k + 189) := by
          rw [Function.iterate_add_apply]

inductive ExtendedStarPath : State → State → Prop where
  | refl (s : State) : ExtendedStarPath s s
  | step {s t u : State} :
      ExtendedStarStep s t → ExtendedStarPath t u → ExtendedStarPath s u

theorem extendedStarPath_preserves_continuation {s t : State}
    (h : ExtendedStarPath s t) : ExtContinuationEq s t := by
  induction h with
  | refl s => exact extContinuationEq_equivalence.1 s
  | step hstep _ ih =>
      exact extContinuationEq_equivalence.trans
        (extendedStar_preserves_continuation hstep) ih

theorem starE_connects_SEis02Seeds (l : Nat) (y : ℤ) (ys : List ℤ) :
    ExtendedStarStep
      ⟨6 * (12 * (l : ℚ) + 7) + 3, y :: ys⟩
      ⟨6 * (l : ℚ) + 3, 2 :: (y - 4) :: ys⟩ := by
  apply ExtendedStarStep.e
  simp [starE]
  ring

theorem SEis02Seeds_extContinuationEq (l : Nat) (y : ℤ) (ys : List ℤ) :
    ExtContinuationEq
      ⟨6 * (12 * (l : ℚ) + 7) + 3, y :: ys⟩
      ⟨6 * (l : ℚ) + 3, 2 :: (y - 4) :: ys⟩ :=
  extendedStar_preserves_continuation (starE_connects_SEis02Seeds l y ys)

end extendedStar
end divseq2
