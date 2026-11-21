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

end extendedStar
end divseq2
