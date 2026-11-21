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

end extendedStar
end divseq2
