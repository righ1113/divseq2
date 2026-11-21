import Mathlib.Tactic.Linarith
import Mathlib.Data.Seq.Seq

-- #eval Lean.versionString

set_option linter.unusedVariables false

open Nat

lemma p₁ (k : Nat) : (succ k) * 2 = succ (succ (k * 2))        := succ_mul_succ_eq k 1
lemma m₁ (k : Nat) : (succ k) * 3 = succ (succ (succ (k * 3))) := succ_mul_succ_eq k 2
inductive Parity : Nat → Prop where
  | even : (k : Nat) → Parity (k * 2)
  | odd  : (k : Nat) → Parity (succ (k * 2))
inductive Mod3 : Nat → Prop where
  | threeZero : (k : Nat) → Mod3 (k * 3)
  | threeOne  : (k : Nat) → Mod3 (succ (k * 3))
  | threeTwo  : (k : Nat) → Mod3 (succ (succ (k * 3)))
def parity (n : Nat) : Parity n := match n with
  | 0      => Parity.even 0
  | succ n => match (parity n) with
    | Parity.even k  => Parity.odd k
    | Parity.odd k   => by rw[←p₁]; exact Parity.even (succ k)
def mod3 (n : Nat) : Mod3 n := match n with
  | 0      => Mod3.threeZero 0
  | succ n => match (mod3 n) with
    | Mod3.threeZero k => Mod3.threeOne k
    | Mod3.threeOne k  => Mod3.threeTwo k
    | Mod3.threeTwo k  => by rw[←m₁]; exact Mod3.threeZero (succ k)

def col (x : Nat) : Nat := if x = 1 then 1 else if x % 2 = 0 then x / 2 else 3 * x + 1

lemma col_two_mul (n : Nat) : col (2 * n) = n := by
  have hne : 2 * n ≠ 1 := by omega
  simp [col, hne]

lemma col_iterate_two_pow_mul (k m : Nat) : col^[k] (2 ^ k * m) = m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have h : col (2 ^ (k + 1) * m) = 2 ^ k * m := by
        rw [pow_succ]
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          col_two_mul (2 ^ k * m)
      rw [h]
      exact ih

lemma col_iterate_odd_factorization (n k m : Nat)
    (hne : n ≠ 1) (hodd : n % 2 ≠ 0)
    (hfactor : 3 * n + 1 = 2 ^ k * m) :
    col^[k + 1] n = m := by
  rw [Function.iterate_succ_apply]
  have hcol : col n = 3 * n + 1 := by
    simp [col, hne, hodd]
  rw [hcol, hfactor]
  exact col_iterate_two_pow_mul k m

inductive ExtsLimited : Nat → Prop where -- コラッツ操作で 1 に到達すれば、完全割数列が有限長
  | is : (t u : Nat) -> col^[u + 1] (6 * t + 3) = 1 -> ExtsLimited t
lemma is01 : ExtsLimited 1 := ExtsLimited.is _ 18 (by native_decide)
lemma is10 : ExtsLimited 0 := ExtsLimited.is _ 6 (by native_decide)

inductive SingleLimited : Nat → Prop where
  | is02 : (l : Nat) → (ExtsLimited <| l)      → (SingleLimited <| succ (succ (succ (succ ((succ (l * 2 * 2)) * 3)))))
  | is03 : (m : Nat) → (ExtsLimited <| 2*m)    → (SingleLimited <| succ (succ (succ (succ ((succ ((succ (m * 3 * 2)) * 2)) * 3)))))
  | is04 : (m : Nat) → (ExtsLimited <| 4*m+1)  → (SingleLimited <| succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3)))))
  | is05 : (m : Nat) → (ExtsLimited <| 8*m+7)  → (SingleLimited <| succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3)))))
  | is06 : (l : Nat) → (ExtsLimited <| 16*l+3) → (SingleLimited <| succ (succ (succ (succ (l * 3 * 2 * 3)))))
  | is07 : (l : Nat) → (ExtsLimited <| 8*l+4)  → (SingleLimited <| succ (succ (succ (succ (((succ (l * 3)) * 2) * 3)))))
  | is08 : (l : Nat) → (ExtsLimited <| 4*l+3)  → (SingleLimited <| succ (succ (succ (succ (((succ (succ (l * 3))) * 2) * 3)))))
  | is09 : (j : Nat) → (ExtsLimited <| j)      → (SingleLimited <| succ (succ (j*3)))
  | is11 : (k : Nat) → (ExtsLimited <| k)      → (SingleLimited <| succ (succ (succ (k * 2 * 3))))
  | is12 : (l : Nat) → (ExtsLimited <| 2*l)    → (SingleLimited <| succ (succ (succ ((succ (l * 3 * 2)) * 3))))
  | is13 : (l : Nat) → (ExtsLimited <| 4*l+1)  → (SingleLimited <| succ (succ (succ (succ (succ (l * 3) * 2) * 3))))
  | is14 : (l : Nat) → (ExtsLimited <| 8*l+7)  → (SingleLimited <| succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3))))
  | is01_2 : ExtsLimited 1 → SingleLimited 1
  | is10_2 : ExtsLimited 0 → SingleLimited 0
