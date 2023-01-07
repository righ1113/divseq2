import Mathlib.Tactic.LibrarySearch

#eval Lean.versionString

open Nat

axiom p₁ (k : Nat) : (succ k) * 2 = succ (succ (k * 2))
axiom m₁ (k : Nat) : (succ k) * 3 = succ (succ (succ (k * 3)))
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

def allDivSeq (x:Nat) : List (List Integer) := [[]] -- TBD

inductive ExtsLimited : Nat → Prop where
  | is09 : (l : Nat)
      → (ExtsLimited <| 12*l+7) -- 02
      → (ExtsLimited <| 3*l+2)  -- 09
      → (ExtsLimited <| 6*l+3)  -- 11
      → (ExtsLimited <| 18*l+13)  -- 03'
      → (ExtsLimited <| 9*l+6)    -- 12'
      → (ExtsLimited <| l+(l-3)/8+1)   -- 06'
        → (ExtsLimited <| l)

inductive SingleLimited : Nat → Prop where
  | is01 : SingleLimited 1
  | is02 : (l : Nat) → (ExtsLimited <| l) → (SingleLimited <| 12*l+7)
  | is03 : (m : Nat) → (ExtsLimited <| 2*m) → (SingleLimited <| 36*m+13)
  | is04 : (m : Nat) → (ExtsLimited <| 4*m+1) → (SingleLimited <| 36*m+25)
  | is05 : (m : Nat) → (ExtsLimited <| 8*m+7) → (SingleLimited <| 36*m+37)
  | is06 : (l : Nat) → (ExtsLimited <| 16*l+3) → (SingleLimited <| 18*l+4)
  | is07 : (l : Nat) → (ExtsLimited <| 8*l+4) → (SingleLimited <| 18*l+10)
  | is08 : (l : Nat) → (ExtsLimited <| 4*l+3) → (SingleLimited <| 18*l+16)
  | is09 : (j : Nat) → (ExtsLimited <| j) → (SingleLimited <| succ (succ (j*3)))
  | is10 : SingleLimited 0
  | is11 : (k : Nat) → (ExtsLimited <| k) → (SingleLimited <| 6*k+3)
  | is12 : (l : Nat) → (ExtsLimited <| 2*l) → (SingleLimited <| 18*l+6)
  | is13 : (l : Nat) → (ExtsLimited <| 4*l+1) → (SingleLimited <| 18*l+12)
  | is14 : (l : Nat) → (ExtsLimited <| 8*l+7) → (SingleLimited <| 18*l+18)



