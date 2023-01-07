import Mathlib.Tactic.LibrarySearch

#eval Lean.versionString

open Nat

axiom p₁ (k : Nat) :  (succ k) * 2 = succ (succ (k * 2)) 
inductive Parity : Nat → Prop where
  | even : (k : Nat) → Parity (k * 2)
  | odd  : (k : Nat) → Parity (succ (k * 2))
inductive Mod3 : Nat → Prop where
  | threeZero : (k : Nat) → Mod3 (k * 3)
  | threeOne  : (k : Nat) → Mod3 (1 + k * 3)
  | threeTwo  : (k : Nat) → Mod3 (2 + k * 3)
def parity (n : Nat) : Parity n := match n with
  | 0      => Parity.even 0
  | succ n => match (parity n) with
    | Parity.even k  => Parity.odd k
    | Parity.odd k   => by rw[←p₁]; exact Parity.even (succ k)

def allDivSeq (x:Nat) : List (List Integer) := [[]] -- TBD

inductive ExtsLimited : Nat → Prop where
  | isExtsLimited09 : (l : Nat)
      → (ExtsLimited <| 12*l+7) -- 02
      → (ExtsLimited <| 3*l+2)  -- 09
      → (ExtsLimited <| 6*l+3)  -- 11
      → (ExtsLimited <| 18*l+13)  -- 03'
      → (ExtsLimited <| 9*l+6)    -- 12'
      → (ExtsLimited <| l+(l-3)/8+1)   -- 06'
        → (ExtsLimited <| l)

inductive SingleLimited : Nat → Prop where
  | isSingleLimited01 : SingleLimited 0
  | isSingleLimited02 : (l : Nat) → (ExtsLimited <| l) → (SingleLimited <| 12*l+7)
  | isSingleLimited03 : (m : Nat) → (ExtsLimited <| 2*m) → (SingleLimited <| 36*m+13)
  | isSingleLimited04 : (m : Nat) → (ExtsLimited <| 4*m+1) → (SingleLimited <| 36*m+25)
  | isSingleLimited05 : (m : Nat) → (ExtsLimited <| 8*m+7) → (SingleLimited <| 36*m+37)
  | isSingleLimited06 : (l : Nat) → (ExtsLimited <| 16*l+3) → (SingleLimited <| 18*l+4)
  | isSingleLimited07 : (l : Nat) → (ExtsLimited <| 8*l+4) → (SingleLimited <| 18*l+10)
  | isSingleLimited08 : (l : Nat) → (ExtsLimited <| 4*l+3) → (SingleLimited <| 18*l+16)
  | isSingleLimited09 : (j : Nat) → (ExtsLimited <| j) → (SingleLimited <| 3*j+2)
  | isSingleLimited10 : SingleLimited 1
  | isSingleLimited11 : (k : Nat) → (ExtsLimited <| k) → (SingleLimited <| 6*k+3)
  | isSingleLimited12 : (l : Nat) → (ExtsLimited <| 2*l) → (SingleLimited <| 18*l+6)
  | isSingleLimited13 : (l : Nat) → (ExtsLimited <| 4*l+1) → (SingleLimited <| 18*l+12)
  | isSingleLimited14 : (l : Nat) → (ExtsLimited <| 8*l+7) → (SingleLimited <| 18*l+18)



