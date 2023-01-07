-- $ cd divseq2
-- $ code .

import «Divseq2»

open Nat

axiom h₆ (l : Nat) : (16 * l + 3) + (16 * l + 3 - 3) / 8 + 1 = 18 * l + 4
theorem singleToExts (n : Nat) (p : SingleLimited (succ (succ n))) : ExtsLimited (n+2) :=
  match p with
    | SingleLimited.isSingleLimited02 l p2 => match p2 with
      | ExtsLimited.isExtsLimited09 _ p3 _ _ _ _ _ => p3
    | SingleLimited.isSingleLimited03 m p2 => match p2 with
      | ExtsLimited.isExtsLimited09 _ _ _ _ p3 _ _ => by rw [←Nat.mul_assoc 18 2 m] at p3; simp[p3]
    | SingleLimited.isSingleLimited04 m p2 => sorry
    | SingleLimited.isSingleLimited05 m p2 => sorry
    | SingleLimited.isSingleLimited06 l p2 => match p2 with
      | ExtsLimited.isExtsLimited09 _ _ _ _ _ _ p3 => have p4 := Eq.subst (h₆ l) p3; p4
    | SingleLimited.isSingleLimited07 l p2 => sorry
    | SingleLimited.isSingleLimited08 l p2 => sorry
    | SingleLimited.isSingleLimited09 l p2 => match p2 with
      | ExtsLimited.isExtsLimited09 _ _ p3 _ _ _ _ => p3
    | SingleLimited.isSingleLimited11 k p2 => match p2 with
      | ExtsLimited.isExtsLimited09 _ _ _ p3 _ _ _ => p3
    | SingleLimited.isSingleLimited12 l p2 => match p2 with
      | ExtsLimited.isExtsLimited09 _ _ _ _ _ p3 _ => by rw [←Nat.mul_assoc 9 2 l] at p3; simp[p3]
    | SingleLimited.isSingleLimited13 l p2 => sorry
    | SingleLimited.isSingleLimited14 l p2 => sorry
theorem hoge (l:Nat) (p : SingleLimited <| 18*l+6) : (ExtsLimited <| 18*l+6) := singleToExts (18 * l + 4) p

def makeLimitedDivSeq (x : Nat) : (∀ x₁, x₁ < x → SingleLimited x₁) → SingleLimited x :=
  match x with
  | 0      => fun _ => sorry
  | succ x => fun f => have foo := f 0 (Nat.lt_of_sub_eq_succ rfl); sorry --f (7 % succ x) (mod_lt _ (zero_lt_succ  _))
-- 最終的な定理
def LimitedDivSeq (n : Nat) : SingleLimited n :=
  WellFounded.fix' (measure id).wf makeLimitedDivSeq n


namespace Nat
  def gcdF2 (x : Nat) : (∀ x₁, x₁ < x → Nat → Nat) → Nat → Nat :=
    match x with
    | 0      => fun _ y => y
    | succ x => fun f y => f (y % succ x) (mod_lt _ (zero_lt_succ  _)) (succ x)
  def gcd2 (a b : @& Nat) : Nat :=
    WellFounded.fix' (measure id).wf gcdF2 a b
end Nat

def main : IO Unit :=
  IO.println s!"Hello,"



