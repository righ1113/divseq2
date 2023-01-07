-- $ cd divseq2
-- $ code .

import «Divseq2»


namespace Nat
  def gcdF3 (x : Nat) : (∀ x₁, x₁ < x → SingleLimited x₁) → SingleLimited x :=
    match x with
    | 0      => fun _ => sorry
    | succ x => fun f => have foo := f 0 (Nat.lt_of_sub_eq_succ rfl); sorry --f (7 % succ x) (mod_lt _ (zero_lt_succ  _))
  def gcd3 (n : Nat) : SingleLimited n :=
    WellFounded.fix' (measure id).wf gcdF3 n
end Nat


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



