-- $ cd divseq2
-- $ code .

import «Divseq2»

open Nat

namespace divseq2
  axiom h₀₃ (m : Nat) : 18 * (2 * m) + 13 = succ (succ (m * 3 * 2) * 2) * 3 + 2 + 2
  axiom h₀₆ (l : Nat) : (16 * l + 3) + (16 * l + 3 - 3) / 8 + 1 = 18 * l + 4
  axiom h₁₂ (l : Nat) : 9 * (2 * l) + 6 = (succ (l * 3 * 2)) * 3 + 1 + 2
  -- 十分条件
  theorem singleToExts (n : Nat) (p : SingleLimited (succ (succ n))) : ExtsLimited (n+2) := match p with
    | SingleLimited.is02 l p2 => match p2 with
      | ExtsLimited.is09 _ p3 _ _ _ _ _ => p3
    | SingleLimited.is03 m p2 => match p2 with
      | ExtsLimited.is09 _ _ _ _ p3 _ _ => have p4 := Eq.subst (h₀₃ m) p3; p4
    | SingleLimited.is04 m p2 => sorry
    | SingleLimited.is05 m p2 => sorry
    | SingleLimited.is06 l p2 => match p2 with
      | ExtsLimited.is09 _ _ _ _ _ _ p3 => have p4 := Eq.subst (h₀₆ l) p3; p4
    | SingleLimited.is07 l p2 => sorry
    | SingleLimited.is08 l p2 => sorry
    | SingleLimited.is09 l p2 => match p2 with
      | ExtsLimited.is09 _ _ p3 _ _ _ _ => p3
    | SingleLimited.is11 k p2 => match p2 with
      | ExtsLimited.is09 _ _ _ p3 _ _ _ => p3
    | SingleLimited.is12 l p2 => match p2 with
      | ExtsLimited.is09 _ _ _ _ _ p3 _ => have p4 := Eq.subst (h₁₂ l) p3; p4
    | SingleLimited.is13 l p2 => sorry
    | SingleLimited.is14 l p2 => sorry

  axiom m₀₂₁ (l : Nat) : succ (succ (l - 2)) < succ (succ (succ (succ (succ (l * 2 * 2) * 3))))
  axiom m₀₃₁ (m : Nat) : succ (succ (2 * (m - 1))) < succ (succ (succ (succ (succ (succ (m * 3 * 2) * 2) * 3))))
  axiom m₀₃₂ (m : Nat) : 2 * (m - 1) + 2 = 2* m
  axiom m₀₉₁ (j : Nat) : succ (succ (j - 2)) < succ (succ (j * 3))
  axiom m₀₉₂ (j : Nat) : j - 2 + 2 = j
  axiom m₁₁₁ (k : Nat) : succ (succ (k - 2)) < succ (succ (succ (k * 2 * 3)))
  axiom m₁₂₁ (l : Nat) : succ (succ (2 * (l - 1))) < succ (succ (succ (succ (l * 3 * 2) * 3)))
  def makeLimitedDivSeq (x : Nat) (rs : ∀ x₁, x₁ < x → SingleLimited x₁) : SingleLimited x := match x with
    | 0             => SingleLimited.is10 -- 6*<0>+3 = 3
    | 1             => SingleLimited.is01 -- 6*<1>+3 = 9
    | succ (succ x) => by cases (mod3 x) with
      -- 6 mod 9
      | threeZero j =>
          have sin := rs (succ (succ (j - 2))) (m₀₉₁ j); have ext := singleToExts (j - 2) sin; rw [m₀₉₂ j] at ext;
          exact SingleLimited.is09 j ext;
      -- 3 mod 9
      | threeOne j  => cases (parity j) with
        | even k =>
            have sin := rs (succ (succ (k - 2))) (m₁₁₁ k); have ext := singleToExts (k - 2) sin; rw [m₀₉₂ k] at ext;
            exact SingleLimited.is11 k ext;
        | odd k  => cases (mod3 k) with
          | threeZero l =>
              have sin := rs (succ (succ (2 * (l - 1)))) (m₁₂₁ l);
              have ext := singleToExts (2 * (l - 1)) sin; rw [m₀₃₂ l] at ext;
              exact SingleLimited.is12 l ext;
          | threeOne l  => sorry
          | threeTwo l  => sorry
      -- 0 mod 9
      | threeTwo j  => cases (parity j) with
        | even k => cases (mod3 k) with
          | threeZero l => sorry
          | threeOne l  => sorry
          | threeTwo l  => sorry
        | odd k  => cases (parity k) with
          | even l =>
              have sin := rs (succ (succ (l - 2))) (m₀₂₁ l); have ext := singleToExts (l - 2) sin; rw [m₀₉₂ l] at ext;
              exact SingleLimited.is02 l ext;
          | odd l  => cases (mod3 l) with
            | threeZero m =>
                have sin := rs (succ (succ (2 * (m - 1)))) (m₀₃₁ m);
                have ext := singleToExts (2 * (m - 1)) sin; rw [m₀₃₂ m] at ext;
                exact SingleLimited.is03 m ext;
            | threeOne m  => sorry
            | threeTwo m  => sorry
  -- 最終的な定理
  def LimitedDivSeq (n : Nat) : SingleLimited n := WellFounded.fix' (measure id).wf makeLimitedDivSeq n
end divseq2



def main : IO Unit :=
  IO.println s!"Hello,"



