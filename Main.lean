-- $ cd divseq2
-- $ code .

import «Divseq2»

open Nat

namespace divseq2
  theorem h₀₃ (m : Nat) : 18 * (2 * m) + 11 = (succ ((succ (m * 3 * 2)) * 2)) * 3 + 2 := by linarith
  theorem h₀₄ (m : Nat) : 9 * (4 * m + 1) + 14 = (succ (succ (succ (m * 3) * 2) * 2)) * 3 + 2 := by linarith
  axiom   h₀₅ (m : Nat) : (9 * (8 * m + 7 - 2) + 25) / 2 = (succ (succ (succ (succ (m * 3)) * 2) * 2)) * 3 + 2
  axiom   h₀₆ (l : Nat) : (16 * l + 3 - 2) + (16 * l + 3 - 2 - 1) / 8 + 1 = l * 3 * 2 * 3 + 2
  axiom   h₀₇ (l : Nat) : 8 * l + 4 - 2 + (8 * l + 4 - 2 - 2) / 4 * 5 + 6 = (succ (l * 3)) * 2 * 3 + 2
  axiom   h₀₈ (l : Nat) : 4 * (4 * l + 3 - 2) + (4 * l + 3 - 2 - 1) / 2 + 10 = (succ (succ (l * 3))) * 2 * 3 + 2
  axiom   h₀₉ (j : Nat) : (j - 2) * 3 + 6 = j * 3
  theorem h₁₂ (l : Nat) : 9 * (2 * l) + 4 = (succ (l * 3 * 2)) * 3 + 1 := by linarith
  axiom   h₁₃ (l : Nat) : (9 * (4 * l + 1) + 11) / 2 = (succ (succ (l * 3) * 2)) * 3 + 1
  axiom   h₁₄ (l : Nat) : (9 * (8 * l + 7) + 1) / 4 = (succ ((succ (succ (l * 3))) * 2)) * 3 + 1
  -- 十分条件
  theorem singleToExts (n : Nat) (p : SingleLimited (succ (succ n))) : ExtsLimited (n) := match p with
    | SingleLimited.is02 _ p2 => match p2 with
      | ExtsLimited.is _ _ p3 _ _ _ _ _ _ _ _ _ _ _ => p3
    | SingleLimited.is03 m p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ p3 _ _ _ _ _ _ _ _ => have p4 := Eq.subst (h₀₃ m) p3; p4
    | SingleLimited.is04 m p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ _ _ p3 _ _ _ => have p4 := Eq.subst (h₀₄ m) p3; p4
    | SingleLimited.is05 m p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ _ _ _ p3 _ _ => have p4 := Eq.subst (h₀₅ m) p3; p4
    | SingleLimited.is06 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ p3 _ _ _ _ _ _ => have p4 := Eq.subst (h₀₆ l) p3; p4
    | SingleLimited.is07 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ p3 _ _ _ _ _ => have p4 := Eq.subst (h₀₇ l) p3; p4
    | SingleLimited.is08 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ _ p3 _ _ _ _ => have p4 := Eq.subst (h₀₈ l) p3; p4
    | SingleLimited.is09 j p2 => match p2 with
      | ExtsLimited.is _ _ _ p3 _ _ _ _ _ _ _ _ _ _ => have p4 := Eq.subst (h₀₉ j) p3; p4
    | SingleLimited.is11 _ p2 => match p2 with
      | ExtsLimited.is _ _ _ _ p3 _ _ _ _ _ _ _ _ _ => p3
    | SingleLimited.is12 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ p3 _ _ _ _ _ _ _ => have p4 := Eq.subst (h₁₂ l) p3; p4
    | SingleLimited.is13 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ _ _ _ _ p3 _ => have p4 := Eq.subst (h₁₃ l) p3; p4
    | SingleLimited.is14 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ _ _ _ _ _ p3 => have p4 := Eq.subst (h₁₄ l) p3; p4

  axiom   m₀₂₁ (l : Nat) : succ (succ (l + 2 - 2)) < succ (succ (succ (succ (succ (l * 2 * 2) * 3))))
  axiom   m₀₃₁ (m : Nat) : succ (succ (2 * m + 2 - 2)) < succ (succ (succ (succ (succ (succ (m * 3 * 2) * 2) * 3))))
  theorem m₀₃₂ (m : Nat) : 2 * m + 2 - 2 = 2* m := rfl
  axiom   m₀₄₁ (m : Nat) : succ (succ (4 * m + 1 + 2 - 2)) < succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3))))
  theorem m₀₄₂ (m : Nat) : 4 * m + 1 + 2 - 2 = 4 * m + 1 := rfl
  axiom   m₀₅₁ (m : Nat) : succ (succ (8 * m + 7 - 2)) < succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3))))
  -- theorem m₀₅₂ (m : Nat) : 8 * m + 7 - 2 + 2 = 8 * m + 7 := rfl
  axiom   m₀₆₁ (l : Nat) : succ (succ (16 * l + 3 - 2)) < succ (succ (succ (succ (l * 3 * 2 * 3))))
  -- theorem m₀₆₂ (l : Nat) : 16 * l + 3 + 2 - 2 = 16 * l + 3 := rfl
  axiom   m₀₇₁ (l : Nat) : succ (succ (8 * l + 4 - 2)) < succ (succ (succ (succ (succ (l * 3) * 2 * 3))))
  -- theorem m₀₇₂ (l : Nat) : 8 * l + 4 - 2 + 2 = 8 * l + 4 := rfl
  axiom   m₀₈₁ (l : Nat) : succ (succ (4 * l + 3 - 2)) < succ (succ (succ (succ (succ (succ (l * 3)) * 2 * 3))))
  -- theorem m₀₈₂ (l : Nat) : 4 * l + 3 - 2 + 2 = 4 * l + 3 := rfl
  axiom   m₀₉₁ (j : Nat) : succ (succ (j - 2)) < succ (succ (j * 3))
  theorem m₀₉₂ (j : Nat) : j + 2 - 2 = j := rfl
  axiom   m₁₁₁ (k : Nat) : succ (succ (k + 2 - 2)) < succ (succ (succ (k * 2 * 3)))
  axiom   m₁₂₁ (l : Nat) : succ (succ (2 * l + 2 - 2)) < succ (succ (succ (succ (l * 3 * 2) * 3)))
  axiom   m₁₃₁ (l : Nat) : succ (succ (4 * l + 1 + 2 - 2)) < succ (succ (succ (succ (succ (l * 3) * 2) * 3)))
  theorem m₁₃₂ (l : Nat) : 4 * l + 1 + 2 - 2 = 4 * l + 1 := rfl
  axiom   m₁₄₁ (l : Nat) : succ (succ (8 * l + 7 + 2 - 2)) < succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3)))
  theorem m₁₄₂ (l : Nat) : 8 * l + 7 + 2 - 2 = 8 * l + 7 := rfl
  def makeLimitedDivSeq (x : Nat) (rs : ∀ x₁, x₁ < x → SingleLimited x₁) : SingleLimited x := match x with
    | 0             => SingleLimited.is10 -- 6*<0>+3 = 3
    | 1             => SingleLimited.is01 -- 6*<1>+3 = 9
    | succ (succ x) => by have rs := rs; cases (mod3 x) with
      -- 6 mod 9
      | threeZero j =>
          have sin := rs (succ (succ (j - 2))) (m₀₉₁ j); have ext := singleToExts (j - 2) sin; --rw [m₀₉₂ j] at ext;
          exact SingleLimited.is09 j ext;
      -- 3 mod 9
      | threeOne j  => cases (parity j) with
        | even k =>
            have sin := rs (succ (succ (k + 2 - 2))) (m₁₁₁ k); have ext := singleToExts (k + 2 - 2) sin; rw [m₀₉₂ k] at ext;
            exact SingleLimited.is11 k ext;
        | odd k  => cases (mod3 k) with
          | threeZero l =>
              have sin := rs (succ (succ (2 * l + 2 - 2))) (m₁₂₁ l);
              have ext := singleToExts (2 * l + 2 - 2) sin; rw [m₀₃₂ l] at ext;
              exact SingleLimited.is12 l ext;
          | threeOne l  =>
              have sin := rs (succ (succ (4 * l + 1 + 2 - 2))) (m₁₃₁ l);
              have ext := singleToExts (4 * l + 1 + 2 - 2) sin; rw [m₁₃₂ l] at ext;
              exact SingleLimited.is13 l ext;
          | threeTwo l  =>
              have sin := rs (succ (succ (8 * l + 7 + 2 - 2))) (m₁₄₁ l);
              have ext := singleToExts (8 * l + 7 + 2 - 2) sin; rw [m₁₄₂ l] at ext;
              exact SingleLimited.is14 l ext;
      -- 0 mod 9
      | threeTwo j  => cases (parity j) with
        | even k => cases (mod3 k) with
          | threeZero l =>
              have sin := rs (succ (succ (16 * l + 3 - 2))) (m₀₆₁ l);
              have ext := singleToExts (16 * l + 3 - 2) sin; --rw [m₀₆₂ l] at ext;
              exact SingleLimited.is06 l ext;
          | threeOne l  =>
              have sin := rs (succ (succ (8 * l + 4 - 2))) (m₀₇₁ l);
              have ext := singleToExts (8 * l + 4 - 2) sin; --rw [m₀₇₂ l] at ext;
              exact SingleLimited.is07 l ext;
          | threeTwo l  =>
              have sin := rs (succ (succ (4 * l + 3 - 2))) (m₀₈₁ l);
              have ext := singleToExts (4 * l + 3 - 2) sin; --rw [m₀₈₂ l] at ext;
              exact SingleLimited.is08 l ext;
        | odd k  => cases (parity k) with
          | even l =>
              have sin := rs (succ (succ (l + 2 - 2))) (m₀₂₁ l);
              have ext := singleToExts (l + 2 - 2) sin; rw [m₀₉₂ l] at ext;
              exact SingleLimited.is02 l ext;
          | odd l  => cases (mod3 l) with
            | threeZero m =>
                have sin := rs (succ (succ (2 * m + 2 - 2))) (m₀₃₁ m);
                have ext := singleToExts (2 * m + 2 - 2) sin; rw [m₀₃₂ m] at ext;
                exact SingleLimited.is03 m ext;
            | threeOne m  =>
                have sin := rs (succ (succ (4 * m + 1 + 2 - 2))) (m₀₄₁ m);
                have ext := singleToExts (4 * m + 1 + 2 - 2) sin; rw [m₀₄₂ m] at ext;
                exact SingleLimited.is04 m ext;
            | threeTwo m  =>
                have sin := rs (succ (succ (8 * m + 7 - 2))) (m₀₅₁ m);
                have ext := singleToExts (8 * m + 7 - 2) sin; --rw [m₀₅₂ m] at ext;
                exact SingleLimited.is05 m ext;
  -- 最終的な定理
  def LimitedDivSeq (n : Nat) : SingleLimited n := WellFounded.fix' (measure id).wf makeLimitedDivSeq n
end divseq2



def main : IO Unit :=
  IO.println s!"Hello,"



