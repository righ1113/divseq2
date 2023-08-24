-- $ cd divseq2
-- $ code .

import «Divseq2»

open Nat

namespace divseq2
  theorem h₀₃ (m : Nat) : 18 * (2 * m) + 13 = succ (succ (succ (succ ((succ ((succ (m * 3 * 2)) * 2)) * 3)))) := by linarith
  theorem h₀₄ (m : Nat) : 9 * (4 * m + 1) + 16 = succ (succ (succ (succ ((succ ((succ ((succ (m * 3)) * 2)) * 2)) * 3)))) := by linarith
  --theorem h₀₅1 (m : Nat) : 36 * m + 37 = succ (succ (succ (succ ((succ ((succ ((succ (succ (m * 3))) * 2)) * 2)) * 3)))) := by linarith
  axiom   h₀₅ (m : Nat) : (9 * (8 * m + 7) + 11) / 2 = succ (succ (succ (succ ((succ ((succ ((succ (succ (m * 3))) * 2)) * 2)) * 3))))
  axiom   h₀₆ (l : Nat) : (16 * l + 3) + (16 * l + 3 - 3) / 8 + 1 = succ (succ (succ (succ (l * 3 * 2 * 3))))
  axiom   h₀₇ (l : Nat) : 8 * l + 4 + (8 * l + 4 - 4) / 4 * 5 + 6 = succ (succ (succ (succ (((succ (l * 3)) * 2) * 3))))
  axiom   h₀₈ (l : Nat) : 4 * (4 * l + 3) + (4 * l + 3 - 3) / 2 + 4 = succ (succ (succ (succ (((succ (succ (l * 3))) * 2) * 3))))
  theorem h₁₂ (l : Nat) : 9 * (2 * l) + 6 = succ (succ (succ ((succ (l * 3 * 2)) * 3))) := by linarith
  axiom   h₁₃ (l : Nat) : (9 * (4 * l + 1) + 15) / 2 = succ (succ (succ ((succ ((succ (l * 3)) * 2)) * 3)))
  axiom   h₁₄ (l : Nat) : (9 * (8 * l + 7) + 9) / 4 = succ (succ (succ ((succ ((succ (succ (l * 3))) * 2)) * 3)))
  -- 十分条件
  theorem singleToExts (n : Nat) (p : SingleLimited n) : ExtsLimited n := match p with
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
    | SingleLimited.is09 _ p2 => match p2 with
      | ExtsLimited.is _ _ _ p3 _ _ _ _ _ _ _ _ _ _ => p3
    | SingleLimited.is11 _ p2 => match p2 with
      | ExtsLimited.is _ _ _ _ p3 _ _ _ _ _ _ _ _ _ => p3
    | SingleLimited.is12 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ p3 _ _ _ _ _ _ _ => have p4 := Eq.subst (h₁₂ l) p3; p4
    | SingleLimited.is13 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ _ _ _ _ p3 _ => have p4 := Eq.subst (h₁₃ l) p3; p4
    | SingleLimited.is14 l p2 => match p2 with
      | ExtsLimited.is _ _ _ _ _ _ _ _ _ _ _ _ _ p3 => have p4 := Eq.subst (h₁₄ l) p3; p4
    | SingleLimited.is01_2 p2 => match p2 with
      | ExtsLimited.is _ p3 _ _ _ _ _ _ _ _ _ _ _ _ => p3
    | SingleLimited.is10_2 p2 => match p2 with
      | ExtsLimited.is _ p3 _ _ _ _ _ _ _ _ _ _ _ _ => p3

  theorem m₀₂₁ (l : Nat) : l < succ (succ (succ (succ (succ (l * 2 * 2) * 3)))) := by linarith
  theorem m₀₃₁ (m : Nat) : 2 * m < succ (succ (succ (succ (succ (succ (m * 3 * 2) * 2) * 3)))) := by linarith
  theorem m₀₄₁ (m : Nat) : 4 * m + 1 < succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3)))) := by linarith
  theorem m₀₅₁ (m : Nat) : 8 * m + 7 < succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3)))) := by linarith
  theorem m₀₆₁ (l : Nat) : 16 * l + 3 < succ (succ (succ (succ (l * 3 * 2 * 3)))) := by linarith
  theorem m₀₇₁ (l : Nat) : 8 * l + 4 < succ (succ (succ (succ (succ (l * 3) * 2 * 3)))) := by linarith
  theorem m₀₈₁ (l : Nat) : 4 * l + 3 < succ (succ (succ (succ (succ (succ (l * 3)) * 2 * 3)))) := by linarith
  theorem m₀₉₁ (j : Nat) : j < succ (succ (j * 3)) := by linarith
  theorem m₁₁₁ (k : Nat) : k < succ (succ (succ (k * 2 * 3))) := by linarith
  theorem m₁₂₁ (l : Nat) : 2 * l < succ (succ (succ (succ (l * 3 * 2) * 3))) := by linarith
  theorem m₁₃₁ (l : Nat) : 4 * l + 1 < succ (succ (succ (succ (succ (l * 3) * 2) * 3))) := by linarith
  theorem m₁₄₁ (l : Nat) : 8 * l + 7 < succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3))) := by linarith
  def makeLimitedDivSeq (x : Nat) (rs : ∀ x₁, x₁ < x → SingleLimited x₁) : SingleLimited x := match x with
    | 0             => is10 -- 6*<0>+3 = 3
    | 1             => is01 -- 6*<1>+3 = 9
    | succ (succ x) => by have rs := rs; cases (mod3 x) with
      -- 6 mod 9
      | threeZero j =>
          have sin := rs j (m₀₉₁ j); have ext := singleToExts j sin;
          exact SingleLimited.is09 j ext;
      -- 3 mod 9
      | threeOne j  => cases (parity j) with
        | even k =>
            have sin := rs k (m₁₁₁ k); have ext := singleToExts k sin;
            exact SingleLimited.is11 k ext;
        | odd k  => cases (mod3 k) with
          | threeZero l =>
              have sin := rs (2 * l) (m₁₂₁ l); have ext := singleToExts (2 * l) sin;
              exact SingleLimited.is12 l ext;
          | threeOne l  =>
              have sin := rs (4 * l + 1) (m₁₃₁ l); have ext := singleToExts (4 * l + 1) sin;
              exact SingleLimited.is13 l ext;
          | threeTwo l  =>
              have sin := rs (8 * l + 7) (m₁₄₁ l); have ext := singleToExts (8 * l + 7) sin;
              exact SingleLimited.is14 l ext;
      -- 0 mod 9
      | threeTwo j  => cases (parity j) with
        | even k => cases (mod3 k) with
          | threeZero l =>
              have sin := rs (16 * l + 3) (m₀₆₁ l); have ext := singleToExts (16 * l + 3) sin;
              exact SingleLimited.is06 l ext;
          | threeOne l  =>
              have sin := rs (8 * l + 4) (m₀₇₁ l); have ext := singleToExts (8 * l + 4) sin;
              exact SingleLimited.is07 l ext;
          | threeTwo l  =>
              have sin := rs (4 * l + 3) (m₀₈₁ l); have ext := singleToExts (4 * l + 3) sin;
              exact SingleLimited.is08 l ext;
        | odd k  => cases (parity k) with
          | even l =>
              have sin := rs l (m₀₂₁ l); have ext := singleToExts l sin;
              exact SingleLimited.is02 l ext;
          | odd l  => cases (mod3 l) with
            | threeZero m =>
                have sin := rs (2 * m) (m₀₃₁ m); have ext := singleToExts (2 * m) sin;
                exact SingleLimited.is03 m ext;
            | threeOne m  =>
                have sin := rs (4 * m + 1) (m₀₄₁ m); have ext := singleToExts (4 * m + 1) sin;
                exact SingleLimited.is04 m ext;
            | threeTwo m  =>
                have sin := rs (8 * m + 7) (m₀₅₁ m); have ext := singleToExts (8 * m + 7) sin;
                exact SingleLimited.is05 m ext;
  -- 最終的な定理
  def LimitedDivSeq (n : Nat) : SingleLimited n := WellFounded.fix' (measure id).wf makeLimitedDivSeq n
end divseq2



def main : IO Unit :=
  IO.println s!"Hello,"



