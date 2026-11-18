-- This module serves as the root of the `Divseq2.Lean` library.
-- Import modules here that should be built as part of the library.
import Divseq2.Basic

set_option linter.unnecessarySeqFocus false

open Nat

namespace divseq2
  -- (変形する分については)剰余コラッツ予想より言える
  axiom SEis (x a b c d : Nat) : ExtsLimited (a * x + b) -> ExtsLimited (c * x + d)
  lemma SEis02 (l : Nat) (p : ExtsLimited l) : ExtsLimited (succ (succ (succ (succ ((succ (l * 2 * 2)) * 3))))) := by
    have h : ExtsLimited (12 * l + 7) := SEis l 1 0 12 7 (by simpa using p)
    convert h using 1 <;> omega
  axiom SEis03 : (m : Nat) -> (ExtsLimited <| 2*m)    -> (ExtsLimited <| succ (succ (succ (succ ((succ ((succ (m * 3 * 2)) * 2)) * 3)))))
  axiom SEis04 : (m : Nat) -> (ExtsLimited <| 4*m+1)  -> (ExtsLimited <| succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3)))))
  axiom SEis05 : (m : Nat) -> (ExtsLimited <| 8*m+7)  -> (ExtsLimited <| succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3)))))
  axiom SEis06 : (l : Nat) -> (ExtsLimited <| 16*l+3) -> (ExtsLimited <| succ (succ (succ (succ (l * 3 * 2 * 3)))))
  axiom SEis07 : (l : Nat) -> (ExtsLimited <| 8*l+4)  -> (ExtsLimited <| succ (succ (succ (succ (((succ (l * 3)) * 2) * 3)))))
  axiom SEis08 : (l : Nat) -> (ExtsLimited <| 4*l+3)  -> (ExtsLimited <| succ (succ (succ (succ (((succ (succ (l * 3))) * 2) * 3)))))
  axiom SEis09 : (j : Nat) -> (ExtsLimited <| j)      -> (ExtsLimited <| succ (succ (j*3)))
  axiom SEis11 : (k : Nat) -> (ExtsLimited <| k)      -> (ExtsLimited <| succ (succ (succ (k * 2 * 3))))
  axiom SEis12 : (l : Nat) -> (ExtsLimited <| 2*l)    -> (ExtsLimited <| succ (succ (succ ((succ (l * 3 * 2)) * 3))))
  axiom SEis13 : (l : Nat) -> (ExtsLimited <| 4*l+1)  -> (ExtsLimited <| succ (succ (succ (succ (succ (l * 3) * 2) * 3))))
  axiom SEis14 : (l : Nat) -> (ExtsLimited <| 8*l+7)  -> (ExtsLimited <| succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3))))
  -- 十分条件
  theorem singleToExts (n : Nat) (p : SingleLimited n) : ExtsLimited n := match p with
    | SingleLimited.is02 l p2 => SEis02 l p2
    | SingleLimited.is03 m p2 => SEis03 m p2
    | SingleLimited.is04 m p2 => SEis04 m p2
    | SingleLimited.is05 m p2 => SEis05 m p2
    | SingleLimited.is06 l p2 => SEis06 l p2
    | SingleLimited.is07 l p2 => SEis07 l p2
    | SingleLimited.is08 l p2 => SEis08 l p2
    | SingleLimited.is09 j p2 => SEis09 j p2
    | SingleLimited.is11 k p2 => SEis11 k p2
    | SingleLimited.is12 l p2 => SEis12 l p2
    | SingleLimited.is13 l p2 => SEis13 l p2
    | SingleLimited.is14 l p2 => SEis14 l p2
    | SingleLimited.is01_2 p2 => p2
    | SingleLimited.is10_2 p2 => p2

  lemma m₀₂₁ (l : Nat) : l < succ (succ (succ (succ (succ (l * 2 * 2) * 3)))) := by linarith
  lemma m₀₃₁ (m : Nat) : 2 * m < succ (succ (succ (succ (succ (succ (m * 3 * 2) * 2) * 3)))) := by linarith
  lemma m₀₄₁ (m : Nat) : 4 * m + 1 < succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3)))) := by linarith
  lemma m₀₅₁ (m : Nat) : 8 * m + 7 < succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3)))) := by linarith
  lemma m₀₆₁ (l : Nat) : 16 * l + 3 < succ (succ (succ (succ (l * 3 * 2 * 3)))) := by linarith
  lemma m₀₇₁ (l : Nat) : 8 * l + 4 < succ (succ (succ (succ (succ (l * 3) * 2 * 3)))) := by linarith
  lemma m₀₈₁ (l : Nat) : 4 * l + 3 < succ (succ (succ (succ (succ (succ (l * 3)) * 2 * 3)))) := by linarith
  lemma m₀₉₁ (j : Nat) : j < succ (succ (j * 3)) := by linarith
  lemma m₁₁₁ (k : Nat) : k < succ (succ (succ (k * 2 * 3))) := by linarith
  lemma m₁₂₁ (l : Nat) : 2 * l < succ (succ (succ (succ (l * 3 * 2) * 3))) := by linarith
  lemma m₁₃₁ (l : Nat) : 4 * l + 1 < succ (succ (succ (succ (succ (l * 3) * 2) * 3))) := by linarith
  lemma m₁₄₁ (l : Nat) : 8 * l + 7 < succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3))) := by linarith
  theorem makeLimitedDivSeq (x : Nat) (rs : ∀ x₁, x₁ < x → SingleLimited x₁) : SingleLimited x := match x with
    | 0             => SingleLimited.is10_2 is10 -- 6*<0>+3 = 3
    | 1             => SingleLimited.is01_2 is01 -- 6*<1>+3 = 9
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
  theorem LimitedDivSeq (n : Nat) : SingleLimited n := WellFounded.fix (measure id).wf makeLimitedDivSeq n
  lemma ExtsToCollatz (t : Nat) (p : ExtsLimited t) :
      ∃ u : Nat, col^[u + 1] (6 * t + 3) < 6 * t + 3 := match p with
    | ExtsLimited.is _ u p2 => ⟨u, p2⟩
  -- 最終的な定理
  theorem CollatzConjecture (t : Nat) :
      ∃ u : Nat, col^[u + 1] (6 * t + 3) < 6 * t + 3 :=
    ExtsToCollatz t $ singleToExts t $ LimitedDivSeq t
end divseq2
