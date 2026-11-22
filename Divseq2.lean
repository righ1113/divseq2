-- This module serves as the root of the `Divseq2.Lean` library.
-- Import modules here that should be built as part of the library.
import Divseq2.Basic
import Divseq2.Extension

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

open Nat

namespace divseq2
  lemma colIterOne (n : Nat) : col^[n] 1 = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp [col, ih]
  lemma extLimitedOfOrbitEq (s t : Nat) (p : ExtsLimited s)
    (h : ∃ i j : Nat, col^[i] (6 * s + 3) = col^[j] (6 * t + 3)) : ExtsLimited t := by
      cases p with
      | is u hu =>
        obtain ⟨i, j, hij⟩ := h
        let k := u + 1
        have hiter : col^[k] (col^[i] (6 * s + 3)) =
          col^[k] (col^[j] (6 * t + 3)) := congrArg (fun z => col^[k] z) hij
        have hsource : col^[k] (col^[i] (6 * s + 3)) = 1 := by
          rw [← Function.iterate_add_apply, Nat.add_comm k i,
            Function.iterate_add_apply, hu]
          exact colIterOne i
        have htarget' : col^[k] (col^[j] (6 * t + 3)) = 1 :=
          hiter.symm.trans hsource
        have htarget : col^[k + j] (6 * t + 3) = 1 := by
          simpa only [← Function.iterate_add_apply] using htarget'
        have hsteps : k + j = (u + j) + 1 := by omega
        rw [hsteps] at htarget
        exact ExtsLimited.is t (u + j) htarget
  axiom SEis02Orbit (l : Nat) : ∃ i j : Nat, col^[i] (6 * l + 3) = col^[j] (6 * (12 * l + 7) + 3)
  lemma SEis02 (l : Nat) (p : ExtsLimited l) : ExtsLimited (succ (succ (succ (succ ((succ (l * 2 * 2)) * 3))))) := by
    have h : ExtsLimited (12 * l + 7) :=
      extLimitedOfOrbitEq l (12 * l + 7) p (SEis02Orbit l)
    convert h using 1 <;> omega

  lemma SEis02Orbit_mod4_one (k : Nat) :
      ∃ i j : Nat,
        col^[i] (6 * (4 * k + 1) + 3) =
          col^[j] (6 * (12 * (4 * k + 1) + 7) + 3) := by
    obtain ⟨i, j, horbit⟩ :=
      extendedStar.SEis02Orbit_mod4_one_canonical k
    refine ⟨i, j, ?_⟩
    rw [show 6 * (4 * k + 1) + 3 = 24 * k + 9 by omega]
    rw [show 6 * (12 * (4 * k + 1) + 7) + 3 = 288 * k + 117 by omega]
    exact horbit
  -- l=4k+2 未完成
  -- l=4k+3 未完成
  lemma SEis02Orbit_mod8_zero (k : Nat) : -- 公理 SEis02Orbit_mod8_zero_residual を要求する
      ∃ i j : Nat,
        col^[i] (6 * (8 * k) + 3) =
          col^[j] (6 * (12 * (8 * k) + 7) + 3) := by
    obtain ⟨i, j, horbit⟩ := extendedStar.SEis02Orbit_mod8_zero k
    refine ⟨i, j, ?_⟩
    simpa only [show 6 * (8 * k) + 3 = 48 * k + 3 by omega,
      show 6 * (12 * (8 * k) + 7) + 3 = 576 * k + 45 by omega] using horbit
  lemma SEis02Orbit_mod8_four (k : Nat) :
      ∃ i j : Nat,
        col^[i] (6 * (8 * k + 4) + 3) =
          col^[j] (6 * (12 * (8 * k + 4) + 7) + 3) := by
    have hA1 : col (48 * k + 27) = 144 * k + 82 := by
      simp [col, show 48 * k + 27 ≠ 1 by omega,
        show (48 * k + 27) % 2 ≠ 0 by omega]
      omega
    have hA2 : col (144 * k + 82) = 72 * k + 41 := by
      simp [col, show 144 * k + 82 ≠ 1 by omega,
        show (144 * k + 82) % 2 = 0 by omega]
      omega
    have hA3 : col (72 * k + 41) = 216 * k + 124 := by
      simp [col, show 72 * k + 41 ≠ 1 by omega,
        show (72 * k + 41) % 2 ≠ 0 by omega]
      omega
    have hA4 : col (216 * k + 124) = 108 * k + 62 := by
      simp [col, show 216 * k + 124 ≠ 1 by omega,
        show (216 * k + 124) % 2 = 0 by omega]
      omega
    have hA5 : col (108 * k + 62) = 54 * k + 31 := by
      simp [col, show 108 * k + 62 ≠ 1 by omega,
        show (108 * k + 62) % 2 = 0 by omega]
      omega
    have hA6 : col (54 * k + 31) = 162 * k + 94 := by
      simp [col, show 54 * k + 31 ≠ 1 by omega,
        show (54 * k + 31) % 2 ≠ 0 by omega]
      omega
    have hB1 : col (576 * k + 333) = 1728 * k + 1000 := by
      simp [col, show 576 * k + 333 ≠ 1 by omega,
        show (576 * k + 333) % 2 ≠ 0 by omega]
      omega
    have hB2 : col (1728 * k + 1000) = 864 * k + 500 := by
      simp [col, show 1728 * k + 1000 ≠ 1 by omega,
        show (1728 * k + 1000) % 2 = 0 by omega]
      omega
    have hB3 : col (864 * k + 500) = 432 * k + 250 := by
      simp [col, show 864 * k + 500 ≠ 1 by omega,
        show (864 * k + 500) % 2 = 0 by omega]
      omega
    have hB4 : col (432 * k + 250) = 216 * k + 125 := by
      simp [col, show 432 * k + 250 ≠ 1 by omega,
        show (432 * k + 250) % 2 = 0 by omega]
      omega
    have hB5 : col (216 * k + 125) = 648 * k + 376 := by
      simp [col, show 216 * k + 125 ≠ 1 by omega,
        show (216 * k + 125) % 2 ≠ 0 by omega]
      omega
    have hB6 : col (648 * k + 376) = 324 * k + 188 := by
      simp [col, show 648 * k + 376 ≠ 1 by omega,
        show (648 * k + 376) % 2 = 0 by omega]
      omega
    have hB7 : col (324 * k + 188) = 162 * k + 94 := by
      simp [col, show 324 * k + 188 ≠ 1 by omega,
        show (324 * k + 188) % 2 = 0 by omega]
      omega
    have hA : col^[6] (48 * k + 27) = 162 * k + 94 := by
      calc
        col^[6] (48 * k + 27) = col^[5] (144 * k + 82) := by
          rw [Function.iterate_succ_apply, hA1]
        _ = col^[4] (72 * k + 41) := by
          rw [Function.iterate_succ_apply, hA2]
        _ = col^[3] (216 * k + 124) := by
          rw [Function.iterate_succ_apply, hA3]
        _ = col^[2] (108 * k + 62) := by
          rw [Function.iterate_succ_apply, hA4]
        _ = col^[1] (54 * k + 31) := by
          rw [Function.iterate_succ_apply, hA5]
        _ = 162 * k + 94 := by
          rw [Function.iterate_succ_apply, hA6]
          simp
    have hB : col^[7] (576 * k + 333) = 162 * k + 94 := by
      calc
        col^[7] (576 * k + 333) = col^[6] (1728 * k + 1000) := by
          rw [Function.iterate_succ_apply, hB1]
        _ = col^[5] (864 * k + 500) := by
          rw [Function.iterate_succ_apply, hB2]
        _ = col^[4] (432 * k + 250) := by
          rw [Function.iterate_succ_apply, hB3]
        _ = col^[3] (216 * k + 125) := by
          rw [Function.iterate_succ_apply, hB4]
        _ = col^[2] (648 * k + 376) := by
          rw [Function.iterate_succ_apply, hB5]
        _ = col^[1] (324 * k + 188) := by
          rw [Function.iterate_succ_apply, hB6]
        _ = 162 * k + 94 := by
          rw [Function.iterate_succ_apply, hB7]
          simp
    refine ⟨6, 7, ?_⟩
    rw [show 6 * (8 * k + 4) + 3 = 48 * k + 27 by omega]
    rw [show 6 * (12 * (8 * k + 4) + 7) + 3 = 576 * k + 333 by omega]
    rw [hA, hB]

  lemma SEis02Orbit_mod4_zero (k : Nat) :
      ∃ i j : Nat,
        col^[i] (6 * (4 * k) + 3) =
          col^[j] (6 * (12 * (4 * k) + 7) + 3) := by
    let q := k / 2
    by_cases hk : k % 2 = 0
    · have hdecomp : k = 2 * q := by
        dsimp [q]
        omega
      obtain ⟨i, j, horbit⟩ := SEis02Orbit_mod8_zero q
      refine ⟨i, j, ?_⟩
      have hlow : 6 * (4 * k) + 3 = 6 * (8 * q) + 3 := by omega
      have hhigh :
          6 * (12 * (4 * k) + 7) + 3 =
            6 * (12 * (8 * q) + 7) + 3 := by omega
      simpa only [hlow, hhigh] using horbit
    · have hdecomp : k = 2 * q + 1 := by
        dsimp [q]
        omega
      obtain ⟨i, j, horbit⟩ := SEis02Orbit_mod8_four q
      refine ⟨i, j, ?_⟩
      have hlow : 6 * (4 * k) + 3 = 6 * (8 * q + 4) + 3 := by omega
      have hhigh :
          6 * (12 * (4 * k) + 7) + 3 =
            6 * (12 * (8 * q + 4) + 7) + 3 := by omega
      simpa only [hlow, hhigh] using horbit



  lemma SEis03 (m : Nat) (p : ExtsLimited (2 * m)) :
    ExtsLimited (succ (succ (succ (succ ((succ ((succ (m * 3 * 2)) * 2)) * 3))))) := sorry
      -- simpa using
      --   (SEis (2 * m)
      --     (succ (succ (succ (succ ((succ ((succ (m * 3 * 2)) * 2)) * 3)))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis04 (m : Nat) (p : ExtsLimited (4 * m + 1)) :
    ExtsLimited (succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3))))) := sorry
      -- simpa using
      --   (SEis (4 * m + 1)
      --     (succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3)))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis05 (m : Nat) (p : ExtsLimited (8 * m + 7)) :
    ExtsLimited (succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3))))) := sorry
      -- simpa using
      --   (SEis (8 * m + 7)
      --     (succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3)))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis06 (l : Nat) (p : ExtsLimited (16 * l + 3)) :
    ExtsLimited (succ (succ (succ (succ (l * 3 * 2 * 3))))) := sorry
      -- simpa using
      --   (SEis (16 * l + 3) (succ (succ (succ (succ (l * 3 * 2 * 3)))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis07 (l : Nat) (p : ExtsLimited (8 * l + 4)) :
    ExtsLimited (succ (succ (succ (succ (((succ (l * 3)) * 2) * 3))))) := sorry
      -- simpa using
      --   (SEis (8 * l + 4)
      --     (succ (succ (succ (succ (((succ (l * 3)) * 2) * 3)))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis08 (l : Nat) (p : ExtsLimited (4 * l + 3)) :
    ExtsLimited (succ (succ (succ (succ (((succ (succ (l * 3))) * 2) * 3))))) := sorry
      -- simpa using
      --   (SEis (4 * l + 3)
      --     (succ (succ (succ (succ (((succ (succ (l * 3))) * 2) * 3)))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis09 (j : Nat) (p : ExtsLimited j) :
    ExtsLimited (succ (succ (j * 3))) := sorry
      -- simpa using (SEis j (succ (succ (j * 3))) 1 0 1 0 (by simpa using p))
  lemma SEis11 (k : Nat) (p : ExtsLimited k) :
    ExtsLimited (succ (succ (succ (k * 2 * 3)))) := sorry
      -- simpa using (SEis k (succ (succ (succ (k * 2 * 3)))) 1 0 1 0 (by simpa using p))
  lemma SEis12 (l : Nat) (p : ExtsLimited (2 * l)) :
    ExtsLimited (succ (succ (succ ((succ (l * 3 * 2)) * 3)))) := sorry
      -- simpa using
      --   (SEis (2 * l) (succ (succ (succ ((succ (l * 3 * 2)) * 3))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis13 (l : Nat) (p : ExtsLimited (4 * l + 1)) :
    ExtsLimited (succ (succ (succ (succ (succ (l * 3) * 2) * 3)))) := sorry
      -- simpa using
      --   (SEis (4 * l + 1) (succ (succ (succ (succ (succ (l * 3) * 2) * 3))))
      --     1 0 1 0 (by simpa using p))
  lemma SEis14 (l : Nat) (p : ExtsLimited (8 * l + 7)) :
    ExtsLimited (succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3)))) := sorry
      -- simpa using
      --   (SEis (8 * l + 7) (succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3))))
      --     1 0 1 0 (by simpa using p))
  -- 十分条件
  theorem singleToExts (n : Nat) (p : SingleLimited n) : ExtsLimited n := by
    cases p with
      | is02 l p2 => exact SEis02 l p2
      | is03 m p2 => exact SEis03 m p2
      | is04 m p2 => exact SEis04 m p2
      | is05 m p2 => exact SEis05 m p2
      | is06 l p2 => exact SEis06 l p2
      | is07 l p2 => exact SEis07 l p2
      | is08 l p2 => exact SEis08 l p2
      | is09 j p2 => exact SEis09 j p2
      | is11 k p2 => exact SEis11 k p2
      | is12 l p2 => exact SEis12 l p2
      | is13 l p2 => exact SEis13 l p2
      | is14 l p2 => exact SEis14 l p2
      | is01_2 p1 => exact p1
      | is10_2 p0 => exact p0

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
    ∃ u : Nat, col^[u + 1] (6 * t + 3) = 1 := match p with
      | ExtsLimited.is _ u p2 => ⟨u, p2⟩
  -- 最終的な定理
  theorem CollatzConjecture (t : Nat) :
    ∃ u : Nat, col^[u + 1] (6 * t + 3) = 1 :=
      ExtsToCollatz t $ singleToExts t $ LimitedDivSeq t
  #print axioms CollatzConjecture
end divseq2
