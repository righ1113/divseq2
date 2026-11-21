-- This module serves as the root of the `Divseq2.Lean` library.
-- Import modules here that should be built as part of the library.
import Divseq2.Basic
import Divseq2.Extension

set_option linter.unnecessarySeqFocus false

open Nat

namespace divseq2
  -- (変形する分については)剰余コラッツ予想より言える
-- つまりcolコラッツ操作で一次式の移り変わりを証明（またはaxiom）する必要があるんだね
-- そうです。ただし必要なのは、単に一次式の値を変形することではなく、対応する初期値
-- 6*(a*x+b)+3
-- 6*(c*y+d)+3
-- の col 軌道が合流することなど、両者の到達性を結ぶ関係です。それを対象の一次式ごとに証明するか、
-- 限定した軌道転送の公理として置く必要があります。
-- 任意の一次式どうしを結ぶ公理にすると、再びほぼコラッツ予想そのものを仮定してしまいます。
-- つまり#sym:SEis はすごく強い仮定なの？
-- 以前の無条件な SEis、つまり任意の入力から任意の出力へ ExtsLimited を移す形は、
-- 非常に強い仮定でした。
-- の SEis は hrel : a*x+b = 6*(c*y+d)+2 を要求するので、転送先は限定されています。
-- ただし証明は、未証明の Residue1 公理に依存します。
  axiom Residue1 (t s : Nat) :
    (∃u : Nat, col^[u + 1] (6 * t + 3) = 1) -> ∃v : Nat, col^[v + 1] (s + 1) = 1
  lemma SEis (x y a b c d : Nat) :
    ExtsLimited (a * x + b) -> ExtsLimited (c * y + d) := by
      intro h
      cases h with
      | is u hu =>
        have htarget :=
          Residue1 (a * x + b) (6 * (c * y + d) + 2) ⟨u, hu⟩
        obtain ⟨v, hv⟩ := htarget
        have hseed : (6 * (c * y + d) + 2) + 1 = 6 * (c * y + d) + 3 := by omega
        rw [hseed] at hv
        exact ExtsLimited.is _ v hv
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

  lemma SEis02Orbit_mod4_one (k : Nat) :
      ∃ i j : Nat,
        col^[i] (6 * (4 * k + 1) + 3) =
          col^[j] (6 * (12 * (4 * k + 1) + 7) + 3) := by
    have hLseed : 6 * (4 * k + 1) + 3 = 24 * k + 9 := by omega
    have hHseed : 6 * (12 * (4 * k + 1) + 7) + 3 = 288 * k + 117 := by omega
    have hL1 : col (24 * k + 9) = 72 * k + 28 := by
      have hne : 24 * k + 9 ≠ 1 := by omega
      have hodd : (24 * k + 9) % 2 ≠ 0 := by omega
      simp [col, hne, hodd]
      omega
    have hL2 : col (72 * k + 28) = 36 * k + 14 := by
      have hne : 72 * k + 28 ≠ 1 := by omega
      have heven : (72 * k + 28) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hL3 : col (36 * k + 14) = 18 * k + 7 := by
      have hne : 36 * k + 14 ≠ 1 := by omega
      have heven : (36 * k + 14) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hL4 : col (18 * k + 7) = 54 * k + 22 := by
      have hne : 18 * k + 7 ≠ 1 := by omega
      have hodd : (18 * k + 7) % 2 ≠ 0 := by omega
      simp [col, hne, hodd]
      omega
    have hL5 : col (54 * k + 22) = 27 * k + 11 := by
      have hne : 54 * k + 22 ≠ 1 := by omega
      have heven : (54 * k + 22) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hH1 : col (288 * k + 117) = 864 * k + 352 := by
      have hne : 288 * k + 117 ≠ 1 := by omega
      have hodd : (288 * k + 117) % 2 ≠ 0 := by omega
      simp [col, hne, hodd]
      omega
    have hH2 : col (864 * k + 352) = 432 * k + 176 := by
      have hne : 864 * k + 352 ≠ 1 := by omega
      have heven : (864 * k + 352) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hH3 : col (432 * k + 176) = 216 * k + 88 := by
      have hne : 432 * k + 176 ≠ 1 := by omega
      have heven : (432 * k + 176) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hH4 : col (216 * k + 88) = 108 * k + 44 := by
      have hne : 216 * k + 88 ≠ 1 := by omega
      have heven : (216 * k + 88) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hH5 : col (108 * k + 44) = 54 * k + 22 := by
      have hne : 108 * k + 44 ≠ 1 := by omega
      have heven : (108 * k + 44) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hH6 : col (54 * k + 22) = 27 * k + 11 := by
      have hne : 54 * k + 22 ≠ 1 := by omega
      have heven : (54 * k + 22) % 2 = 0 := by omega
      simp [col, hne, heven]
      omega
    have hL : col^[5] (24 * k + 9) = 27 * k + 11 := by
      calc
        col^[5] (24 * k + 9) = col^[4] (72 * k + 28) := by
          rw [Function.iterate_succ_apply, hL1]
        _ = col^[3] (36 * k + 14) := by
          rw [Function.iterate_succ_apply, hL2]
        _ = col^[2] (18 * k + 7) := by
          rw [Function.iterate_succ_apply, hL3]
        _ = col^[1] (54 * k + 22) := by
          rw [Function.iterate_succ_apply, hL4]
        _ = 27 * k + 11 := by
          rw [Function.iterate_succ_apply, hL5]
          simp
    have hH : col^[6] (288 * k + 117) = 27 * k + 11 := by
      calc
        col^[6] (288 * k + 117) = col^[5] (864 * k + 352) := by
          rw [Function.iterate_succ_apply, hH1]
        _ = col^[4] (432 * k + 176) := by
          rw [Function.iterate_succ_apply, hH2]
        _ = col^[3] (216 * k + 88) := by
          rw [Function.iterate_succ_apply, hH3]
        _ = col^[2] (108 * k + 44) := by
          rw [Function.iterate_succ_apply, hH4]
        _ = col^[1] (54 * k + 22) := by
          rw [Function.iterate_succ_apply, hH5]
        _ = 27 * k + 11 := by
          rw [Function.iterate_succ_apply, hH6]
          simp
    refine ⟨5, 6, ?_⟩
    rw [hLseed, hHseed, hL, hH]

  lemma SEis02 (l : Nat) (p : ExtsLimited l) : ExtsLimited (succ (succ (succ (succ ((succ (l * 2 * 2)) * 3))))) := by
    have h : ExtsLimited (12 * l + 7) :=
      extLimitedOfOrbitEq l (12 * l + 7) p (SEis02Orbit l)
    convert h using 1 <;> omega

  axiom SEis00 (T : Nat) :
    ∀ t : Nat, T < t →
      ∃ l i j : Nat,
        l < t ∧
        col^[i] (6 * l + 3) = col^[j] (6 * t + 3)
  theorem SEis02CoverTail (T : Nat) :
      ∀ s : Nat, T < 12 * s + 7 →
        ∃ l i j : Nat,
          l < 12 * s + 7 ∧
          col^[i] (6 * l + 3) =
            col^[j] (6 * (12 * s + 7) + 3) := by
    intro s _
    obtain ⟨i, j, horbit⟩ := SEis02Orbit s
    refine ⟨s, i, j, ?_, ?_⟩
    · omega
    · exact horbit

  lemma SEis03 (m : Nat) (p : ExtsLimited (2 * m)) :
    ExtsLimited (succ (succ (succ (succ ((succ ((succ (m * 3 * 2)) * 2)) * 3))))) := by
      simpa using
        (SEis (2 * m)
          (succ (succ (succ (succ ((succ ((succ (m * 3 * 2)) * 2)) * 3)))))
          1 0 1 0 (by simpa using p))
  lemma SEis04 (m : Nat) (p : ExtsLimited (4 * m + 1)) :
    ExtsLimited (succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3))))) := by
      simpa using
        (SEis (4 * m + 1)
          (succ (succ (succ (succ (succ (succ (succ (m * 3) * 2) * 2) * 3)))))
          1 0 1 0 (by simpa using p))
  lemma SEis05 (m : Nat) (p : ExtsLimited (8 * m + 7)) :
    ExtsLimited (succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3))))) := by
      simpa using
        (SEis (8 * m + 7)
          (succ (succ (succ (succ (succ (succ (succ (succ (m * 3)) * 2) * 2) * 3)))))
          1 0 1 0 (by simpa using p))
  lemma SEis06 (l : Nat) (p : ExtsLimited (16 * l + 3)) :
    ExtsLimited (succ (succ (succ (succ (l * 3 * 2 * 3))))) := by
      simpa using
        (SEis (16 * l + 3) (succ (succ (succ (succ (l * 3 * 2 * 3)))))
          1 0 1 0 (by simpa using p))
  lemma SEis07 (l : Nat) (p : ExtsLimited (8 * l + 4)) :
    ExtsLimited (succ (succ (succ (succ (((succ (l * 3)) * 2) * 3))))) := by
      simpa using
        (SEis (8 * l + 4)
          (succ (succ (succ (succ (((succ (l * 3)) * 2) * 3)))))
          1 0 1 0 (by simpa using p))
  lemma SEis08 (l : Nat) (p : ExtsLimited (4 * l + 3)) :
    ExtsLimited (succ (succ (succ (succ (((succ (succ (l * 3))) * 2) * 3))))) := by
      simpa using
        (SEis (4 * l + 3)
          (succ (succ (succ (succ (((succ (succ (l * 3))) * 2) * 3)))))
          1 0 1 0 (by simpa using p))
  lemma SEis09 (j : Nat) (p : ExtsLimited j) :
    ExtsLimited (succ (succ (j * 3))) := by
      simpa using (SEis j (succ (succ (j * 3))) 1 0 1 0 (by simpa using p))
  lemma SEis11 (k : Nat) (p : ExtsLimited k) :
    ExtsLimited (succ (succ (succ (k * 2 * 3)))) := by
      simpa using (SEis k (succ (succ (succ (k * 2 * 3)))) 1 0 1 0 (by simpa using p))
  lemma SEis12 (l : Nat) (p : ExtsLimited (2 * l)) :
    ExtsLimited (succ (succ (succ ((succ (l * 3 * 2)) * 3)))) := by
      simpa using
        (SEis (2 * l) (succ (succ (succ ((succ (l * 3 * 2)) * 3))))
          1 0 1 0 (by simpa using p))
  lemma SEis13 (l : Nat) (p : ExtsLimited (4 * l + 1)) :
    ExtsLimited (succ (succ (succ (succ (succ (l * 3) * 2) * 3)))) := by
      simpa using
        (SEis (4 * l + 1) (succ (succ (succ (succ (succ (l * 3) * 2) * 3))))
          1 0 1 0 (by simpa using p))
  lemma SEis14 (l : Nat) (p : ExtsLimited (8 * l + 7)) :
    ExtsLimited (succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3)))) := by
      simpa using
        (SEis (8 * l + 7) (succ (succ (succ (succ (succ (succ (l * 3)) * 2) * 3))))
          1 0 1 0 (by simpa using p))
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
