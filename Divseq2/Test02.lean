import Mathlib.Tactic.Linarith

open Nat

lemma p₁ (k : Nat) : (succ k) * 2 = succ (succ (k * 2))        := succ_mul_succ_eq k 1
lemma m₁ (k : Nat) : (succ k) * 3 = succ (succ (succ (k * 3))) := succ_mul_succ_eq k 2
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

inductive ExtsLimited2 : Nat → Prop where
  | is : (k : Nat)
      → (ExtsLimited2 <| k) -- この条件があるから、この後どんな条件を置いても良い
      → (ExtsLimited2 <| succ (succ (k*2)))           -- 09
      → (ExtsLimited2 <| succ (k*2))                  -- 11
      → (ExtsLimited2 0)                              -- 14'
        → (ExtsLimited2 <| k)
inductive SingleLimited2 : Nat → Prop where
  | is09 : (k : Nat) → (ExtsLimited2 <| k)      → (SingleLimited2 <| succ (succ (k*2)))
  | is11 : (k : Nat) → (ExtsLimited2 <| k)      → (SingleLimited2 <| succ (k * 2))
  | is10_2 : ExtsLimited2 0 → SingleLimited2 0
axiom is10 : SingleLimited2 0

-- 十分条件
theorem singleToExts2 (n : Nat) (p : SingleLimited2 n) : ExtsLimited2 n := match p with
  | SingleLimited2.is09 _ p2 => match p2 with
    | ExtsLimited2.is _ _ p3 _ _  => p3
  | SingleLimited2.is11 _ p2 => match p2 with
    | ExtsLimited2.is _ _ _ p3 _  => p3
  | SingleLimited2.is10_2 p2      => p2

theorem makeLimitedDivSeq2 (x : Nat) (rs : ∀ x₁, x₁ < x → SingleLimited2 x₁) : SingleLimited2 x := match x with
  | 0      => is10
  | succ x => by have rs := rs; cases (parity x) with
    | even k =>
        have sin := rs k (by simp_arith)
        have ext := singleToExts2 k sin
        exact SingleLimited2.is11 k ext
    | odd k  =>
        have sin := rs k (by simp_arith)
        have ext := singleToExts2 k sin
        exact SingleLimited2.is09 k ext
-- 最終的な定理
theorem LimitedDivSeq (n : Nat) : SingleLimited2 n := WellFounded.fix (measure id).wf makeLimitedDivSeq2 n
