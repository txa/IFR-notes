notation "ℕ" => Nat
open Nat

-- inductive LE : Nat → Nat → Prop where
-- | refl (n) : LE n n
-- | step {n m} : LE n m → LE n (m + 1)

open Nat.le

-- I prove antisymmetry by using the alternative definition
-- of ≤ , it shoud be possible to factor this

inductive LE' : Nat → Nat → Prop where
| le'_zero (n) : LE' zero n
| le'_succ {n m} : LE' n m → LE' (n + 1) (m + 1)

open LE'

infix:50 " ≤' " => LE'

theorem anti_sym_le' : ∀ l m : ℕ , l ≤' m → m ≤' l → m = l := by
intro l m lm ml
induction lm with
| le'_zero =>
    cases ml with
    | le'_zero => rfl
| le'_succ h ih =>
    cases ml with
    | le'_succ h =>
        case le'_succ m n h =>
          have q : n = m := by
            apply ih
            assumption
          rw [q]

theorem le'_refl : ∀ m : ℕ, m ≤' m := by
intro m
induction m with
| zero =>
    apply le'_zero
| succ m ih =>
    apply le'_succ
    assumption

theorem le'_step : ∀ m n : ℕ, m ≤' n → m ≤' succ n := by
intro m n mn
induction mn with
| le'_zero =>
    apply le'_zero
| le'_succ h ih =>
    apply le'_succ
    assumption

theorem le2le' : ∀ m n : ℕ, m ≤ n → m ≤' n := by
intro m n mn
induction mn with
| refl => apply le'_refl
| step h ih =>
    apply le'_step
    assumption

def anti_sym_le : ∀ l m : ℕ , l ≤ m → m ≤ l → m = l := by
intro l m lm ml
apply anti_sym_le'
. apply le2le'
  assumption
. apply le2le'
  assumption
