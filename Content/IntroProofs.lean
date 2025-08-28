-- ANCHOR: ExampleOddSum
import Mathlib.Tactic
open Nat

def sumℕ : ℕ → (ℕ → ℕ) → ℕ
  | 0,   _ => 0
  | n+1, f => f n + sumℕ n f

def nthOdd (i : ℕ) : ℕ :=
  2*i+1

#eval nthOdd 3

#eval sumℕ 5 nthOdd

theorem oddSum (n : ℕ) : sumℕ n nthOdd = n^2 := by
  induction n with
  | zero =>
      simp [sumℕ]
  | succ n ih =>
      simp [sumℕ]
      calc
        2 * n + 1 + sumℕ n nthOdd
          = 2 * n + 1 + n^2 := by rw [ih]
        _ = (n + 1)^2 := by ring
-- ANCHOR_END: ExampleOddSum
