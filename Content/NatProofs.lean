namespace NatProofs

namespace NatDef

-- ANCHOR: NatDef
inductive Nat : Type
| zero : Nat
| succ : Nat → Nat
-- ANCHOR_END: NatDef

end NatDef

notation "ℕ" => Nat
open Nat

-- ANCHOR: NoConf
example : ∀ n : ℕ , succ n ≠ zero := by
intro n h
cases h
-- ANCHOR_END: NoConf

-- ANCHOR: pred
def pred : ℕ → ℕ
| zero => zero
| succ n => n
-- ANCHOR_END: pred

-- ANCHOR: succInj
example : ∀ m n : ℕ, succ m = succ n → m = n := by
intro m n h
change pred (succ m) = n
rw [h]
rfl
-- ANCHOR_END: succInj

-- ANCHOR: succInj2
example : ∀ m n : ℕ, succ m = succ n → m = n := by
intro m n h
injection h
-- ANCHOR_END: succInj2

-- ANCHOR: double
def double : ℕ → ℕ
| zero => zero
| succ n => succ (succ (double n))
-- ANCHOR_END: double

-- ANCHOR: half
def half : ℕ → ℕ
| zero => zero
| succ zero => zero
| succ (succ n) => succ (half n)
-- ANCHOR_END: half

-- ANCHOR: halfDouble
example : ∀ n : ℕ , half (double n) = n := by
intro n
induction n with
 | zero => rfl
 | succ m ih =>
    dsimp [double,half]
    rw [ih]
-- ANCHOR_END: halfDouble
