notation "ℕ" => Nat
open Nat

-- inductive LE : Nat → Nat → Prop where
-- | refl (n) : LE n n
-- | step {n m} : LE n m → LE n (m + 1)

open Nat.le

def refl_le : ∀ n : ℕ , n ≤ n := by
intro n
apply refl

def trans_le : ∀ l m n : ℕ, l ≤ m → m ≤ n → l ≤ n := by
intro l m n
intro lm mn
induction mn with
| refl =>
    assumption
| step h ih =>
    apply step
    assumption
