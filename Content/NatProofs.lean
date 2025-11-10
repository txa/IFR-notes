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


example : ∀ n : ℕ , half (double n) = n := by
intro n
induction n with
 | zero => rfl
 | succ m ih =>
    dsimp [double,half]
    rw [ih]


-- ANCHOR: halfDouble
theorem half_double :
  ∀ n : ℕ, half (double n) = n := by
intro n
induction n with
| zero => rfl
| succ n ih =>
    calc
      half (double (succ n))
      = half (succ (succ (double n))) := by rfl
      _ = succ (half (double n)) := by rfl
      _ = succ n := by rw [ih]
-- ANCHOR_END: halfDouble

-- ANCHOR: add
def add : ℕ → ℕ → ℕ
| m  , zero     => m
| m  , (succ n) => succ (add m n)
-- ANCHOR_END: add

-- ANCHOR: add_rneutr
theorem add_rneutr : ∀ n : ℕ, n + 0 = n := by
intro n
rfl
-- ANCHOR_END: add_rneutr

-- ANCHOR: add_lneutr
theorem add_lneutr : ∀ n : ℕ, 0 + n  = n := by
intro n
induction n with
 | zero => rfl
 | succ m ih =>
     calc 0 + (succ m)
          = succ (0 + m)  := by rfl
          _ = succ m := by rw [ih]
-- ANCHOR_END: add_lneutr

-- ANCHOR: add_assoc
theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) := by
intro l m n
induction n with
| zero => rfl
| succ n' ih =>
     calc  (l + m) + (succ n')
         = succ ((l + m) +n') := by rfl
      _  = succ (l + (m + n')) := by rw [ih]
      _  = l + (succ (m + n')) := by rfl
      _  = l + (m + (succ n')) := by rfl
-- ANCHOR_END: add_assoc

-- ANCHOR: add_succ
theorem add_succ :
∀ l m : ℕ, (succ l) + m = succ (l + m) := by
intro l m
induction m with
 | zero => rfl
 | succ m ih =>
     calc
       (succ l) + (succ m)
         = succ ((succ l ) + m) := by rfl
       _ = succ (succ (l + m)) := by rw [ih]
       _ = succ (l + succ m) := by rfl
-- ANCHOR_END: add_succ

-- ANCHOR: add_comm
theorem add_comm :
∀ l m : ℕ, l + m = m + l := by
intro l m
induction m with
| zero =>
    calc l + 0
        = l := by rfl
      _ = 0 + l := by rw [add_lneutr]
| succ m ih =>
      calc   l + (succ m)
           = succ (l + m) := by rfl
         _ = succ (m + l) := by rw[ih]
         _ = (succ m) + l := by rw [← add_succ]
-- ANCHOR_END: add_comm
