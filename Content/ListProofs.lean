import Content.NatProofs

namespace ListProofs
set_option tactic.customEliminators false -- to stop lean using +1
-- notation "ℕ" => Nat
-- open Nat

open NatProofs
open Nat

namespace ListDef

inductive List(A : Type) : Type where
| nil : List A
| cons : A → List A → List A

local notation "[]" => List.nil
local infixr:67 "::" => List.cons

end ListDef

open List

#check cons 1 (cons 2 (cons 3 nil))
#check 1 :: 2 :: 3 :: []
#check [1,2,3]

#check [[1,2],[],[3]]
--#check [1,2,true]

inductive NatOrBool : Type where
| nat : ℕ → NatOrBool
| bool : Bool → NatOrBool

open NatOrBool

#check [nat 1,nat 2,bool true]

-- Peano style axioms

-- no confusion

variable {A B C : Type}

example : ∀ a : A , ∀ as : List A, [] ≠ a :: as := by
intro a as h
cases h

example : ∀ a b : A, ∀ as bs : List A, a :: as = b :: bs → a = b := by
intro a b as bs h
injection h

example : ∀ a b : A, ∀ as bs : List A, a :: as = b :: bs → as = bs := by
intro a b as bs h
injection h

def tl : List A → List A
| [] => []
| a :: as => as

example : ∀ a b : A, ∀ as bs : List A, a :: as = b :: bs → as = bs := by
intro a b as bs h
change tl (a :: as) = bs
rw [h]
rfl

-- can we do this for hd ?

namespace hd
def hd : List A → A
| [] => sorry
| a :: as => a
end hd

def hd : (as : List A) → as ≠ [] → A
| [] , h => by
    have pcf : False := by
      apply h
      rfl
    cases pcf
| a :: as , _ => a

example : ∀ a b : A, ∀ as bs : List A, a :: as = b :: bs → a = b := by
intro a b as bs h
have h_as : a :: as ≠ [] := by
  intro p
  cases p
have h_bs : b :: bs ≠ [] := by
  intro p
  cases p
change hd (a :: as) h_as = b
have hh : hd (a :: as) h_as = hd (b :: bs) h_bs := by
  cases h
  rfl
rw [hh]
rfl

def length : List A → ℕ
| [] => 0
| a :: as => succ (length as)

#eval (length [1,2,3])

def append : List A → List A → List A
| [] , as => as
| a :: as , bs => cons a (append as bs)

#eval append [1,2,3] [4,5,6]

infixr:65(priority := 1001) " ++ " => append

#eval [1,2,3]++[4,5,6]

def append' : List A → List A → List A
| as , [] => as
| as , b :: bs => cons b (append' as bs)

#eval append' [1,2,3] [4,5,6]

example : ∀ as bs : List A , length (as ++ bs) = length as + length bs := by
intro as bs
induction as with
| nil =>
    calc length ([] ++ bs)
      = length bs := by rfl
    _ = 0 + length bs := by rw [add_lneutr]
    _ = length []+length bs := by rfl
| cons a as ih =>
    calc length (a :: as ++ bs)
       = length (a :: (as ++ bs)) := by rfl
       _ = succ (length (as ++ bs)) := by rfl
       _ = succ (length as + length bs) := by rw [ih]
       _ = succ (length as) + length bs := by rw [← NatProofs.add_succ]
       _ = length (a :: as) +length bs := by rfl









end ListProofs
