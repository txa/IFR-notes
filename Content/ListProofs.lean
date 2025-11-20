import Content.NatProofs

namespace ListProofs
set_option tactic.customEliminators false -- to stop lean using +1
-- notation "ℕ" => Nat
-- open Nat

open NatProofs
open Nat

namespace ListDef

-- ANCHOR: ListDef
inductive List(A : Type) : Type where
| nil : List A
| cons : A → List A → List A
-- ANCHOR_END: ListDef

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

-- ANCHOR: noConf
theorem noConf : ∀ a : A , ∀ as : List A, [] ≠ a :: as := by
intro a as h
cases h
-- ANCHOR_END: noConf

-- ANCHOR: injCons
theorem injCons_1 : ∀ a b : A, ∀ as bs : List A,
  a :: as = b :: bs → a = b := by
intro a b as bs h
injection h

theorem injCons_2 : ∀ a b : A, ∀ as bs : List A,
  a :: as = b :: bs → as = bs := by
intro a b as bs h
injection h
-- ANCHOR_END: injCons

-- ANCHOR: tl
def tl : List A → List A
| [] => []
| _ :: as => as
-- ANCHOR_END: tl

-- ANCHOR: injCons_2
theorem injCons_2' : ∀ a b : A, ∀ as bs : List A,
  a :: as = b :: bs → as = bs := by
intro a b as bs h
change tl (a :: as) = bs
rw [h]
rfl
-- ANCHOR_END: injCons_2

-- can we do this for hd ?

namespace hd

-- ANCHOR: hd
def hd : List A → A
| [] => sorry
| a :: as => a
end hd
-- ANCHOR_END: hd

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

-- ANCHOR: length
def length : List A → ℕ
| [] => 0
| a :: as => succ (length as)
-- ANCHOR_END: length

#eval (length [1,2,3])

-- ANCHOR: append
def append : List A → List A → List A
| [] , as => as
| a :: as , bs => cons a (append as bs)
-- ANCHOR_END: append

#eval append [1,2,3] [4,5,6]

infixr:65(priority := 1001) " ++ " => append

#eval [1,2,3]++[4,5,6]

def append' : List A → List A → List A
| as , [] => as
| as , b :: bs => cons b (append' as bs)

#eval append' [1,2,3] [4,5,6]

-- ANCHOR: length_append
theorem length_append : ∀ as bs : List A ,
  length (as ++ bs) = length as + length bs := by
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
-- ANCHOR_END: length_append

namespace length_append_ex

-- ANCHOR: length_append'
theorem length_append' : ∀ as bs : List A ,
  length (as ++ bs) = length bs + length as :=
by sorry
-- ANCHOR_END: length_append'

end length_append_ex

theorem length_append' : ∀ as bs : List A ,
  length (as ++ bs) = length bs + length as := by
intro as bs
induction as with
| nil =>
  calc length ([] ++ bs)
      = length bs := by rfl
    _ = length bs + length [] := by rfl
| cons a as ih =>
  calc length (a :: as ++ bs)
       = length (a :: (as ++ bs)) := by rfl
       _ = succ (length (as ++ bs)) := by rfl
       _ = succ (length bs + length as) := by rw [ih]
       _ = length bs + length (a :: as) := by rfl

-- ANCHOR: app_lneutr
theorem app_lneutr : ∀ as : List A, [] ++ as = as := by
intro as
rfl
-- ANCHOR_END: app_lneutr

-- ANCHOR: app_rneutr
theorem app_rneutr : ∀ as : List A, as ++ [] = as := by
intro as
induction as with
| nil =>
  rfl
| cons a as ih =>
  calc
    a :: as ++ []
    = a :: (as ++ []) := by rfl
    _ = a :: as := by rw [ih]
-- ANCHOR_END: app_rneutr

-- ANCHOR: app_assoc
theorem app_assoc :
∀ as bs cs : List A, (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
intro as bs cs
induction as with
| nil =>
  rfl
| cons a as ih =>
  calc
    (a :: as ++ bs) ++ cs
      = a :: ((as ++ bs) ++ cs) := by rfl
    _ = a :: (as ++ (bs ++ cs)) := by rw [ih]
    _ = a :: as ++ (bs ++ cs) := by rfl
-- ANCHOR_END: app_assoc

-- ANCHOR: snoc
def snoc : List A → A → List A
| [] , a => [a]
| a :: as , b => a :: (snoc as b)
-- ANCHOR_END: snoc

-- ANCHOR: rev
def rev : List A → List A
| [] => []
| (a :: as) => snoc (rev as) a
-- ANCHOR_END: rev

-- ANCHOR: revsnoc
theorem revsnoc : ∀ a : A, ∀ as : List A,
  rev (snoc as a) = a :: rev as := by
intro a as
induction as with
| nil => rfl
| cons b as ih =>
    calc
      rev (snoc (b :: as) a)
        = rev (b :: snoc as a) := by rfl
      _ = snoc (rev (snoc as a)) b := by rfl
      _ = snoc (a :: rev as) b := by rw [ih]
      _ = a :: rev (b :: as) := by rfl
-- ANCHOR_END: revsnoc

namespace revrev

-- ANCHOR: revrev_try
theorem revrev : ∀ as : List A , rev (rev as) = as := by
intro as
induction as with
| nil => rfl
| cons a as ih =>
  calc
    rev (rev (a :: as))
      = rev (snoc (rev as) a) := by rfl
    _ = a :: rev (rev as) := by sorry
    _ = a :: as := by rw [ih]
-- ANCHOR_END: revrev_try

end revrev

-- ANCHOR: revrev
theorem revrev : ∀ as : List A , rev (rev as) = as := by
intro as
induction as with
| nil => rfl
| cons a as ih =>
  calc
    rev (rev (a :: as))
      = rev (snoc (rev as) a) := by rfl
    _ = a :: rev (rev as) := by rw [revsnoc]
    _ = a :: as := by rw [ih]
-- ANCHOR_END: revrev

-- ANCHOR: fastrev
def revaux : List A → List A → List A
| [] , bs => bs
| a :: as , bs => revaux as (a :: bs)

def fastrev : List A → List A
| l => revaux l []
-- ANCHOR_END: fastrev

namespace fastrev

-- ANCHOR: fastrev_thm
theorem fastrev_thm : ∀ as : List A ,
    fastrev as = rev as := by
sorry
-- ANCHOR_END: fastrev_thm
end fastrev

theorem snoc_append : ∀ as bs : List A, ∀ a : A,
  as ++ a :: bs = snoc as a ++ bs := by
  intro as bs a
  induction as with
  | nil => rfl
  | cons b as ih =>
      calc b :: as ++ a :: bs
          = b :: (as ++ a :: bs) := by rfl
        _ = b :: (snoc as a ++ bs) := by rw [ih]
        _ = snoc (b :: as) a ++ bs:= by rfl

theorem fastrev_lem : ∀ as bs : List A,
  revaux as bs = rev as ++ bs := by
intro as
induction as with
| nil =>
    intro bs
    rfl
| cons a as ih =>
    intro bs
    calc
      revaux (a :: as) bs
        = revaux as (a :: bs) := by rfl
      _ = rev as ++ a :: bs := by rw [ih]
      _ = snoc (rev as) a ++ bs := by rw [snoc_append]
      _ = rev (a :: as) ++ bs := by rfl

theorem fastrev_thm : ∀ as : List A ,
    fastrev as = rev as := by
intro as
calc
  fastrev as
    = revaux as [] := by rfl
  _ = rev as ++ [] := by rw [fastrev_lem]
  _ = rev as := by rw [app_rneutr]

end ListProofs
