import Content.NatProofs

namespace ListProofs
set_option tactic.customEliminators false -- to stop lean using +1
set_option pp.fieldNotation false
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

--open List
open List hiding Perm perm_cons perm_nil

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

--- sort


-- ANCHOR: insert
def insert : ℕ → List ℕ → List ℕ
| n , [] => [n]
| n , (m :: ms) =>
    match le_ℕ n m with
    | true => n :: m :: ms
    | false => m :: insert n ms
-- ANCHOR_END: insert

-- ANCHOR: sort
def sort : List ℕ → List ℕ
| [] => []
| (n :: ns) => insert n (sort ns)
-- ANCHOR_END: sort

#eval sort [6,3,8,2,3]

-- ANCHOR: Mem
inductive Mem : A → List A → Prop

| mem_hd : ∀ {a : A}, ∀ {as : List A},
    ---------------
    Mem a (a :: as)

| mem_tl : ∀ {a b : A}, ∀ {as : List A},
      Mem a as →
      ---------------
      Mem a (b :: as)
-- ANCHOR_END: Mem

infix:50 (priority := 1001)" ∈ " => Mem

open Mem

-- ANCHOR: x2in123
example : 2 ∈ [1,2,3] := by
  apply mem_tl
  apply mem_hd
-- ANCHOR_END: x2in123

-- ANCHOR: mem_empty
example : ∀ a : A , ¬ (a ∈ ([] : List A)) := by
  intro a pcf
  cases pcf
-- ANCHOR_END: mem_empty

-- ANCHOR: mem12
example : ∀ n : ℕ, n ∈ [1,2] → n = 1 ∨ n = 2 := by
  intro n h
  cases h with
  | mem_hd =>
      left
      rfl
  | mem_tl h' =>
      cases h' with
      | mem_hd =>
          right
          rfl
      | mem_tl pcf =>
          cases pcf
-- ANCHOR_END: mem12

-- ANCHOR: Sorted
inductive Sorted : List ℕ → Prop

| sorted_nil :
    ---------
    Sorted []

| sorted_cons : ∀ {m : ℕ}, ∀ {ns : List ℕ},
    Sorted ns →
    (∀ n : ℕ , n ∈ ns → m ≤ n)
    --------------------------
    → Sorted (m :: ns)
-- ANCHOR_END: Sorted

open Sorted

-- ANCHOR: Sorted123
example : Sorted [1,2,3] := by
  apply sorted_cons
  . apply sorted_cons
    . apply sorted_cons
      . apply sorted_nil
      . intro n h
        cases h
    . intro n h
      cases h with
      | mem_hd =>
          apply le2LE
          rfl
      | mem_tl x => cases x
  . intro n h
    cases h with
    | mem_hd =>
        apply le2LE
        rfl
    | mem_tl hh =>
       cases hh with
       | mem_hd =>
          apply le2LE
          rfl
       | mem_tl hhh => cases hhh
-- ANCHOR_END: Sorted123

theorem LE_lem : ∀ n m : ℕ, ¬ (m ≤ n) → n ≤ m := by
  intro n
  induction n with
    intro m h
    | zero =>
        exists m
    | succ n ih =>
        cases m with
        | zero =>
            have pcf : False := by
              apply h
              exists succ n
            cases pcf
        | succ m =>
            have hh : ¬ (m ≤ n) := by
              intro mn
              apply h
              cases mn with
              | intro k kmn =>
                  exists k
                  rw [← kmn]
                  rfl
            have nm : n ≤ m := by
              apply ih
              assumption
            cases nm with
            | intro j jnm =>
                exists j
                rw [← jnm]
                rfl

variable (PP QQ : A → Prop)

theorem forall_mono :
  (∀ a : A, PP a → QQ a)
  → ∀ as : List A,
    (∀ a : A, a ∈ as → PP a)
    →
    (∀ a : A, a ∈ as → QQ a) := by
  intro pq as p a aas
  induction as with
  | nil => cases aas
  | cons b bs ih =>
      cases aas with
      | mem_hd =>
          apply pq
          apply p
          apply mem_hd
      | mem_tl hh =>
          apply ih
          intro a abs
          apply p
          apply mem_tl
          assumption
          assumption


theorem mem_mono :
    ∀ m l k : ℕ, ∀ ns : List ℕ,
    (∀ i : ℕ , i ∈ ns → m ≤ i)
    → l ≤ m
    → k ∈ ns
    → l ≤ k := by
    intro m l k ns h lm hh
    induction hh with
    | mem_hd =>
        have nk : m ≤ k := by
          apply h
          apply mem_hd
        apply trans_LE
        apply lm
        assumption
    | mem_tl x ih =>
        apply ih
        intro i ii
        apply h
        apply mem_tl
        assumption

theorem insert_lem : ∀ m n i : ℕ , ∀ ns : List ℕ ,
   m ≤ n → (∀ (j : ℕ), j ∈ ns → m ≤ j)
   → i ∈ insert n ns → m ≤ i :=
   by
    intro m n i ns mn h ins
    induction ns with
    | nil =>
        dsimp [insert] at ins
        cases ins with
        | mem_hd =>
            assumption
        | mem_tl x =>
            cases x
    | cons k ns ih =>
          dsimp [insert] at ins
          cases b : le_ℕ n k with
          | true =>
              rw [b] at ins
              cases ins with
              | mem_hd =>
                  assumption
              | mem_tl x =>
                  apply h
                  assumption
          | false =>
              rw [b] at ins
              cases ins with
              | mem_hd =>
                  apply h
                  apply mem_hd
              | mem_tl x =>
                  apply ih
                  intro j jns
                  apply h
                  apply mem_tl
                  assumption
                  assumption


theorem sorted_insert : ∀ ns : List ℕ, ∀ n : ℕ,
  Sorted ns → Sorted (insert n ns) := by
intro ns n sns
induction ns with
| nil =>
    dsimp [insert]
    apply sorted_cons
    . apply sorted_nil
    . intro k pcf
      cases pcf
| cons m ns ih =>
    dsimp [insert]
    cases b : le_ℕ n m with
    | true =>
        change Sorted (n :: m :: ns)
        apply sorted_cons
        . assumption
        . cases sns with
          | sorted_cons s h =>
            intro k kmns
            have nm : n ≤ m := by
              apply le2LE
              assumption
            cases kmns with
            | mem_hd => assumption
            | mem_tl kns =>
                apply mem_mono
                . apply h
                . assumption
                . assumption
    | false =>
        change Sorted (m :: insert n ns)
        cases sns with
          | sorted_cons s h =>
              apply sorted_cons
              . apply ih
                assumption
              . have mn : m ≤ n := by
                  have nh : ¬ (n ≤ m) := by
                    intro nm
                    have lnm : le_ℕ n m = true := by
                      apply LE2le
                      assumption
                    rw [b] at lnm
                    cases lnm
                  apply LE_lem
                  assumption
                intro i hi
                apply insert_lem
                . apply mn
                . apply h
                . assumption

-- ANCHOR: sort_sorts
theorem sort_sorts : ∀ ns: List ℕ, Sorted (sort ns) := by
  intro ns
  induction ns with
  | nil =>
      apply sorted_nil
  | cons n ns ih =>
    dsimp [sort]
    apply sorted_insert
    assumption
-- ANCHOR_END: sort_sorts

namespace sortspec1
-- ANCHOR: sort_sorts1
theorem sort_sorts : ∀ ns: List ℕ, Sorted (sort ns) := by
  sorry
-- ANCHOR_END: sort_sorts1
end sortspec1

namespace sortspec2
-- ANCHOR: sort_sorts2
theorem sort_sorts : ∀ ns: List ℕ, Sorted (sort ns) := by
  intro ns
  induction ns with
  | nil =>
      apply sorted_nil
  | cons n ns ih =>
    dsimp [sort]
    sorry
-- ANCHOR_END: sort_sorts2

-- ANCHOR: sorted_insert
theorem sorted_insert : ∀ ns : List ℕ, ∀ n : ℕ,
  Sorted ns → Sorted (insert n ns) := by
  sorry
-- ANCHOR_END: sorted_insert

end sortspec2

-- Permutation

namespace PermSpec

axiom Perm : List A → List A → Prop

-- ANCHOR: perm_sort_spec
theorem perm_sort :
  ∀ ns : List ℕ, Perm ns (sort ns) := by
sorry
-- ANCHOR_END: perm_sort_spec

end PermSpec

-- ANCHOR: Insert
inductive Insert : A → List A → List A → Prop

| ins_hd : ∀ {a:A}, ∀ {as : List A},

    ---------------------
    Insert a as (a :: as)

| ins_tl : ∀ {a b:A}, ∀ {as as': List A},

    Insert a as as' →
    -----------------------------
    Insert a (b :: as) (b :: as')
-- ANCHOR_END: Insert

open Insert

-- ANCHOR: Insert123
example : Insert 2 [1,3] [1,2,3] := by
  apply ins_tl
  apply ins_hd
-- ANCHOR_END: Insert123

-- ANCHOR: Perm
inductive Perm : List A → List A → Prop
| perm_nil :

  ---------
  Perm [] []

| perm_cons : ∀ {a : A}, ∀ {as bs bs' : List A},

  Perm as bs →
  Insert a bs bs' →
  -------------------
  Perm (a :: as) bs'
-- ANCHOR_END: Perm

open Perm

-- ANCHOR: Perm123
example : Perm [1,2,3] [3,2,1] := by
  apply perm_cons
  . apply perm_cons
    . apply perm_cons
      . apply perm_nil
      . apply ins_hd
    . apply ins_tl
      apply ins_hd
  . apply ins_tl
    apply ins_tl
    apply ins_hd
-- ANCHOR_END: Perm123

#check Insert

-- ANCHOR: insert_inserts
theorem insert_inserts : ∀ ns : List ℕ,∀ n : ℕ,
  Insert n ns (insert n ns) := by
  intro ns n
  induction ns with
  | nil =>
      dsimp [insert]
      apply ins_hd
  | cons m ms ih =>
      dsimp [insert]
      cases le_ℕ n m with
      | true =>
          change Insert n (m :: ms) (n :: m :: ms)
          apply ins_hd
      | false =>
          change Insert n (m :: ms) (m :: insert n ms)
          apply ins_tl
          assumption
-- ANCHOR_END: insert_inserts

-- ANCHOR: perm_sort
theorem perm_sort :
  ∀ ns : List ℕ, Perm ns (sort ns) := by
  intro ns
  induction ns with
  | nil =>
      dsimp [sort]
      apply perm_nil
  | cons n ns ih =>
      dsimp [sort]
      apply perm_cons
      . apply ih
      . apply insert_inserts
-- ANCHOR_END: perm_sort

-- ANCHOR: reflPerm
theorem refl_perm : ∀ as : List A, Perm as as := by
  intro as
  induction as with
  | nil => apply perm_nil
  | cons a as ih =>
      apply perm_cons
      . apply ih
      . apply ins_hd
-- ANCHOR_END: reflPerm

namespace permProps

-- ANCHOR: PermEq
theorem sym_perm : ∀ as bs : List A,
  Perm as bs → Perm bs as := by sorry

theorem trans_perm : ∀ as bs cs ds : List A,
  Perm as bs → Perm bs cs → Perm as ds := by sorry
-- ANCHOR_END: PermEq

theorem perm_tl : ∀ a : A, ∀ as bs : List A,
  Perm (a :: as) (a :: bs) → Perm as bs := by sorry

end permProps

variable {as bs cs as' bs' cs' : List A}
variable {a b : A}

theorem add_lem : Insert a as bs → Insert b bs cs → ∃ ds : List A, Insert b as ds ∧ Insert a ds cs := by
  intro h1 h2
  induction h1 generalizing cs
  case ins_hd a' =>
    cases h2
    case ins_hd =>
      constructor
      constructor
      apply ins_hd
      apply ins_tl
      apply ins_hd

    case ins_tl a' h1 =>
      constructor
      constructor
      apply h1
      apply Insert.ins_hd

  case ins_tl a' b' as' as'' h1  =>
    cases h2
    case ins_hd =>
      constructor
      constructor
      apply Insert.ins_hd
      apply Insert.ins_tl
      apply Insert.ins_tl
      exact as''

    case ins_tl ds h2' =>
      cases h1 h2' with
      | intro ds hh =>
        cases hh with
        | intro hh1 hh2 =>
          constructor
          constructor
          apply Insert.ins_tl
          apply hh1
          apply Insert.ins_tl
          apply hh2

theorem transLem : Perm bs cs → Insert a bs' bs →
  ∃ cs':List A, Perm bs' cs' ∧ Insert a cs' cs := by
  intro h1 h2
  induction h1 generalizing bs'
  case perm_nil => cases h2
  case perm_cons b as ds ds' h1 h2' ih =>
    cases h2
    case ins_hd =>
      constructor
      constructor
      apply h1
      apply h2'
    case ins_tl xs h3 =>
      cases ih h3 with
      | intro ys hh =>
        cases hh with
        | intro h4 h5 =>
          cases add_lem h5 h2' with
          | intro zs hh' =>
            cases hh' with
            | intro h6 h7 =>
              exists zs
              constructor
              apply perm_cons
              apply h4
              exact h6
              exact h7

theorem trans_perm : Perm as bs → Perm bs cs → Perm as cs := by
  intro h1 h2
  induction h1 generalizing cs
  case perm_nil =>
      cases h2
      apply perm_nil
  case perm_cons a xs ys zs h1' h ih =>
      cases transLem  h2 h with
      | intro ds' hh =>
        cases hh with
        | intro h3 h4 =>
          apply perm_cons
          apply ih h3
          apply h4

theorem sym_lem : Perm cs as → Insert a cs bs → Perm bs (a :: as) := by
  intro h1 h2
  induction h2 generalizing as
  case ins_hd a =>
    apply perm_cons
    exact h1
    apply ins_hd
  case ins_tl c ys zs h3 ih =>
    cases h1 with
    | perm_cons h4 h5 =>
      apply perm_cons
      apply ih h4
      apply ins_tl
      exact h5

theorem sym_perm : Perm as bs → Perm bs as := by
  intro h
  induction h
  case perm_nil =>
    apply Perm.perm_nil
  case perm_cons a xs ys zs h1 h2 ih =>
    apply sym_lem ih h2

namespace perm_tl
-- ANCHOR: perm_tl
theorem perm_tl : ∀ a : A, ∀ as bs : List A,
  Perm (a :: as) (a :: bs) → Perm as bs := by sorry
-- ANCHOR_END: perm_tl
end perm_tl

theorem perm_tl : ∀ a : A, ∀ as bs : List A,
  Perm (a :: as) (a :: bs) → Perm as bs := by
  intro a as bs h
  cases h
  case perm_cons bs' h1 h2 =>
    cases h2
    case ins_hd => assumption
    case ins_tl cs hi =>
      apply trans_perm
      apply h1
      apply perm_cons
      apply refl_perm
      assumption

end ListProofs
