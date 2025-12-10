import Content.NatProofs
import Content.ListProofs
set_option pp.fieldNotation false
set_option tactic.customEliminators false -- to stop lean using +1

namespace tree_sort
open NatProofs hiding add
open ListProofs

open Nat
-- tree sort

inductive Tree : Type
| leaf : Tree
| node : Tree → ℕ → Tree → Tree

open Tree

def add : Tree → ℕ → Tree
| leaf , n => node leaf n leaf
| node l m r , n =>
    match le_ℕ n m with
    | true => node (add l n) m r
    | false => node l m (add r n)

def list2tree : List ℕ → Tree
| [] => leaf
| n :: ns => add (list2tree ns) n

def tree2list : Tree → List ℕ
| leaf => []
| node l m r => tree2list l ++ [m] ++ tree2list r

def sort : List ℕ → List ℕ
| ns => tree2list (list2tree ns)

#eval sort [6,3,8,2,3]

open Sorted

inductive Sorted_tree : Tree → Prop
| sorted_leaf :

    -----------
    Sorted_tree leaf

| sorted_node :

    ∀ {l r : Tree}, ∀ {n : ℕ},

    Sorted_tree l →
    (∀ i : ℕ, i ∈ tree2list l → i ≤ n) →
    Sorted_tree r →
    (∀ i : ℕ, i ∈ tree2list r → n ≤ i) →
    -------------------------------------
    Sorted_tree (node l n r)

open Sorted_tree

variable {A B C : Type}

theorem mem_append : 
  ∀ a : A, ∀ as bs : List A,
  a ∈ as ++ bs → a ∈ as ∨ a ∈ bs := by sorry

theorem add_lem : ∀ t : Tree, ∀ i n : ℕ,
  i ∈ tree2list (add t n) → i ∈ tree2list t ∨ i = n := by 
  intro t i n h
  induction t with 
  | leaf => 
      cases h with 
      | mem_hd => 
          right
          rfl
      | mem_tl pcf =>
          cases pcf
  | node l m r ihl ihr =>
      dsimp [add] at h
      cases b : le_ℕ n m with
      | true => 
          rw [b] at h
          change i ∈ tree2list (add l n) ++ ([m]++ tree2list r )at h
          have hh : i ∈ tree2list (add l n) ∨ i ∈ [m] ++ tree2list r := by sorry
          cases hh with 
          | inl iln => sorry
          | inr imr => sorry
      | false => sorry


theorem sort_adds : ∀ t : Tree, ∀ n : ℕ,
   Sorted_tree t → Sorted_tree (add t n) := by
  intro t n h
  induction t with
  | leaf =>
      dsimp [add]
      apply sorted_node
      . assumption
      . intro n pcf
        cases pcf
      . apply sorted_leaf
      . intro n pcf
        cases pcf
  | node l m r ihl ihr =>
        dsimp [add]
        cases h with
        | sorted_node sl hl sr hr =>
            cases b : le_ℕ n m with
            | true =>
                change Sorted_tree (node (add l n) m r)
                apply sorted_node
                . apply ihl
                  assumption
                . intro i h
                  have hh : i ∈ tree2list l ∨ i = n := by 
                    apply add_lem
                    assumption
                  cases hh with
                  | inl il => 
                      apply hl
                      assumption
                  | inr ir => 
                      rw [ir]
                      apply le2LE 
                      assumption
                . assumption
                . assumption
            | false => sorry


theorem list2tree_sorts : ∀ ns : List ℕ,
    Sorted_tree (list2tree ns) := by
  intro l
  induction l with
  | nil =>
      apply sorted_leaf
  | cons n ns ih =>
      dsimp [list2tree]
      apply sort_adds
      assumption

-- theorem sort_adds : ∀ t : Tree, ∀ n : ℕ,
--   Sorted→ Sorted (tree2list (add t n)) := by
--   intro t n h
--   induction t with
--   | leaf =>
--       dsimp [add,tree2list]
--       change (Sorted (n :: []))
--       apply sorted_cons
--       apply sorted_nil
--       intro n pcf
--       cases pcf
--   | node l m r ihl ihr =>
--       dsimp [add]
--       cases b : le_ℕ n m with
--       | true =>
--           dsimp [tree2list]
--           sorry
--       | false => sorry


-- theorem sort_sorts : ∀ ns: List ℕ, Sorted (sort ns) := by
--   intro ns
--   induction ns with
--   | nil =>
--       apply sorted_nil
--   | cons n ms ih =>
--       dsimp [sort,list2tree]
--       apply sort_adds
--       apply ih

end tree_sort