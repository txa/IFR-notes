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

open Mem

theorem mem_append_1 :
  ∀ a : A, ∀ as bs : List A,
  a ∈ as ++ bs → a ∈ as ∨ a ∈ bs := by
  intro a as bs
  induction as with
  | nil =>
      intro h
      right
      apply h
  | cons c cs ih =>
      intro h
      cases h with
      | mem_hd =>
          left
          apply mem_hd
      | mem_tl x =>
          have h2 : a ∈ cs ∨ a ∈ bs := by
            apply ih
            assumption
          cases h2 with
          | inl h2l =>
              left
              apply mem_tl
              assumption
          | inr h2r =>
              right
              assumption

theorem mem_append_2 :
  ∀ a : A, ∀ as bs : List A,
  a ∈ as ∨ a ∈ bs → a ∈ as ++ bs := by
  intro a as bs
  induction as with
  | nil =>
      intro h
      cases h with
      | inl hl =>
          cases hl
      | inr hr =>
          apply hr
  | cons c cs ih =>
      intro h
      cases h with
        | inl hl =>
            cases hl with
            | mem_hd =>
                apply mem_hd
            | mem_tl x =>
                apply mem_tl
                apply ih
                left
                assumption
        | inr hr =>
            apply mem_tl
            apply ih
            right
            assumption

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
      dsimp [tree2list]
      cases b : le_ℕ n m with
      | true =>
          rw [b] at h
          change i ∈ tree2list (add l n) ++ ([m]++ tree2list r )at h
          have hh : i ∈ tree2list (add l n) ∨ i ∈ [m] ++ tree2list r := by
            apply mem_append_1
            assumption
          cases hh with
          | inl iln =>
              have h3 : i ∈ tree2list l ∨ i = n := by
                apply ihl
                assumption
              cases h3 with
              | inl h3l =>
                    left
                    apply mem_append_2
                    left
                    assumption
              | inr h3r =>
                    right
                    assumption
          | inr imr =>
              left
              apply mem_append_2
              right
              assumption
      | false =>
          rw [b] at h
          change i ∈ tree2list l ++ ([m]++ tree2list (add r n)) at h
          have hh : i ∈ tree2list l ∨ i ∈ [m] ++ tree2list (add r n) := by
            apply mem_append_1
            assumption
          cases hh with
          | inl il =>
              left
              apply mem_append_2
              left
              assumption
          | inr imr =>
              have h3 : i ∈ [m] ∨ i ∈ tree2list (add r n) := by
                apply mem_append_1
                assumption
              cases h3 with
              | inl h3l =>
                  left
                  apply mem_append_2
                  right
                  apply mem_append_2
                  left
                  assumption
              | inr h3r =>
                  have h4 : i ∈ tree2list r ∨ i = n := by
                    apply ihr
                    assumption
                  cases h4 with
                    | inl h4l =>
                        left
                        apply mem_append_2
                        right
                        apply mem_append_2
                        right
                        assumption
                    | inr h4r =>
                        right
                        assumption


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
            | false =>
                change Sorted_tree (node l m (add r n))
                apply sorted_node
                . assumption
                . assumption
                . apply ihr
                  assumption
                . intro i h
                  have hh : i ∈ tree2list r ∨ i = n := by
                    apply add_lem
                    assumption
                  cases hh with
                  | inl il =>
                      apply hr
                      assumption
                  | inr ir =>
                      rw [ir]
                      apply LE_lem
                      intro nnm
                      have nm : le_ℕ n m = true := by
                        apply LE2le
                        assumption
                      rewrite [b] at nm
                      cases nm

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


end tree_sort
