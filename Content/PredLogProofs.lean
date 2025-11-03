--import Content.ClassicalProofs
--import Mathlib.Tactic
--open ClassicalProofs
notation "ℕ" => Nat

variable {P Q R : Prop}

-- ANCHOR: ExampleTypes
variable {A B C : Type}
-- ANCHOR_END: ExampleTypes

-- ANCHOR: ExampleFuns
def double : ℕ → ℕ
| n => n + n

def foo : ℕ → ℕ → ℕ
| m , n => m + n + n
-- ANCHOR_END: ExampleFuns

axiom n : ℕ
--axiom (a : ℕ) (b : Bool)
-- ANCHOR: ExampleFuns2
def double' (n : ℕ) : ℕ
:= n + n

def foo' (m n : ℕ) : ℕ
:= m + n + n
-- ANCHOR_END: ExampleFuns2

-- ANCHOR: ExampleApp
#eval double 2
#eval foo' 2 3
-- ANCHOR_END: ExampleApp

-- ANCHOR: ExamplePred
variable {PP QQ : A → Prop}
-- ANCHOR_END: ExamplePred

-- ANCHOR: ExampleProps
#check ∀ x : A, PP x ∧ Q
#check (∀ x : A , PP x) ∧ Q
#check ∀ x:A , (∃ x : A , PP x) ∧ QQ x
#check ∀ y:A , (∃ z : A , PP z) ∧ QQ y
-- ANCHOR_END: ExampleProps

-- ANCHOR: ExampleForall
example : (∀ x : A, PP x)
  → (∀ y : A, PP y → QQ y)
  → ∀ z : A , QQ z := by
  intro p pq a
  apply pq
  apply p
-- ANCHOR_END: ExampleForall

-- ANCHOR: ExampleAllAnd
example : (∀ x : A, PP x ∧ QQ x)
  ↔ (∀ x : A , PP x) ∧ (∀ x : A, QQ x) := by
  constructor
  intro h
  constructor
  intro a
  have pq : PP a ∧ QQ a := by
    apply h
  cases pq with
  | intro pa qa => exact pa
  intro a
  have pq : PP a ∧ QQ a := by
    apply h
  cases pq with
  | intro pa qa => exact qa
  intro h
  cases h with
  | intro hp hq =>
    intro a
    constructor
    apply hp
    apply hq
-- ANCHOR_END: ExampleAllAnd

-- ANCHOR: ExampleExists
example :
    (∃ x : A, PP x) →
    (∀ y : A, PP y → QQ y) →
    ∃ z : A , QQ z := by
  intro p pq
  cases p with
  | intro a pa =>
    exists a
    apply pq
    apply pa
-- ANCHOR_END: ExampleExists

-- ANCHOR: ExampleExistsConstr
example :
    (∃ x : A, PP x) →
    (∀ y : A, PP y → QQ y) →
    ∃ z : A , QQ z := by
  intro p pq
  cases p with
  | intro a pa =>
    constructor
    apply pq
    assumption
-- ANCHOR_END: ExampleExistsConstr

-- ANCHOR: ExampleExOr
example :
    (∃ x : A, PP x ∨ QQ x) ↔
    (∃ x : A , PP x) ∨ (∃ x : A, QQ x) := by
  constructor
  · intro h
    cases h with
    | intro a ha =>
      cases ha with
      | inl pa =>
          left
          exists a
          -- exact pa, not needed
      | inr qa =>
          right
          exists a
          -- exact qa, not needed
  · intro h
    cases h with
    | inl hp =>
        cases hp with
        | intro a pa =>
          exists a
          left
          exact pa
    | inr hq =>
        cases hq with
        | intro a qa =>
          exists a
          right
          exact qa
-- ANCHOR_END: ExampleExOr

-- ANCHOR: ExampleCurryPred
theorem curryPred :
    ((∃ x : A, PP x) → R)  ↔  (∀ x : A, PP x → R) := by
  constructor
  · intro ppr
    intro a p
    apply ppr
    exists a
  · intro ppr
    intro pp
    cases pp with
    | intro a p =>
      exact ppr a p
-- ANCHOR_END: ExampleCurryPred

-- ANCHOR: ExampleEqRefl
example : ∀ x : A, x = x := by
  intro a
  rfl
-- ANCHOR_END: ExampleEqRefl

-- ANCHOR: ExampleEqRw
example : ∀ x y : A, x = y → PP y → PP x := by
  intro x y eq p
  rw [eq]
  exact p
-- ANCHOR_END: ExampleEqRw

-- ANCHOR: ExampleEqRw2
example : ∀ x y : A, x = y → PP x → PP y := by
  intro x y eq p
  rw [← eq]
  exact p
-- ANCHOR_END: ExampleEqRw2

-- ANCHOR: ExampleEqSym
theorem symEq : ∀ x y : A, x = y → y = x := by
  intro x y p
  rw [p]
-- ANCHOR_END: ExampleEqSym

-- ANCHOR: ExampleEqTrans
theorem transEq : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  rw [xy]
  exact yz
-- ANCHOR_END: ExampleEqTrans

-- ANCHOR: ExampleEqTrans2
theorem transEq' : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  rw [← xy] at yz
  exact yz
-- ANCHOR_END: ExampleEqTrans2

-- ANCHOR: ExampleEqTacs
example : ∀ x y : A, x = y → y = x := by
  intro x y p
  symm
  exact p

example : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  apply transEq
  exact xy
  exact yz
-- ANCHOR_END: ExampleEqTacs

-- ANCHOR: ExampleCalc
example : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  calc
    x = y := by exact xy
    _ = z := by exact yz
-- ANCHOR_END: ExampleCalc

-- ANCHOR: ExampleCongr
example : ∀ f : A → B, ∀ x y : A, x = y → f x = f y := by
  intro f x y h
  rw [h]
-- ANCHOR_END: ExampleCongr

-- ANCHOR: ExampleDm1Pred
theorem dm1_pred {A : Type} {PP : A → Prop} :
    ¬ (∃ x : A, PP x) ↔ ∀ x : A, ¬ PP x := by
  constructor
  · intro h x px
    apply h
    constructor
    apply px
  · intro h np
    cases np with
    | intro a pa =>
        apply h
        apply pa
-- ANCHOR_END: ExampleDm1Pred

open Classical

-- ANCHOR: ExampleDm2Pred
theorem dm2Pred {A : Type} {PP : A → Prop} :
    ¬ (∀ x : A, PP x) ↔ ∃ x : A, ¬ PP x := by
  constructor
  · intro h
    apply byContradiction
    intro ne
    apply h
    intro a
    apply byContradiction
    intro np
    apply ne
    constructor
    apply np
  · intro h na
    cases h with
    | intro a np =>
        apply  np
        apply na
-- ANCHOR_END: ExampleDm2Pred
