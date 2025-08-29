variable {P Q R : Prop}

-- ANCHOR: ExampleTypes
variable {A B C : Type}
-- ANCHOR_END: ExampleTypes

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
    constructor
    apply pq
    apply pa
-- ANCHOR_END: ExampleExists

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
          apply Or.inl
          constructor
          apply pa
      | inr qa =>
          apply Or.inr
          constructor
          exact qa
  · intro h
    cases h with
    | inl hp =>
        cases hp with
        | intro a pa =>
          constructor
          apply Or.inl
          exact pa
    | inr hq =>
        cases hq with
        | intro a qa =>
          constructor
          apply Or.inr
          exact qa
-- ANCHOR_END: ExampleExOr
