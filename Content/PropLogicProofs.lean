-- ANCHOR: Vars
variable (P Q R : Prop)
-- ANCHOR_END: Vars
-- ANCHOR: CheckImpl
#check P → Q
-- ANCHOR_END: CheckImpl
-- ANCHOR: ExampleI
theorem I : P → P := by
  intro h
  exact h
-- ANCHOR_END: ExampleI
-- ANCHOR: ExampleC
theorem C : (P → Q) → (Q → R) → P → R := by
  intro p2q
  intro q2r
  intro p
  apply q2r
  apply p2q
  exact p
-- ANCHOR_END: ExampleC
-- ANCHOR: ExampleSwap
theorem swap : (P → Q → R) → (Q → P → R) := by
  intro f q p
  apply f
  exact p
  exact q
-- ANCHOR_END: ExampleSwap

-- ANCHOR: PrintI
#print I
-- ANCHOR_END: PrintI

-- ANCHOR: PrintC
#print C
-- ANCHOR_END: PrintC

-- ANCHOR: ExampleAndI
example : P → Q → P ∧ Q := by
  intro p q
  constructor
  exact p
  exact q
-- ANCHOR_END: ExampleAndI

-- ANCHOR: ExampleComAnd
theorem comAnd : P ∧ Q → Q ∧ P := by
  intro pq
  cases pq with
  | intro p q =>
    constructor
    exact q
    exact p
-- ANCHOR_END: ExampleComAnd

-- ANCHOR: ExampleComAndIff
theorem comAndIff : P ∧ Q ↔ Q ∧ P := by
  constructor
  apply comAnd
  apply comAnd
-- ANCHOR_END: ExampleComAndIff
