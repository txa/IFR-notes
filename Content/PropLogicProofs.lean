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
