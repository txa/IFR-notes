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
