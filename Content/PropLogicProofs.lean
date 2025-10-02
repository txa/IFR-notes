namespace PropLogicProofs
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

-- ANCHOR: ExampleComAndIfalse
theorem comAndIfalse : P ∧ Q ↔ Q ∧ P := by
  constructor
  apply comAnd
  apply comAnd
-- ANCHOR_END: ExampleComAndIfalse

-- ANCHOR: ExampleCurry
theorem curry : P ∧ Q → R ↔ P → Q → R := by
  constructor
  · intro pqr p q
    apply pqr
    constructor
    · exact p
    · exact q
  · intro pqr pq
    cases pq with
    | intro p q =>
      apply pqr
      · exact p
      · exact q
-- ANCHOR_END: ExampleCurry

-- ANCHOR: ExamplesOr
example : P → P ∨ Q := by
  intro p
  left
  exact p

example : Q → P ∨ Q := by
  intro q
  right
  exact q
-- ANCHOR_END: ExamplesOr

-- ANCHOR: ExampleCaseLem
theorem caseLem : (P → R) → (Q → R) → P ∨ Q → R := by
  intro p2r q2r pq
  cases pq with
  | inl p =>
    apply p2r
    exact p
  | inr q =>
    apply q2r
    exact q
-- ANCHOR_END: ExampleCaseLem

--ANCHOR: ExampleDistr
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
--ANCHOR_END: ExampleDistr

-- ANCHOR: ExampleTrue
example : True := by
  constructor
-- ANCHOR_END: ExampleTrue

-- ANCHOR: ExampleFalse
theorem efq : False → P := by
  intro pigs_can_fly
  cases pigs_can_fly
-- ANCHOR_END: ExampleFalse

-- ANCHOR: ExampleContr
theorem contr : ¬ (P ∧ ¬ P) := by
  intro pnp
  cases pnp with
  | intro p np =>
    apply np
    exact p
-- ANCHOR_END: ExampleContr

-- ANCHOR: ExampleHave
example : (P → Q ∨ Q) → (P → Q) := by
  intro h p
  have qorq : Q ∨ Q := by
    apply h
    exact p
  cases qorq with
  | inl q =>
      exact q
  | inr q =>
      exact q
-- ANCHOR_END: ExampleHave

-- ANCHOR: ExampleAss
example : P → P := by
  intro h
  assumption
-- ANCHOR_END: ExampleAss

end PropLogicProofs
