namespace ClassicalProofs
variable {P Q R : Prop}

-- ANCHOR: ExampleDm1
theorem dm1 : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  · intro npq
    constructor
    · intro p
      apply npq
      left
      exact p
    · intro q
      apply npq
      right
      exact q
  · intro npnq pq
    cases npnq with
    | intro np nq =>
      cases pq with
      | inl p =>
        apply np
        exact p
      | inr q =>
        apply nq
        exact q
-- ANCHOR_END: ExampleDm1

-- ANCHOR: ExampleDm2Attempt
theorem dm2_attempt : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro npq
    left
    intro p
    apply npq
    constructor
    exact p
    -- stuck here
    sorry
  · intro npnq pq
    cases pq with
    | intro p q =>
        cases npnq with
      |   inl np =>
          apply np
          exact p
      | inr nq =>
          apply nq
          exact q
-- ANCHOR_END: ExampleDm2Attempt

-- ANCHOR: OpenClassical
open Classical

#check em
-- ANCHOR_END: OpenClassical

-- ANCHOR: ExampleDm2Em
theorem dm2_em : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro npq
  have pnp : P ∨ ¬ P := by
    apply em
  cases pnp with
  | inl p =>
    right
    intro q
    apply npq
    constructor
    · exact p
    · exact q
  | inr np =>
    left
    exact np
-- ANCHOR_END: ExampleDm2Em

-- ANCHOR: ExampleRaa
theorem byContradiction : ¬¬ P → P := by
  intro nnp
  have pnp : P ∨ ¬ P := by
    apply em
  cases pnp with
  | inl p =>
      exact p
  | inr np =>
      have pcf : False := by
        apply nnp
        exact np
      cases pcf
-- ANCHOR_END: ExampleRaa

-- ANCHOR: ExampleNnEm
theorem nnEm : ¬ ¬ (P ∨ ¬ P) := by
  intro npnp
  apply npnp
  right
  intro p
  apply npnp
  left
  exact p
-- ANCHOR_END: ExampleNnEm

-- ANCHOR: ExampleAxRaa
axiom AxbyContradiction : ¬¬ P → P

theorem em : P ∨ ¬ P := by
  apply AxbyContradiction
  apply nnEm
-- ANCHOR_END: ExampleAxRaa

end ClassicalProofs
