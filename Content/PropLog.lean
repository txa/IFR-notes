import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.PropLogicProofs"

#doc (Manual) "Propositional Logic" =>

# What is a proposition?

See {ref "intro"}[The Introduction]

A proposition is a definitive statement which we may be able to
prove. In Lean we write `P : Prop` to express that `P` is a
proposition.

We will later introduce ways to construct interesting propositions
i.e. mathematical statements or statements about programs, but in the moment
we will use propositional variables instead. We declare in Lean:
```anchor Vars
variable (P Q R : Prop)
```

This means that  {anchorTerm Vars}`P Q R` are propositional variables which may
be substituted by any concrete propositions. In the moment it is helpful to think of them as statements
like "The sun is shining" or "We go to the zoo."

We introduce a number of connectives and logical constants to construct propositions:
* Implication (`→`), read `P → Q` as *if* `P` *then* `Q`.
* Conjunction (`∧`), read `P ∧ Q` as `P` *and* `Q`.
* Disjunction (`∨`), read `P ∨ Q` as `P` *or* `Q`.
Note that we understand *or* here as inclusive, it is ok that both are true.

* `false`, read `false` as *Pigs can fly*.
* `true`, read `true` as *It sometimes rains in England.*
* Negation (`¬`), read `¬ P` as *not* `P`.

  We define `¬ P` as `P → false`.

* Equivalence, (`↔`), read `P ↔ Q` as `P` *is equivalent to* `Q`.

We define `P ↔ Q` as `(P → Q) ∧ (Q → P)`.

As in algebra we use parentheses to group logical expressions. To save parentheses there are a number of conventions:

* Implication and equivalence bind weaker than conjunction and disjunction.

  E.g. we read `P ∨ Q → R` as `(P ∨ Q) → R`.
* Implication binds stronger than equivalence.

  E.g. we read `P → Q ↔ R` as `(P → Q) ↔ R`.
* Conjunction binds stronger than disjunction.

  E.g. we read `P ∧ Q ∨ R` as `(P ∧ Q) ∨ R`.
* Negation binds stronger than all the other connectives.

  E.g. we read `¬ P ∧ Q` as `(¬ P) ∧ Q`.
* Implication is right associative.

  E.g. we read `P → Q → R` as `P → (Q → R)`.

This is not a complete specification. If in doubt use parentheses.

We will now discuss how to prove propositions in Lean. If we are
proving a statement containing propositional variables then this means
that the statement is true for all replacements of the variables with
actual propositions. We say it is a tautology.

Tautologies are sort of useless in everyday conversations because they contain no information. However, for our study of logic they are important because they exhibit the basic figures of reasoning.

# Our first proof

In Lean we write `p : P` for `p` proves the proposition `P`. For our purposes a proof is a sequence of *tactics* affecting the current proof state (the assumptions we have made and the current goal). In Lean 4, a tactic proof starts with `by`, and tactics go on separate lines (no commas).

We start with a very simple tautology `P → P`: If `P` then `P`. We can illustrate this with the statement *if the sun shines then the sun shines*. Clearly, this sentence contains no information about the weather; it is vacuously true—indeed, a tautology.

Here is how we prove it in Lean:

with anchor
```anchor ExampleI
theorem I : P → P := by
  intro h
  exact h
```
We tell Lean that we want to prove a `theorem` (maybe a bit too
grandiose a name for this) named `I` (for identity). The actual proof
is just two lines, which invoke *tactics*:

* `intro h` means that we are going to prove an implication by assuming the premise (the left hand side) and using this assumption to prove
  the conclusion (the right hand side). If you look at the html version of this document you can click on *Try it* to open lean in a separate
  window.  When you move the cursor before `assume h` you see that the proof state is:
