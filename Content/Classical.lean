import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.ClassicalProofs"

#doc (Manual) "Classical Logic" =>

We stick to propositional logic for the moment but discuss a
difference between the logic based on truth you may have
seen before and the logic based on evidence which we have introduced
in the previous chapter.

The truth‑based logic is called *classical logic* while the evidence‑
based one is called *intuitionistic logic*.

# The de Morgan laws

The de Morgan laws state that if you negate a disjunction or
conjunction this is equivalent to the negation of their components
with the disjunction replaced by conjunction and vice versa. More
precisely:

```
¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q
¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q
```

These laws reflect the observation that the truth tables for `∧` and
`∨` can be transformed into each other if we turn them around and
swap `True` and `False`.

:::table
*
  * P
  * Q
  * `P ∧ Q`
  * `P ∨ Q`
  * `¬ P ∧ ¬ Q`
  * `¬ P ∨ ¬ Q`
  * `¬(P ∧ Q)`
  * `¬(P ∨ Q)`
*
  * False
  * False
  * False
  * False
  * True
  * True
  * True
  * True
*
  * True
  * False
  * False
  * True
  * False
  * True
  * True
  * False
*
  * False
  * True
  * False
  * True
  * False
  * True
  * True
  * False
*
  * True
  * True
  * True
  * True
  * False
  * False
  * False
  * False
:::

Here is the proof of the first de Morgan law in its full glory.
```anchor ExampleDm1
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
```
It is rather boring because there are a lot of symmetric cases but I
didn't break a sweat proving it. However, the 2nd law is a different
beast. Here is my attempt (left‑to‑right direction gets stuck):
```anchor ExampleDm2Attempt
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
```
As you see I got stuck with the left to right direction, the right to
left one went fine. What is the problem? The proof state after
`intro npq`
is (ignoring the propositional assumptions and the other goal):

```
  npq : ¬(P ∧ Q)
  ⊢ ¬P ∨ ¬Q
```

Now the question is do we go `left` or `right` - there seems to be
no good reason for either because everything is symmetric. Ok let's
try `left` we end up with:

```
  npq : ¬(P ∧ Q)
  ⊢ ¬P
```

Now the next steps is obvious `intro p`:

```
  npq : ¬(P ∧ Q),
  p : P
  ⊢ false
```

There is only one purveyor of `False`, hence we say `apply npq`:

```
  npq : ¬(P ∧ Q),
  p : P
  ⊢ P ∧ Q
```

Now we say `constructor` and the first subgoal is easily disposed
with `exact p` but we end up with:

```
  npq : ¬(P ∧ Q),
  p : P
  ⊢ Q
```

And there is no good way to make progress here, indeed it could be
that `P` is true but `Q` is false. As soon as we said `left` we
ended up with an unprovable goal.

What has happened? The truth tables provided clear evidence that the
de Morgan law should hold but we couldn't prove it. Indeed let's
consider the following example: *It is not the case that I have a cat*
*and* *that I have a dog* can we conclude that *I don't have a cat*
*or* *I
don't have a dog* ? No because we don't know which one is the case,
that is we don't have evidence for either.

# The law of the excluded middle

To match the truth semantics we need to assume one axiom, the *law of
the excluded middle* (`em`). This expresses the idea that every proposition
is either true or false: `P ∨ ¬ P` for any proposition `P`.
```anchor OpenClassical
open Classical

#check em
```
```anchorInfo OpenClassical
Classical.em (p : Prop) : p ∨ ¬p
```

Using `em P`, we can prove the missing direction of the 2nd de Morgan
law (and hence the equivalence `¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q`).
```anchor ExampleDm2Em
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
```
The idea of the proof is that we look at both cases of `P ∨ ¬ P`. If
`P` holds then we can prove `¬ Q` from `¬ (P ∧ Q)`, otherwise if
we know `¬ P` then we can obviously prove `¬ P ∨ ¬ Q`.

# Indirect proof

There is another law which is equivalent to the principle of excluded
middle and this is the *principle of indirect proof* or in latin
*reduction ad absurdo* (reduction to the absurd). This principle tells
you that to prove `P` it is sufficient to show that `¬ P` is
impossible. Here is how we derive this using `em`:
```anchor ExampleRaa
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
```

The idea is to assume `¬¬ P` and then prove `P` by analysing `P ∨
¬ P`: In the case `P` we are done and in the case `¬ P` we have a
contradiction with `¬¬ P` and we can use that false implies
everything.

We can also derive `em` from `byContradiction`. The key observation is that we can
actually prove `¬ ¬ (P ∨ ¬ P)` without using classical logic.
```anchor ExampleNnEm
theorem nnEm : ¬ ¬ (P ∨ ¬ P) := by
  intro npnp
  apply npnp
  right
  intro p
  apply npnp
  left
  exact p
```
This proof is a bit weird. After `apply npnp` we have the following
state:

```
P : Prop,
npnp : ¬(P ∨ ¬P)
⊢ P ∨ ¬P
```

Now you may say again do we go left or right? But this time the cases
are not symmetric. we certainly cannot prove `P` hence let's go
right. After a few steps we are in the same situation again:

```
P : Prop,
npnp : ¬(P ∨ ¬P),
p : P
⊢ P ∨ ¬P
```

But something has changed! We have picked up the assumption `p :
P`. And hence this time we go left and we are done.

Here is a little story which relies on the idea that double negating
corresponds to time travel:

  "There was a magician who could time travel who wanted to marry the
  daughter of a king. There was no gold in the country but people were
  not sure wether diamonds exist. Hence the king set the magician the
  task to either find a diamond or to produce a way to turn diamonds
  into gold. The magician went for the 2nd option and gave the king an
  empty box so he could marry the daughter. However, if the king would
  get hold of a diamond at some point and his lie would become obvious
  he would just take the diamond, travel back in time and go for the
  first option."

Now if we assume we have an axiom proving `byContradiction` we can show `em`:
```anchor ExampleAxRaa
axiom AxbyContradiction : ¬¬ P → P

theorem em : P ∨ ¬ P := by
  apply AxbyContradiction
  apply nnEm
```
Note that while `em` and `raa` are equivalent as global principles
this is not the case for individual propositions. That is if we assume
`P ∨ ¬ P` we can prove `¬¬ P → P` for the same proposition `P`
but if we assume `¬¬ P → P` we cannot prove `P ∨ ¬ P` for that
proposition but we actually need a different instance of `raa`
namely : `¬¬ (P ∨ ¬ P) → P ∨ ¬ P`.

# Intuitionistic vs classical logic

Should we always assume `em` (or alternatively `raa`), hence should we always work in
classical logic? There is a philosophical and a pragmatic argument in
favour of avoiding it and using intuitionistic logic.

The philosophical argument goes like this: while facts about the real
world are true or false even if we don't know them this isn't so
obvious about mathematical constructions which take place in our
head. The set of all numbers doesn't exist in the real world it is
like a story we share and we don't know wether anything we make up is
either true or false. However, we can talk about evidence without
needing to assume that.

The idea that the world of ideas is somehow real, and that the real
world is just a poor shadow of the world of ideas was introduced by
the greek philosopher Plato and hence is called *Platonism*. In contrast that our ideas are
just constructions in our head is called *Intuitionism*.

However, the pragmatic argument is maybe more
important. Intuitionistic logic is constructive,
indeed in a way that is dear to us computer scientists: whenever we
show that something exists we are actually able to compute it.
As a consequence intuitionistic logic introduces many distinctions
which are important especially in computer science. For example we can
distinguish decidable properties from properties in general. Also by a
function we mean something we can compute like in a (functional) programming
language.

Here is a famous example to show that the principle of excluded middle
destroys constructivity. Since we haven't yet introduced predicate
logic and many of the concepts needed for this example in Lean I
present this just as an informal argument:

{comment}[Math mode doesn't work]
  We want to show that there are two irrational numbers `p` and `q`
  (that is numbers that cannot be written as fractions) such that
  their power $`p^q` is rational. We know that $`\sqrt{2}`
  is irrational. Now what is $`\sqrt{2}^{\sqrt{2}}`? Using the
  excluded middle it is either rational or irrational. If it is
  rational then we are done $`p = q =\sqrt{2}` . Otherwise we use
  $`p = \sqrt{2}^{\sqrt{2}}` which we now assume to be irrational
  and  $`q = \sqrt{2}`. Now a simple calculation shows
  $`p^q = (\sqrt{2}^{\sqrt{2}}) ^{\sqrt{2}} = \sqrt{2}^{\sqrt{2}\sqrt{2}} = \sqrt{2}^2 = 2`
  which is certainly rational.

Now after this proof we still don't know two irrational numbers whose
power is rational. I hasten to add that we can establish this fact
without using `em` but this particular proof doesn't provide a
witness because it is using excluded middle.

In the homework we will distinguish proofs that use excluded middle
and once which do not. In my logic poker I ask you to prove
propositions intuitionistically where possible and only use classical
reasoning where necessary.

Now a common question is how to see wether a proposition is only
provable classically. E.g. why can we prove all the first de Morgan
law and one direction of the 2nd but not `¬ (P ∧ Q) → ¬ P ∨ ¬ Q`?
The reason is that the right hand side contains some information,
i.e. which of the `¬ P` or `¬ Q` is true while `¬ (P ∧ Q)` is a
*negative* proposition and hence does contain no
information. In contrast the both sides of the first de Morgan law
`¬ (P ∨ Q)` and `¬ P ∧ ¬ Q` are negative, i.e. contain no
information.
