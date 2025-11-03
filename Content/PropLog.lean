import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.PropLogicProofs"

#doc (Manual) "Propositional Logic" =>

# What is a proposition?

```comment
See {ref "intro"}[The Introduction]
```

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

* `False`, read `False` as *Pigs can fly*.
* `True`, read `True` as *It sometimes rains in England.*
* Negation (`¬`), read `¬ P` as *not* `P`.

  We define `¬ P` as `P → False`.

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

In Lean we write `p : P` for `p` proves the proposition `P`. For our purposes a proof is a sequence of *tactics* afalseecting the current proof state (the assumptions we have made and the current goal). In Lean 4, a tactic proof starts with `by`, and tactics go on separate lines (no commas).

We start with a very simple tautology `P → P`: If `P` then `P`. We can illustrate this with the statement *if the sun shines then the sun shines*. Clearly, this sentence contains no information about the weather; it is vacuously true—indeed, a tautology.

Here is how we prove it in Lean:

```anchor ExampleI
theorem I : P → P := by
  intro h
  exact h
```
We tell Lean that we want to prove a `theorem` (maybe a bit too
grandiose a name for this) named `I` (for identity). The actual proof
is just two lines, which invoke *tactics*:

* `intro h` means that we are going to prove an implication by assuming the premise (the left hand side) and using this assumption to prove
  the conclusion (the right hand side). If you look at the html version of this document you
  can view the proof state by hovering over the bubble at the end of a line.
 When you move the cursor after `by` you see that the proof state is:
```
    P : Prop
    ⊢ P → P
```
  This means we assume that `P` is a proposition and want to prove `P → P`. The `⊢` symbol (pronounced *turnstile*) separates the assumptions and the goal. After
  `intro h` the proof state is:
```
    P : Prop,
    h : P
    ⊢ P
```
  This means our goal is now `P` but we have an additional assumption `h : P`.
* `exact h` We complete the proof by telling Lean that there is an assumption that *exactly* matches the current goal. If you move the cursor to the end of the line  you see `All goals completed`. We are done.
* Alternatively we can use `assumption` in the last line which just uses any assumption which fits without us having to tell it which one.

# Using assumptions
Next we are going to prove another tautology: `(P → Q) → (Q → R) → P → R`.
Here is a translation into English:

*If if the sun shines then we go to the zoo then if if we go to the zoo then we are happy then if the sun shines then we are happy.*

Maybe this already shows why it is better to use formulas to write propositions.

Here is the proof in Lean (I call it `C` for *compose*).
```anchor ExampleC
theorem C : (P → Q) → (Q → R) → P → R := by
  intro p2q
  intro q2r
  intro p
  apply q2r
  apply p2q
  exact p
```
First of all it is useful to remember that `→` associates to the right; putting in the invisible brackets this corresponds to:
```
  (P → Q) → ((Q → R) → (P → R))
```
After the three `intro` we are in the following state:
```
  P Q R : Prop,
  p2q : P → Q,
  q2r : Q → R,
  p : P
  ⊢ R
```
Now we have to *use* an implication. Clearly it is `q2r` which can be of any help because it promises to show `R` given `Q`. Hence once we say `apply q2r` we are left to show `Q`:
```
  P Q R : Prop,
  p2q : P → Q,
  q2r : Q → R,
  p : P
  ⊢ Q
```

The next step is to use `apply p2q` to reduce the goal to `P`, which can be shown using `exact p`.

Note that there are two kinds of steps in these proofs:

* `intro h` means that we are going to prove an implication `P → Q` by assuming `P` (and we call this assumption `h`) and then
  proving `Q` with this assumption.
* `apply h` if we have assumed an implication `h : P → Q` and our current goal matches the right hand side we can use this assumption to
  *reduce* the problem to showing `P` (whether this is indeed a good idea depends on whether it is actually easier to show `P`).

The `apply` tactic is a bit more general; it can also be used to handle repeated implications. Here is an example:
```anchor ExampleSwap
theorem swap : (P → Q → R) → (Q → P → R) := by
  intro f q p
  apply f
  exact p
  exact q
```
After `intro f q p` (which is a shortcut for writing `intro` three times) we are in the following state:

```
P Q R : Prop
f : P → Q → R
q : Q
p : P
⊢ R
```

Now we can use `f` because its conclusion matches our goal, but we are left with two goals:

```
2 goals
P Q R : Prop
f : P → Q → R
q : Q
p : P
⊢ P

P Q R : Prop
f : P → Q → R
q : Q
p : P
⊢ Q
```

After completing the first goal with `exact p` it disappears and only one goal is left:

```
P Q R : Prop
f : P → Q → R
q : Q
p : P
⊢ Q
```

which we can quickly eliminate using `exact q`.

# Proof terms

What is a proof? It looks like a proof in Lean is a sequence of tactics. But this is only the surface: the tactics are more like editor commands which *generate* the real proof, which is a *program*. This also explains the syntax `p : P`, reminiscent of the notation for typing `3 :: Int` in Haskell (that Haskell uses `::` instead of `:` is a regrettable historic accident).

We can look at the programs generated from proofs by using the `#print` command in Lean. For example:
```anchor PrintI
#print I
```
```anchorInfo PrintI
theorem PropLogicProofs.I : ∀ (P : Prop), P → P :=
fun P h => h
```
and
```anchor PrintC
#print C
```
```anchorInfo PrintC
theorem PropLogicProofs.C : ∀ (P Q R : Prop), (P → Q) → (Q → R) → P → R :=
fun P Q R p2q q2r p => q2r (p2q p)
```

If you have studied functional programming (e.g. *Haskell*) you should have a *déjà vu*: indeed proofs are *functional programs*. Lean exploits the *propositions as types* translation (also known as the *Curry–Howard Equivalence*) and associates to every proposition the type of evidence for this proposition. This means that to see that a proposition holds all we need to do is to find a program in the type associated to it.

Not all Haskell programs correspond to proofs; in particular, general recursion is not permitted in proofs, only certain forms of recursion that always terminate. Also, the Haskell type system isn't expressive enough to be used in a system like Lean: it is fine for propositional logic, but it doesn't cover predicate logic, which we will introduce soon. The functional language on which Lean relies is called *dependent type theory* — more specifically, the *Calculus of Inductive Constructions*.

Type theory is an interesting subject, but we won't be able to say much in this course. If you want to learn more about this, you can attend *Proofs, Programs and Types* (COMP4074), which can also be done in year 3.

# Conjunction

How to prove a conjunction? Easy! To prove `P ∧ Q` we need to prove both `P` and `Q`. This is achieved via the `constructor` tactic. Here is a simple example (and since I don't want to give it a name, I am using `example` instead of `theorem`).

```anchor ExampleAndI
example : P → Q → P ∧ Q := by
  intro p q
  constructor
  exact p
  exact q
```
`constructor` turns the goal:

```
P Q : Prop
p : P
q : Q
⊢ P ∧ Q
```

into two goals:

```
2 goals
P Q : Prop
p : P
q : Q
⊢ P

P Q : Prop
p : P
q : Q
⊢ Q
```

Now what is your next question? Exactly! How do we use a conjunction in an assumption? Here is an example: we show that `∧` is *commutative*.

```anchor ExampleComAnd
theorem comAnd : P ∧ Q → Q ∧ P := by
  intro pq
  cases pq with
  | intro p q =>
    constructor
    exact q
    exact p
```

After `intro pq` we are in the following state:

```
P Q : Prop
pq : P ∧ Q
⊢ Q ∧ P
```

Assuming `P ∧ Q` is the same as assuming both `P` and `Q`. This is facilitated via the `cases` tactic which matches how a conjuction was created (and we learn the the *constructor* for `∧` is called `intro`). Hence after
```
cases pq with
  | intro p q =>
```
the state is
```
P Q : Prop
p : P
q : Q
⊢ Q ∧ P
```
The name `cases` seems to be a bit misleading since there is only one case to consider here. However, as we will see, `cases` is applicable more generally in situations where the name is better justified. And yes this is just pattern matching as you may have seen already in Haskell.

I hope you notice the same symmetry between tactics for *how to prove* and *how to use* which we have seen for implication also shows for conjunction. This pattern is going to continue.

It is good to know that Lean always abstracts the propositional variables we have declared. We can actually use `comAnd` with different instantiation to prove the following:

```anchor ExampleComAndIfalse
theorem comAndIfalse : P ∧ Q ↔ Q ∧ P := by
  constructor
  apply comAnd
  apply comAnd
```

Why is the first step `constructor`? Because as we said before

>  We define `P ↔ Q` as `(P → Q) ∧ (Q → P)`.

(actually this is only approximately true but good enough at our current stage.)

In the second use of `comAnd` we instantiate `Q` with `P` and `P` with `Q`. Lean can usually infer these instantiations automatically from the goal, but in more complicated situations it may need a hint. We can write:
```
apply (comAnd (P:=Q) (Q:=P))
```

# The Currying Equivalence

Maybe you have already noticed that a statement like `P → Q → R`
basically means that `R` can be proved from assuming both `P` and `Q`.
Indeed, it is equivalent to `P ∧ Q → R`. We can show this formally by using
`↔`.

All the steps we have already explained, so we won't comment further here. It is a
good idea to step through the proof (by hovering over the bubbles) or by using Lean.
```anchor ExampleCurry
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
```
I call this the currying equivalence, because this is the logical counterpart of currying in functional programming: that a function with several parameters can be reduced to a function which returns a function. For example, in Haskell addition has the type `Int -> Int -> Int` instead of `(Int, Int) -> Int`.

# Disjunction

To prove a disjunction `P ∨ Q` we can either prove `P` or we can prove `Q`. This is achieved via the appropriately named tactics `left` and `right`. Here are some simple examples:
```anchor ExamplesOr
example : P → P ∨ Q := by
  intro p
  left
  exact p

example : Q → P ∨ Q := by
  intro q
  right
  exact q
```
To use a disjunction `P ∨ Q` we have to show that the current goal
follows both from assuming `P` and from assuming `Q`. To achieve
this we use `cases` again, and this time the name actually
makes sense. Here is an example:
```anchor ExampleCaseLem
theorem caseLem : (P → R) → (Q → R) → P ∨ Q → R := by
  intro p2r q2r pq
  cases pq with
  | inl p =>
    apply p2r
    exact p
  | inr q =>
    apply q2r
    exact q
```
After `intro` we are in the following state:

```
P Q R : Prop
p2r : P → R
q2r : Q → R
pq : P ∨ Q
⊢ R
```

We use
```
cases pq with
| inl p => …
| inr q => …
```
which means that we are going to use the assumption `P ∨ Q`.
There are two cases to consider, one for `P` and one for `Q`, resulting in two subgoals.
We indicate which names we want to use for the assumptions in each case, namely `p` and `q`:

```
2 goals
case Or.inl
P Q R : Prop
p2r : P → R
q2r : Q → R
p : P
⊢ R

case Or.inr
P Q R : Prop
p2r : P → R
q2r : Q → R
q : Q
⊢ R
```

To summarise: there are two ways to prove a disjunction using `left`
and `right`. To *use* a disjunction in an assumption we use `cases` to
perform a case analysis and show that the current goal follows from
either of the two components.

# Logic and algebra

As an example which involves both conjunction and disjunction we prove
distributivity. In algebra we know the law
`x(y+z) = xy + xz`; a
similar law holds in propositional logic:
```anchor ExampleDistr
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```
Sorry, but I was too lazy to do the proof so I left it to you. In
Lean you can say `sorry` and omit the proof. This is an easy way
out if you cannot complete your Lean homework: you just type
`sorry` and it is fine. However, then I will say *Sorry but you
don't get any points for this.*

The correspondence with algebra goes further: the counterpart to
implication is exponentiation but you have to read it backwards, that
is `P → Q` becomes `Q^P`. Then the translation of the law
`x^{yz} = (x^y)^z` corresponds to the currying equivalence
`P ∧ Q → R ↔ P → Q → R`.

Maybe you remember that there is another law of exponentiation
`x^{y+z} = x^y x^z`. And indeed its translation is also a law
of logic:
```
theorem caseThm : P ∨ Q → R ↔ (P → R) ∧ (Q → R) := by
  sorry
```
# True, false and negation

There are two logical constants `True` and `False`. It is a bit awkward to translate them into everyday English, so we think of `True` as something obviously true (e.g. *It sometimes rains in England*) and `False` as something obviously false (e.g. *Pigs can fly*).

As far as logic and proof are concerned, `True` behaves like an empty conjunction and `False` like an empty disjunction. Hence it is easy to prove `True`:
```anchor ExampleTrue
example : True := by
  constructor
```
While in the case of `∧` we were left with two subgoals, here we are left with none—we are already done.

Symmetrically, there is no way to prove `False` (there is neither `left` nor `right`, and that's good!). On the other hand, doing cases on `False` as an assumption makes the current goal go away “by magic” and leaves no goals to be proven:
```anchor ExampleFalse
theorem efq : False → P := by
  intro pigs_can_fly
  cases pigs_can_fly
```
`efq` is short for the Latin phrase *Ex falso quodlibet* — “from falsehood, anything follows.” This can feel odd in everyday reasoning, but in formal logic the inference “If pigs can fly then I am the president of America” is valid.

We define `¬ P` as `P → False`, which means that `P` is impossible. If someone says *If we get married then pigs can fly*, that means *no*.

As an example, we can prove the law of contradiction: it cannot be that both `P` and `¬ P` hold.
```anchor ExampleContr
theorem contr : ¬ (P ∧ ¬ P) := by
  intro pnp
  cases pnp with
  | intro p np =>
    apply np
    exact p
```
# Use `have`

There is one more useful tactic which is not related to any propositional connective. Let's say we want to prove
```
(P → Q ∨ Q) → (P → Q)
```
Now it is pretty easy to *cut* this proof by showing that `Q ∨ Q → Q` and then use this to show the result. But there is a better way which avoids introducing a new theorem and which is called `have`. This is best explained by an example:

```anchor ExampleHave
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
```

We introduce a new goal by saying
```
have qorq : Q ∨ Q := by
```
and now the proof state is
```
h : P → Q ∨ Q
p : P
⊢ Q ∨ Q
```
In the next lines we prove this and afterwards we can use `qorq`
```
h : P → Q ∨ Q
p : P
qorq : Q ∨ Q
```

So we use `have` to introduce intermediate goals. This is called a *cut*.

# Summary of tactics

Below is a table summarising the tactics we have seen so far (Lean 4 syntax):

:::table
*
  * {comment}[]
  * How to prove?
  * How to use?
*
  * `→`
  * `intro h`
  * `apply h`
*
  * `∧`
  * `constructor`
  * `cases h with | intro p q => …`
*
  * `∨`
  * `left` / `right`
  * `cases h with | inl p => … | inr q => …`
*
  * `True`
  * `constructor`
  * —
*
  * `False`
  * —
  * `cases h`
:::

These correspond to the introduction and elimination rules in *natural deduction*, a system devised by the German logician Gerhard Gentzen.

![Gerhard Gentzen (1909–1945)](diagrams/gentzen.jpeg)
*Gerhard Gentzen (1909–1945)*

He also proved that in his system cuts can always be avoided (called the *cut elimination theorem* or the *Hauptsatz*).

The surface syntax for using conjunction and disjunction looks similar—both use `cases`—but the effect is different. For `∧`, both components become available in the single subgoal; for `∨`, you get two subgoals, one per alternative.


We also have `exact h`, which is a structural tactic that doesn't fit the scheme above (and more generally `exact t` for any proof term `t`). Another structural tactic is `have` for introducing intermediate goals. There is also `assumption`, which checks whether any assumption matches the current goal. Thus we could have written the first proof as:

```anchor ExampleAss
example : P → P := by
  intro h
  assumption
```

*Important.* There are many more tactics available in Lean, some with a higher degree of automation, and some tactics can be used in ways we have not discussed here. When solving exercises, please use only the tactics we have introduced and only in the ways we have described.
