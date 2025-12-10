import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.PredLogProofs"

#doc (Manual) "Predicate Logic" =>

# Predicates, relations and quantifiers

Predicate logic extends propositional logic, we can use it to talk about objects and their properties.
The objects are organized in *types*, such as `ℕ : Type` the type of natural
numbers $`\{0,1,2,3\dots\}` or `Bool : Type` the type of
Booleans $`\{\mathrm{true} , \mathrm{false}\},` or lists over a
given `A : Type`: `list A : Type`,  which we will
introduce in more detail soon.

To avoid talking about specific types which we will introduce later
we introduce some type variables:

```anchor ExampleTypes
variable {A B C : Type}
```

We talk about types where you may be used to *sets*. While they are
subtle differences (types are static while we can reason about set
membership in set theory) for our purposes types are just a replacement of
sets.

We also have function types `A → B` which you know from functional programming. So for example we can define
```anchor ExampleFuns
def double : ℕ → ℕ
| n => n + n

def foo : ℕ → ℕ → ℕ
| m , n => m + n + n
```
As in Haskell functions with several arguments are curried but note that you have to separate the parameters by `,`. An alternative is to use explicit function definitions:
```anchor ExampleFuns2
def double' (n : ℕ) : ℕ
:= n + n

def foo' (m n : ℕ) : ℕ
:= m + n + n
```
As in Haskell function application is written without brackets, e.g.
```anchor ExampleApp
#eval double 2
#eval foo' 2 3
```

A predicate is just another word for a property, e.g. we may use
`Prime : ℕ → Prop` to express that a number is a prime number. Note that a predicate is just a function!

We can form
propositions such as `Prime 3` and `Prime 4`, the first one
should be provable while the negation of the second holds. Predicates
may have several inputs in which case we usually call them relations,
examples are `Nat.le : ℕ → ℕ → Prop` or `List.mem : A → list A → Prop` to
form propositions like `Nat.le 2 3` and `List.mem 1 [1,2,3]` (both of
them should be provable). Using defined notations these two examples can also be written as `2 ≤ 3` and `1 ∈ [1,2,3]`.

In the sequel we will use some generic predicates for examples, such
as
```anchor ExamplePred
variable {PP QQ : A → Prop}
```

# Quantifiers

The most important innovation of predicate logic are the quantifiers,
which we can use to form new propositions:

* universal quantification (`∀`), read `∀ x : A , PP x` as all
  `x` in `A` satisfy `PP x`.
* existential quantification (`∃`), read `∃ x : A, PP x` as there
  is an `x` in `A` satisfying `PP x`.

Here are some examples of propositions in predicate logic:
```anchor ExampleProps
#check ∀ x : A, PP x ∧ Q
#check (∀ x : A , PP x) ∧ Q
#check ∀ x:A , (∃ x : A , PP x) ∧ QQ x
#check ∀ y:A , (∃ z : A , PP z) ∧ QQ y
```

Both quantifiers bind weaker than any other propositional operator,
that is we read `∀ x : A, PP x ∧ Q` as `∀ x : A , (PP x ∧ Q)`. We
need parentheses to limit the scope, e.g. `(∀ x : A, PP x) ∧ Q` which
has a different meaning to the proposition before.

It is important to understand bound variables, essentially they work
like scoped variables in programming. We can shadow variables as in
`∀ x:A , (∃ x : A , PP x) ∧ QQ x`, here the `x` in  `PP x`
refers to `∃ x : A` while the `x` in `QQ x` refers to `∀ x :
A`. Bound variables can be consistently renamed, hence the previous
proposition is the same as `∀ y:A , (∃ z : A , PP z) ∧ QQ y`, which
is actually preferable since shadowing variables should be avoided
because it confuses the human reader.

Now we have introduced all these variables what can we do with
them. We have a new primitive proposition:

* equality (`=`), given `a b : A` we write `a = b` which we read
  as `a` is equal to `b`.

In the moment we only have variables as elements of types but this
will change soon when we introduce datatypes and functions.

# The universal quantifier

To prove that a proposition of the form `∀ x : A , PP x` holds we
assume that there is given an arbitrary element `a` in `A` and
prove it for this generic element, i.e. to prove `PP a`, we use `intro a` to do
this.

If we have an assumption `h : ∀ x : A , PP x` and our current
goal is `PP a` for some `a : A` then we can use `apply h` to
prove our goal. Usually we have some combination of implication and forall like `h : ∀ x : A, PP x → QQ x` and now if our current goal is
`QQ a` and we invoke `apply h` Lean will instantiate `x` with
`a` and it remains to show `PP a`.

Best to do some examples. Let's say we want to prove

`(∀ x : A, PP x) → (∀ y : A, PP y → QQ y) → ∀ z : A , QQ z`

Here is a possible translation into English where we assume that `A`
stands for the type of students in the class, `PP x` means *x is
clever* and `QQ x` means *x is funny* then we arrive at:

  *If all students are clever then if all clever students are funny
  then all students are funny.*

```anchor ExampleForall
example : (∀ x : A, PP x)
  → (∀ y : A, PP y → QQ y)
  → ∀ z : A , QQ z := by
  intro p pq a
  apply pq
  apply p
```
Note that after `intro` the proof state is::

  p : ∀ (x : A), PP x,
  pq : ∀ (y : A), PP y → QQ y,
  a : A
  ⊢ QQ a

That is the `x` in `QQ x` has been replaced by `a`. I could have
used `x` again but I thought this may be misleading because you may
think that you have to use the same variable as in the quantifier.

Let's prove a logical equivalence involving `∀` and `∧`, namely
that we can interchange them. That is we are going to prove

`(∀ x : A, PP x ∧ QQ x)  ↔ (∀ x : A , PP x) ∧ (∀ x : A, QQ x)`

To illustrate this: to say that *all students are clever and funny* is
the same as saying that *all students are clever and all students are
funny*.

Here is the Lean proof:
```anchor ExampleAllAnd
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
```
I am using `have` which we have already seen in ... After `intro a` I am in the
following state (ignoring the parts not relevant now)::
```
  h : ∀ (x : A), PP x ∧ QQ x,
  a : A
  ⊢ PP a
```
Now I cannot say `apply h` because `PP a` is not the conclusion of
the assumption. My idea is that I can prove `PP a ∧ QQ a` from `h`
and from this I can prove `PP a`. Hence I am using
```
have pq : PP a ∧ QQ a := by
    apply h
```
and then I can proof `PP a` by using `cases` on `pq`.

# The existential quantifier

To prove a proposition of the form `∃ x : A , PP x` it is enough to
prove `PP a` for some `a : A`. We say `exists a` and are left to prove `PP a`.

On the other hand to use an assumption of the form
`h : ∃ x : A ,  P x` we are using
```
cases h with
| intro x px => ...
```
which
replaces `h` with two assumptions `x : A` and `px : P x`.

Again it is best to look at an example. We are going to prove a
proposition very similar to the one for `∀`:

`(∃ x : A, PP x) → (∀ y : A, PP y → QQ y) → ∃ z : A , QQ z`

Here is the english version using the same translation as before:

  *If there is a clever student and all clever students are funny then
  there is a funny student.*

Here is the Lean proof (Lean 4):

```anchor ExampleExists
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
```

After the `intro` we are in the following state::
```
  p : ∃ (x : A), PP x,
  pq : ∀ (y : A), PP y → QQ y
  ⊢ ∃ (z : A), QQ z
```
We first take `p` apart using `cases`:
```
  pq : ∀ (y : A), PP y → QQ y,
  a : A,
  pa : PP a
  ⊢ ∃ (z : A), QQ z
```
and now we can use `exists a`. We are left with
```
pq : ∀ (y : A), PP y → QQ y
a : A
pa : PP a
⊢ QQ a
```
which is easy to prove.

As `∀` can be exchanged with `∧`, `∃` can be exchanged with
`∨`. That is we are going to prove the following equivalence:

`(∃ x : A, PP x ∨ QQ x) ↔ (∃ x : A , PP x) ∨ (∃ x : A, QQ x)`

Here is the english version

  *There is a student who is clever or funny is the same as saying
  there is a student who is funny or there is a student who is clever.*

Here is the complete Lean proof (for you to step through online):

```anchor ExampleExOr
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
```

## Use `constructor` for `∃`

There is an alternative to `exists` to prove `∃` which shows the similarity of `∃` and `∧`: we can use `constructor` to prove `exists`. Let's revisit our first example
```anchor ExampleExistsConstr
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
```
After `constructor` we are in the following state (ignoring the assumptions inroduced by `variable`):
```
case intro.h
pq : ∀ (y : A), PP y → QQ y
a : A
pa : PP a
⊢ QQ ?intro.w
case intro.w
pq : ∀ (y : A), PP y → QQ y
a : A
pa : PP a
⊢ A
```
Indeed we have two goals: the 2nd one is finding the witness an element of `A` which is displayed as `⊢ A` and the first one is to show that `QQ` holds for that witness which is `QQ ?intro.w` where `?intro.w` refers to the other yet incomplete goal. Instead of finding a witness first (as with `exists`) we just try to prove `QQ ?intro.w` and hope that the other goal gets instantiated automtically. Which is what happens because after `apply pq` we see
```
pq : ∀ (y : A), PP y → QQ y
a : A
pa : PP a
⊢ PP ?intro.w
```
and once we prove this using `assumption` lean will use `pa` nd hence knows that `?intro.w` nust be `a`. So this goal gets discharged utomatically.

This is clearly better because it saves us ti have to construct the witness manually. However, some care is in place when using `constructor`. We may try to postpone the `cases` until the end
```
example (A : Type) (PP QQ : A → Prop) :
    (∃ x : A, PP x) →
    (∀ y : A, PP y → QQ y) →
    ∃ z : A , QQ z := by
  intro p pq
  constructor
  apply pq
  cases p with
    | intro a pa =>
        assumption
```
Before the last step we are in the following state
```
pq : ∀ (y : A), PP y → QQ y
a : A
pa : PP a
⊢ PP (?m.27 ⋯)
```
but `assumption` fails because the weird looking `PP (?m.27 ⋯)` cannot be instantiated with `a`. The problem has to do with scope we have introduced the goal `⊢ A` *before* we introduced `a` when doing `cases`. Indeed the situation is similar as with `∧` where we would replicate code if we do `cases` later. However, here doing things in the wrong order means it is impossible to complete the proof.

# Another Currying equivalence

You may have noticed that the way we prove propositions involving `→`
and `∀` is very similar. In both cases wem use `intro` to prove
them by introducing an assumption in the first case a proposition and
in the secnde an element in a type and in both cases we use them using
`apply` to prove the current goal. Similarily `∧` and `∃` behave
similar: we need to supply two components. And in both cases we are using `cases` with
two components which basically replaces the assumption by its two
components.

The similarity can be seen by establishing another currying-style
equivalence. While currying in propositional logic had the form

`P ∧ Q → R ↔ P → Q → R`

where we turn a conjunction into an implication, currying for
predicate logic has the form

`(∃ x : A, QQ x) → R  ↔ (∀ x : A , QQ x → R)`

ths time we turn an existential into a universal quantifier. For the
intuition, we use `QQ x` to mean `x` *is clever* and `R` means *the
professor is happy*.  Hence the equivalence is:

  *If there is a student who is clever then the professor is happy is
  equivalent to saying if any student is clever then the professor is happy.*

Here is the proof in Lean:
```anchor ExampleCurryPred
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
```

# Equality

There is a generic relation which can be applied to any type:
*equality*.  Given `a b : A` we can construct `a = b : Prop`
expressing that `a` and `b` are equal. We can prove that
everything is equal to itself using the tactic `rfl` (or `reflexivity`).
```anchor ExampleEqRefl
example : ∀ x : A, x = x := by
  intro a
  rfl
```
If we have assumed an equality `h : a = b` we can use it to *rewrite*
`a` into `b` in the goal. That is if our goal is `PP a` we say
`rw [h]` and this changes the goal into `PP b`. Here is a
simple example (with a little twist):
```anchor ExampleEqRw
example : ∀ x y : A, x = y → PP y → PP x := by
  intro x y eq p
  rw [eq]
  exact p
```
Sometimes we want to use the equality in the other direction, that is
we want to replace `b` by `a`. In this case we use `rw [← h]`. Here is
another example which is actually what I wanted to do first:
```anchor ExampleEqRw2
example : ∀ x y : A, x = y → PP x → PP y := by
  intro x y eq p
  rw [← eq]
  exact p
```
Equality is an *equivalence relation*, it means that it is

- reflexive  (`∀ x : A, x = x`),
- symmetric (`∀ x y : A, x = y → y = x`)
- transitive (`∀ x y z : A, x = y → y = z → x = z`)

We have already shown reflexivity using `rfl`. We can show symmetry and
transitivity using `rw`:

```anchor ExampleEqSym
theorem symEq : ∀ x y : A, x = y → y = x := by
  intro x y p
  rw [p]
```
After the `intro` the goal is::

```
x y : A,
p : x = y
⊢ y = x
```

After `rw [p]` the goal becomes `y = y` which is solved automatically
because `rw` applies reflexivity if possible.

Moving on to transitivity:
```anchor ExampleEqTrans
theorem transEq : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  rw [xy]
  exact yz
```
Sometimes we want to use an equality not to rewrite the goal but to
rewrite another assumption. We can do this using `at`, giving another
proof of transitivity:
```anchor ExampleEqTrans2
theorem transEq' : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  rw [← xy] at yz
  exact yz
```
Lean also provides built-in tactics to deal with symmetry and
transitivity:
```anchor ExampleEqTacs
example : ∀ x y : A, x = y → y = x := by
  intro x y p
  symm
  exact p

example : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  apply transEq
  exact xy
  exact yz
```

After we say `trans` the goals are split:

```
2 goals
⊢ x = ?m_1
⊢ ?m_1 = z
```

Lean will infer `?m_1 := y` after we solve the first subgoal with
`exact xy`.

A very nice way to do equational proofs is to use `calc`:

```anchor ExampleCalc
example : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z xy yz
  calc
    x = y := by exact xy
    _ = z := by exact yz
```

Here each line shows an equality and its justification; `_` refers to
the right side of the previous line.

Finally, equality is a *congruence*: functions preserve equality.
If `f : A → B` and `x = y`, then `f x = f y`:

```anchor ExampleCongr
example : ∀ f : A → B, ∀ x y : A, x = y → f x = f y := by
  intro f x y h
  rw [h]
```

# Classical Predicate Logic

We can use classical logic in predicate logic even though the
explanation using truth tables does not scale well. Think of them as
"infinite truth tables."

There are predicate-logic counterparts of de Morgan’s laws, which say
that you can move negation through a quantifier by negating the
component and switching the quantifier.

## First de Morgan law (intuitionistic proof)

```anchor ExampleDm1Pred
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
```

This direction does not require classical logic.

## Second de Morgan law (needs classical logic)

We need *reductio ad absurdum* (`byContradiction`), which depends on excluded middle.
Now the de Morgan law:

```anchor ExampleDm2Pred
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
```

We needed `byContradiction` twice in the first direction.

## Intuition

The existential statement `∃ x : A, ¬ PP x` contains explicit
information (it points to a witness `a`), but the negated universal
`¬ (∀ x : A, PP x)` does not. Intuitively: *knowing that not all
students are stupid does not give you a way to name a student who is
not stupid*.

# Summary of tactics

Here is the summary of basic tactics for predicate logic:

:::table
*
  *            {comment}[]
  * How to prove?
  * How to use?
*
  * `∀`
  * `intro h`
  * `apply h`
*
  * `∃`
  * `exists a` / `constructor`
  * `cases h with | intro x p => …`
*
  * `=`
  * `rfl`
  * `rw [h]` / `rw [← h]`
:::
