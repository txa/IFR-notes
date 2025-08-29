import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.PredLogProofsX"
--set_option verso.exampleModule "Content.ClassicalProofs"

#doc (Manual) "Predicate Logic" =>

# Predicates, relations and quantifiers

Predicate logic extends propositional logic, we can use it to talk about objects and their properties.
The objects are organized in *types*, such as $`ℕ : Type` the type of natural
numbers $`\{0,1,2,3\dots\}` or $`bool : Type` the type of
booleans $`\{tt , ff\},` or lists over a
given $`A : Type`: $`list A : Type`,  which we will
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

A predicate is just another word for a property, e.g. we may use
`Prime : ℕ → Prop` to express that a number is a prime number. We can form
propositions such as `Prime 3` and `Prime 4`, the first one
should be provable while the negation of the second holds. Predicates
may have several inputs in which case we usually call them relations,
examples are `≤ : ℕ → ℕ → Prop` or `inList : A → list A → Prop` to
form propositions like `2 ≤ 3` and `InList 1 [1,2,3]` (both of
them should be provable).

In the sequel we will use some generic predicates for examples, such
as
```anchor ExamplePred
variable {PP QQ : A → Prop}
```

# Quantifiers

The most important innovation of predicate logic are the quantifiers,
which we can use to form new propositions:

* universal quantification ($`∀`), read $`∀ x : A , PP x` as all
  $`x` in $`A` satisfy $`PP x`.
* existential quantification ($`∃`), read $`∃ x : A, PP x` as there
  is an $`x` in $`A` satisfying $`PP x`.

Here are some examples of propositions in predicate logic:
```anchor ExampleProps
#check ∀ x : A, PP x ∧ Q
#check (∀ x : A , PP x) ∧ Q
#check ∀ x:A , (∃ x : A , PP x) ∧ QQ x
#check ∀ y:A , (∃ z : A , PP z) ∧ QQ y
```

Both quantifiers bind weaker than any other propositional operator,
that is we read $`∀ x : A, PP x ∧ Q` as $`∀ x : A , (PP x ∧ Q)`. We
need parentheses to limit the scope, e.g. $`(∀ x : A, PP x) ∧ Q` which
has a different meaning to the proposition before.

It is important to understand bound variables, essentially they work
like scoped variables in programming. We can shadow variables as in
$`∀ x:A , (∃ x : A , PP x) ∧ QQ x`$, here the $`x` in  $`PP x`$
refers to $`∃ x : A`$ while the $`x` in $`QQ x`$ refers to $`∀ x :
A`$. Bound variables can be consistently renamed, hence the previous
proposition is the same as $`∀ y:A , (∃ z : A , PP z) ∧ QQ y`$, which
is actually preferable since shadowing variables should be avoided
because it confuses the human reader.

Now we have introduced all these variables what can we do with
them. We have new primitive proposition:

* equality ($`=`), given $`a b : A`$ we write $`a = b`$ which we read
  as $`a`$ is equal to $`b`$.

In the moment we only have variables as elements of types but this
will change soon when we introduce datatypes and functions.

# The universal quantifier

To prove that a proposition of the form `∀ x : A , PP x` holds we
assume that there is given an arbitrary element `a` in `A` and
prove it for this generic element, i.e. to prove `PP a`, we use `assume a` to do
this.

If we have an assumption `h : ∀ x : A , PP x` and our current
goal is `PP a` for some `a : A` then we can use `apply h` to
prove our goal. Usually we have some combination of implication and for
all like `h : ∀ x : A, PP x → QQ x` and now if our current goal is
`QQ a` and we invoke `apply h` Lean will instantiate `x` with
`a` and it remains to show `QQ a`.

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
prove `PP a` for some `a : A`. We use `constructor` for
this and we are left having to prove `PP a` for some `a`. Since lean cannot gues which `a` we want to use it will ask you to prove `PP ?` and it will instantiate `?` later to `a` when the choice is obvious.

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
    constructor
    apply pq
    apply pa
```

After the `intro` we are in the following state::
```
  p : ∃ (x : A), PP x,
  pq : ∀ (y : A), PP y → QQ y
  ⊢ ∃ (z : A), QQ z
```
We first take `p` apart using `cases`::
```
  pq : ∀ (y : A), PP y → QQ y,
  a : A,
  pa : PP a
  ⊢ ∃ (z : A), QQ z
```
and now we can use `constructor`. We have now 2 goals but only the first one matters (the second is the unknown `?intro.w`):
```
pq : ∀ (y : A), PP y → QQ y
a : A
pa : PP a
⊢ QQ ?intro.w
```
After `apply pq` we stil have `?` :
```
a : A
pa : PP a
⊢ PP ?intro.w
```
Nw we want are using `pa` but note that we have to use `apply` here not `exact` because `?intro.w` needs to be instantiated. But after `apply pa` the proof is done and lean has instantiated `?intro.w` with `a`.

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
```
