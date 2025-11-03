import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.BoolProofs"

#doc (Manual) "The Booleans" =>

The logic we have introduced so far was very generic. We fix this in
this chapter by looking at a very simple type, the Booleans `Bool`
which has just two elements `true` and `false`  and
functions on this type. Then we are going to use predicate logic to
prove some simple theorems about Booleans.

`Bool` is defined as an inductive type (this is just a copy of the definition in the Lean prelude).
```anchor boolDef
inductive Bool : Type
| false : Bool
| true : Bool
```
This declaration means:

- There is a new type `Bool : Type`,
- There are two elements `true false : Bool`,
- These are the only elements of `Bool`,
- `true` and `false` are different elements of `Bool`.

The `inductive` keyword is quite versatile: we can use it to define
other finite types, infinite types like `ℕ`, and type constructors like
`Option` (`Maybe` in Haskell) or `List`. It is similar to the `data` type constructor in
Haskell, but not exactly, since there are `data` definitions in Haskell
which are not permitted in Lean.

# Proving some basic properties

How do we prove facts about `Bool`? Let's prove the first basic property that `true` and `false` are the only elements of `Bool`:
```anchor allBool
theorem allBool : ∀ b : Bool, b=true ∨ b=false := by
intro b
cases b with
| true =>
   left
   rfl
| false =>
   right
   rfl
```
Here we use `cases` again. Our goal is
```
b : Bool
⊢ b = true ∨ b = false
```
using `cases` we reduce this to two goals :
```
case false
⊢ false = true ∨ false = false
case true
⊢ true = true ∨ true = false
```
both of them are easy to prove.

To show that `true` and `false` are different we need to do a case on equality using the fact that Lean already know that it is impossible to prove a equality between different constructors. The proof of this *no confusion theorem* looks like this:
```anchor noConfBool
theorem noConfBool : true ≠ false := by
intro q
cases q
```
We use the fact that `true ≠ false` is defined as `¬ (true = false)` and hence `true = false → False`. Hence after `intro q` we are in the following stata:
```
q : true = false
⊢ False
```
Now there is no way to prove `False` but we can ask Lean to analyze our assumption `q` and it knows that this is impossible.

You may think that we are cheating here  bit because basically Lean already knows that there is no proof of `true = false`. Indeed we can actually prove `true ≠ false` from first principles using only `rewrite` and a function `Bool → Prop` (see next section for functions on `Bool`). And this is the way it is done in the Lean library.

# Functions on Bool

Let's define negation on Booleans as a function. We define the function by matching all possible inputs:

```anchor not
def not : Bool → Bool
| true => false
| false => true
```

To define a function with two inputs, such as the boolean conjunction (we’ll implement it as `and`),
we use *currying*.

We could list all four cases, reproducing the full truth table, but we can
get away with just two by matching only on the first argument:

```anchor and
def and : Bool → Bool → Bool
| true , b => b
| false , _ => false
```

If the first argument is `true`, i.e. we look at `and true : Bool → Bool`,
then this is just the identity on the second argument, because
`and true true = true` and `and true false = false`. If the first argument is
`false` then the outcome will be `false` whatever the second argument is. In other
words `and false : Bool → Bool` is the constant function which always returns `false`.

Symmetrically we can define disjunction (implemented as `bor`) with just two cases:

```anchor or
def or : Bool → Bool → Bool
| true , _ => true
| false , b => b
```

In this case, if the first argument is `true`, then `or true : Bool → Bool`
is always `true`, while if the first argument is `false`, `bor false : Bool → Bool`
is just the identity.

We use the standard notation for boolean operators, i.e.
:::table
*
  * `! b`
  * `not b`
*
  * `b && c`
  * `b and c`
*
  * `b || c`
  * `b or c`
:::

Note that the precedence is the same as for the propositional operations which means that we always have to use brackets when writing equations involving boolean operators otherwise `x && y = z` is read as `x && (y = z)`. Hence we write `(x && y) = z`.

If you wonder why `x && (y = z)` even makes sense we will come to that later.

We can try this out by evaluating a boolean expression:
```anchor evalBool
#eval ! false || false && true
```
```anchorInfo evalBool
true
```

When we defined these binary boolean functions, our choice to match on the
first argument was quite arbitrary — we could have matched on the second
argument instead:
```anchor boolx
def and' : Bool → Bool → Bool
| b , true => b
| _ , false  => false

def or' : Bool → Bool → Bool
| _ , true => true
| b , false => b
```

These functions produce the same truth tables as the ones we defined before,
but their *computational behaviour* is different, which becomes important
when proving properties about them.

# Proving equations about bool

Next, let's prove some interesting equalities. We are going to revisit our old
friend, *distributivity* — but this time for booleans:
```anchor distr_b
theorem distr_b : ∀ x y z : Bool,
  (x && (y || z)) = (x && y || x && z) := by
  intro x y z
  cases x
  . dsimp [and,or]
  . dsimp [and]
```

After `intro x y z,` we are in the following state:

```
x y z : Bool
⊢ (x && (y || z)) = (x && y || x && z)
```

We do case analysis on `x`, which can be either `tt` or `ff`. Hence, after `cases x`, we are left with two subgoals:

```
case false
y z : Bool
⊢ (false && (y || z)) = (false && y || false && z)
case true
y z : Bool
⊢ (true && (y || z)) = (true && y || true && z)
```

Let's discuss the first one. We can instruct Lean to use the
definition of `&&` (i.e. `and`) by saying `dsimp [and]`. We are then left with:

```
y z : Bool
⊢ false = (false || false)
```

Now we just need to apply the definition of `||` (i.e. `or`) using `dsimp [or]` and we get `false = false` which is automatically discharged.

Can you see why in the second case it is enough to use `dsimp [and]`?

We can apply several definitions in one tactic; for example, in the first case
`dsimp [and, or]` would have done the same. But actually, in this proof there
is no need for `dsimp` at all because `rfl` automatically reduces its
arguments. Hence we could have just written:
```anchor distr_br
example : ∀ x y z : Bool,
  (x && (y || z)) = (x && y || x && z) := by
  intro x y z
  cases x
  . rfl
  . rfl
```
However, when doing proofs interactively it may be helpful to see the
reductions. Also, later we will encounter cases where using `dsimp` (or its friend `simp`)
is actually necessary.

Could we have used another variable than `x`? Let's see — what about
`z`?
```anchor distr_bz
example : ∀ x y z : Bool,
  (x && (y || z)) = (x && y || x && z) := by
  intro x y z
  cases z
  . sorry
  . sorry
```
After `cases z`, we are stuck in the following state:

```
x y : bool
⊢ x && (y || ff) = x && y || x && ff
```

No reduction is possible because we defined the functions by matching
on the first argument. Using `cases y` would have done a bit of
reduction but not enough. `cases x` was the right choice.

Now have a go at proving the *De Morgan* laws for `bool` yourself.
Both are provable just using case analysis:

```anchor dm1_b
theorem dm1_b : ∀ b c : Bool,
  (! (b || c)) = (! b && ! c) := by
```
```anchor dm2_b
theorem dm2_b : ∀ b c : Bool,
   (! (b && c)) = (!b || ! c) := by
```
# Relating bool and Prop

It may not have escaped your notice that we seem to define logical
operations twice: once for `Prop` and once for `Bool`. How are the two
related? We now define a function that maps `Bool` to the corrresponding `Prop`
```anchor isTrue
def isTrue : Bool → Prop
| b => b = true
```
`isTrue true` evaluates to `true = true` which is equivalent to `True` while `isTrue false` evluates to `false = true` which is equivalent to `false`.

Using `isTrue` we can express the correctness of `&&` wrt `∧` : namely `isTue (b && c)` is equivalent to `isTrue b ∧ isTrue c`:
```anchor and_ok
theorem and_ok : ∀ b c : Bool,
  isTrue (b && c) ↔ isTrue b ∧ isTrue c := by
intro b c
constructor
. intro H
  cases b
  . dsimp [and,isTrue] at H
    cases H
  . constructor
    . rfl
    . dsimp [and] at H
      assumption
. intro H
  cases H with
  | intro Hb Hc =>
    dsimp [isTrue] at Hb
    rw [Hb]
    dsimp [and]
    assumption
```
I am using `dsimp ... at ...` which simplfies a definition. Actually the proof also works without the `dsimp`s.

The proof from left to right explores the truth table via case analysis while the proof from right to left uses equational reasoning. I recommend stepping through this proof interactively. We are only
using tactics already explained. Note that `cases` is used in two
different ways: for case analysis on booleans and to eliminate
inconsistent assumptions.

I leave it as an exercise to prove the corresponding facts about
negation and disjunction:
```anchor or_ok
theorem or_ok : ∀ b c : Bool,
  isTrue (b || c) ↔ isTrue b ∨ isTrue c := by
```
```anchor not_ok
theorem not_ok : ∀ b : Bool, isTrue (! b) ↔ ¬ isTrue b := by
```

# No confusion from first principles

Previously we proved `true ≠ false` by doing cases on `true = false` and lean knows that this is impossible. However, we can actually prove this without this kind of magic and behind the curtains this is how the proof is actually implemented.

First of all we define an alternative version of `isTrue` but this tie by pattern matching:
```anchor isTrueD
def isTrueD : Bool → Prop
| true => True
| false => False
```

Now we can prove no confusion just using rewriting:
```anchor noConfBoolD
theorem noConfBoolD : true ≠ false := by
  intro pcf
  have t : isTrueD true := by
    constructor
  rw [pcf] at t
  assumption
```

We know that we can prove `isTrueD true` but if `true = false` this can be rewritten to `isTrueD false` and this is `False` by definition.
