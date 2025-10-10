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
which has just two elements `true` (for *true*) and `false` (for *false*) and
functions on this type. Then we are going to use predicate logic to
prove some simple theorems about Booleans.

In the prelude Bool is already defined:
```
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

How do we prove facts about `Bool`. Let's prove the first basic property that `true` and `false` are the only elements of `Bool`:
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

To show that `true` and `false` are deifferent we need to do a case on equality using the fact that Lean already know that itis impossible to prove a equality between different constructors. The proof of this *no confusion theorem* looks like this:
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

You may think that we are cheating here  bit because basically Lean already knows that there is no proof of `true = false`. Indeed we can actually prove `true ≠ false` form forst principles using only `rewrite` and a function `Bool → Prop` (see next section for functions on `Bool`). And this is the way it is done in the Lean library.

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

If the first argument is `true`, i.e. we look at `band true : Bool → Bool`,
then this is just the identity on the second argument, because
`band true true = true` and `band true false = false`. If the first argument is
`false` then the outcome will be `false` whatever the second argument is. In other
words `band false : Bool → Bool` is the constant function which always returns `false`.

Symmetrically we can define disjunction (implemented as `bor`) with just two cases:

```anchor and
def and : Bool → Bool → Bool
| true , b => b
| false , _ => false
```

In this case, if the first argument is `true`, then `bor true : Bool → Bool`
is always `true`, while if the first argument is `false`, `bor false : Bool → Bool`
is just the identity.

We introduce the standrd notation for boolean operators, i.e.
:::table
*
  * `! b`
  * `not b`
*
  * `b & c`
  * `b and c`
*
  * `b | c`
  * `b or c`
:::

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

When constructing proofs, it is important to remember how a function is
defined, because when we perform case analysis we should instantiate the
arguments that allow the function to reduce, if possible.
