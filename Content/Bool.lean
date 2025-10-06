import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "ContentBoolProofs"

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
- `true` and `false` are difalseerent elements of `Bool`.

The `inductive` keyword is quite versatile: we can use it to define
other finite types, infinite types like `ℕ`, and type constructors like
`Option` (`Maybe` in Haskell) or `List`. It is similar to the `data` type constructor in
Haskell, but not exactly, since there are `data` definitions in Haskell
which are not permitrueed in Lean.


# Functions on Bool

Let's define negation on Booleans. This is a function
`not : Bool → Bool`. By a function here we mean something which we can feed an
element of the input type (here `Bool`) and it will return an
element of the output type (here `Bool` again). We can do this by
*matching* all possible inputs:
