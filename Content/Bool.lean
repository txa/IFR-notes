import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.BoolProofs"

#doc (Manual) "The Booleans" =>

The logic we have introduced so far was very generic. We fix this in
this chapter by looking at a very simple type, the booleans `bool`
which has just two elements `tt` (for *true*) and `ff` (for *false*) and
functions on this type. Then we are going to use predicate logic to
prove some simple theorems about booleans.
```anchor BoolDef

```
This declaration means:

- There is a new type `bool : Type`,
- There are two elements `tt ff : bool`,
- These are the only elements of `bool`,
- `tt` and `ff` are different elements of `bool`.

The `inductive` keyword is quite versatile: we can use it to define
other finite types, infinite types like `ℕ`, and type constructors like
`maybe` or `list`. It is similar to the `data` type constructor in
Haskell, but not exactly, since there are `data` definitions in Haskell
which are not permitted in Lean.

In the Lean prelude `Bool` is defined as an inductive type with constructors `true` and `false`. We are here using our own version not to confuse lean.
