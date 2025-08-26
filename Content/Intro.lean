import VersoManual
import Content.Meta
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.PropLogicProofs"

#doc (Manual) "Introduction" =>
%%%
tag := "intro"
%%%
These are lecture notes for COMP2065: Introduction to formal
reasoning. The main goal is to teach
formal logic using an interactive proof system called *Lean*. You will be
able to use predicate logic to make precise statements and to verify
them using a proof system. The covers both statements in Mathematics
and statements about computer programs, e.g. their correctness.
```anchor CheckImpl
#check P → Q
```
```anchorInfo CheckImpl
P → Q : Prop
```

```comment
Also anchorWarning and AnchorError
```
