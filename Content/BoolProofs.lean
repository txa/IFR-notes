namespace BoolProofs

-- ANCHOR: BoolDef
inductive bool : Type
| ff : bool
| tt : bool
-- ANCHOR_END: BoolDef

open bool

-- ANCHOR: bnot
def bnot : bool → bool
| tt => ff
| ff => tt
-- ANCHOR_END: bnot

def band : bool → bool → bool
| tt , b => b
| ff , _ => ff

def bor : bool → bool → bool
| tt , _ => tt
| ff , b => b

local prefix:90 "!" => bnot
local infixl:50 " && " => band
local infixl:40 " || " => bor

#eval ! tt
example : ∀ b : bool, b=tt ∨ b=ff := by
intro b
cases b with
| tt =>
   left
   rfl
| ff =>
   right
   rfl

example : tt ≠ ff := by
intro q
cases q



theorem b_dm2 : ∀ b c : bool,
   (! (b && c)) = ((! b) || (! c)) := by
  intro b c
  cases b with
  | tt => dsimp [band,bnot,bor]
  | ff => dsimp [band,bnot,bor]







end BoolProofs
