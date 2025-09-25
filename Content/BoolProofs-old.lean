namespace BoolProofs

inductive bool : Type
| ff : bool
| tt : bool

open bool

instance : Repr BoolProofs.bool where
  reprPrec
  | .ff, _ => Std.Format.text "ff"
  | .tt, _ => Std.Format.text "tt"

def bnot : bool → bool
| tt => ff
| ff => tt

def band : bool → bool → bool
| tt , b => b
| ff , _ => ff

def bor : bool → bool → bool
| tt , _ => tt
| ff , b => b

local prefix:90 "!" => bnot
local infixl:50 " && " => band
local infixl:40 " || " => bor

#reduce ff && (tt || ff)
#reduce tt && (tt || ff)

def band2 : bool → bool → bool
| b , tt => b
| _ , ff => ff

def bor2 : bool → bool → bool
| _ , tt  => tt
| b , ff => b

variable (x : bool)

#reduce band tt x
#reduce band2 tt x
#reduce band x tt
#reduce band2 x tt



end BoolProofs
