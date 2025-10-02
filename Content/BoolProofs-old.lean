namespace BoolProofs

inductive Bool : Type
| false : Bool
| true : Bool

open Bool

instance : Repr BoolProofs.Bool where
  reprPrec
  | .false, _ => Std.Format.text "false"
  | .true, _ => Std.Format.text "true"

def bnot : Bool → Bool
| true => false
| false => true

def band : Bool → Bool → Bool
| true , b => b
| false , _ => false

def bor : Bool → Bool → Bool
| true , _ => true
| false , b => b

local prefix:90 "!" => bnot
local infixl:50 " && " => band
local infixl:40 " || " => bor

#reduce false && (true || false)
#reduce true && (true || false)

def band2 : Bool → Bool → Bool
| b , true => b
| _ , false => false

def bor2 : Bool → Bool → Bool
| _ , true  => true
| b , false => b

variable (x : Bool)

#reduce band true x
#reduce band2 true x
#reduce band x true
#reduce band2 x true



end BoolProofs
