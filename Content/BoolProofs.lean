namespace BoolProofs

open Bool

-- ANCHOR: not
def not : Bool → Bool
| true => false
| false => true
-- ANCHOR_END: not

-- ANCHOR: and
def and : Bool → Bool → Bool
| true , b => b
| false , _ => false
-- ANCHOR_END: and

-- ANCHOR: or
def or : Bool → Bool → Bool
| true , _ => true
| false , b => b
-- ANCHOR_END: or

-- local notation:max "!'" b:90 => bnot b
-- local infixl:50 " && " => band
-- local infixl:40 " || " => bor

macro_rules
  | `(! $b)      => `(not $b)
  | `($a && $b)  => `(and $a $b)
  | `($a || $b)  => `(or  $a $b)

#eval (! true)
#eval true || false
#eval true && false

example : ∀ b : Bool, b=true ∨ b=false := by
intro b
cases b with
| true =>
   left
   rfl
| false =>
   right
   rfl

example : true ≠ false := by
intro q
cases q

example : ∀ b:Bool, (! b) ≠ b := by
   intro b eq
   cases b
   . cases eq
   . cases eq

theorem b_dm2 : ∀ b c : Bool,
   (! (b && c)) = (!b || ! c) := by
intro b c
cases b
. dsimp [and,not,or]
. dsimp [and,not,or]

def isTrue : Bool → Prop
| b => b = true

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








end BoolProofs
