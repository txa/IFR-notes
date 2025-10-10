namespace BoolProofs

open Bool

-- ANCHOR: allBool
theorem allBool : ∀ b : Bool, b=true ∨ b=false := by
intro b
cases b with
| true =>
   left
   rfl
| false =>
   right
   rfl
-- ANCHOR_END: allBool

-- ANCHOR: noConfBool
theorem noConfBool : true ≠ false := by
intro q
cases q
-- ANCHOR_END: noConfBool

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

macro_rules
  | `(! $b)      => `(not $b)
  | `($a && $b)  => `(and $a $b)
  | `($a || $b)  => `(or  $a $b)

-- ANCHOR: evalBool
#eval ! false || false && true
-- ANCHOR_END: evalBool

-- ANCHOR: boolx
def and' : Bool → Bool → Bool
| b , true => b
| _ , false  => false

def or' : Bool → Bool → Bool
| _ , true => true
| b , false => b
-- ANCHOR_END: boolx

example : ∀ b:Bool, (! b) ≠ b := by
   intro b eq
   cases b
   . cases eq
   . cases eq

theorem b_dm2 : ∀ b c : Bool,
   (! (b && c)) = (!b || ! c) := by
intro b c
cases b
. rfl --dsimp [and,not,or]
. rfl --dsimp [and,not,or]

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
    . --dsimp [and] at H
      assumption
. intro H
  cases H with
  | intro Hb Hc =>
    --dsimp [isTrue] at Hb
    rw [Hb]
    dsimp [and]
    assumption








end BoolProofs
