namespace BoolProofs

namespace BoolDef

-- ANCHOR: boolDef
inductive Bool : Type
| false : Bool
| true : Bool
-- ANCHOR_END: boolDef

end BoolDef

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

namespace BoolOps
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

end BoolOps

open Bool

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

-- ANCHOR: distr_b
theorem distr_b : ∀ x y z : Bool,
  (x && (y || z)) = (x && y || x && z) := by
  intro x y z
  cases x
  . dsimp [and,or]
  . dsimp [and]
-- ANCHOR_END: distr_b

-- ANCHOR: distr_br
example : ∀ x y z : Bool,
  (x && (y || z)) = (x && y || x && z) := by
  intro x y z
  cases x
  . rfl
  . rfl
-- ANCHOR_END: distr_br

-- ANCHOR: distr_bz
example : ∀ x y z : Bool,
  (x && (y || z)) = (x && y || x && z) := by
  intro x y z
  cases z
  . sorry
  . sorry
-- ANCHOR_END: distr_bz

example : ∀ b :Bool, (true && b) = b := by
  intro b
  rfl

example : ∀ b:Bool, (! b) ≠ b := by
   intro b eq
   cases b
   . cases eq
   . cases eq

-- ANCHOR: dm1_b
theorem dm1_b : ∀ b c : Bool,
  (! (b || c)) = (! b && ! c) := by
-- ANCHOR_END: dm1_b
intro b c
cases b
. rfl
. rfl


-- ANCHOR: dm2_b
theorem dm2_b : ∀ b c : Bool,
   (! (b && c)) = (!b || ! c) := by
-- ANCHOR_END: dm2_b
intro b c
cases b
. rfl
. rfl


-- ANCHOR: isTrue
def isTrue : Bool → Prop
| b => b = true
-- ANCHOR_END: isTrue

-- ANCHOR: and_ok
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
-- ANCHOR_END: and_ok

-- ANCHOR: or_ok
theorem or_ok : ∀ b c : Bool,
  isTrue (b || c) ↔ isTrue b ∨ isTrue c := by
-- ANCHOR_END: or_ok
intro b c
constructor
. intro H
  cases b
  . right
    assumption
  . left
    rfl
. intro H
  cases H with
  | inl Hb =>
      rw [Hb]
      rfl
  | inr Hc =>
      cases b
      . assumption
      . rfl


-- ANCHOR: not_ok
theorem not_ok : ∀ b : Bool, isTrue (! b) ↔ ¬ isTrue b := by
-- ANCHOR_END: not_ok
intro b
constructor
. intro H
  cases b
  . intro pcf
    cases pcf
  . cases H
. intro H
  cases b
  . rfl
  . have pcf : False := by
      apply H
      rfl
    cases pcf

-- ANCHOR: isTrueD
def isTrueD : Bool → Prop
| true => True
| false => False
-- ANCHOR_END: isTrueD

-- ANCHOR: noConfBoolD
theorem noConfBoolD : true ≠ false := by
  intro pcf
  have t : isTrueD true := by
    constructor
  rw [pcf] at t
  assumption
-- ANCHOR_END: noConfBoolD


example : ∀ x y z : Bool, x && (y = z) := by
sorry


end BoolProofs
