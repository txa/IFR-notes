namespace NatProofs

namespace NatDef

-- ANCHOR: NatDef
inductive Nat : Type
| zero : Nat
| succ : Nat → Nat
-- ANCHOR_END: NatDef

end NatDef

notation "ℕ" => Nat
open Nat

-- ANCHOR: NoConf
example : ∀ n : ℕ , succ n ≠ zero := by
intro n h
cases h
-- ANCHOR_END: NoConf

-- ANCHOR: pred
def pred : ℕ → ℕ
| zero => zero
| succ n => n
-- ANCHOR_END: pred

-- ANCHOR: succInj
example : ∀ m n : ℕ, succ m = succ n → m = n := by
intro m n h
change pred (succ m) = n
rw [h]
rfl
-- ANCHOR_END: succInj

-- ANCHOR: succInj2
example : ∀ m n : ℕ, succ m = succ n → m = n := by
intro m n h
injection h
-- ANCHOR_END: succInj2

-- ANCHOR: double
def double : ℕ → ℕ
| zero => zero
| succ n => succ (succ (double n))
-- ANCHOR_END: double

-- ANCHOR: half
def half : ℕ → ℕ
| zero => zero
| succ zero => zero
| succ (succ n) => succ (half n)
-- ANCHOR_END: half


example : ∀ n : ℕ , half (double n) = n := by
intro n
induction n with
 | zero => rfl
 | succ m ih =>
    dsimp [double,half]
    rw [ih]


-- ANCHOR: halfDouble
theorem half_double :
  ∀ n : ℕ, half (double n) = n := by
intro n
induction n with
| zero => rfl
| succ n ih =>
    calc
      half (double (succ n))
      = half (succ (succ (double n))) := by rfl
      _ = succ (half (double n)) := by rfl
      _ = succ n := by rw [ih]
-- ANCHOR_END: halfDouble

-- ANCHOR: add
def add : ℕ → ℕ → ℕ
| m  , zero     => m
| m  , (succ n) => succ (add m n)
-- ANCHOR_END: add

-- ANCHOR: add_rneutr
theorem add_rneutr : ∀ n : ℕ, n + 0 = n := by
intro n
rfl
-- ANCHOR_END: add_rneutr

-- ANCHOR: add_lneutr
theorem add_lneutr : ∀ n : ℕ, 0 + n  = n := by
intro n
induction n with
 | zero => rfl
 | succ m ih =>
     calc 0 + (succ m)
          = succ (0 + m)  := by rfl
          _ = succ m := by rw [ih]
-- ANCHOR_END: add_lneutr

-- ANCHOR: add_assoc
theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) := by
intro l m n
induction n with
| zero => rfl
| succ n' ih =>
     calc  (l + m) + (succ n')
         = succ ((l + m) +n') := by rfl
      _  = succ (l + (m + n')) := by rw [ih]
      _  = l + (succ (m + n')) := by rfl
      _  = l + (m + (succ n')) := by rfl
-- ANCHOR_END: add_assoc

-- ANCHOR: add_succ
theorem add_succ :
∀ l m : ℕ, (succ l) + m = succ (l + m) := by
intro l m
induction m with
 | zero => rfl
 | succ m ih =>
     calc
       (succ l) + (succ m)
         = succ ((succ l ) + m) := by rfl
       _ = succ (succ (l + m)) := by rw [ih]
       _ = succ (l + succ m) := by rfl
-- ANCHOR_END: add_succ

-- ANCHOR: add_comm
theorem add_comm :
∀ l m : ℕ, l + m = m + l := by
intro l m
induction m with
| zero =>
    calc l + 0
        = l := by rfl
      _ = 0 + l := by rw [add_lneutr]
| succ m ih =>
      calc   l + (succ m)
           = succ (l + m) := by rfl
         _ = succ (m + l) := by rw[ih]
         _ = (succ m) + l := by rw [← add_succ]
-- ANCHOR_END: add_comm

-- ANCHOR: mult
def mult : ℕ → ℕ → ℕ
| _ , zero => zero
| m , (succ n) => mult m n + m
-- ANCHOR_END: mult

-- ANCHOR: mult_cmon
theorem mult_rneutr : ∀ n : ℕ, n * 1 = n := by sorry
theorem mult_lneutr : ∀ n : ℕ, 1 * n  = n := by sorry
theorem mult_assoc : ∀ l m n : ℕ , (l * m) * n = l * (m * n) := by sorry
theorem mult_comm :  ∀ m n : ℕ , m * n = n * m := by sorry
-- ANCHOR_END: mult_cmon

-- ANCHOR: mult_distr
theorem mult_lzero : ∀ n : ℕ , 0 * n = 0 := by sorry
theorem mult_rzero : ∀ n : ℕ , n * 0 = 0 := by sorry
theorem mult_ldistr :  ∀ l m n : ℕ , (m + n) * l = m * l + n * l := sorry
theorem mult_rdistr :  ∀ l m n : ℕ , l * (m + n) = l * m + l * n := sorry
-- ANCHOR_END: mult_distr

-- ANCHOR: LE'
def LE' : Nat → Nat → Prop
| m , n => ∃ k : ℕ , k + m = n

infix:50 " ≤' " => LE'
-- ANCHOR_END: LE'

-- ANCHOR: refl_LE'
theorem refl_LE' : ∀ n : ℕ, n ≤' n := by
intro n
exists 0
apply add_lneutr
-- ANCHOR_END: refl_LE'

-- ANCHOR: trans_LE'
theorem trans_LE' : ∀ l m n : ℕ, l ≤' m → m ≤' n → l ≤' n := by
intro l m n
intro lm mn
cases lm with
| intro k klm =>
    cases mn with
    | intro j jmn =>
        exists j + k
        calc j + k + l
             = j + (k + l) := by rw [add_assoc]
            _ = j + m := by rw [klm]
            _ = n := by assumption
-- ANCHOR_END: trans_LE'

namespace anti_sym_LE'_ex
-- ANCHOR: anti_sym_LE'
theorem anti_sym_LE' : ∀ l m : ℕ , l ≤' m → m ≤' l → m = l := by
sorry
-- ANCHOR_END: anti_sym_LE'
end anti_sym_LE'_ex

theorem add_0 : ∀ x y : ℕ , x + y = y → x=0 := by
intro x y h
induction y with
| zero =>
    calc
      x = x + 0 := by rfl
      _ = 0 := by assumption
| succ y ih =>
    apply ih
    have hh : succ (x + y) = y + 1 := by
       rw [← h]
       rfl
    injection hh

theorem add_lem : ∀ x y : ℕ , x + y = 0 → x = 0 := by
intro x y h
cases y with
| zero =>
    rw [← h]
    rfl
| succ y =>
    cases h

theorem anti_sym_LE' : ∀ l m : ℕ , l ≤' m → m ≤' l → m = l := by
intro l m lm ml
cases lm with
| intro k klm =>
  cases ml with
  | intro j jml =>
      have h : j + k + l = l := by
        calc
          j + k + l
            = j + (k + l) := by rw [add_assoc]
          _ = j + m := by rw [klm]
          _ = l := by rw [jml]
      have g : j = 0 := by
        apply add_lem
        apply add_0
        apply h
      calc m =
           0 + m := by rw [add_lneutr]
           _ = j + m := by rw [← g]
           _ = l  := by rw [← jml]


-- ANCHOR: LT'
def LT' : ℕ → ℕ → Prop
| m , n => m+1 ≤' n

infix:50 " <' " => LT'
-- ANCHOR_END: LT'

-- ANCHOR: trich_LT'
theorem trich_LT' : ∀ m n : ℕ, m < n ∨ m = n ∨ n < m := by
sorry
-- ANCHOR_END: trich_LT'

-- ANCHOR: eq_ℕ
def eq_ℕ : ℕ → ℕ → Bool
| zero , zero => true
| zero , succ n => false
| succ m , zero => false
| succ m , succ n => eq_ℕ m n
-- ANCHOR_END: eq_ℕ

-- ANCHOR: refl_eq_ℕ
theorem refl_eq_ℕ : ∀ n : ℕ, eq_ℕ n n = true := by
intro n
induction n with
| zero => rfl
| succ n ih => calc
    eq_ℕ (n + 1) (n + 1) =
    eq_ℕ n n := by rfl
    _ = true := by rw [ih]
-- ANCHOR_END: refl_eq_ℕ

-- ANCHOR: equal2eq
theorem equal2eq : ∀ m n : ℕ, m = n → eq_ℕ m n = true := by
intro m n mn
calc
  eq_ℕ m n
  = eq_ℕ m m := by rw [mn]
  _ = true := by rw [refl_eq_ℕ]
-- ANCHOR_END: equal2eq

-- ANCHOR: eq2equal_bad
example : ∀ m n : ℕ, eq_ℕ m n = true → m = n := by
intro m n mn
induction m with
| zero =>
    cases n with
    | zero => rfl
    | succ n' => cases mn
| succ m' ih =>
    cases n with
    | zero => cases mn
    | succ n' => sorry
-- ANCHOR_END: eq2equal_bad

-- ANCHOR: eq2equal
theorem eq2equal : ∀ m n : ℕ, eq_ℕ m n = true → m = n := by
intro m
induction m with
| zero =>
    intro n mn
    cases n with
    | zero => rfl
    | succ n' => cases mn
| succ m' ih =>
    intro n mn
    cases n with
    | zero => cases mn
    | succ n' =>
        have h : m' = n' := by
          apply ih
          calc
            eq_ℕ m' n'
              = eq_ℕ (succ m') (succ n') := by rfl
            _ = true := by rw [mn]
        rw [h]
-- ANCHOR_END: eq2equal

-- ANCHOR: dec_eq_ℕ
theorem dec_eq_ℕ : ∀ m n : ℕ, m = n ↔ eq_ℕ m n = true := by
intro m n
constructor
. apply equal2eq
. apply eq2equal
-- ANCHOR_END: dec_eq_ℕ

namespace dec_le'_ℕ_ex
-- ANCHOR: dec_le'_ℕ
def le'_ℕ : ℕ → ℕ → Bool
:= sorry

theorem dec_le'_ℕ : ∀ m n : ℕ, m ≤' n ↔ le'_ℕ m n = true
:= by sorry
-- ANCHOR_END: dec_le'_ℕ
end dec_le'_ℕ_ex

def le'_ℕ : ℕ → ℕ → Bool
| zero , n => true
| succ m , zero => false
| succ m , succ n => le'_ℕ m n

theorem refl_le_ℕ : ∀ n : ℕ , le'_ℕ n n = true := by
intro n
induction n with
| zero => rfl
| succ n ih => calc
    le'_ℕ (n + 1) (n + 1) =
    le'_ℕ n n := by rfl
    _ = true := by rw [ih]

theorem nle0 : ∀ m : ℕ , ¬ m + 1 ≤' 0 := by
intro m h
cases h with
| intro j jm => cases jm

theorem lePred : ∀ m n : ℕ , m + 1 ≤' n + 1 → m ≤' n := by
intro m n mn
cases mn with
| intro j jmn =>
    exists j
    injection jmn

theorem le2LE : ∀ m n : ℕ, m ≤' n → le'_ℕ m n := by
intro m
induction m with
| zero =>
    intro n mn
    rfl
| succ m ih =>
    intro n mn
    cases n with
    | zero =>
        have pcf : False := by
          apply nle0
          apply mn
        cases pcf
    | succ n =>
        have h : le'_ℕ m n = true := by
          apply ih
          apply lePred
          assumption
        calc
          le'_ℕ (m + 1) (n + 1)
            = le'_ℕ m n := by rfl
          _ = true := by rw [h]

theorem LE2le : ∀ m n : ℕ, le'_ℕ m n → m ≤' n := by
intro m
induction m with
| zero =>
    intro n mn
    exists n
| succ m ih =>
     intro n mn
     cases n with
     | zero => cases mn
     | succ n =>
         have h : m ≤' n := by
          apply ih
          calc
            le'_ℕ m n
              = le'_ℕ (m + 1) (n + 1) := by rfl
            _ = true := by rw [mn]
         cases h with
         | intro j jmn =>
             exists j
             calc
               j + (m + 1)
                 = (j + m) + 1 := by rfl
               _ = n + 1 := by rw [jmn]
