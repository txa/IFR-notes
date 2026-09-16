import Content.NatProofs
import Content.ListProofs
set_option pp.fieldNotation false
set_option tactic.customEliminators false -- to stop lean using +1
--notation "ℕ" => Nat
namespace TreeProofs

open NatProofs hiding add
open ListProofs

open Nat

-- ANCHOR: Expr
inductive Expr : Type
| const : ℕ → Expr
| var : String → Expr
| plus : Expr → Expr → Expr
| times : Expr → Expr → Expr
-- ANCHOR_END: Expr

open Expr

-- ANCHOR: e1
def e1 : Expr
:= times (var "x") (plus (var "y") (const 2))
-- ANCHOR_END: e1

-- ANCHOR: e2
def e2 : Expr
:= plus (times (var "x") (var "y")) (const 2)
-- ANCHOR_END: e2

-- ANCHOR: lean_eval
def x : ℕ := 3
def y : ℕ := 5

#eval x * (y + 2)
#eval (x * y) + 2
-- ANCHOR_END: lean_eval

-- ANCHOR: lean_no_eval
#eval e1
#eval e2
-- ANCHOR_END: lean_no_eval

-- ANCHOR: Env
def Env : Type
  := String → ℕ
-- ANCHOR_END: Env

-- undefined = 0

-- ANCHOR: env0
def env0 : Env
| "x" => 3
| "y" => 5
| _ => 0
-- ANCHOR_END: env0

-- ANCHOR: eval
def eval : Expr → Env  → ℕ
| const n , env => n
| var x , env => env x
| plus e1 e2 , env =>
    (eval e1 env) + (eval e2 env)
| times e1 e2 , env =>
    (eval e1 env) * (eval e2 env)
-- ANCHOR_END: eval

-- ANCHOR: eval_ex
#eval (eval e1 env0)
#eval (eval e2 env0)
-- ANCHOR_END: eval_ex

-- ANCHOR: Instr
inductive Instr : Type
| pushC : ℕ → Instr
| pushV : String → Instr
| add : Instr
| mult : Instr
-- ANCHOR_END: Instr

open Instr

-- def is not good enough
--def Code : Type
-- ANCHOR: Code
abbrev Code : Type
:= List Instr
-- ANCHOR_END: Code

-- ANCHOR: c1
def c1 : Code
:= [pushV "x", pushV "y", pushC 2,add,mult]
-- ANCHOR_END: c1

-- ANCHOR: Stack
def Stack : Type
:= List ℕ
-- ANCHOR_END: Stack

-- ANCHOR: run
def run : Code → Stack → Env → ℕ
| [] ,[n] , env => n
| pushC n :: c, s , env =>
    run c (n::s) env
| pushV x :: c , s, env =>
    run c (env x :: s) env
| add :: c , m :: n :: s , env =>
    run c ((n + m) :: s) env
| mult :: c ,m :: n :: s, env =>
    run c ((n * m) :: s) env
| _ ,_ , _ => 0 -- error
-- ANCHOR_END: run

-- ANCHOR: run_c1
#eval (run c1 [] env0)
-- ANCHOR_END: run_c1

namespace compile1

-- ANCHOR: compile1
def compile : Expr → Code
| (const n) => [pushC n]
| (var x) => [pushV x]
| (plus l r) =>
    (compile l) ++ (compile r) ++ [add]
| (times l r) =>
    (compile l) ++ (compile r) ++ [mult]
-- ANCHOR_END: compile1

-- ANCHOR: compile1_test
#eval (run (compile e1) [] env0)
#eval (run (compile e2) [] env0)
-- ANCHOR_END: compile1_test

-- ANCHOR: compile1_ok
theorem compile_ok :
  ∀ e : Expr, ∀ env : Env,
  eval e env = run (compile e) [] env := by sorry
-- ANCHOR_END: compile1_ok

end compile1

-- ANCHOR: compile_aux
def compile_aux : Expr → Code → Code
| const n , c => pushC n :: c
| var x , c => pushV x :: c
| plus l r , c =>
    compile_aux l (compile_aux r (add :: c))
| times l r , c =>
    compile_aux l (compile_aux r (mult :: c))
-- ANCHOR_END: compile_aux

-- ANCHOR: compile
def compile : Expr → Code
| e => compile_aux e []
-- ANCHOR_END: compile

#eval (run (compile e1) [] env0)
#eval (run (compile e2) [] env0)

open List

-- ANCHOR: compile_aux_ok
theorem compile_aux_ok :
  ∀ e : Expr, ∀ env : Env,
  ∀ c : Code, ∀ s : Stack,
  run (compile_aux e c) s env
  = run c (eval e env :: s) env := by
intro e
induction e with
| const n =>
    intro env c s
    dsimp [compile_aux,run,eval]
| var x =>
    intro env c s
    dsimp [compile_aux,run,eval]
| plus l r ihl ihr =>
    intro env c s
    calc
      run (compile_aux (plus l r) c) s env
      = run (compile_aux l (compile_aux r (add :: c))) s env := by rfl
      _ = run (compile_aux r (add :: c)) (eval l env :: s) env
      := by rw [ihl]
      _ = run (add :: c) (eval r env :: eval l env :: s) env
      := by rw [ihr]
      _ = run c ((eval l env + eval r env) :: s) env
      := by rfl
      _ = run c (eval (plus l r) env :: s) env := by rfl
| times l r ihl ihr =>
    intro env c s
    calc
      run (compile_aux (times l r) c) s env
      = run (compile_aux l (compile_aux r (mult :: c))) s env := by rfl
      _ = run (compile_aux r (mult :: c)) (eval l env :: s) env
      := by rw [ihl]
      _ = run (mult :: c) (eval r env :: eval l env :: s) env
      := by rw [ihr]
      _ = run c ((eval l env * eval r env) :: s) env
      := by rfl
      _ = run c (eval (times l r) env :: s) env := by rfl
-- ANCHOR_END: compile_aux_ok

-- ANCHOR: compile_ok
theorem compile_ok :
  ∀ e : Expr, ∀ env : Env,
  eval e env = run (compile e) [] env := by
  intro e env
  calc
    eval e env
    = run [] [eval e env] env := by rfl
    _ = run (compile_aux e []) [] env := by rw [compile_aux_ok]
    _ = run (compile e) [] env := by rfl
-- ANCHOR_END: compile_ok



end TreeProofs
