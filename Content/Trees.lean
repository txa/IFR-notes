import VersoManual
import Content.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.TreeProofs"

#doc (Manual) "Trees" =>

Trees are everywhere, there isn't just one type of trees but many
datatypes that can be subsumed under the general concept of
trees. Indeed the types we have seen in the previous chapters (natural numbers and lists) are special instances of trees.

Trees are also the most dangerously underused concept in
programming. Bad programmers tend to try to do everything with
strings, unaware how much easier it would be with trees. You
don't have to be a functional programmer to use trees, trees can be
just as easily defined in languages like Python - see
[my computerphile video](https://youtu.be/7tCNu4CnjVc)

In this chapter we are going to look at two instances of trees:
expression trees and sorted trees.

Expression trees are used to encode
the syntax of expressions, we are going to define an interpreter and a
compiler which compiles expression into the code for a simple stack
machine and then show that the compiler is correct wrt the
interpreter. This is an extended version of *Hutton's razor* an
example invented by Prof Hutton.

The 2nd example is tree-sort: an efficient alternative to
insertion-sort. From a list we produce a sorted tree and then we turn
this into a sorted list. Actually, tree-sort is just quicksort in
disguise.

# Compiler correctness

I am trying to hammer this in: when you see an expression like `x * (y + 2)` or `(x * y) + 2` then try to see the tree. Really expressions
are a 2-dimensional structure but we use a 1-dimensional notation with
brackets to write them.

![expr1](diagrams/expr1.pdf)

`x * (y + 2)`

![expr2](diagrams/expr2.pdf)

`(x * y) + 2`

But it isn't only about seeing the tree we can turn this into a
datatype, indeed an inductive datatype.

```anchor Expr
inductive Expr : Type
| const : ℕ → Expr
| var : String → Expr
| plus : Expr → Expr → Expr
| times : Expr → Expr → Expr
```

and we can translate our examples: `x * (y + 2)`:
```anchor e1
def e1 : Expr
:= times (var "x") (plus (var "y") (const 2))
```
and `(x * y) + 2`:
```anchor e2
def e2 : Expr
:= plus (times (var "x") (var "y")) (const 2)
```

It is important to realize that there is no direct connection between elements of the type `Expr` and expressions in lean. While lean knows how to evaluate expressions:
```anchor lean_eval
def x : ℕ := 3
def y : ℕ := 5

#eval x * (y + 2)
#eval (x * y) + 2
```
it doesn't know how to evaluate `Expr`. If we try
```anchor lean_no_eval
#eval e1
#eval e2
```
all we get is the tree again (with names fully qualified).

Our first goal is to implement a specialized version of `#eval` which we call `eval`. It proceeds by recursion over the expression tree. To implement `eval` we need to resolve references to variables (which are our version of the heap). We do this by defining a type `Env`:
```anchor Env
def Env : Type
  := String → ℕ
```
We really should take care of variables which aren't defined (and use `Option`, which you may know as `Maybe` from Haskell) but we postpone run-time errors until later (refactoring) and adopt the very problematic convention that undefined is `0`. Hence our test environment looks like this:
```anchor env0
def env0 : Env
| "x" => 3
| "y" => 5
| _ => 0
```
The definition of `eval` now is straightforward proceeding by structural induction over the tree - translating every syntactical element with their meaning, variable are looked up in the environment and constants stand for themselves:
```anchor eval
def eval : Expr → Env  → ℕ
| const n , env => n
| var x , env => env x
| plus e1 e2 , env =>
    (eval e1 env) + (eval e2 env)
| times e1 e2 , env =>
    (eval e1 env) * (eval e2 env)
```
We test `eval` with our example expression and environment leading to the expected outcome:
```anchor eval_ex
#eval (eval e1 env0)
#eval (eval e2 env0)
```

We have defined an interpreter which provides a straightforward *denotational semantics* of our language. Next we provide a machine which can evaluate expressions. The machine is a stack machine which also accesses the environment which plays the role of a heap here. We define a type of instructions `Instr` and our `Code` is just a list of instructions.
```anchor Instr
inductive Instr : Type
| pushC : ℕ → Instr
| pushV : String → Instr
| add : Instr
| mult : Instr
```
Our machine just has 4 instructions:
- `pushC n` : push `n` on the stack,
- `pushV x` : push the value of variable `x` into the stack,
- `add` : pop the two top items of the stack and replace them by their sum
- `mult` : pop the two top items of the stack and replace them by their product

We use `abbrev` to define `Code` so that we can use `++` on `Code`:
```anchor Code
abbrev Code : Type
:= List Instr
```
Here is the hand translation of the first expression into stack machine code:
```anchor c1
def c1 : Code
:= [pushV "x", pushV "y", pushC 2,add,mult]
```
I leave it as an exercise to hand translate `e2`. To implement our machine we need a representation of a stack, we use lists again.
```anchor Stack
def Stack : Type
:= List ℕ
```
We are now ready to define the *operational semantics*, i.e. the `run` function implementing our machine:
```anchor run
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
```
How does `run` work:
- if there is no code left, the stack should just contain the result which we return.
- in the other cases we dispatch on the first instruction:
  - if it is `pushC` or `pushV` we push the appropriate value on the stack.
  - if it is `add` or `mult` we assume that the arguments are on the top of the stack (note the order), pop them and replace them by the result.
- there are a number of error conditions, which we should signal explicitly (using `Option` or a more specific error type) but we play still quick and dirty and return `0`.

Here is the first version of the compiler:
```anchor compile1
def compile : Expr → Code
| (const n) => [pushC n]
| (var x) => [pushV x]
| (plus l r) =>
    (compile l) ++ (compile r) ++ [add]
| (times l r) =>
    (compile l) ++ (compile r) ++ [mult]
```
The compiler translates every expression with a code that would leave the result of evaluating the expression on the stack. In particular for the binary operations it appends the code for the two subexpression and then issues the appropriate operation.

Let's test it on our examples:
```anchor compile1_test
#eval (run (compile e1) [] env0)
#eval (run (compile e2) [] env0)
```

The compile works fine and we could go on to prove correctness which is
```anchor compile1_ok
theorem compile_ok :
  ∀ e : Expr, ∀ env : Env,
  eval e env = run (compile e) [] env := by sorry
```

However, we will first reimplement the compiler using *continuation passing style* which is both more efficient and easier to verify because we avoid using `++` by passing the rest of the code (the continuation) as an argument. The idea is basically the same as for `fastrev`. It is easier to verify because since we avoid `++` we don't have to refer to the monoid laws of `List`. Here is the continuation passing version of the compiler which uses an auxiliary function:
```anchor compile_aux
def compile_aux : Expr → Code → Code
| const n , c => pushC n :: c
| var x , c => pushV x :: c
| plus l r , c =>
    compile_aux l (compile_aux r (add :: c))
| times l r , c =>
    compile_aux l (compile_aux r (mult :: c))
```
In each of the cases we pass the code which comes after the current piece of code. The binary operations are translated into nested calls of `compile_aux`. We derive `compile` by supplying the empty code as the continuation:
```anchor compile
def compile : Expr → Code
| e => compile_aux e []
```
To verify the compiler we need to prove a lemma which does the heavy lifting
```anchor compile_aux_ok
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
```
The interesting bit is the use of tree induction. It is important to not introduce the quantifiers for `c` and `s` to early because they are changing during the proof. Note also the presence of two induction hypotheses for the binary constructors.

Using this lemma compiler correctness is now very straightforward:
```anchor compile_ok
theorem compile_ok :
  ∀ e : Expr, ∀ env : Env,
  eval e env = run (compile e) [] env := by
  intro e env
  calc
    eval e env
    = run [] [eval e env] env := by rfl
    _ = run (compile_aux e []) [] env := by rw [compile_aux_ok]
    _ = run (compile e) [] env := by rfl
```

Admittedly this is a very simple language but it is sufficient to demonstrate the basic idea of compiler correctness. We could use this as a starting point for more realistic languages:
- we want to introduce some kind of branching via 'if-then-else'. A good approach is first to introduce a *tree structured code* which can then be translated into gotos in a separate step.
- we may want to define a simple type system, eg to distinguish numbers from booleans. Well typed code should avoid any run-time errors.
- we can also introduce functions using the stack and extending the type system.
- we may want also to implement loops or general recursion. The syntax for loops would also use tree-structured code but `eval` and `run` are problematic because a loop may fail to terminate. We can define a denotational semantics which allows non-termination using domain theory but this is a bit more challenging. A cheap solution is to supply a number of steps which limits the number of unfoldings and to define the operational semantics via a relation instead of a function.
