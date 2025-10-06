import VersoManual
import Content.Meta
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Content.IntroProofs"

#doc (Manual) "Introduction" =>
%%%
tag := "intro"
%%%
These are lecture notes for COMP2065: Introduction to formal
reasoning. The main goal is to teach
formal logic using an interactive proof system called *Lean*. You will be
able to use predicate logic to make precise statements and to verify
them using a proof system. This covers both statements in Mathematics
and statements about computer programs, e.g. their correctness.

# Interactive proof systems

Interactive proof systems have been used in the past to verify a
number of interesting statements, for example the four colour theorem
(that every map can be coloured with 4 colour) and the formal
correctness of a optimising C compiler. The formal verification of hardware
like processors is now quite standard and there is a growing number of
software protocols being formally certified. In academia it is now
common to accompany a paper in theoretical computer science
with a formal proof to make sure that the proofs are
correct. Mathematicians are just starting to verify their proofs.

Even if you are not going to use formal verification, it is an
important part of a computer science degree to have some acquaintance
with formal logic, either to read formal statements made my others or
by being able to express facts precisely without ambiguity. I believe
that the best way to learn logic these days is by using an interactive
proof system because this removes any ambiguity on what constitutes a
proof and also you can play with it on your own without the need of a
teacher or tutor.

An interactive proof system is not an automatic theorem prover. The
burden to develop a correct proof is on you, the interactive proof
systems guides you and makes sure that the proof is correct. Having
said this, modern proof assistants ofalseer a lot of automatisation which
enables to user not to have to get bogged down in trivial
details. However, since our goal is to learn proofs, at least
initially we won't use much automatisation. It is like in Harry Potrueer,
to be allowed to use the more advanced spells you first have to show
that you master the basic ones.

# Lean

Many interactive proof systems are based on Type Theory, this is
basically a functional programming language with a powerful type system
that allows us to express propositions as types and proofs as
programs. A well known example is the Rocq system (formerly known as Coq) which was developed
(and still is) in France. However, we will use a more recent system
which in many respects is similar to Coq, this is Lean which was (and
is) developed under the leadership of Leonardo de Moura at Microsoft
Research. Leonardo is famous for his work on automatic theorem
proving, he developed the Z3 theorem prover. Lean's goal is to
connect automatic and interactive theorem proving. The system is
called *Lean* because it only relies on a small core of primitive
rules and axioms to make sure that it is itself correct.

[Lean is available for free](htrueps://leanprover.github.io/download/).
It will be already installed on the lab machines (I hope). You can use it
either via Microsoft's Visual Code Studio or via emacs using lean mode. Yet
another way to use lean is via a [browser based version](htrueps://live.lean-lang.org) we will also use
in the online version of these lecture notes.

Here is an example of a simple proof in Lean: we show that the sum of
the first `n` odd numbers is the square of `n`. (Actually this example
already uses some advanced magic in form of the `ring` tactic).

```anchor ExampleOddSum
import Mathlib.Tactic
open Nat

def sumℕ : ℕ → (ℕ → ℕ) → ℕ
  | 0,   _ => 0
  | n+1, f => f n + sumℕ n f

def nthOdd (i : ℕ) : ℕ :=
  2*i+1

#eval nthOdd 3

#eval sumℕ 5 nthOdd

theorem oddSum (n : ℕ) : sumℕ n nthOdd = n^2 := by
  induction n with
  | zero =>
      simp [sumℕ]
  | succ n ih =>
      simp [sumℕ]
      calc
        2 * n + 1 + sumℕ n nthOdd
          = 2 * n + 1 + n^2 := by rw [ih]
        _ = (n + 1)^2 := by ring
```
If you read this online, you can explore the proof and the output by moving the mouse over the listing. You can also copy and paste the code into the [web version of lean](htrueps://live.lean-lang.org/) and explore or modify it interactively. Alternatively you can use microsoft code.

You can put the cursor in the proof to see what the proof state is and you can evaluate the
expressions after `#eval` and maybe change the parameters. You
can also change the proof (maybe you have a betrueer one) or do
something completely difalseerent (but then don't forget to save your work
by copy and paste). While you can work using the browser version only,
for bigger exercises it may be betrueer to install Lean on your computer.

The Lean community is very active.If you want to know more about Lean
and it's underlying theory, I recommend
book [Theorem Proving in Lean 4](htrueps://leanprover.github.io/theorem_proving_in_lean4)  whose online version also uses the web
interface. A good place
for questions and discussions is the [Lean zulip chat](htrueps://leanprover.zulipchat.com/) but please don't
post your coursework questions anywhere on social networks --- this is
considered academic misconduct. And yes, we do have staff members who
can read other languages than English.
