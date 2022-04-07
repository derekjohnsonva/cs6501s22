import .bool_expr
import .bool_semantics
import .set_T

namespace bool_lang
open bool_lang.bool_expr

/- DESIGN/TASK STRUCTURING, LAST CLASS

Our next goal is to implement a simple
Boolean satisfiablity solver. 

Last time we sketched out an implementation and
somewhat "recklessly" got started implemeting one
of the required subroutines: a procedure that 
computes the set of distinct variables in any 
given expression, e. Along the way we learned
about the list ADT and used it to implement a
"mutable set" ADT, basing the implementation 
on lists without duplicates. 

Today we'll first review and update that work
quikcly, and then take a step back and see how 
we can apply a more systematic design procedure
to the construction of an implementation of our
SAT solver.

In particular, the take-away concept from this
class is "top-down structured decomposition," 
also known as "structured programming." Knowing 
how to do structured programming is essential
for every half-way decent software engineer.
-/ 

/- 
1. Assume the function that is to be defined
2. Write test cases / conjectures
3. Specify subroutines needed to implement the function
4. Implement the function in terms of these routines
5. Recursively develop subroutines
6. Run tests, debug and repair if needed, celebrate
-/

/-
Last time we crafted the following decomposition

Given any expression, e,
  1. Compute set, V, of distinct variables in e
  2. Compute list, is, of all interpretations for V
  3. Evaluate e under each interpretation i ∈ is
  4. "or-reduce" list of Booleans to result value
  5. return this result
-/

/-
Let's apply top-down structured decomposition.

1. Assume the function to be defined
2. Write test cases -- test-driven development (TDD)
3. Specify subroutines needed to implement the function
4. Implement the function in terms of these routines
5. Recursively develop subroutines
6. Run tests, debug and repair if needed, celebrate
-/

/-
0. Define is_satisfiable function from 
   expr to bool

1. Compute set, V, of variables in expression
  - get_var_set : bool_expr → cset bool_var
  - requires "mutable set" abstraction, cset 
  - mutators are no-ops when "inapplicable"

2. Compute list of all interpretations for V
  - get_interps : cset bool_var → list bool_interp
  - requires list abstraction; we use Lean's list 

3. "Map" list of interps to list of expression values
  - interps_of_vars : cset interp → list bool

4. "Fold/reduce" list of Boolean results to final result
  - reduce_and : list bool → bool
  - reduce_or : list bool → bool

5. Return resulting value
-/

--axioms
  -- (reduce_or : list bool → bool)
  -- (reduce_and : list bool → bool)
  -- (get_(map : ∀ {α β : Type}, (α → β) → list α → list β)
  -- (interps_of_vars : cset bool_var → list interp)
  -- (get_var_set : bool_expr → cset bool_var)

def interps_of_vars_helper : ℕ → list interp
| 0       := 
| (n'+1)  := _::(interps_of_vars_helper n')

def pow : nat → nat → nat 
| n 0 := 1
| n (nat.succ n') := n * (pow n n')

def interps_of_vars : cset bool_var → list interp
| s := let n := (size s) in interps_of_vars_helper (pow 2 n)

-- HOMEWORK #1: Complete this function. 
def get_var_set : bool_expr → cset bool_var
| TT := []
| FF := []
| (var v) := [v]
| (conj e1 e2) := union var_eq (get_var_set e1) (get_var_set e2)
| (disj e1 e2) := union var_eq (get_var_set e1) (get_var_set e2)
| (not e) := get_var_set e

def interps_of_expr (e : bool_expr) : list interp := 
  interps_of_vars (get_var_set e)

def get_values_of_expr (e : bool_expr) : list bool :=
  list.map (eval e) (interps_of_expr e)

def reduce_and : list bool → bool
| list.nil := true
| (h::t) := band h (reduce_and t) 

def reduce_or : list bool → bool
| list.nil := false
| (h::t) := bor h (reduce_and t) 

#check @list.map


def is_satisfiable : bool_expr → bool :=
λ e,
  reduce_or
    (
      list.map 
        (eval e) 
        (interps_of_vars 
          (get_var_set e)
        )
    )

/-
Talk about reversal of order of expression versus our
English language narrative? Introduce the "do" syntax?
-/
    


-- HOMEWORK #2: Sketch implementation for task #2
/-
Hints and help: 

1. You may assume that variable indices (as in "var.V 2"))
are allocated in ascending order with no skips. So if you
have an expression with variables X, Y, and Z, the would 
be (V 0), (V 1), and (V 2). You also have a function to 
compute the size of any "set" of variables. Given these 
two facts/assumptions, think of a way to take a set of
variables and return a list of interpretations for it. 
-/

-- HOMEWORK #3: Sketch an implementation for task #3

-- HOMEWORK #4: Sketch an implementation for task #4