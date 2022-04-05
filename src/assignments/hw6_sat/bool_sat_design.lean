import .bool_expr
import .bool_semantics
import .set_T

namespace bool_lang
open bool_lang.bool_expr

/- DESIGN/TASK STRUCTURING, LAST CLASS

Our next goal is to implement a simple
Boolean satisfiablity solver. 

Along the way, we'll be introduced to the 
higher-order functions, map and fold, on
lists.
-/

/-
First, let's write a declarative specification.
Satisfiability is a property of Boolean expressions.
-/

def is_satisfiable (e : bool_expr) : Prop := 
  ∃ (i : interp), eval e i = tt 

/-
Satisfiability a "decideable" property, in that 
there is an algorithm (guaranteed to terminate in
a finite number of steps for any input) that will
compute whether a given expression has this property
or not. 

For an expressions with n distinct variables, a 
brute force algorithm will enumerate all 2^n 
interpretations, will evaluate the expression 
under each one, and will determine whether the 
expression evaluates to true under at least one 
of them. 
-/

/-
Last time we sketched out an implementation and
somewhat "recklessly" got started implemeting one
of them: a procedure that computes the set of 
distinct variables in any given expression, e.

1. Compute set, V, of variables in expression
  - get_var_set : bool_expr → cset bool_var
  - requires "mutable set" abstraction, cset 
  - mutators are no-ops when "inapplicable"

2. Compute list of all interpretations for V
  - get_interps : cset bool_var → list bool_interp
  - requires list abstraction; we use Lean's list 

3. Map list of interps to list of bool values
  - interps_of_vars : cset interp → list bool

4. Reduce list of Boolean values to final result
  - reduce_or : list bool → bool (satisfiability)
  - reduce_and : list bool → bool (validity)
-/

/-
Today we'll learn a much more systematic design
and extremely important and fundamental design
procedure: top-down structured decomposition. It
is also known simple as "structured programming." 
Understanding structured programming is essential
for any competent software engineer.

1. Assume the function that is to be defined
2. Write test cases / conjectures that should
   pass when the programming is complete
3. Assume subroutines needed to implement function
4. Implement the function in terms of these routines
5. Recursively apply this procedure to subroutines
6. Run tests, debug, repair if needed, celebrate
-/

--axioms
  -- (reduce_or : list bool → bool)
  -- (reduce_and : list bool → bool)
  -- (map : ∀ {α β : Type}, (α → β) → list α → list β)
  -- (interps_of_vars : cset bool_var → list interp)
  -- (get_var_set : bool_expr → cset bool_var)

def interps_of_vars_helper : ℕ → list interp
| 0       := []
| (n'+1)  := _::(interps_of_vars_helper n')


def interps_of_vars : cset bool_var → list interp
| s := let n := (size s) in interps_of_vars_helper n

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


def is_satisfiable' : bool_expr → bool :=
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