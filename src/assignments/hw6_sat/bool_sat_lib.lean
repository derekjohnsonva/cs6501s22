import .bool_expr
import .bool_semantics
import .set_T

namespace bool_lang
open bool_expr

-- HOMEWORK #1: Complete this function. 
def get_var_set : bool_expr → cset bool_var
| TT := []
| FF := []
| (var v) := [v]
| (conj e1 e2) := union var_eq (get_var_set e1) (get_var_set e2)

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

end bool_lang