import .bool_sat_dev

namespace bool_lang
open bool_lang.bool_var

/-
Write a few test cases here, expressed as little
theorems to be proved. 
-/

def X := (bool_var.V 0)
def Y := (bool_var.V 1)
def Z := (bool_var.V 2)

open bool_expr

def e1 := TT
def e1' := FF
def e2 := var X
def e3 := var Y
def e4 := bool_expr.conj e2 e3

/-
What list of interps should arise from a 
set of zero variables? It can't be the
empty list of interpretations bcause we
need at least one interpretation under
which to evaluate an expression, e, even
if it's one without any use of variables.
-/

#eval is_satisfiable e1
#eval is_satisfiable e1'
#eval is_satisfiable e2
#eval is_satisfiable (conj e2 (not e2))
#eval is_satisfiable (disj e2 (not e2))


end bool_lang