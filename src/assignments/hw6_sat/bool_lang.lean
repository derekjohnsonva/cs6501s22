namespace bool_lang

inductive bool_var 
| V (n : ℕ)

open bool_var

inductive bool_expr : Type
| TT : bool_expr
| FF : bool_expr
| var (v : bool_var) : bool_expr
| conj (e1 e2 : bool_expr) : bool_expr
| disj (e1 e2 : bool_expr) : bool_expr
| neg (e : bool_expr)

open bool_expr

-- NOTATIONS
notation b1 * b2 := conj b1 b2
notation b1 + b2 := disj b1 b2
prefix ! := neg

end bool_lang