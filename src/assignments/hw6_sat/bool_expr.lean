import .bool_var 

namespace bool_lang

open bool_var

-- DATA TYPE
inductive bool_expr : Type
| TT : bool_expr
| FF : bool_expr
| var (v : bool_var) : bool_expr
| conj (e1 e2 : bool_expr) : bool_expr
| disj (e1 e2 : bool_expr) : bool_expr
| not (e : bool_expr)

open bool_expr

-- NOTATIONS
notation b1 * b2 := conj b1 b2
notation b1 + b2 := disj b1 b2
prefix ! := not

end bool_lang