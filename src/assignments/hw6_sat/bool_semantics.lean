import .bool_expr
import .bool_interp

namespace bool_lang

open bool_expr

-- OPERATIONS

/-
Evaluate a Boolean expression under a given
interpretation. See bool_interpr for details
of interp.
-/
def eval : bool_expr → interp → bool
| TT _ := tt
| FF _ := ff
| (var v) i := i v
| (conj e1 e2) i := and (eval e1 i) (eval e2 i)
| (disj e1 e2) i := or (eval e1 i) (eval e2 i)
| (neg e) i := not (eval e i)

end bool_lang