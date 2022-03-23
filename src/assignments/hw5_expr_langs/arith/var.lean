-- SYNTAX

namespace arith

-- Variables ADT

-- data type
inductive var 
| Δ (n : ℕ)

open var

-- operations
def var_eq : var → var → bool
| (Δ n) (Δ m) :=  n = m   -- coercion here

-- notationss
notation e1 = e2 := var_eq e1 e2

end arith