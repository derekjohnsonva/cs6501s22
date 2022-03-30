import .interp
namespace arith


-- data types (abstract syntax)
inductive expr : Type
| lit (n : nat)
| var (v : var) 
| dec (e : expr) 
| inc (e : expr) 
| add (e1 e2 : expr)


-- notations(concrete syntax)
open arith.expr
notation `[`n`]` := lit n     -- we overload []
notation `⟨`v`⟩` := var v     -- differently now
postfix `++` :=  inc
notation e1 + e2 := add e1 e2


-- semantics (operations)
def eval : expr → var_interp → nat
| (lit n) _ := n
| (expr.var v) i := i v       -- the name, 'var,' is ambiguous here
| (dec e) i := (eval e i) - 1
| (inc e) i := (eval e i) + 1
| (add e1 e2) i := (eval e1 i) + (eval e2 i)

end arith
