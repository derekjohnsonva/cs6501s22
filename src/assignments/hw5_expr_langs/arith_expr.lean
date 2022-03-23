-- SYNTAX

-- Variables ADT

-- data type
inductive nat_var 
| Δ (n : ℕ)

open nat_var

-- operations
def nat_var_eq : nat_var → nat_var → bool
| (Δ n) (Δ m) :=  n = m   -- coercion here

-- notationss
notation e1 = e2 := nat_var_eq e1 e2

-- expression ADT

-- data type
inductive nat_expr : Type
| lit (n : nat)
| var (v : nat_var) 
| dec (e : nat_expr) 
| inc (e : nat_expr) 
| add (e1 e2 : nat_expr)

open nat_expr

-- notations
notation `[`n`]` := lit n     -- we overload []
notation `[`v`]` := var v     -- there and here
postfix `++` :=  inc
notation e1 + e2 := add e1 e2

-- interpretation ADT

-- type
def nat_var_interp := (nat_var → nat)

-- operations
def override : 
  nat_var_interp → 
  nat_var → 
  nat → 
  nat_var_interp :=
λ i v n,
  λ x, 
    if (nat_var_eq x v) 
    then n 
    else i x

-- semantics : assign nat value to any expr given interp

def eval : nat_expr → nat_var_interp → nat
| (lit n) _ := n
| (var v) i := i v
| (dec e) i := (eval e i) - 1
| (inc e) i := (eval e i) + 1
| (add e1 e2) i := (eval e1 i) + (eval e2 i)
