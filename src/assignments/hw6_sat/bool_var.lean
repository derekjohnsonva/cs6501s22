namespace bool_lang

/-
We define a type of Boolean variables and
a function for comparing variables for equality.
-/

-- DATA TYPE
inductive bool_var 
| V (n : ℕ)


-- OPERATIONS
open bool_var
def var_eq : bool_var → bool_var → bool
| (V n1) (V n2) := n1 = n2  -- auto coercion to bool result

end bool_lang