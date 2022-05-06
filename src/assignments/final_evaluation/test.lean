import .option .list

namespace hidden

/-
You can write test cases in this file.
-/

universes u v

--
def poly_map
  {α β : Type u} 
  {t : Type u → Type u}   -- list, option
  [m : functor t]         -- functor list, functor option
  (f : α → β)
  (i : t α) :
  t β
:= functor.map f i

/-
Exception propagation functor
-/
#reduce poly_map nat.succ none
#reduce poly_map nat.succ (some 0)

/-
Non-deterministic (multi-valued) argument functor
-/
#reduce poly_map nat.succ []
#reduce poly_map nat.succ [1,2,3]

end hidden