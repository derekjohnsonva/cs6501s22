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

def add_two : ℕ → ℕ := λ(a : ℕ), a + 2
#reduce add_two 1

/-
Exception propagation functor
-/
#reduce poly_map nat.succ none
#reduce poly_map nat.succ (some 0)
#reduce poly_map add_two (some 0)



/-
Non-deterministic (multi-valued) argument functor
-/

#reduce poly_map nat.succ []
#reduce poly_map nat.succ [1,2,3]
#reduce poly_map add_two [1,2,3]

-- Aplicative Functors
def poly_seq
  {α β : Type u}
  {t : Type u → Type u}
  [m : applicative t]
  (f : t (α → β))
  (i : t α) :
  t β
:= has_seq.seq f i


-- examples with one-argument functions
 -- using option
#reduce poly_seq (has_pure.pure add_two) (some 1)

#reduce poly_seq (some (nat.succ)) none -- none
#reduce poly_seq (some(@id ℕ)) (some 5)
#reduce poly_seq (none) (some 1)
#eval hidden.has_pure.pure (nat.succ) <**> (some 1)

-- examples with multi-argument functions
#reduce poly_seq (some nat.mul) (some 3) 
#reduce poly_seq(poly_seq (some nat.mul) (some 3)) (some 4)
#reduce hidden.has_pure.pure (nat.mul) <**> none <**> some 4
#reduce hidden.has_pure.pure (nat.mul) <**> some 3 <**> none

#reduce some(nat.add) <**> some 3 <**> some 4
 -- using list
#reduce poly_seq (has_pure.pure add_two) [1,2,3]

#reduce poly_seq [nat.succ] []
#reduce [nat.succ] <**> []

#reduce [nat.succ] <**> [1,2,3]

#reduce (hidden.has_pure.pure nat.succ) <**> [1,2,3]

#reduce [nat.succ, nat.pred] <**> []
#reduce [nat.succ, nat.pred] <**> [1,2,3]

-- tests with two-argument functions!
#reduce (hidden.has_pure.pure nat.add) <*> [1,2,3] 
#reduce (hidden.has_pure.pure nat.add) <**> [1,2,3] <**> [2,4,6]
#reduce [nat.add, nat.mul] <**> [1,2,3] <**> [2,4,6]

#reduce [nat.add] <**> [1,1,1] <**> [2,2,2]
-- QUESTION: WHY is the result of this so long?



end hidden