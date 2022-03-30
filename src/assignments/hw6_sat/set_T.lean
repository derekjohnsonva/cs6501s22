namespace bool_lang

open list

/-
We are going to represent a set of T values as a list 
of T values with an invariant: no element appears in 
such a list more than once. That is, we will represent
sets as lists without duplicates.
-/

-- DATA TYPE

def cset (T : Type) := list T

def contains {T : Type}: (T → T → bool) → T → cset T → bool
| _ _ nil := ff
| t_eq v (h::t) := if (t_eq v h) then tt else (contains t_eq v t)

def size {T : Type} : cset T → nat
| nil := 0
| (h::t) := size t + 1

def insert {T : Type} : (T → T → bool) → T → cset T → cset T 
| t_eq v nil := [v]
| t_eq v l := if (contains t_eq v l) then l else v::l

def remove {T : Type} : (T → T → bool) → T → cset T → cset T 
| t_eq v nil := nil
| t_eq v (h::t) := if (t_eq v h) then t else (h::(remove t_eq v t))

def union {T : Type} : (T → T → bool) → cset T → cset T → cset T 
| t_eq nil s2 := s2
| t_eq (h::t) s2 := union t_eq t (insert t_eq h s2)  

end bool_lang