namespace hidden

inductive inhabited''' (α : Type)
| mk (a : α) : inhabited'''

-- Proofs of inhabitation for three unrelated types
example : inhabited''' bool   := inhabited'''.mk tt
example : inhabited''' nat    := inhabited'''.mk 0
example : inhabited''' string := inhabited'''.mk ""
-- The idea is that you might have a function that needs to get a default value for a type
-- You would want to constrain this getDefaultValue function to only be able to do so on inhabited types

/- 
Lets Talk About Parametric Polymorphism (aka Generics)
  This is basically when a function can be applied to multiple types without changing 
  the implementation of the function.
-/
def list_len (α : Type) : list α → nat
| [] := 0
| (h::t) := 1 + list_len t

/-
If instead, you wanted to make a function called list_sum that would return the sum of all of the elements of a list,
you would want to have an instance of some add class (has_add)
-/

-- A structure is an inductive type with only one constructor. Just syntactic sugar around inductive
--Constructor name is mk
structure inhabited'' (α :Type) :=
mk :: (a : α)
-- Yet another way to write this
structure inhabited' (α : Type) :=
(a : α)

-- This is new. We are now annotating this structure definition. We are declaring instances of it to be new types that
-- we will be able to look up
@[class] structure inhabited (α : Type) :=
(a : α)

-- What this construct below has done it to both
-- 1) Create an instance of inhabited for bool
-- 2) Register this instance in a dictionary indexed by type
instance bool_inhabited : inhabited bool :=
inhabited.mk tt

-- Lets do the same for nat
instance nat_inhabited : inhabited nat :=
inhabited.mk 0
-- and for String
-- you do not have to name these things
instance : inhabited string :=
inhabited.mk ""

def get_default_value (α : Type) [i : inhabited α] : α :=
i.a

#eval get_default_value string
#eval get_default_value nat
#eval get_default_value empty -- Should throw an error because we have no and can make no default value for empty


-- Write something like this for monoid
class monoid (α : Type) :=
(op : α → α → α)
(id : α)
(pf : ∀ (a : α), op a id = a)



instance add_monoid : monoid nat :=
monoid.mk
  nat.add
  0
  nat.add_zero

def foldr (α : Type) [m : monoid α] : list α → α
| [] := m.id
| (h::t) := let x:=m.op in x h (foldr t)


end hidden