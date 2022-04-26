/-
As another example of overloading, this short course module
introduces a typeclass, has_truish (α : Type), that enables
overloading of a function, truish : α → bool, that takes any
value of a type, α, to one of type Boolean, thereby allowing 
values of any such a type, α,to be used where Booleans are 
expected, e.g., as conditions in conditional expressions or
statements. For example, in C and C++, the integer value, 0,
will be interpreted (converted to) false, while any other
integer value will be interpreted as true when used as the
condition in a conditional (if/then/else) statement.  
-/


/-
The has_truish typeclass enables overloading of the
"truish" operator for any type, α, for which there is
a typeclass instance.
-/
class has_truish (α : Type) :=
(truish : α → bool)

-- overload truish for bool
instance : has_truish bool :=
⟨ λ b, b ⟩ 

-- overload truish for string
instance : has_truish string :=
⟨
  λ s, 
    match s with
    | "" := ff
    | _ := tt
    end 
⟩ 

-- overload truish for nat
instance : has_truish nat :=
⟨
  λ s, 
    match s with
    | 0 := ff
    | _ := tt
    end 
⟩ 

/-
A function polymorphic in any α for which truish is defined that takes
a value, a, of this type and returns a Boolean true or false (tt or ff)
value, reflecting the truishness of a.
-/
open has_truish
def is_truish { α : Type } [has_truish α] (a : α) : bool := truish a

/-
Examples of ad hoc polymorphism
-/
#eval is_truish tt
#eval is_truish ff
#eval is_truish 0
#eval is_truish 1
#eval is_truish ""
#eval is_truish "Hello, Lean!"

def if_truish_then_else { α β : Type } [has_truish α] (c : α) (t f : β) : β :=
if is_truish c then t else f

--                        ad hoc  parametric
#eval if_truish_then_else   tt    "Yep" "Nope" 
#eval if_truish_then_else   ff    "Yep" "Nope" 
#eval if_truish_then_else   0     tt    ff 
#eval if_truish_then_else   1     tt    ff

/-
Classic example. See YesNo in Learn You a Haskell.
-/

