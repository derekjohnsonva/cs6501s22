/-
-/

#check @eq.refl

/-
∀ {α : Sort u_1} (a : α), a = a
-/

#check @eq.subst

/-
∀ 
 {α : Sort u_1} 
 {P : α → Prop} 
 {a b : α}, 
 a = b → 
 P a → 
 P b
-/

/-
Okay, so what's P? What do we mean
by a predicate or a property of values
of a given type?
-/

/-
What do we even mean by a = b? 

Answer: = is just an infix notation
for (eq α a b), where α is generally
inferred from a. So let's look at eq
carefully.
-/

#check @eq

/-
Π {α : Sort u_1}, α → α → Prop

Π is like ∀ and is used especially 
where one is expressing a function
type (as in our case here) rather
than a logical proposition.

We can read this type then as the 
type of a function that takes as 
its arguments: a type, α (implicit),
and two values, a and b, of type, 
α; and that returns a proposition
"about" those values, in this case
asserting that they are equal.

We interpret, (eq a b), to be the
proposition, a=b. Indeed, Lean
defines a=b as an infix notation
for (eq a b). 


α and any
-/
def two_eq_three := eq 2 3    -- longhand for 2 = 3

namespace hidden

inductive empty : Type

inductive unit : Type
| star

inductive bool 
| tt : bool
| ff

open bool

-- types define namespaces
def true := tt

/-
Constructors are disjoint.
Construtors are injective.
Constructors are exhaustive.
-/

inductive nat_with_error : Type
| some (n : ℕ)
| none 

open nat_with_error

def isEven (n : ℕ) := n%2 = 0

def maybe_returns_good_result (n : ℕ) : nat_with_error :=
none

universe u
inductive option (α : Type u)
| some (a : α) : option 
| none : option

def b1 : option bool := option.none
def b2 : option bool := option.some bool.tt

inductive nat : Type
| zero : nat 
| succ (n' : nat) : nat

def z := nat.zero
def t := nat.succ (nat.succ (nat.zero))

end hidden

#check nat


def isEven (n : ℕ) : Prop := n % 2 = 0

#check isEven 1
#reduce isEven 1
#reduce isEven 2
#check isEven

def foo (a b : ℕ) (h_eq : a = b) (h_ev : isEven a) : isEven b :=
(eq.subst h_eq h_ev)

#check foo (1+1) 2 (rfl) (rfl)





