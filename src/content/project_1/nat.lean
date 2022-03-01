/-
In this file, we'll start to build a certified abstract
data type for the natural numbers. What we want is for
our implementations to faithfully present the properties
of natural numbers that we're familar with from highschool
algebra. For example, zero is a left identify for addition;
zero is also a right identity; addition is associative and
commutative; the distributive law holds; etc. We'll get
you started, and you will then finish off development of
a certified abstract data type for natural numbers.
-/

namespace hidden

/-
DATA TYPE
-/
inductive nt 
| zero
| succ (n' : nt)

open nt 

/-
Some example values of this type, with nice names.
-/
def one := succ zero
def two := succ (succ zero)
def three := succ (succ (succ zero))
def four := succ three  -- works just fine
def five := succ four
def six := succ five

-- tests
#reduce four
#reduce five
#reduce six


/-
OPERATIONS
-/

-- unary operations

/-
This implementation of the identity function
shows that we can match "any" argument with the
use of an available (unbound) identifier, here n.
You can read this definition as saying that id
is a function from nt to nt, and in particular
when applied to any argument, n, it returns n.
Importantly, we don't need to "analyze" n to 
decide what to return. 
-/
def id : nt → nt 
| n := n

/-
A similar strategy works for defining increment.
-/
def inc : nt → nt 
| n := succ n


/-
Next we'll look at the decrement function, defined
mathemtically as mapping 0 to 0 and and any positive
natural number, n = n'+1, to n', i.e., to n-1. Make
sure you understand what we just said! To implement
this function, we need to analyze the argument in
order to determine if it's zero or non-zero (which
is to say, the successor of some natural number, n').
-/
def dec : nt → nt 
| zero := zero 
| (succ n') := n' 

-- tests
#reduce dec two
#reduce dec one
#reduce dec zero

/-
The key to this definition is in the pattern match
that occurs in the second case. Take, for example,
the expression (dec two). To evaluate this we first
evaluate the identifier expression, two, which then
unfolds to (succ (succ zero)), then we do pattern
matching. This term does not match the term, zero,
so Lean moves on to match it with (succ n'). 

The essential technical concept at this point what
we call unification. Lean sees that the pattern, 
(succ n'), can be unified with (succ (succ zero)),
where the "succ" in (succ n') matches the first
"succ" in (succ (succ zero)), and where n' matches
the rest, namely (succ zero); and that n' is what
gets returned. 

The big idea is that you can use pattern matching
to "analyze" a term (argument in this case), to pull 
it apart into subterms pieces, giving subterms names
(here n') that we can then use to express the return
result to the right of the colon-equals separator.
-/

/-
Next, we define an isZero "predicate function", a
function that returns true if an argument has a
particular property (here that of being zero), or
false if it doesn't. We again have to analyze the
argument (doing a kind of case analysis). The one
new concept introduced here is that sometimes you
will want to match on any value of a given argument 
without giving it a name. This function matches on
its argument to determine if it's zero, in which
case the function returns true, otherwise it just
returns false without further naming or analysis 
of the argument value.
-/
def isZero : nt → bool
| zero := tt 
| _ := ff

/-
Another example of a function where there's no 
need to analyze the argument: this function takes
a natural number and returns zero no matter what
it is.
-/
def const_zero : nt → nt 
| _ := zero

/-
As an aside, it would be preferable for readability
to use simpler syntax to define this function. Here
is an alternative.
-/

def const_zero' (n : nt) := zero

-- some simple tests
#check const_zero'
#reduce const_zero' six


-- binary operations

/-
Addition is defined as iterated application of the
increment (inc) function to the second argument the
first argument number of times. For example, 3 + 2
reduces to 1 + 1 + 1 + 2. That's three applications
of inc to two. 
-/
def add : nt → nt → nt
| zero m := m
| (succ n') m := succ (add n' m)

-- tests
#reduce add two three                 -- check by eye
example : add two three = five := rfl -- prove it

/-
Multiplication implemented as iteration of 
addition of the second argument the first
argument number of times. Note that iterating
multiplication 0 times is defined to be one,
while iterating addition zero times is defined
to be zero.
-/
def mul : nt → nt → nt
| zero m := zero
| (succ n') m := add (mul n' m) m 

-- test
example : mul two three = six := rfl

/-
Exponentiation is defined to be iteration
of multiplication of the first argument the
second argument number of times. Take some
time to really study the similarities and
differences in the definitions of add, mul,
and exp.
-/
def exp : nt → nt → nt
| n zero := one
| n (succ m') := mul n (exp n m')

-- tests 
example : exp two three = succ (succ six) := rfl
example : exp zero three = zero := rfl
example : exp three zero = one := rfl

/-
PROOFS OF PROPERTIES

There are many properties we can try to prove. As
a starter, let's try to prove that zero is a left
identity for addition.
-/
example : ∀ (m : nt), add zero m = m := by simp [add] 

/-
The crucial point in this case is that we already
know that, ∀ (m : nt), add zero m = m, *from the 
definition of add*. 

  def add : nt → nt → nt
  | zero m := m
  | (succ n') m := succ (add n' m)

The first rule serves as an axiom that allows us
instantly to conclude that: ∀ m, add zero m = m. 
The proof is by simply invoking this axiom, which
we do by using the simplify (simp) tactic in Lean,
pointing it to the definition whose rules we want
it to employ.

Note that "by" is a way of introducing a proof written
using tactics without having the write "begin ... end."
-/

/-
Perhaps somewhat surprisingly, we hit a roadblock when
we try to prove that zero is a right identity. We don't
have an axiom for that! Rather we'll need to prove it 
as a theorem.
-/
example : ∀ (m : nt), add m zero = m := by simp [add] --fail

-- You prove it!
example : ∀ (m : nt), add m zero = m :=
begin
end

end hidden