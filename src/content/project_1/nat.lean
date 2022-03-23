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

-- COMPUTATIONAL

/-
This implementation of the identity function can
be read as saying that id is a function from nt 
to nt, and in particular when applied to any
argument, n, it returns n. Importantly, we don't
need to "analyze/destructure" n to decide what 
to return: we just return whatever we got. 
-/
def id : nt → nt 
| n := n

-- we can compute results of evaluating applications
#reduce (id two)

/-
We can also write test cases as equality propositions
that assert that actual outputs are equal to expected
outputs, with simple equality proofs. The failure of
rfl here indicates that either the computation or the
test case is wrong.
-/
example : id two = two := rfl
example : id three = two := rfl -- oops, bad test case

/-
A similar approaches works for defining increment.
-/
def inc : nt → nt 
| n := succ n


/-
Next we'll look at the decrement function, defined
mathemtically as mapping 0 to 0 and and any positive
natural number, n = n'+1, to n', i.e., to n-1. Make
sure you understand what we just said! To implement
this function, we need to *analyze/destructure* the 
argument in order to determine if it's zero or some
non-zero number (which is to say, the successor of 
some one-smaller natural number, n').
-/
def dec : nt → nt 
| zero := zero 
| (succ n') := n'   -- you must understand this!

-- tests
#reduce dec two     -- expect one
#reduce dec one     -- expect zero
#reduce dec zero    -- expect zero

/-
Test cases as equality propositions for 
individual inputs.
-/

example : dec two = one := rfl
example : dec one = zero := rfl
example : dec zero = zero := rfl


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
#reduce const_zero' six -- expect zero


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


/- Represent the sqare function on natural numbers declaratively-/
-- Computational form
def square (n : nt) := mul n n

example : square two = four := rfl

-- Logical Form
inductive square_ind : nt → nt → Prop
| const : ∀ (n1 n2 : nt), mul n1 n1 = n2 → square_ind n1 n2

example : square_ind two four :=
begin
  apply square_ind.const,
  exact rfl,
end

/-
Problem: represent the square function
on natural numbers declaratively.
-/

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

def add : nt → nt → nt
| zero m := m
| (succ n') m := succ (add n' m)
-/
example : ∀ (m : nt), add zero m = m := by simp [add]
example : ∀ (m n: nt), ∃(p : nt), add m n = p := by 

/-
The crucial point in this case is that we already
know that, ∀ (m : nt), add zero m = m, *from the 
definition of add*. In other words, add zero m is
*definitionally* equal to m.

  def add : nt → nt → nt
  | zero m := m
  | (succ n') m := succ (add n' m)

The first rule serves as an axiom that allows us
instantly to conclude that: ∀ m, add zero m = m. 
The proof is by simply invoking this axiom, which
we do by using the simplify (simp) tactic in Lean,
pointing it to the definition whose rules we want
it to employ.

Note that "by" is a way of introducing a proof 
written using tactics without having the write 
a complete "begin ... end" block.
-/

/-
Perhaps somewhat surprisingly, we hit a roadblock when
we try to prove that zero is a *right* identity. We don't
have an axiom for that! Rather we'll need to prove it 
as a theorem.
-/
example : ∀ (m : nt), add m zero = m := by simp [add] --fail
/-
def add : nt → nt → nt
| zero m := m
| (succ n') m := succ (add n' m)
-/

-- Prove it!
theorem zero_is_right_zero : ∀ (m : nt), add m zero = m :=
begin
  assume m,
  induction m with m' h,  -- by induction!
  simp [add],
  simp [add],
  exact h,
end
theorem zero_is_left_zero : ∀ (m : nt), add zero m = m :=
begin
  intros,
  induction m with m' h,
  simp [add],
  simp [add],
end

-- NOTATION

/-
A complete, beautiful, and highly usable "module"
that implements an algebraic structure, such as 
Boolean algebra or Peano arithmetic, often needs
to introduce convenient *notations* for applying
operations to arguments. We'd rather write (2 + 3)
than (nat.add zero.succ.succ zero.succ.succ.succ),
for example, even though we understand that they
mean the same thing. 

In Lean, we can overload operators, such as +, 
that are already defined in Lean's libraries, 
and we will thereby inherit both precedence and
associativity properties that were carefully
crafted by the library designers. 
-/

notation x + y := add x y
notation x * y := mul x y

#reduce five + six        -- expect 11 .succs of zero
#reduce five * six + two  -- expect 32 .succs of zero

-- Now we can use these notations in writing expressions
example : five + six = zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ := rfl


-- NOTATION

notation x + y := add x y
notation x * y := mul x y

#reduce one + two * two -- Mult has higher precedence 

-- HOMEWORK
-- PROVE Associativity, Commutivity, Distrubility

theorem succ_is_associative: ∀ (m n : nt), (n + m).succ = n + m.succ :=
begin
  intros,
  induction m with m' h,
  rewrite zero_is_right_zero,
  induction n with n' h2,
  simp [add],
  simp [add],
  apply h2,
  
end


theorem mul_by_zero_is_zero : ∀ (m : nt), mul m zero = zero :=
begin
  intros,
  induction m with m' h,
  simp [mul],
  simp [mul],
  rw h,
  simp [add],
end

theorem mul_by_zero_is_zero_other : ∀ (m : nt), mul zero m = zero :=
begin
  intros,
  induction m with m' h,
  simp [mul, mul],
end

/-
def add : nt → nt → nt
| zero m := m
| (succ n') m := succ (add n' m)
-/
-- https://proofwiki.org/wiki/Natural_Number_Addition_is_Commutative
theorem add_commutes : ∀ (m n : nt), m + n = n + m :=
begin
  intros,
  induction m with m' h,
  simp [add],
  rw zero_is_right_zero,
  simp [add],
  rw h,
  -- What to do?? we have it in the wrong order
end

-- https://proofwiki.org/wiki/Natural_Number_Multiplication_Distributes_over_Addition
theorem mull_distribute : ∀ (m n t : nt), m * (n + t) = (m * n) + (m * t) :=
begin
  intros,
  induction m with m' h1,
  simp [mul],
  simp [add],
  -- 1 goal
  simp [mul],
  simp [h1],
  -- just need to reorder ???
  rw add_commutes,
end

/-
def mul : nt → nt → nt
| zero m := zero
| (succ n') m := add (mul n' m) m 
-/
-- https://proofwiki.org/wiki/Natural_Number_Multiplication_is_Commutative
theorem mul_commutes : ∀ (m n : nt), m * n = n * m :=
begin
  intros,
  induction m with m' h,
  simp [mul],
  rw mul_by_zero_is_zero,
  simp [mul],
  rw h,
  -- now we need to prove multiplication distributes over addition
  -- n*m'+n = n*m'.succ

end

theorem add_associative : ∀ (m n t :nt), m + (n + t) = (m + n) + t :=
begin
  intros,
  induction m with m' h1,
  simp [add],
  induction n with n' h2,
  simp [add],
  rewrite zero_is_right_zero,
  induction t with t' h3,
  simp [add],
  rewrite zero_is_right_zero,
  rewrite zero_is_right_zero,
  simp [add],
  apply h1,
end

theorem mull_associative_basis : ∀ (m n : nt), (m * n) * zero = zero :=
begin
  intros,
  rw mul_by_zero_is_zero,
end

theorem mull_associative : ∀ (m n t :nt), m * (n * t) = (m * n) * t :=
begin
  intros,
  induction t with t' h,
  rw mull_associative_basis,
  rw mul_by_zero_is_zero,
  rw mul_by_zero_is_zero,
  simp [mul],
  
end

end hidden