import data.real.basic


/-
Q: Are there different types of numbers?
A: There are: both of numbers, per se, and of operations on them.

Q: Are there ways of representing them  - these numbers and operations?
A: There are.

Q: Can you provide an overview and a deeper dive into one especially 
important example?
A: Sure. Let's go.
-/

/-
NUMBER SYSTEMS

Mathematicians think about operations on many kinds of objects.
In early mathematics, the objects are numbers. In later maths,
they can be polynomials, matrices, functions, symmetries, or any
manner of other "mathematical things". 

[Later: As we're going to see, in some logics, they can represent 
propositions and proofs, with which one can then compute. The name,
automated reasoning, is sometimes used to refer to computations that
in effect compute with propositions and proofs of them in addition
to computing with "usual" numerical and other data types.

Q: Can you review what you mean by "the 'usual' data types?"
A: We can. Let's limit ourselves for now to numberical data types.


As you might have learned in high school, there are different types
of numbers. They include the natural numbers (the whole numbers from 
zero up), the integers (negative, zero, and positive whole numbers), 
the rational numbers (ratios of integers), real numbers (requiring
more complex representations), complex numbers (pairs of real numbers
with associating operations for adding and multiplying these pairs),
and so forth. 

Here we review a few 
of the most familiar numerical types and notations for referring
to the sets of values that these types comprise.

ℕ: Natural numbers. The non-negative whole numbers. {0, 1, 2, ...}
ℤ: Integers: The negative, zero, and positive whole numbers. 
ℚ: Rationals: A natural number numerator and non-zero integer denominator.
ℝ: Reals: Equivalence classes of convergent sequence of rationals.
-/


/-
The following examples illustrates the use of these types in
Lean. We give definitions to the identifiers, n, z,, q, and r.
Each gets a value, "1", but these values are of different types: 
natural number, integer, rational, and real, respectively. 
-/
def n : ℕ := 1   -- 1 taken as a natural number
def z : ℤ := 1    -- 1 taken as an integer
def q : ℚ := 1/1  -- 1 as a rational number 
def r : ℝ := 1.0  -- 1 taken as a real number 

/-
We can also ask Lean to tell us the type of the value bound to
each of these identifiers using the #check command.
-/
#check n
#check z
#check q
#check r

/-
We can also reduce any given identifier to the value to 
which it is bound, using the #reduce command in Lean. 
-/

#reduce n
#reduce z
#reduce q

/-
At 
least we can try. Real numbers in both mathematics and 
therefore in Lean are represented by ("equivalence classes"
of) infinite sequences of rational numbers that "converge"
to some point. They cannot be used in computations. They
cannot be printed out. If you uncomment the fourth line in
what follows, Lean will get itself into a state in which 
it's trying (indicated by an orange line in the VS Code
IDE) but not making any progress.
-/
--#reduce r

/-
But let's start with something really simple. The number, 1. Ok,
it's actually not that simple, because 1 can be interpreted as 
denoting a natural number, integer, real number, rational number,
identity matrix, identity function, identity element of a group,
or any manner (again) of "mathematical thingy". If Lean sees a 
bare numeral, 1, it interprets it as the natural number, 1. It
is possible to force many other interpretations however, as the
following examples show.

As you read the code, remember the following.

Examples:

Natural numbers:  0, 3, 11, 29
Integers:         -29, 0, 3, 11
Rationals:        1/2, -3/4, 23/7
Reals:            0.000..., .333..., 3.1415...
Irrationals:      3.1415..., e, sqrt 2
-/

/-
Each proceeding line of code has the following elements
- def: a keyword, binds the given identifer to the given value
- n, m, z, r, q: identifiers, a.k.a., variables or variable names
- : T, where T is ℕ, ℤ, ℝ, or ℚ: specifies the *type* of the value
- := 1.0: specifies the value, 1.0, to be bound to the identifier 
-/

/-
The same definitions could be written as follows, allowing Lean
to fill in type information that it can infer from the way in
which the values are given.
-/

def m' := 1           -- Lean assumes 1 is a natural number (built into Lean)
def n' := (1 : ℕ)     -- 1 as a natural number (non-negative whole number)
def z' := (1 : ℤ)     -- 1 as an integer (negative or non-negative whole number)
def r' := (1.0 : ℝ)   -- 1 as a real number (infinite decimal sequence)
def q' := 1/1         -- Here Lean infers 1/1 is rational number (fraction)

/-
We've now seen literal terms, such as (1 : ℕ) as well
as "identifier terms," such as m'. Let's talk about how
to * such terms. 

(1) Evaluating a literal terms yields the term (value) itself
-/
#reduce (1: ℕ)
/-
Evaluating an identifier term return the term (value) to
which the identifier is bound.
-/
#reduce m'

/-
We also have "function application" terms, in which a
function is applied to an argument of the type that it
is defined to take. Consider, for example, the function,
nat.pred (the "predecessor" function define in the "nat"
namespace). Here we can see that an application term 
in which this function is applied to an argument term
of type nat is itself of type nat.
-/

#check nat.pred m'    -- Lean likes the notation m'.pred

/-
Not that we write an application term as a function name
then a space then its argument -- no parentheses enclose
the argument (list).
-/

/-
Next, to evaluate a an application term, you first 
evaluate the argument term, then you replace every
occurrence of the formal parameter in the "body" of
the function with this value, then you evaluate that
expression and return its result, or "reduced" form. 
-/

#reduce nat.pred m'

/-
In summary, we've seen literal, identifier, and 
application terms. And in Lean and similar proof
assistants, types are also terms (values) and can
be passed as arguments, named as values, returns
as results, etc.
-/

#check nat
def x := nat
#reduce x

/-
But if types are values, and the type of nat is Type
(aka Type 0 or Sort 1), then what is the type of Type?
-/

#check Type
#check Type 1
#check Type 2
-- etc

-- Here are your computational types by another name
#check Sort 1
#check Sort 2

-- Finally, Sort 0 is the type of logical types, or "propositions!"
