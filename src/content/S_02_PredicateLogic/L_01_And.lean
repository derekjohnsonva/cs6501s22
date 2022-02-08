/-
In this class, we introduce conjunction,
∧ (and), as connective that combines any
two propositions into a larger one; and
we show how we define the introduction and
elimination rules for this connective *so
that* it behaves in Lean as it behaves in
predicate logic: to prove P ∧ Q we need to
provide proofs of P and of Q, respectively
(the introduction rule), and given a proof
of P ∧ Q, we can *use* it to obtain a proof
of P, and a proof of Q (the left and right
elimination rules for ∧). 

Once we've defined these rules as "axioms" 
then we can use them to prove new theorems
about the properties of the ∧ connective:
that it's *commutative* and *associative*.

That's our agenda.
-/

/-
THE AXIOMS (INTRO & ELIM RULES) FOR ∧.
-/

/-
To get started, let assume that P and Q 
are arbitrary propositions. We'll use the
"axiom" keyword in Lean, which introduces
assumptions into the current environment,
which is here the "global" environment of
this file.
-/
axioms P Q : Prop

/- The syntax of predicate logic dictates that if
P and Q are propositions, then P ∧ Q is one as well. 
For this reason we use the term "connective" for 
logical symbols such as ∧, in that they "connect"
give propositions (P, Q) into larger propositions
(here, P ∧ Q). 

Given thatwe propositions are types in the logic of
Lean, you can also say that ∧ is a "type builder:"
it takes two types as arguments (P, Q) and returns 
a new, type, P ∧ Q, as a result. What is the type of
P ∧ Q? Try to answer yourself before leaning on the
proof assistant (ha ha) to tell you.
-/
#check P ∧ Q

/- 
∧ is just an infix notation for "and", with the
correct precendence to work together correctly 
with the other logical connectives Lean defines,
and with *right* associativity. That means that
Lean will parse P ∧ Q ∧ R as P ∧ (Q ∧ R), not as
(P ∧ Q) ∧ R.
-/
#check and P Q

/-
∧ is a logical "connective." That means
it "connects" (a better word is "composes")
two propositions into a larger proposition. 
Given the propositions are types in Lean, 
∧ is a *polymorphic type building function 
that takes two propositions (types) as its
arguments and yields a proposition (type)
as a result. 

What, then, is the type of "and,"" viewed 
as a function? Try hard to answer yourself
before using Lean to get the answer for you.
-/
#check @and 

/-
Right. ∧ takes two propositions, P and Q, 
and gives us back a new proposition, P ∧ Q,
(which "desugars" to "and P Q").
-/

/-
What we are going to see now is that ∧ is
implemented in Lean as a polymorphic type.
It's implemented as an inductive type that
takes two propositions (types!) as arguments.
These type arguments are the propositions to 
be connected.  

The constructor for this type then defines 
the introduction rule (a way to build proof 
objects) for this new type. 

Finally, the elimination rules allow us to 
use a proof of P ∧ Q to derive proofs of P
and of Q. We'll see later in this file how
to implement these logical rules, again as
functions, in Lean. 
-/

/-
First, though, we want to see exactly where
the and.intro rule comes from. Here's Lean's 
definition of and (∧). What you can see is 
that and.intro is just a constructor of data
values (proofs!) of *type* (and a b), where 
a and b are themselves propositions.

structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)

Constructors are introduction rules! Indeed,
if you look back at the eq polymorphic type,
you will be reminded that eq.refl is just a
(the only) constructor for building terms of
type (@eq α a b), the shorthand notation for
which is a = b. Constructors are introduction
"axioms" for their types.
-/

/-
We now use this example to explore a number
of core concepts in the Lean language. First,
and hew here, is the use of "structure"  as a
keywork. It can be used in place of inductive 
when a type has just exactly one constructor.
The main benefit of using "structure" is that
it tells Lean to *synthesize* functions with
the same names as the fields for *accessing*
the field values in any instances of the type.

It allows the argument names, left and right, 
in this case, to be used as names of functions
to "access" the field values of an object of 
type P ∧ Q. So, if you have an object, pf, of 
type P ∧ Q , then (and.left pf) and (and.right 
pf) give you proofs of P and of Q. For these
function calls you can also use the notation,
pf.left and pf.right. These functions are, of
course, the two elimination rules for and! 
-/

/-
In sum, the "intro" constructor for ∧ 
implements the introduction rule for ∧,
while the Lean-provided accessor functions,
left and right, implement the elimination
rules for ∧: left and right, respectively. 
-/

/-
With these "rules" in hand, we can now
construct proofs of theorems about the
*and* operator, just as we did for eq
(proving symmetry and transitivity) once
we had the intro (refl) and elim (subst)
rules for equality.  
-/

/-
To illustrate, beyond assuming that P and 
Q are propositions (above), we'll now also
assume that we have proofs of P and of Q. 
Remember that the propositions P and Q are 
*types*. What we want now are values of 
these types, which we now understand are
proofs. Heres how we assume "axiomatically" 
that p and q are proofs of P and of Q.respectively.
-/
axioms (p : P) (q : Q)

/-
Given that we're now in a (global) context
in which we have assumed P and Q are in Prop
and that p and q are proofs of P and of Q,  
we can now claim that there must be a proof
of P ∧ Q --- that P ∧ Q is true. Now we can
produce a proof to show that it is true. 
-/
example : P ∧ Q := and.intro p q

/-
Yay. That's how we use the introduction 
rule for ∧ to prove propositions of the
form P ∧ Q (conjunctions).
-/

/-
Here's the equivalent formulation using 
ordinary function definition notation. We
define func (a name we're just making 
up) to be a function that takes P, Q, p, 
and q as arguments and returns a proof of 
P ∧ Q.
-/
def func 
  (P Q : Prop) 
  (p : P) 
  (q : Q) : 
  P ∧ Q :=
and.intro p q

/-
We can also write our own functions that mimic
the elimination rules for and (by "wrapping" 
them in an added layer of abstraction)
-/
def and_elim_left 
  (P Q : Prop) 
  (pq : P ∧ Q) : 
  P 
  :=
and.elim_left pq

/- 
Homework #1: Define an analogous function,
and_elim_right.
-/ 

-- Here.

/-
From a proof of P ∧ Q we can derive a proof 
of P, and we can derive a proof of Q, using 
the elimination rules for ∧:
-/

#check @and.elim_left
#check @and.left 
#check @and.elim_right
#check @and.right


/-
Mental exercise: To what values do the following
expressions evaluate/reduce?

and.elim_left (and.intro p q)
and.elim_right (and.intro p q)
-/
#reduce and.elim_left (and.intro p q)
#reduce and.elim_right (and.intro p q)

/-
and.left : ∀ {a b : Prop}, a ∧ b → a
and.right : ∀ {a b : Prop}, a ∧ b → b

Conceptually, each elimination rules takes
a pair and returns either the first or the
second of its two fields. They are what we 
can call "projection functions."
-/

/-
THEOREM CONCERNING ∧ 
-/

/-
We now have the basic *axioms* for
creating and using proofs of *conjunctions*
(propositions built using ∧). With them we
can state and prove new *theorems* about the
behavior of the ∧ connective. For example,
we can now prove (almost) that it's both
"commutative" and "associative."
-/

/-
Example 1: From a proof of P ∧ Q we can
construct/derive a proof of Q ∧ P. 
-/
theorem and_commutes 
  (P Q : Prop) (pq : P ∧ Q) : Q ∧ P :=
  and.intro 
    (and.right pq)
    (and.left pq)

/-
The idea here is pretty simple. A proof of
P ∧ Q is of the form (and.intro p q), which
you can think of as a labelled order pair of
proofs. (The label is and.intro.) Given such
a proof, we use our elimination functions,
left and right, to extract p and q, then we
use and.intro to put them together again, in
the opposite order, to construct a proof,
(and.intro q p), of Q ∧ P. 

Here's another version of our proof. We use
example to avoid giving it a name. We specify
the same arguments (before the colon) and the
same return type (just after the colon). We
then write the "implementation" (after the :=)
using both angle-bracket and dot notation for
field access. What's new here is the use of 
⟨...⟩ notation. It can be used whenever you
are creating a value of structure (a type
with just one constructor and zero or more
arguments). This angle bracket notation calls
the single constructor with its arguments in
the comma separated list inside the angle
bracket pair. Note that you have to type a
backslash before a less-than or greater-than
keyboard character to get these special angle
brackets.
-/

example (P Q : Prop) (pq : P ∧ Q) : Q ∧ P :=
  ⟨ pq.right, pq.left ⟩ 

/-
At this point, we've now seen the introduction
and elimination "rules" for both = and ∧. The 
introduction rules are eq.refl and and.intro,
while the elimination rules are eq.subst, and
and.left and and.right (aka and.elim_left and
and.elim_right).

/-
Seeing the introduction and elimination
rules for ∀ and →.
-/

We've also seen, implicitly, the introduction
and elimination rules for ∀ and →. The intro
rule says "assume the argument/premise and, in
that context, show that you can construct and
"return" a proof of the conclusion/return type.

To prove P → Q, assume you're given a proof of 
P and in that context show that you can have a
proof of Q. That proves P → Q. Similarly, to
prove ∀ (p : P), Q, assume that you're given
an arbitrary proof/value of P and show that
in that context you can construct a proof/value
of type Q.

In Lean these connectives, ∀ and →, are in fact
essentially just notations for the same idea! To
see that this is the case, look at how Lean prints 
the proposition, ∀ (p : P), Q. It's just P → Q! 
(Recall again that we defined P and Q above.)
-/

#check ∀ (p : P), Q

/-
Homework #2: NFormally state and prove the 
proposition that "∧ is associative." 

Okay, any logic text or web page will tell you
that this statement, "∧ is associative", means
that for any three propositions, P, Q, and R,
if (P ∧ Q) ∧ R is true then P ∧ (Q ∧ R) is too,
and vice versa! We will just state and prove 
the first of these.  
-/

-- theorem and_assoc (partial) ...

-- TOP DOWN
example : ∀ (P Q R), (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) := 
begin
  intros P Q R h,
  apply and.intro 
    (and.intro 
      (and.elim_left h) 
      (h.right.left)
    ) 
    (h.right.right),
end

/-
BOTTOM UP
-/

example : ∀ (P Q R), (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) := 
begin
  intros P Q R h,
  have p : P := h.left,       -- binds identifier, p, to h.left
  have q : Q := h.right.left, -- scoped locally to this tactic script
  have r : R := h.right.right,-- we're building objects to be assembled 
  have pq : P ∧ Q := and.intro p q, -- here's the final assembly
  exact and.intro pq r,       -- exactly the proof term we needed
end

/-
Note that we can move arguments to the left or right of
the colon. When to the left, we give them names. If on the
right, if one or more needs names, then we use ∀ or Π to 
bind names, then a comma, then the rest of the type. In 
this example, we move the ∀ (P Q R : Prop) in the last
example to the left of the colon in this example. In
both cases, the effect is to bind names, P, Q, and R,
to assumed objects which enables us to use those names
in the rest of the expression that specifies the overall
type of the function. 
-/
example (P Q R : Prop) : (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) := 
begin
  intros h,
  have p : P := h.left,
  have q : Q := h.right.left,
  have r : R := h.right.right,
  have pq : P ∧ Q := and.intro p q,
  exact and.intro pq r,
end

namespace hidden

#check and

/-
DEEP DIVE: Now let's take an even deeper
look at how the and elimination rules are 
actually implemented. In short, they are
just functions. The first takes a proof
of P ∧ Q, comprising a pair of proofs,
⟨ p, q ⟩, takes apart this pair, and
returns its first element, p. The and
elimination right rules takes the same
pair, takes it apart, and returns q.

The technical means for doing this kind
of taking apart, or "analysis", of an
object is by "pattern matching." (There
is an even deeper level involving what
Lean calls recursors, but we can't go
there yet.)
-/

/-
To begin, recall Lean's actual definition
of and (∧).

structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)

Let's go ahead an implement this ourselves
to make the details clear. The first point
is that we could have used inductive instead 
of structure. The following definition is
equivalent to Leans (almost).
-/

inductive and (P Q : Prop) : Prop
| intro (p : P) (q : Q) : and 

#check and
#check and P Q

/-
What about that almost? The definition 
above is logically equivalent to Lean's,
but if we use inductive, we have to write
our own "accessor functions" to get at 
the fields of a proof of P ∧ Q.
-/

def elim_left : (and P Q) → P
| (and.intro x y) := x  -- pattern matching

/-
After the type signature, (and P Q) → P,
we give a list of cases, typically one per
constructor for the type of the argument,
(and P Q). For ∧, there is only one case
to consider: a proof ⟨ p, q ⟩ of P ∧ Q can
*only* have been constructed by applying
and.intro to two arguments, here we give
them arbitrary names, x and y; and what
pattern matching does is to match the term
we're given as an argument, (and.intro p q) 
with the pattern (and.intro x y), *unifying*
x with p and y with q. That is, if there's 
a match, then x becomes bound to p and y
becomes bound to q. In this way, we get at
the fields of the object we were given and
we give the field values names, *so that 
we can refer to these objects using these
names in the expression to the right of the
:=, which gives the value that the function
returns "in this case." A little further 
on, we'll see examples of case analysis
of objects of types with several constructors.
-/

def elim_right : (and P Q) → Q
| (and.intro x y) := y


/-
To see that our functions appear to be doing
the right thing, let's assume h is bound to a
proof of and P Q (using our definition of and),
and then see that our elim_left and elim_right
functions are returning values of the right
types, namely proofs of P and Q, respectively.

-/
axiom h : and P Q
#check elim_left h
#check elim_right h

/-
We can't really expect to use reduce here
because h is assumed as an axiom, without
specified field values. What happens if you
try to reduce, say, (elim_left h)? The answer
is that such terms are of the right types 
but simply will not reduce any further.
-/
#reduce elim_left h
#reduce elim_right h

/-
BASIC ABSTRACT DATA TYPES
-/ 

/-
An abstract data type associates a type of
object with a set of fundamental operations
on values of that type.
-/
namespace a
theorem and_assoc: ∀ (P Q R : Prop), (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) := 
begin
  intros P Q R h,
  exact ⟨⟨h.left, h.right.left⟩ , h.right.right⟩ 
end

theorem and_assoc': ∀ (P Q R : Prop), (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) := 
begin
  intros P Q R h,
  apply and.intro (_) (_),
  exact and.intro h.left h.right.left,
  exact h.right.right,
end

example : ∀ (P Q R : Prop), (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) := 
begin
  intros P Q R h,
  have p : P := h.left,
  have q : Q := h.right.left,
  have r : R := h.right.right,
  exact ⟨⟨p, q⟩, r ⟩,
end


/-
Consider the Boolean type, bool, in Lean. Here
is how it's defined. It's a simple enumerated
type, with just two constant values, ff and tt.

inductive bool : Type
| ff : bool
| tt : bool
-/

/-
Now that we've defined our inductive data type,
we define fundamental operations on values of 
this type, and the combination of the type and
this set of operations constitutes an abstract
data type, rudimentary but complete.

Here's an example of a function that operates
on values of type bool: negate. It takes a bool
value and returns one. It's interesting aspect
is that it has to analyze the argument value to
which it is applied in order to decice which of
two possible return values to actually return.
-/

def negate : bool → bool
| ff := tt  -- if argument is ff reduce to tt
| tt := ff  -- if argument is tt reduce to ff

-- here are a few test cases
example : negate tt = ff := rfl
example : negate ff = tt := rfl

/-
We discussed the option type. It has at least
three interesting features: it's polymorphic
(in α); it has *two* constructors; and one of 
them takes as an argument a value of type α.

inductive option (α : Type u)
| none : option
| some (val : α) : option
-/

/-
Here's the standard definition of the nat 
type in Lean. There are two shapes that a
given nat can have: it is either zero or
it is succ applied to another term of type
nat, we could call it n. And in this second
case, n, being just some nat, could also
be either zero or succ of an even "smaller"
nat. What is guaranteed by the semantics
of inductive definitions is that one will
eventually reach zero after some finite, even
if large. number of steps.

inductive nat
| zero : nat
| succ (n : nat) : nat
-/

/-
We can now put a few pieces together into a 
working example. We represent a partial function
from natural numbers to natural numbers as a
total function (all functions in Lean are total)
from nat to option nat. A value of type otion
nat, in turn, is either "none" or "some a." If
the value of the mathematical function on some
argument, a, is defined, and has value b, then 
our total function would return (some b). In 
the case where the mathematical function is 
*undefined*, e.g., at zero, then our total
function applied to that view would return
option.none.

Let part_fun be a partial function of type
ℕ to ℕ, and suppose that at every value n
it's defined to have the value n, except at
zero, at which part_fun is simply undefined.
Here's a standard solution using an option 
return type.
-/
def posnat : nat → option nat 
/-
Case analysis using pattern matching 
on argument. For an argument of type
nat, there are two basis cases: it's
either zero or it's the successor of
some smaller nat.
-/
| nat.zero := none
| n := n

#reduce posnat 5
#reduce posnat 4
#reduce posnat 3
#reduce posnat 2
#reduce posnat 1
#reduce posnat 0

end hidden 

/-
To finish up, we started to compare and
contrast the definitions in Lean of = and
of ∧. We've now seen that we implement each
as a parameterized family of propositions. 
-/

#check @eq
/-
eq : Π {α : Sort u_1}, α → α → PropLean
-/

#check @and
/-
and : Prop → Prop → Prop
-/

/-
Finally, and very briefly, the ↔ operator (if and only if,
often written as iff): it's like a special case of and, in
that it has one intro rule, and it takes two arguments, but
now they are of type P → Q and Q → P. And with analogy with
and, iff has two elimination rules, so if h is a proof of
P ↔ Q, then h.left is a proof of P → Q, and h.right is a 
proof of Q → P.
-/

/-
For example, suppose h is a proof of P ↔ Q
-/
axiom h : P ↔ Q

/-
Now we can see that the elimination rules work
as one should expect.
-/
#check iff.elim_left h
#check iff.mp h   -- weird names but whatever

#check iff.elim_right h
#check iff.mpr h  -- weird names but whatever

/-
Similarly, if we have proofs of P → Q and of
Q → P, then we can compose them into a proof
of P ↔ Q using iff.intro.
-/

axioms (pq : P → Q) (qp : Q → P)
#check iff.intro pq qp

/-
Can you guess how iff is defined in Lean's libraries?
-/

#print iff

/-
`iff P Q`, with notation `P ↔ Q`, is the proposition 
asserting that `P` and `Q` are equivalent, that is, 
that they have the same truth value.

structure iff (a b : Prop) : Prop :=
intro :: (mp : a → b) (mpr : b → a)
-/

/-
Example: ∧ is associative
-/

example : ∀ ( P Q R : Prop), P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
begin
  intros P Q R,
  split,    -- does apply iff.intro _ _

  -- forward
  sorry,   -- skip proof, fill in later

  -- reverse 
  sorry,   -- skip proof, fill in later
end

/-
Example: P ∧ (P ↔ Q) → Q
-/

example : P ∧ (P ↔ Q) → Q :=
begin
  assume h,
  cases h,
  cases h_right,
  exact h_right_mp h_left,
end

/-
The cases tactic does case analysis
on a value in the context, here h.
For each possible way in which h
could have been constructed, you'll
need to show that you can satisfy 
the goal. In each case, Lean will 
also provide values of the arguments
that that case's constructor would
have to have been given in that case.

Here there is just one constructor,
and.intro, with two arguments, a proof
of P and a proof of P ↔ Q. So in the
case being analyzed, we can assume
we have such values. The rest is 
straightforward.
-/