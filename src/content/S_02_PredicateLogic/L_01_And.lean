-- Let assume P and Q are propositions
axioms P Q : Prop

-- Then P ∧ Q is also a proposition 
#check P ∧ Q

-- And ∧ is just notation for "and"
#check and P Q

#check @and 

/-
∧ is a logical "connective." That means
it "connects" two propositions into one
larger proposition. Given the propositions
are types in our logic, and is basically
a polymorphic type builder that takes two
propositional types as arguments and yields
one as a result.

and : Prop → Prop → Prop
-/

/-
Here's Lean's definition of and (∧):

structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)

New here is the use of "structure." This 
keyword can be used in place of "inductive" 
when a type has exactly one constructor. 
It allows the argument names to be used as
functions to "access" the field values of
an object of a given type. So now, if you
have an object, pf, of type P ∧ Q, you can
write (and.left pf) or (and.right pf) to 
obtain the constituent proofs. The and.elim
"rules" are just another way to use these
accessor functions.


So the constructor defines the introduction
rule for ∧, namely and.intro (a way to build
a proof of P ∧ Q for arbitary propositions P
and Q). The field accessors functions provide 
the elimination rules for ∧: and.left and 
and.right, respectively. 
-/

/-
To see what we can do with our new "rules"
let's assume that we now also have proofs
of P and of Q. Remembers the propositions
are the *types* P and Q, and for proofs we
want values of these types. So let's assume
"axiomatically" that (little) p and q are 
proofs of P and Q, respectively.
-/
axioms (p : P) (q : Q)

/-
Give that we're now in a (global) context
in which we have assumed P and Q are in Prop
and that p and q are proofs of them, we can
claim and provide a proof of P ∧ Q. Here it
is.
-/
example : P ∧ Q := 
  and.intro p q

/-
Here's the equivalent formulation using 
ordinary function definition notation. We
define func to be a function that takes P,
Q, p, and q as arguments and that returns
a proof of P ∧ Q.
-/
def func 
  (P Q : Prop) 
  (p : P) 
  (q : Q) : 
  P ∧ Q :=
and.intro p q

/-
We can also write our own functions that
simply call and.left and and.right in turn.
-/
def and_elim_left 
  (P Q : Prop) 
  (pq : P ∧ Q) : 
  P 
  :=
and.elim_left pq

/-
From a proof of P ∧ Q we can derive a proof 
of P, and we can derive a proof of Q, using 
the elimination rules for ∧:

and.elim_left
and.elim_right
-/

#check @and.elim_left
#check @and.left 
#check @and.elim_right
#check @and.right

/-
and.left : ∀ {a b : Prop}, a ∧ b → a
and.right : ∀ {a b : Prop}, a ∧ b → b
-/

/-
So, yay! We now have the basic *axioms* for
creating and using proofs of *conjunctions*
(propositions built using ∧). With them we
can state and prove new *theorems* about the
behavior of the ∧ connective. For example,
it's "commutative": whenever we have a proof
of P ∧ Q we can derive a proof of Q and P!
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
⟨ q, p ⟩ of Q ∧ P. Yes, we just used a new
notation.

Here's another version of our proof. We use
example to avoid giving it a name. We specify
the same arguments (before the colon) and the
same return type (just after the colon). We
then write the "implementation" (after the :=)
using both angle-bracket and dot notation for
field access. Use \< and \> to get the angle
brackets in the VSCode Lean IDE.
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

We've also seen, implicitly, the introduction
and elimination rules for ∀ and →. The intro
rule says "assume the argument/premise and in
that context, show that you can construct and
"return" a proof of the conclusion/return type.
To prove P → Q, assume you're given a proof of 
P and in that context show that you can have a
proof of Q. That proves P → Q. Similarly, to
prove ∀ (p : P), Q, assume that you're given
a proof of P and show that you can construct
a proof of Q.

Do they sound similar? Yes, indeed. In Lean
these connectives are in fact essentially 
just different notations for the same idea!
Look at how Lean prints ∀ (p : P), Q. It's
just P → Q! (Recall we defined P and Q above.)
-/

#check ∀ (p : P), Q

/-
Homework: Formally state and prove the 
proposition that "∧ is associative" by
uncommenting and completing the following
definition.
-/

-- theorem and_assoc ...

