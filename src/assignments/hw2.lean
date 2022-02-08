/-
The purpose of this assignment is to develop
and deepen your understanding of the concepts
we've covered so far: equality of values/terms 
of any type, and conjunction of propositions.
-/

/-
Compare and contrast the distinct ways that 
we represented these ideas in Lean.

- inductive eq  { α : Sort u }, α → α → Prop
- inductive and (α β : Prop) : Prop 

Each of "eq" and and builds "propositions", 
but they build them in different ways. 

For any given type, eq takes two *values* of
that type, yields a proposition "about" those
values, and provides constructors that define
the only possible proofs of a proposition of
this kind. 

By contrast, "and" takes two propositions, i.e., 
*types, not values*, as its arguments, reduces to
another proposition as a result, namely (and P Q), 
also written P ∧ Q, and also provide a constructor
(introduction axiom) for building proofs of this
type. 

Popping into the everyday language of programming
languages, we can say that "and" is a polymorphic
type; but, by contrast eq, defines a family of binary
(equality) relations *indexed by an arbitrary type*,
α. There's thus a separate binary equality relation
on terms for each distinct type, (α : Sort u).  
-/

/-
Ex 1: Embed the concept of the logical or (∨)
connective into Lean in the same style we used
to embed ∧. To do this we'll need to talk about
the introduction and elimination rules for or.
-/

namespace hidden



end hidden

/-
#2. Let's using an inductive family to 
specify the successor relationship between
pairs of natural numbers. For any natural
numbers, n and m, (n, m) ∈ succ_rel if and
only if m = n + 1. Once you've done this,
state and prove the lemma, (0,1) ∈ succ_rel.
-/

#check and