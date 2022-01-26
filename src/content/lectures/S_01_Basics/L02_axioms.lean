/-
Axioms and theorems. 

An axiom is a logical proposition that one 
accepts as true. In our logic this means that
one accepts there is a proof of it, even if
one doesn't have such a proof in hand. When
we assume that a proposition is true, we do
so by assuming that there is a proof of it.  

In classical logic, an "inference rule" is a 
procedure for deriving the *truth* of one 
proposition from the truths of others. As an
example, if we've assumed that the propositions,
x = y and y = z, are true, then we can apply the
inference rule (actually a theorem, in this case, 
rather than axiom) that expresses that equality is 
a transitive relation to deduce the truth of x = z.
The "rule" basicall states, x = y → y = z → x = z.

But in our "software" logic, an inference 
rule is not just a reasoning principle for
deriving new truths from old truths, it is 
a program for deriving new proofs from old
proofs (and perhaps other values). 

So old paper & pencil logic now becomes an
exercise in "programming." But it's of a kind 
that you have not likely seen before, for now
we will be programming not only with data tyoes
and values with with propositions (logical types)
and proofs (values of these logical types).
-/

/-
In this file, we give formal statements (our 
version) of the two basic axioms of equality
as a relation on any given type of object.  We 
then present Lean's versions of these rules.
By the end of this unit, you'll be programming
with propositions and proofs.
-/

/-
INFERENCE RULE #1/2: EQUALITY IS REFLEXIVE

Everything is equal to itself. A bit more formally,
if you can given a type, T, and a value, t, of this
type, then you may apply the reflexivity axiom to
construct and return a proof of (a value/term of the 
type) t = t.
-/

axiom eq_refl  : 
  ∀ (T : Type)  -- for any type of thing, T 
    (t : T),    -- and for any value, t, of that type
  t = t         -- there is a proof of type t = t

/-
This "axiom" is in the form of a proof building
function. Now that you've assumed it, you can use
it to construct terms of type t = t, for any t of
any given type, T.
-/

#check eq_refl nat 2

/-
Lean responds with this: eq_refl ℕ 2 : 2 = 2. What
it's saying is that type of the term, (eq_refl ℕ 2),
is 2 = 2. In other words, the term eq_refl ℕ 2) *is*
a proof of 2 = 2. 
-/

/-
INFERENCE RULE #2/2: SUBSTITUTION OF EQUALS FOR EQUALS

Given any type, T, of objects, and any *property*, P,
of objects of this type, if you know that x = y and 
you know that x has property P (this proposition is
written as P x), then you can deduce y has property P,
i.e., P y.
-/
axiom eq_subst : 
  ∀ (T : Type)      -- if T is any type
    (P : T → Prop)  -- and P is any property of T objects
    (x y : T)       -- and x and y are T objects
    (e : x = y)     -- and you have a proof that x = y
    (px : P x),     -- and you have a proof that x has property P
  P y               -- then you can deduce (and get a proof) that P y

/-
The Lean versions of these axioms are called eq.refl and 
eq.subst. They're defined in ways that allow (and require) one 
not to give the T, P, x, or y parameters explicitly. This is a
convenience for the user, as values of these parameters can
always be inferred from the remaining explicit arguments. Here 
are Lean's library-provided axioms for equality. Notice that
unlike our axioms, these generalize to any "universe level."
-/

#check @eq.refl
#check @eq.subst

-- Example using eq.refl: (terms encoding) proof of 2 = 2
#check eq.refl 2       -- remember that ℕ is inferred
#check @eq.refl nat 2  -- to state it explicitly, use @

/-
Example using eq.subst.

We can use the "axiom" command in Lean to introduce
arbitrary assumptions into the global environment of
definitions within which we're working here. So let's
do that to assume that we have the arguments needed 
to apply eq.subst.

∀ {α : Sort u_1} {P : α → Prop} {a b : α}, a = b → P a → P b
-/

universe u
axioms 
  (α_type : Sort u)           -- α_type is some type
  (beautiful : α_type → Prop) -- beautiful is a property of α_type
  (a b : α_type)              -- a and b are objects of α_type
  (h_eq : a = b)              -- h_eq is a proof of (a value of type) a = b
  (h_beaut : beautiful a)     -- h_beaut is a proof that a is beautiful

def bb : beautiful b := eq.subst h_eq h_beaut
#check bb
/-
Note that the first four argument values are implicit and inferred.
{α : Sort u_1} 
{P : α → Prop} 
{a b : α}

Self quiz: What is the type of bb? Answer yourself before checking.
-/

def func 
  (α_type : Sort u)           -- α_type is some type
  (beautiful : α_type → Prop) -- beautiful is a property of α_type
  (a b : α_type)              -- a and b are objects of α_type
  (h_eq : a = b)              -- h_eq is a proof of (a value of type) a = b
  (h_beaut : beautiful a) : 
  beautiful b :=
  eq.subst h_eq h_beaut 

#check bb

def func
  (α_type : Sort u)           
  (beautiful : α_type → Prop) 
  (a b : α_type)              
  (h_eq : a = b)              
  (h_beaut : beautiful a) :
  beautiful b :=
  eq.subst h_eq h_beaut
