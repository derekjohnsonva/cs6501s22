import .bool

namespace hidden 

-- DATA TYPE

inductive bool_lang : Type
| TT : bool_lang
| FF : bool_lang
-- | var (v : bool_var) : bool_lang
| conj (e1 e2 : bool_lang) : bool_lang
| disj (e1 e2 : bool_lang) : bool_lang
| neg (e : bool_lang)


-- REFACTOR INTO TEST FILE
open bool_lang
def be1 := TT
def be2 := FF
def be3 := conj be1 be2
def be4 := neg be3

open boo

-- OPERATIONS
def eval : bool_lang → boo
| TT := tt
| FF := ff
-- | (var v) i := i v
| (conj e1 e2) := and (eval e1) (eval e2)
| (disj e1 e2) := or (eval e1) (eval e2)
| (neg e) := not (eval e)

-- NOTATIONS
notation b1 * b2 := conj b1 b2
notation b1 + b2 := disj b1 b2
prefix ! := neg

-- REFACTOR INTO TEST FILE
#reduce eval be4
#reduce eval (conj (disj be2 be4) be3)
#reduce eval ((be2 + be4) * be3)

/-
How do we know that eval terminates?
-/

/- 
We must we insist that functions always 
terminate. The following example shows if 
we accept functions that infinitely loop,
then our logic is inconsistent insofar
as we can then have a proof of false. We
cannot have a proof of false in our logic,
so we cannot admit functions that are not
known the terminate.
-/

-- Non-terminating functions would be fatal
def bad : ℕ → false
| n := bad n    -- see this error message
#check (bad 3)  -- Yikes, a proof of false!


-- PROPERTIES?

/-
A property of an expression, e, is that e
evaluates to true. Let's call this property
evaluates_to_true.
-/
def evaluates_to_true : bool_lang → Prop 
| e := eval e = boo.tt
/-
This definition broke when we added an interpretation,
i, as a second argument to eval.
-/

example : evaluates_to_true TT :=
begin
  unfold evaluates_to_true,
  trivial,
end
--ditto last comment

/-
Let's assert that TT*FF evaluates to
true. We won't be able to prove it.
-/
example : evaluates_to_true (TT * FF) :=
begin
  unfold evaluates_to_true,
  simp [eval],
  apply rfl,  -- it's just not true!
end
--ditto last comment

-- This time our proof will go through
example : evaluates_to_true (TT * TT) :=
begin
  unfold evaluates_to_true,
  simp [eval],
  apply rfl,  -- false
end
--ditto last comment

/-
The take-away concept from the preceding
examples is that we can formalize the 
a *property* of an expression in a given
language (here our bool_lang language).
-/


/-
We can also formalize properties of a
language as a whole. The example we'll 
use here is that we can state and prove
the proposition that semantic evaluation
in bool_lang is deterministic. If we
evaluate the meaning of an expression 
twice, we should always get the same
answer.  
-/
-- Property of the language as a whole: 
-- evaluation is deterministic.

-- HOMEWORK

/-
What deterministic means is that if you evaluate the same
expression twice (in the same environment) that you'll get
the same answer. A language with a statement that returns 
a truly random number wouldn't have this property. Show that
evaluation is deterministic for our "Bool" language.
-/

def eval_is_deterministic : 
  ∀ (e : bool_lang) (b1 b2 : boo), 
  b1 = (eval e) → 
  b2 = (eval e) → 
  b1 = b2 := 
begin
  intros e b1 b2 h1 h2,
  rw h1,
  rw h2,
end

-- What is the type of eval_is_deterministic
#check @eval_is_deterministic

end hidden