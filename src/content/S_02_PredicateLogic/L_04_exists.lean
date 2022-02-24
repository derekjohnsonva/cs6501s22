/-
Today we cover three issues. (1) We start 
by completing our discussion of negation. 
We compare its behavior in Boolean algebra
and classical predicate logic with its 
behavior in constructive logic. To get at
this difference we prove one of DeMorgan's
laws, first in Boolean algebra by (nested)
case analysis, then in Boolean algebra by
applying the induction axiom for the bool
data type, then in the constructive logic
of Lean, where we find we get stuck unless
we're willing to accept the axiom of the
excluded middle, which enables us to do a
nested case analysis on non-constructive
proofs of two arbitrary propositions. We
will also see that only one direction of
this proof (of a bi-implication) requires
classical reasoning.

Second, we will introduce and see a few 
examples of applications of the introduction
and elimination rules for ∃ (existential
quantification).

Finally, we will start to look at induction
in a little more depth and generality. 
-/


/-
First, a proof of one of the DeMorgan laws, 
for Boolean algebra. What we'll see is that
case analysis is all we really need to do to
construct a proof.
-/
-- proof by case analysis
theorem demorgan_1 : 
  ∀ (b1 b2 : bool), 
    bnot (b1  &&  b2) = 
    (bnot b1) || (bnot b2) :=
  begin 
    intros,
    cases b1,

    -- case 1 for b1
    cases b2,
      -- case 1 for b2
      exact rfl,
      -- case 2 for b2
      exact rfl,

    -- case 2 for b1
    cases b2,
      -- case 1 for b2
      exact rfl,
      -- case 2 for b2
      exact rfl, 
  end


/-
Now let's look at doing a proof of the
same proposition "by induction," which is
to say by application of the induction
axiom for the bool data type. What we'll
see is that this principle is equivalent
to case analysis.
-/

#check @bool.rec_on

/-
bool.rec_on : 
Π {motive : bool → Sort u_1} 
  (n : bool), 
  motive ff → 
  motive tt → 
  motive n

In English: If we want to show "motive n" 
(that an arbitrary bool n has some "motive"
property, which is to say that *all* bool
values have this property), it suffices to
show that tt has this property and that ff
has it too. 
-/

example : 
  ∀ (b1 b2 : bool), 
    bnot (b1 && b2) = 
    (bnot b1) || (bnot b2) :=
begin
  intros,
  
  apply bool.rec_on b1, -- induction/recursion on b1
    -- b1 = ff
    apply bool.rec_on b2, 
      -- b2 = ff
      exact rfl,
      -- b2 = tt
      exact rfl,
    -- b1 = tt
    apply bool.rec_on b2,
      -- b2 = ff
      exact rfl,
      -- b2 = tt
      exact rfl,
end


/-
rec.on is the induction principle for 
any value of a given data type. So, as
we've seen here, bool.rec_on is the (or
one of the forms of induction principle)
for the bool type in Lean. What you now
see is that a "proof by induction" is
really just a proof step involvin the
application of an induction principle,
usually leaving the arguments (a base
value/proof and an inductive step value/
proof) to be provided as solutions to
subgoals. 
-/

example : 
  ∀ (b1 b2 : bool), 
    bnot (b1 && b2) = 
    (bnot b1) || (bnot b2) :=
begin
  intros,
  induction b1,
  induction b2,
  exact rfl,
  exact rfl,
  induction b2,
  exact rfl,
  exact rfl,
end

/-
Ok, so we've seen that this DeMorgan's 
law is a theorem in Boolean algebra, or,
equivalently in *propositional* logic.
But what about in predicate logic, where
we're dealing not with Boolean truth 
values and compositions of Boolean
functions, but with truth judgments
for propositions in predicate logic.
Let's state the theorem in predicate
logic and see if it's valid.
-/
example : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
intros,
split,
-- forward direction 
assume h,
-- without classical reasoning we are *stuck*
-- em lets us do case analysis on any *proposition* 
have pnp := classical.em P,
have qnq := classical.em Q,
cases pnp,
cases qnq,
have pq := and.intro pnp qnq,
have f := h pq,
contradiction,
exact or.inr qnq,
exact or.inl pnp,
-- reverse direction -- is constructively valid
assume h,
cases h,
assume k,
cases k,
contradiction,
assume k,
cases k,
contradiction,
end

/-
A takeaway message here is that one of the
directions of this DeMorgan law is not valid
(it is not a theorem) in constructive logic,
even though it is in classical predicate logic.
-/

/-
Next, we introduce the axioms for reasoning
about existentials: for proving propositions
of the form, ∃ (t : T), P (exists.intro) and
for using proofs of this form (exists.elim).
-/

/-
Our examples will use natural numbers, and
here, again is our favorite simple definition
of "property" of natural numbers: evenness.
-/
def ev (n : ℕ) := n%2 = 0

/-
As a first example, we claim then prove that
there exists *some* even number. To do this
we have to apply exists.intro to two arguments:
a specific natural number, n, along with a 
proof that that specific n has the property 
in question. 
-/
example : ∃ (n : ℕ), ev n :=
begin
  apply exists.intro 0, -- apply it to first argument (your witness)
  unfold ev,            -- construct second argument interactively 
  exact rfl,
end 

/-
There's nothing special about 0 beyond the
fact that it's even. We could give a different
proof of the same proposition using a different
witness. Any witness for which a proof of its
evenness can be given will do.
-/
example : ∃ (n : ℕ), ev n :=
begin
  apply exists.intro 2,
  exact rfl,
end 

/-
Here's a not great example, but it works.
The idea we illustrate here is that if we
*have* a proof of an exists, we can obtain
a witness and proof for that witness, and
we can then use those elements in building
a proof of another existentially quantified
proposition.
-/
example : (∃ (n : ℕ), ev n) → (exists l, ev (l + 2)) :=
begin
  assume h,
  cases h with w k,
  apply exists.intro (w),
  unfold ev at k,
  unfold ev,
  simp,
  assumption,
end

/-
In this proof we really do have to use
(by exists.elim, as applied by the cases
tactic) the assumed proof of the premise
in order to obtain the witness and proof
that are required to prove the conclusion.
-/
example (h k : ℕ → Prop) : 
  (∃ (n : ℕ), (h n) ∧ (k n)) →
  (∃ (n : ℕ), (h n)) :=
begin
  assume a,
  cases a with w p,
  cases p with wh wk,
  exact exists.intro w wh,
end

/-
That concludes our introduction to the existential
quantifer and its rules of reasoning in predicate
logic, whether classical first-order predicate logic
or the higher-order constructive logic of Lean.
-/

/-
Now we just broad the subject of "proofs by induction"
as a much more general idea. We've seen the induction 
principle for bool. Check out the corresponding rules
for unit and the empty type. For the rest of this file
we'll focus on induction on a natural number value.
-/

#check @nat.rec_on

/-
Π {motive : ℕ → Sort u_1} 
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n

  Read it like this: for any property,
  "motive," of natural numbers, to show
  that *any* (arbitrary) natural number,
  n, has this property, it suffices to
  show two things: (1) there is a proof
  that 0 has the property; (2) there is
  a proof that *if* you have any n and a
  proof for n (that n has the property)
  then you can construct a proof for n+1.
-/

/-
To be continued next time!
-/
