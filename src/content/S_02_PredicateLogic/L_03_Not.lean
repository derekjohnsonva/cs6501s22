/-
If P is a proposition then so is ¬P.
-/

axiom excl_middle : ∀ (P : Prop), P ∨ ¬ P

axiom KevinIsFromCville : Prop

example : KevinIsFromCville ∨ ¬ KevinIsFromCville :=
excl_middle KevinIsFromCville

/-
To construct a proof of Π for some proposition P,
we need to show that there can be no proof of P.
To show there can be no proof of P we assume that
there is a proof of P and show that this leads to
a contradition.

What do we mean by a contradiction.
-/

#check false

namespace hidden

def not (P : Prop) : Prop := P → false 

end hidden

#check not

example : ¬ 0 = 1 := 
begin
  show not (0 = 1),
  -- the result of this application
  -- is the proposition (0=1) → false.
  assume h,
  cases h,
end

example : false → KevinIsFromCville :=
begin
  assume f,
  cases f,
end

/-
For any proposition at all, if false is
true then that proposition, P, is true. 
One way to understand this is that if false
is true, then anything is true, because if
it's true, it's true, and if it's false it's
also true.
-/
theorem exfalso : ∀ (P : Prop), false → P :=
begin
  intro P,
  assume f,
  cases f,
end

theorem non_contradition : ∀ (P : Prop), ¬ (P ∧ ¬P) :=
begin 
  intro P,
  assume h,
  cases h with p np,
  have f := _,
end

/-
Is the following proposition valid in Lean
-/

example : ∀ (P : Prop), ¬ ¬ P → P :=
begin
  intro P,
  assume h,
  -- no use of classical reasoning allowed.
  -- stuck! this is not a theorem in
  -- the constructive logic of Lean
  -- or Coq, or ...
end

#check classical.em

/-
∀ (p : Prop), p ∨ ¬p
-/

example : ∀ (P : Prop), ¬¬ P → P :=
begin
  intro P,
  assume h,
  /-
  At this point we're stuck! All we
  have to work with is our assumed
  proof of ¬¬P, but all that tells 
  us is that *if* we have a proof 
  of ¬P we can derive a proof of 
  false (which which we could deduce
  P); but we have no proof of ¬P to
  use. The bottom line is that ¬¬P→ P
  is *not* valid in the constructive
  logic of Lean. On the other hand, as
  we now show, if we accept the law of
  the excluded middle, we can finish
  the proof. The steps are (1)use em
  to derive a proof of P ∨ ¬P, then
  (2) show that in either case, P is
  true, in the first case by assumption
  and in the second case by contradiction.
  -/
  have o := classical.em P,
  cases o,
  assumption,     -- case #1: P is true  
  contradiction,  -- case #2: ¬P is true
  /-
  If you're not sure what "contradiction 
  is doing here, comment it out and then
  uncomment the following two lines, which
  make clear that from a contradiciton we
  can derive a proof of false, and then we
  can use false elimination (case analysis
  where to prove the conclusion follows in
  all cases requires no proofs at all as 
  there are no possible cases for a proof
  of false to consider)."
  
  have f := h o,    -- <<< understand this!
  cases f,
  -/
end

/-
If we assume the law of the excluded middle,
then negation elimination, ¬¬P → P, is valid.

That ¬¬P → P is valid is the essence of proof
by contradiction. 

Let's start by noting that we have now seen
two different proof techniques involving
contradictions.

In "proof by negation," we prove ¬P by 
proving P → false, assuming P and showing
that from that assumption we can derive 
a proof false. That is, to prove ¬P we 
prove P → false.

By contrast, proof by contradiction seeks
to prove P (rather than ¬ P) by assuming 
¬P and showing that *that* assumption leads 
to a contradiction. That is, we seek to 
show ¬P → false, which is just what we mean 
by ¬¬P. *THEN*, having shown ¬¬P, we apply 
(classical) negation elimination (¬¬P → P)
to derive a proof of P, our overall goal. 

What we've seen today, then, is that while
proof by negation is "constructively valid"
proof by contradiction is *not*. However it
is valid if we assume the classical axiom 
of the excluded middle. That axiom is what 
allows us to infer P from ¬¬P, which is the
last step in a proof by contradiction, as
we have just seen.
-/
