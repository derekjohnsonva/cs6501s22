/-
The purpose of this lecture/assignment is to
develop and deepen your understanding of the 
lofical concepts covered so far: equality of 
values/terms of any type, and conjunction of
propositions. We present the embedding of the
∨ connective of predicate logic into Lean and
elaborate on the representation of relations,
such as equality, as inductive families of
propositions along with proof-building and 
proof-consuming inference rules for them, in
Lean.
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
to embed ∧. To do this we'll need to represent
the connective as a family of propositions of
the form P ∨ Q, parameterized by propositions,
P and Q. Then we'll need to define introduction 
and elimination rules for ∨ that capture the
intended meaning of this connective: that it's
true (and there's a proof of that) if at least
one of P or Q is true (has a proof). 
-/

namespace hidden

/- 
Represent ∨ as a family of propositions,
α ∨ β, parameterized by (polymorphic in)
two propositions, α and β, where such a 
proposition, α ∨ β has a proof, iff at
least one of α and β has a proof. That is,
we must be able to construct a proof of 
α ∨ β from a proof of α or from a proof
of β. We define the introduction rules 
for "or" accordingly.
-/
inductive or (α β : Prop) : Prop 
| inl (a : α) : or 
| inr (b : β) : or


/-
Now we can state and prove disjunctive
(or) propositions. To do so at least one
"disjuct" has to be true, and we have to
pick one and apply the right constructor. 
In the following example, it would not
do to use or.intro_right because there
is no proof of that proposition.
-/
example : or (3=3) (3=4) := 
or.inl rfl

/-
Similarly here it wouldn't do to use
or.intro_left, again because the left
disjunct, 3=4, doesn't have a proof.
-/
example : or (3=4) (3=3) := 
or.inr rfl

/-
In this example, we could use either
the left or right introduction rules.
There are thus two distinct proofs in
this case.
-/

lemma left_proof : or (3=3) (4=4) := or.inl rfl
lemma right_proof : or (3=3) (4=4) := or.inr rfl

-- You can see that these are different proofs
#reduce left_proof
#reduce right_proof

/-
Both of these proofs are of type "or (3=3) (4=4)"
and you can see that they're different. And yet,
as you can see next, Lean treats them as equal!
This behavior implements the concept of "proof
irrelevance." Lean enforces the notion that any
proof of a given proposition "will do" by treating
all proofs of the same proposition as being equal.
-/
example : left_proof = right_proof := rfl

end hidden

/-
Now let's see the same ideas using Lean's own
definitions (from its libraries) of "or" and
its related introduction rules.
-/
#check @or
#check or (3=3) (1=0)

example : 3 = 3 ∨ 1 = 0 :=
or.inl rfl 

example : 1 = 0 ∨ 3 = 3  :=
or.inr rfl 

/-
In the preceding examples, Lean knows
what proposition is to be proved because
it's stated explicitly in each case (right
after the colons). Here's a case where we
leave out the proposition to be proved and
where Lean can't infer it.
-/


-- can't infer second disjunct (return type)
lemma ex1 := or.inl (eq.refl 3) 

/-
Here, the term, or.inl (eq.refl 3), is a
proof of "(3=3) ∨ ___", but we have no way
of knowing what that something, the second
disjuct, is. In such cases, we can use an
alternative introduction function, called
or.intro_left, where we specify the right 
conjunct explicitly (first argument), and
give a proof of the left, from which the
left conjunct is inferred. 
-/

#check or.intro_left (4=5) (eq.refl 3)
--  right proposition ^^^   ^^^^ left proof
#check or.intro_right (4=5) (eq.refl 3)
--    left proposition ^^^   ^^^^ right proof


/-
#2. Define an inductive family of propositions 
to specify the successor relationship, succ_rel,
between pairs of natural numbers. Given any two
natural numbers, n and m, (n, m) ∈ succ_rel if 
and only if m = n + 1. Then state and prove the
lemma, (0,1) ∈ succ_rel.
-/

/-
Before specifying this relation logically, let's
write a *computational* definition. (As a review
of syntactic alternatives for defining functions,
we give three variants.)
-/
def incr (n : ℕ) : ℕ := n + 1
def incr' : ℕ → ℕ := λ (n : ℕ), n + 1
def incr'' : ℕ → ℕ | n := n + 1

/-
The wonderful thing about function definitions in
Lean and other programming languages, is that they
compute. You can apply a function to an argument 
and the machine will derive the result. Here for
example, we apply the incr function to the actual
parameter 7. To reduce this application expression,
Lean fetches the body of the function, substitutes
the 7 for each occurence of n, yielding (7 + 1) in
this case. It then reduces that expression, giving
8, as a final result. In this sense, we *computed*
that the pair, (7, 8), belongs to the relation.
-/
#reduce incr 7


/-
By contrast, we *specify* the relation "declaratively" 
by giving rules that can be used to prove (or not) that
a given pair is in the relation. The rule in this case
is succ_rel.intro. What it specifies is that if one is
given any two natural numbers, n and m, along with a
proof, h, that (m = n + 1) then (succ_rel n m h) is a 
a proof of succ_rel n m.
-/
inductive succ_rel : ℕ → ℕ → Prop
| intro (n m : ℕ) (h : m = n + 1) : succ_rel n m

/-
Note that applying succ_rel to n and m, say 3 and 4,
just returns the *proposition*, (n,m) is in succ_rel.
You can't apply succ_rel to 3 and expect to get a 4
in return as is possible with the incr functions we
defined above. 
-/
#check succ_rel 3 4
#check @succ_rel.intro

/-
Rather, with such a declarative specification in hand,
what we can do is to try to prove that certain pairs 
of numbers are in this relation. Next, for example, we
first prove that (3, 4) is in this relation, and then
we see that we get stuck if we try to prove that the
pair, (3,5), satisfies the specification of succ_rel.

-/

example : succ_rel 3 4 := succ_rel.intro 3 4 rfl
example : succ_rel 3 5 := succ_rel.intro 3 5 rfl


/-
We've now seen that we can specify a mathematical 
function either computationally, as a function, or
declaratively, as a relation. Two questions arise.
First, are these definitions mathematically equivalent?
Second, why would we ever want to use a declarative
specification rather than a "computable" function?
-/

/-
To answer the first question, we formulate the claim
that the two definitions are equivalent as a formal
proposition, and we prove it. We claim and show that
(n,m) ∈ succ_rel if and only if m = incr m. This is
your first example of a kind of program verification,
wherein we prove that a function that we can run will
always give us the answer that the declarative spec
says it should give us.
-/
theorem def_equivalent : ∀ (n m : ℕ), (m = incr n) ↔ succ_rel n m :=
begin
  intros,
  apply iff.intro _ _,  -- hint: try "split" instead 

  -- forward
  assume h,
  rw h,
  unfold incr,
  apply succ_rel.intro,
  trivial,
  --
  assume h,
  cases h,
  unfold incr,
  assumption,
end

/-
Yay! Now for the second question: why would we ever
want to use a declarative specification of a binary
relation rather than a function that we can "run" to
get the second element of any pair from the value of
the first?

The answer is that functions in Lean are total, so 
if we want to represent partial functions, we need
to use declarative specifications. 

To make this idea concrete, consider the partial 
function, F, that is exactly the identity function
on natural numbers except that it's undefined for 
the input, zero. The mathematical function, F, is 
of type ℕ → ℕ, but we can't implement it properly in
Lean as a function, say f1, of type ℕ → ℕ, because 
what this type really means is ∀ (n : ℕ), ℕ, which
is to say that it has to return a value of type ℕ
*for any* argument, n, including 0. 

There are some workarounds, but none is perfect.
Let's look at a few work-arounds.
-/

/-
Alternative #1. Just use the identify function and
leave the programmer resposible for never applying
it to the value, zero.
-/
def f1 : ℕ → ℕ := λ n, n

/-
Alternative #2. For zero, return an unusual value
as a sort of error flag. This solution also demands
that the programmer understand the "hack" that we're
using here. Clearly g doesn't *really* represent the
partial function 
-/
def f2 : ℕ → ℕ := 
  λ n, if (n = 0) then 1000 else n

#reduce f2 2
#reduce f2 1
#reduce f2 0

/-
Alternative #3: Use an option return type. Now we
have an implementation that is more faithful to the
behavior of our mathematical function, F, but at
the cost of (1) changing the type from ℕ → ℕ to
ℕ → option ℕ, and (2) forcing the user of f3 always
to check whether they received an error (none) or 
a normal return value (some n).
-/
def f3 : ℕ → option ℕ := 
  λ n, if (n = 0) then none else some n

def demo_f3 : ℕ → string :=
λ n,
  let r := f3 n in      -- temporarily bind r to result
  match r with          -- error check: case analysis on r
    | none := "error"   -- if "none", return "error" string
    | some n := "good"  -- else return "good" string
  end

#eval demo_f3 2
#eval demo_f3 1
#eval demo_f3 0

/-
Whereas f3 requires the caller to check for an
error *after* calling the function, we can also
add an argument to our implementation requiring
the programmer to show *before* the function is
called that the argument is good.
-/
def f4 : ∀ (n : ℕ), (n ≠ 0) → ℕ := λ n h, n

/-
The proof argument establishes a "precondition"
for f4. One cannot even call it without having
a proof that n≠0.  In each of the following 
examples, we apply f4 to n and a proof of n≠0,
and we provide the proof argument as the result
of a simple tactic script. In the final case, 
of n = 0, you will see that we can't provide 
that second proof argument, which prevents us
from calling the function without getting an
error. 
-/    

#reduce f4 2 begin assume k, cases k, end  
#reduce f4 1 begin assume k, cases k, end
#reduce f4 0 begin assume k, cases k, end

/-
In the last case we're prevented from
calling the function properly by the
non-existence of the required proof
argument.

This solution shows that in Lean we can
incorporate precondition specifications
and a kind of precondition checking by
defining functions that require proofs
be given as arguments to show that the
required conditions for using a function
are satisfied. 
-/

/-
For the sake of completeness, another
similar solution is based on the notion
of a subtype in Lean. Here we define a
subtype, positive, of the natural numbers,
then we use pos as the argument type.
-/

def positive : Type := { n : ℕ // n ≠ 0 }

/-
A value of this type is a pair, comprising
a natural number, n, and a proof that n ≠ 0.
We then implement F as a total function from 
positive to ℕ, knowing that if we do get a 
value of type, positive, as input, that it's
a number and a proof that that number is not
zero. So we just extract the number from the
pair and return it.

But this is still not perfect. The domain 
of F is ℕ, even though the domain on which
it's defined (it's domain of definition) does
not include 0. So mathematically speaking, F
is a partial function from ℕ to ℕ, not a total 
function from positive to nat. Our code does
not quite express the nature of the concept
(F) that we're implementing.
-/

def f5 : positive → ℕ := 
  λ n, match n with 
    | ⟨ n, pf ⟩ := n 
  end

/-
In many cases, the most practical solution will
be to switch from a "computable" function to a
declarative specification of a relation. That is
what we've done in this file.
-/

inductive F : ℕ → ℕ → Prop 
| intro : ∀ (n m : ℕ), (n≠0) → (n=m) → F n m

/-
Now instead of computing m from n in any given
case, we assert and prove that a given m relates
to a given n. And of course we require that n≠0
in any case.
-/

-- (2,2) is in the identity relation on pos nats
example : F 2 2 := 
  F.intro 2 2 (begin intro h, cases h end) rfl

-- (1,1) is in the identity relation on pos nats
example : F 1 1 := 
  F.intro 1 1 (begin intro h, cases h end) rfl

-- (1,2) is not in the relation: the check that m=n fails
example : F 1 2 := 
  F.intro 1 2 (begin intro h, cases h end) rfl

-- (0,0) is not in the relation: the check that n≠0 fails
example : F 0 0 := 
  F.intro 0 0 (begin intro h, cases h end) rfl

