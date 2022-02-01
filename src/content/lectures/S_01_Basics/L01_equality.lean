import data.real.basic


/-
AXIOMS, PROPOSITIONS, PROOFS
-/

/-
Let's again talk about propositions and 
proofs involving "equality" propositions,
such as the proposition that 1 = 1. We
all *know* intuitively that 1 = 1, but
how would you prove it, given that it's
not an axiom of ordinary predicate logic?


Without getting into the weeds, suffice
it to say that the standard Lean Prover
libraries define equality pretty much as 
we've discussed here: with an axiom in 
the form of a universal generaliztion: 
∀ {T : Type} (t : T), t = t.

In English, this says, "if you give me 
*any* Type, T, and any object, t, of that
type, I will return you a proof of the 
proposition, t = t. The existence of such
a proof, in turn, justifies the judgment 
that the proposition, 1 = 1, is *true*.  

Let's take another look at the axiom that
let's us *deduce* the *theorem* that 1 = 1.

Here it is: ∀ {T : Type} (t : T), t = t.

What that means is that if I choose any
type, T, say T = ℕ, and any value of that
type, say t = (1 : ℕ), then I should be 
able to apply the axiom to the argument
values, ℕ and 1, to get back a *proof* of
the proposition, 1 = 1. 

Indeed, that's just how it works, as the
follow example shows formally (in Lean).
-/

example : 1 = 1 := eq.refl 1   -- T = ℕ 
--  id    type     value
--  id    propo    proof

example (n: ℕ) : n = n := eq.refl n 
/-
Yay! We just constructed a formal proof: a
mathematical object that certifies that 1=1. 
It might not be super-impressive that Lean 
rejects "eq.refl 2" as a suitable proof (try
it, and don't fail to read the entire error
message when you hover your cursor over the
red squiggle!); but the principle extends to 
commplex proofs of profound propositions.
-/

example : 1 = 2 := eq.refl 1
example : 1 = 2 := eq.refl 2

/-
Nice: you've not only constructed a formal 
proof object but you have a "high assurance" 
check that the proof itself is correct, in
that the Lean type checker takes it as such. 
Lean is not just for formalizing mathematics
and logic, but for checking that given proofs
really prove what they're claimed to prove. 
-/

/-
Of course, if formalized and mechanically
checked proofs came without andy additional
costs, we'd all be using them. The benefit 
of a *natural language* "proof description"
(written in, say, English, but in a highly
mathematical style) is that it's easier for
people to follow, often because details can
be elided on the assumption that the reader
will know from context what is meant. 

In this case at hand, you could give a proof, 
of the proposition, 1 = 1, as follows:

Proof: By the reflexive property of equality
as applied to the particular value, 1. QED." 

How much detail to put in an informal proof,
or what I sometimes call a proof description,
is a matter of style and of a willingness to
make your readers fill in the missing details. 

The QED, by the way, is short for quod est 
demonstratum, Latin for "so it is shown." It is
a sort of traditional punctuation for natural
language proof descriptions that signals that 
a given proof presentation is complete.

The downside of using natural language proof
descriptions, in lieu of formal proof objects,
is that when things get complex, it can be 
hard to impossible to tell whether a proof in
natural language is correct or not. In hard
cases, it can require years of work by world
experts to decide whether a proposed, and
plausible, proof description is mathematically
correct, or, as sometimes happens, not.

In this class, we will insist, because all
mathematicians do, that your propositions 
be fully formal, i.e., syntactically correct
by the grammatical rules of predicate logic, 
as enforced by Lean. 

While quasi-formal proofs are what most people
who are working in or with mathematics use 
today. But there are now also thriving communities
in both mathematics and computer science that
are aggressively pursuing the formalization,
and the *computerization* of logic and proof,
and indeed of mathematics much more broadly.

A traditional software engineering application
of such "automated reasoning" systems is for
the specification and verification of program
behaviors. These systems are also extensively
used in the design and implementaiton of new
programming languages and compilation systems. 
By contrast, the community around Lean is 
more interested in formalizing mathematics.
-/

/-
So that brings us back the the purely 
mathematical, not a software, question of
how to prove that 1 = 1. Now we have a
beautiful computational way to understand
the problem and its solution. 

Let's write our own proof-returning function,
We'll call it gimme_a_proof. It'll take two
arguments: a type, T, and a value, t, *of that
type*; and it will return a proof of t = t, 
*for that particular t*, allowing us then to
accept the judgment that the proposition, 
t = t, is *true*.
-/

def gimme_a_proof   -- function name
    {T : Type}       -- first argument, value inferred from curly brace
    (t : T)         -- second argument, value given explicitly
    : t = t         -- return "type" 
    := eq.refl t    -- return "value" (function body)

/-
Let's decode that. We're defining a function
called gimme_a_proof that takes T and t as 
its arguments and promises to return a value 
of type t = t (a proof of this proposition).
The way that it upholds this promise is by
*applying* eq.refl to t, to construct a proof
of t = t as the result, the "return value" of
this function. 
-/

/- 
What by the way is the type of this object?
This function? Let's see. We'll use Lean's
check command, prefixing the term with @ so
that implicitness of arguments is ignored in
displaying the type of the term in question.
You can try #check without the @. You'll see
that the explicit type parameter is replaced
by an implicit "meta-variable." You can learn
to read such types either way, with really it
is often easiest to read them with implicitness
temporarily disabled for purposes of display. 
-/

#check @gimme_a_proof

/-
Now that we've got this function defined, 
we can apply *it* to arguments to have it
construct values that constitute proofs of 
t = t, just as we can apply any function to
any argument(s) of the right type(s). 

If you hover over #reduce in the 
following Lean commands, Lean will report
to you the results of applying the function
to arguments of various numerical types.
Remember when reading the outputs that
"eq.refl x" *is* an object that serves 
as a proof of x = x
-/
#check gimme_a_proof 0
#reduce gimme_a_proof 0         -- T = ℕ 
#reduce gimme_a_proof tt        -- T = bool
#reduce @gimme_a_proof ℚ 1      -- T = ℚ, complicated
#reduce @gimme_a_proof ℤ (-3)   -- T = ℝ, really complicated 

/-++++++++++
EXERCISES #1.
Give a rigorous English language "proof" 
of the proposition that 2 = 2 (where 2
is the natural number,two).

Theorem: 2 = 2.
Proof: [your answer here]

-/


/-++++++++++
EXERCISE #2.
Give, below, a formal statement and proof of 
the proposition, 2 = 2. (See above for a good
example to follow!)
-/

-- answer here

example : 2 = 2 := @eq.refl ℕ 2 -- implicit args off
example : 2 = 2 := eq.refl 2    -- implicit arguments on
example : 2 = 2 := rfl          -- this varient infors both arguments

#check @rfl     -- same as eq.refl but with both arguments implicit
#check @eq.refl --

def foobar : 1 = 1 := rfl

#reduce foobar
