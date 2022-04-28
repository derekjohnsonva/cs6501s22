/-
The functor typeclass enables us to change the behavior
of (what amounts to) *function application* In particular,
the functor.map operation (<$>) lifts any pure function, 
h : α → β, to a "structure-preserving" function on data 
values containing α and β values: e.g., mapping options, 
lists, or trees of α values into structurally identical 
trees of β values. Preservation of structure is assured
by the functor laws. 
-/

/-
The applicative functor typeclass enables us to change 
the behavior of *multi-argument* function application.
The pure function takes a function and lifts it into
one that can then serve as a first argument to the seq
function, which then "applies" that function to a data
structure containing first arguments to that function. 
The result is then a data structure holding partially
evaluated functions that is then "applied" to the next
data structure containing argument values. Overriding
the definitions of pure and seq in particular ways for
different data structures, such as option and list,
has given us nice ways to implement "non-deterministic"
function application as well as error propagation over
applications of functions to multiple arguments. Note:
an applicative functor *is a kind of functor,* so we
can assume that the map function is availabel when we
define pure and seq.
-/

/-
We can now explain the purpose of the monad typeclass.
It provides us with a way to override the behavior of
ordinary function *composition*. So, to begin, we will
review this essential concept.
-/

/-
Suppose we have three sets: dogs = {Benji, ChewChew}; 
breeds = {poodle, husky}; and messy = { true, false }; 
as well as two functions, breedOf : dogs → breeds; 
and messy : breed → sheds. For each dog, breedOf returns
its breed; and for each breed, sheds returns true or 
false reflecting whether that breed of dog sheds or not. 

In this context, we can apply the composition operator
to sheds and breedOf, to derive a new function, isMessy : 
from dog → bool.
-/

/-
axioms 
  (dogs breeds messy : Type)
  (breed : dogs → breeds)
  (sheds : breeds → messy)
noncomputable def isMessy : dogs → messy := (sheds ∘ breed)
-/

/-
Next we confirm that (1) isMessy is a function that takes 
a dog and returns its messiness, and (2) that when applied
to an argument (dog), x, it works by first computing the
value of (breed x), yielding a breed, and then applying the
sheds function to that result of that first operation.
-/

inductive dogs | fido | polly
inductive breeds | poodle | husky
inductive coats | fur | hair
inductive yesno | yes | no
  
open dogs breeds coats yesno

def breed : dogs → breeds
| polly := poodle
| fido := husky

def coat : breeds → coats
| poodle := hair
| husky := fur

def sheds : coats → yesno 
| fur := yes
| hair := no

def messy : dogs → yesno := 
  sheds ∘ coat ∘ breed

#check messy  -- isMessy : dogs → messy
#reduce messy -- λ (x : dogs), sheds (breed x)

#reduce messy polly 
#reduce messy fido

/-
We pronounce (sheds ∘ coat ∘ breed) as "sheds after 
coat after breed." It is defined to be the function 
obtained by taking a dog as an argument and returning 
the value obtained by first applying breed to the dog, 
yielding its breed, then applying coat to that breed,
to obtain whether it's fur or hair, and then finally
applying sheds to that value to get a yes/no answer
to the question of whether that partiular dog is messy
(because it sheds).#check

Function composition is associative.
-/


/-
Let's unpack one of these examples. We know now that 
(messy polly) reduces to no. We also know it reduces 
to (λ d, (messy (coat (breed d)))). We see again that 
to get a final answer we apply "messy *after* applying
coat after applying breed to the given dog, d. 

This is a sort of "backwards" sequential notation, in
the sense that the last operation to be applied is the
leftmost one in the expression. The argument d "flows" 
into the breed function from the right; the result comes
out and "flows" left into coat function; the result of
that emerges and flows to the left into sheds function;
yielding a final result.

English is read from left to right and top to bottom, 
and so English speakers expect temporal sequences to 
be organized in that style. By a simple notation change
we can express the same composition of functions.  
-/

def isPollyMessy :=
  (let 
    b := (breed polly) in let
    c  := (coat b) in let
    m := (sheds c) in
    m
  )


/-
Of course, even though our new code looks sequential,
it's still purely functional. In the first line we
*bind* the result of the first application to b. We
use this value as an argument in the second line and
bind its result to c. Next in this context in which
b and c are thus bound, we evaluate (sheds c) and bind
its result to m; and in the very last line we "return"
(reduce to) the value of m.

If we generalize the choice of polly as the dog in
this case (replacing it with a parameter) then we
get our messy function back.
-/

def messy' (d : dogs) :=
(
  let b := (breed d) in   -- bind b, call rest
    let c := (coat b)  in   -- bind c, call rest
      let m := (sheds c) in   -- bind m, call rest
        m                       -- "return" m
)

/-
Some form of bind here
-/

-- It desugars to just what we expect
#reduce messy'

/-
As a conceptual step without being formal, we can
easily imagine a new notation that allows us to
write that program in a more sequential style.
-/

/-
Note that we can see a sequential chain of function
applications in this code: sheds ∘ coat ∘ breed means 
  - apply sheds after (to the result of) 
  - apply coat after (to the result of) 
  - apply breed to polly. 

But in this style of presentation, the applications
appear in the reserse order in which they occur. We
can reasily develop a new notation in which functions
appear in our code in the same order in which they
are actually applied. The easy trick is to define a
notation for function application where the argument
is on the left and the function to be applied is on
the right. We'll use >> as an infix operator. So, for
example 0 >> nat.succ would evaluate to 1, because
it means nothing other than nat.succ 0.

-/

local notation v ` >> ` f :120 := f v

example : 0 >> nat.succ = 1 := rfl
example : 0 >> (λ n, n + 1) = 1 := rfl

/-
Study the second example. What it means if we desugar
the >> is ((λ n, n + 1) 0); and what this means is to
first *bind* n to the incoming argument, then in this
context evaluate the expression, n + 1. We'll return
to this perspective later in these notes.
-/

#reduce 
  polly >>  -- a pure argument bound as argument of rest
  breed >>  -- apply bread to incoing, pass result to rest
  coat >>   -- apply coat to incoming, pass result to rest
  sheds     -- apply sheds to incoming, return final result
  
/-
So now we have an abstraction of a sequential pipeline
that works by taking a pure argument (like polly), or in
general the result of a preceding computation, and passes 
that value as the argument to the function that implements 
the rest of the pipeline.
-/

-- Example: the following programs pairs are equivalent
#reduce polly >> breed  -- feed polly as argument into breed
#reduce   
  (λ d, breed d)         -- bind d and apply breed to it
    polly                -- argument to be bound


#reduce polly >> breed >> coat
#reduce 
  (λ b, coat b)     -- function
    ((λ d, breed d) -- argument (rest)
      polly
    )

#reduce polly >> breed >> coat >> sheds
#reduce 
  (λ c, sheds c)  -- function
    ((λ b, coat b) -- argument (rest)
      ((λ d, breed d)
          polly
      )
  )



/-
========================
-/


/-
So what does a monad do? The answe: it gives us a
more powerful version of >>, in the form of a generic
function call bind, denoted >>=, that enables one to
add hidden processing of metadata to the evaluation
of pipelines like the ones we've just seen. Monads 
give us *function composition with effects*.

Let's start to illustrate this idea by continuing
to develop our dog examle above. Evaluating messy 
applied to a dog will result in three function 
application operations. What if we wanted a way
to have application of compositions of functions
return both the expected pure answer along with a
natural number count of the number of pure function
applications were performed to produce the final
result.

For example, now we'd expect the result of evaluating 
(messy fido) to return not just "yes" but the pair, 
"(yes, 3)," meaning yes fido's messy and oh by the
way, computing this answer took three ordinary
function applications.  
-/

/-
Clearly the types of the functions that we need to
"compose" changes. Each function in the "chain"
needs to return not just the correct "pure" result 
but also a natural number accounting for the call 
to this function and to any other functions it might
have called. Focus especially on the types of these
functions. Remember if S and T are types then S × T
is a type, the type of (S value, T value) pairs.  
Note that each of these functions takes a pure
argument but returns a result embedded in a larger
context object, here in a pair that also contains
a natural number.
-/

universe u

def prof_result (α : Type u) := α × ℕ

def m_breed : dogs → prof_result breeds :=
  λ d, (breed d, 1)

def m_coat : breeds → prof_result coats :=
  λ b, (coat b, 1)

def m_sheds : coats → prof_result yesno :=
  λ c, (sheds c, 1)

/-
The operation of pure function composition will not
work here as it did before, because it requires that
the argument type of the next function to be applied
is the same as the return type of the function most
recently applied. For example, breed takes a dog and
returns a breed, coat takes a breed and returns what
kind of coat it has, and messy takes a kind of coat
and returns a yesno as the final answer.
-/
#check coat ∘ breed

/-
But our extended functions won't compose this way. 
The m_breed function takes a dog and returns a pair
containing it's breed and the value 1. But we can'
feed this pair to m_coat because takes a pure breed 
value. We need a new kind of composition operator 
for our "effectful" functions.
-/

#check m_coat ∘ m_breed   -- type error!

/-
Clearly we need to define a new form of function
composition: one that handles any pure applications
that are needed but that also handles the metadata
returned along with a pure result value. 

Let's just write a concrete implementation of the
our desired pipeline. Then we can study it as a
basis from which to generalize. 
-/

def messy'' : dogs → yesno × ℕ :=
λ d,
  let 
    (b, n1) := m_breed d in let -- use d, get b, n1 
    (c, n2) := m_coat b in let  -- use b, get  c, n2
    (s, n3) := m_sheds c in     -- use c, get s, n3
    (s, n1+n2+n3)               -- produce final result

-- Let's compute whether polly is messy''
#reduce messy'' polly
-- No! And that took 3 operations to compute

/-
Let's rewrite messy'' applied to polly once again, 
but put it in the style using lambda to bind a variable 
to the result of running the rest of the computation and
returning the result of performing some operation on it.
We'll do it in steps, as we did before.
-/

/- 
this is a function application: bind d to polly, and
then in this context, compute and return (m_breed d). 
-/

#reduce   
  (λ d, m_breed d)  -- bind d to polly, apply breed to d
    polly  

/-
So far so good, but that's the end of our good luck. In
retrospect it should be clar that we won't be able to chain
our effectful functions using plain old function composition. 
-/

#reduce m_coat ∘ m_breed

/-
Here the problem is that m_breed returns a breed along with
a count, while m_coat just expects to receive a breed value
as an argument. Somehow what we need is a novel composition
operator: one that can (1) "reach into" the data structure
that m_breed returns, to pull out the "breed" value that it
contains, and pass it on to m_coat, while also combining the
counts from both function applications to return as part of
the final result. Let's denote this new composition operator
as >>=, an infix notation for a function we can call "bind'."

Now let's think about types:

- m_breed : dogs → (breeds × ℕ)
- m_coat : breeds → (coats × ℕ)
- m_coat >>= m_breed : dog → (coats × ℕ)
-/


def compose_coat_breed :  (dogs → (breeds × ℕ)) → (breeds → (coats × ℕ)) → (dogs → (coats × ℕ))
| db bc := 
  λ (d : dogs), 
    let (b, c1) := db d in 
    let (c, c2) := bc b in
    (c, c1+c2)

/-
We can now see that the composition of m_breed and m_coat using our
new, special case, compose-like function does two things: it computes
the desired composition of the pure functions, breed and coat, while 
also combining the effects of m_breed and m_coat in an effect that is
returned along with the pure result.
-/
#reduce compose_coat_breed m_breed m_coat
#reduce (compose_coat_breed m_breed m_coat) polly

/-
Now the question is, can we somehow generalize the approach we've
taken here to the special case of composing m_coat and m_breed. A
first step is to recognize that the arguments to this function are
all similar in an important way: each is of a pair type, combining 
a pure value and an effect in the form of a natural number. Let's 
start by factoring out the common structure  of these pairs.
-/

#check prof_result

def compose_coat_breed' :  
  (dogs → (prof_result breeds)) → 
  (breeds → (prof_result coats)) → 
  (dogs → prof_result coats)
| db bc := 
  λ (d : dogs), 
    let (b, c1) := db d in 
    let (c, c2) := bc b in
    (c, c1+c2)

/-
Now let's simply generalize the pure argument and result types.
-/

def prof_compose {α β γ : Type} :  (α → (prof_result β)) → (β → (prof_result γ)) → (α → prof_result γ)
| f g := 
  λ (a : α), 
    let (b, c1) := f a in 
    let (c, c2) := g b in
    (c, c1+c2)

/-
Finally, let's think about generalizing prof_result to any kind
of object possibly containing values of type α. Note that in a
strong sense, prof_result is analogous to list, option, tree, 
etc: a data structure that can contain values of type α. We've
seen how to do this kind of generalization before.
-/

def m_compose' {α β γ : Type} (m : Type → Type):  (α → m β) → (β → m γ) → (α → m γ)
| f g := 
  λ (a : α), 
    let (b, c1) := f a in   -- we don't know that m is a pair!
    let (c, c2) := g b in
    (c, c1+c2)

/-
The problem is that we can no longer rely on a value of type
(m α) to be a pair, which is what we have assumed in the let
expressions up to now. So this is not going to work as is. We 
can see that if m is, say, list or option, an implementation
of composition for pairs isn't going to work at all. We will
need a different implementation for option, a different one,
again, for list, and so forth. Indeed, for each type builder,
m, we'll need a different implementation of the binding code,
where we bind b to the "pure" result of applying f to a then 
then treat b as an argument to the rest of the computation. 
-/

/-
That is, we need an overloaded definition of m_compose for 
each "context-imposing" type, m. And central to this goal
is an operation that takes an effectful result, unpacks its
pure result value, and passes that on to the next effectful
operation, itself taking a *pure* value and returning an
effectful result. That is, we're going to need an operation
like the one that follows here.
-/

class has_bind' (m : Type → Type) :=
(bind : ∀ {α β : Type}, m α → (α → m β) → m β)

local infixl ` >>= `:55 := has_bind'.bind

instance bind_prof_result : has_bind' (prof_result) := 
⟨ 
  λ {α β : Type } (ma : prof_result α) a2mb, 
    let (a, c1) := ma in 
    let (b, c2) := a2mb a in
    (b, c1+c2)
⟩

def m_comp'
  {α β γ : Type} 
  {m : Type → Type} [has_bind' m]
  (f : α → m β)
  (g : β → m γ) :
  (α → m γ) :=
λ a : α, 
  let mb := f a in mb >>= g

#reduce m_comp' m_breed m_coat

local infixl ` >=> `:55 := m_comp'

def is_messy_prof := (m_breed >=> m_coat >=> m_sheds)

#reduce is_messy_prof fido
#reduce is_messy_prof polly
