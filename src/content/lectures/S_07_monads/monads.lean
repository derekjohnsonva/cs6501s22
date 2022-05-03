
import .composition

namespace hidden 


/-
Composition. It's what ∘ does with functions. Now
we generalize to composition but in a category of
computationally embellished functions, rather than
in the catetory or ordinary functions we've been
using all along.

A pure function, f : α → β, associates objects
of type α with objects of type, β. The magic is 
in how they compose: (g : β → γ) → (f : α → β) →
(α → γ), denoted as g ∘ f, pronounced "g after f,"
and defined as (g ∘ f) a = g (f a): "g after f,"
"applied to a." The output of f is "piped" to the
input of g.


Now we turn to an analogous notion of composition:
no longer of pure functions, but the compoisition 
of functions that perform auxiliary computations
and and return "embellished" results, or results,
if any, in a larger context.  

While a pure function, f : α → β, takes pure α 
values to pure β values, a "monadic" function, 
mf, takes a pure α value to an embellished β 
value, of type m β, with m, being a "context" 
type constructor. Thus, mf : α → m β. Results
(of type β) are now embellished: being carried
now (or not) within context-extended values of
type m β.

What does a monad do? It gives us a more powerful
version of >>, in the form of a generic function, 
call bind, denoted >>=, that enables one to add 
compose functions but with extra hidden processing
of "metadata" as a composition is evaluated. Monads 
give us *function composition with extra effects*.
-/

/-
Let's illustrate this idea by continuing with our 
dog examle above. Evaluating messy applied to a dog 
will result in three function application operations. 
What if we wanted a way to have the application of 
a compositions of functions return both the expected
"pure" answer along with a natural number count of 
the number of pure function applications that were
performed along the way. That is, the result will be
an embellished pure answer: we will get both a pure
yesno answer *and* a count of operations performed.

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
have called. Focus on the types of these embellished
functions. 
-/

universe u

def profiled_result (α : Type u) := α × ℕ

def m_breed : dogs → profiled_result breeds :=
  λ d, (breed d, 1)

def m_coat : breeds → profiled_result coats :=
  λ b, (coat b, 1)

def m_sheds : coats → profiled_result yesno :=
  λ c, (sheds c, 1)

/-
Recall that pure function compose in a very simple
way: the output of one is fed to the input of the
next. 
-/

#check coat ∘ breed

/-
Our embellished functions won't compose this way. 
The m_breed function, for example, takes a dog and
returns a *pair* of result, containing it's breed 
and the value 1. We can't feed this pair to m_coat
because it, too, takes a pure breed value as its
argument. 
-/

#check m_coat ∘ m_breed   -- type error!

/-
We need to define a new form of function composition.
Let's just write a concrete implementation of what we
need for our concrete example; then we can generalize
from there to discover the general principles that are
involved.  
-/

/-
The key trick in the following implementation is to 
"destructure" the pair returned by each embellished
function, and to bind names its component values. In
this way, we get a handle on both the pure result and
on the embellishment (here a count of operations). We
can then pass the pure value to the next embellished
function in line, and compose the return operation
counts (embellishments) "on the side." 
-/

def messy'' : dogs → yesno × ℕ :=
λ d,
  let 
    (b, n1) := m_breed d in let -- use d, get b, n1 
    (c, n2) := m_coat b in let  -- use b, get  c, n2
    (s, n3) := m_sheds c in     -- use c, get s, n3
    (s, n1+n2+n3)               -- final result


-- Let's compute whether polly is messy''
open dogs
#reduce messy'' polly
-- No. And it took 3 operations to compute.

/-
Now that we've got this trick in our bag, we can
use to write a function that composes our embellished
functions. Let's start simply by composing m_coat and
m_breed to obtain a function of type dog → (coats × ℕ).

- m_breed : dogs → (breeds × ℕ)
- m_coat : breeds → (coats × ℕ)
-/


def compose_coat_breed : 
  (dogs → (breeds × ℕ)) → (breeds → (coats × ℕ)) → (dogs → (coats × ℕ))
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
Now the question is, can we generalize the approach 
we've taken to the special case of composing m_coat 
and m_breed? Let's start by factoring out the common
structure  of the embellished arguments: each is of
a pair type, where the second element is of type ℕ. 
This is our profile_result type, polymorphic in one
type argument: the type of pure result to be returned
"in a context."

-/

#check profiled_result

def compose_coat_breed' :  
  (dogs → (profiled_result breeds)) → 
  (breeds → (profiled_result coats)) → 
  (dogs → profiled_result coats)
| db bc := 
  λ (d : dogs), 
    let (b, c1) := db d in 
    let (c, c2) := bc b in
    (c, c1+c2)

/-
Next we generalize the pure argument and result types.
-/

def prof_compose {α β γ : Type} :  
  (α → (profiled_result β)) → 
  (β → (profiled_result γ)) → 
  (α → profiled_result γ)
| f g := 
  λ (a : α), 
    let (b, c1) := f a in 
    let (c, c2) := g b in
    (c, c1+c2)

/-
Finally, we generalize profiled_result to any kind
of object possibly containing values of type α, which
is to say, to an object of type m α for some type 
constructor, m. 
-/

def m_compose' 
  {α β γ : Type} (m : Type → Type):  (α → m β) → (β → m γ) → (α → m γ)
| f g := 
  λ (a : α), 
    let (b, c1) := f a in   -- uh oh, m not necessarily a pair!
    let (c, c2) := g b in   -- need different implementations per m!
    (c, c1+c2)

/-
The problem is that we can no longer rely on a value of type
(m α) to be a pair, which is what we have assumed in the let
expressions up to now. If m is, say, list or option, then an
implementation of composition for pairs isn't going to work. 
We need a different implementation for option, a different one,
again, for list, and so forth. Indeed, for each type builder,
m, we'll need a different implementation of the binding code,
where we bind b to the "pure" result of applying f to a then 
then treat b as an argument to the rest of the computation. 
-/

/-
That is, we need an overloaded definition of m_compose for 
each "context-imposing" type, m. Central to this goal is an 
operation that takes an effectful value, m α, understood as
the embellished value returned by a previous computation, 
and a function from α → m β, the next function in line, and
that destructures the (m α) value, whatever it might be, in
order to get at any pure values and embellished values that
it might contain, and that passes the pure values on to the
next function while also handling the embellishments. That 
is, we're going to need an overloaded operation, as follows.
-/

class has_bind' (m : Type → Type) :=
(bind : ∀ {α β : Type}, m α → (α → m β) → m β)

/-
Here's the standard infix notation for bind.
You can read it as "feeding" a monadic value
into a monadic function to obtain a monadic
result.
-/

local infixl ` >>= `:55 := has_bind'.bind

/-
With our abstract bind operator in hand we can
how implement a polymorphic composition operator
for monadic functions! 
-/

def m_compose
  {α β γ : Type} 
  {m : Type → Type} [has_bind' m]
  (f : α → m β)
  (g : β → m γ) :
  (α → m γ) :=
λ a : α, 
  let mb := f a in mb >>= g

/-
To use this machinery we do need to implement
has_bind for each given type of monadic context.
Let's do this for our "profiled_result" monad.
-/
instance : has_bind' (profiled_result) := 
⟨ 
  λ {α β : Type } (ma : profiled_result α) a2mb, 
    let (a, c1) := ma in 
    let (b, c2) := a2mb a in
    (b, c1+c2)
⟩

/- 
We can now see how it all works.
-/

#reduce m_compose m_breed m_coat

local infixl ` >=> `:60 := m_compose  -- the fish operator

def is_messy_prof := (m_breed >=> m_coat >=> m_sheds)

#reduce is_messy_prof fido
#reduce is_messy_prof polly

/-
So the fish operator supports the feeding of 
a monadic value into a composition of monadic
functions. What is doesn't support is feeding 
of a pure value into such a pipeline, as the 
following example shows.
-/

/-
The problem is that polly is pure but >=> expects
a monadic value. The solution is to define a new
function, one that will have to be overloaded for
each monadic type) that takes a pure value as its
argument "lifts" it to a monadic value. Then we 
can use >=> to feed it into a pipeline composed
of monadic functions.
-/

class has_return' (m : Type → Type) :=
(return' : ∀ {α : Type}, α → m α)

open has_return'

instance : has_return' (profiled_result) := 
⟨
  λ α a, (a, 0)
⟩  

/-
Now we can write a complete pipeline with
input fed in "from the left."
-/

#reduce (return' polly) >>= (m_breed >=> m_coat >=> m_sheds)

/-
We can now define a profiled result "monad" by defining
a monad typeclass with our overload-able bind and return
operations, to be implemented for each monadic context
type constructor, m. 
-/

/-
Let's do this for the option type.
-/
instance bind_option : has_bind' (option) :=
⟨ 
  λ {α β : Type } (ma : option α) a2mb, 
    match ma with
    | none := none
    | (some a) := a2mb a
    end
⟩

instance : has_return' (option) := 
⟨
  λ α a, some a
⟩ 

/-
If we insist that a monad also be an applicative, then
a further simplification is possible leading to a new 
definition of monad, based on operators usually called 
return and flatten. We won't have time to cover this in
in this class, but you should be able now to go learn 
it on your own if you're interested.  
-/

/-
So why do monads matter? By supporting composition they
enable decomposition, which is fundamental to problem
solving. They also support a broad range of effectful
styles of programming in otherwise purely functional
styles of programming. Finally, they illustrate a very
beautiful point: they implement composition not in the
category of ordinary sets and functions, but in what are
called Kleisli categories. Composition is the essential
concept in category theory, and now we have a second,
and quite distinct notion of composition. This idea
puts you on a whole new path of discovery.
-/

end hidden

/-

-/