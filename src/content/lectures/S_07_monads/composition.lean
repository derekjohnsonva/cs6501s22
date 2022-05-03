/-
The functor typeclass enables us to change the behavior
of (what amounts to) function *application* In particular,
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
function application as well as "exceptions" over
applications of functions to multiple arguments. Note:
an applicative functor *is a kind of functor,* so we
can assume that the map function is available when we
define pure and seq.
-/

/-
We can now state the purpose of the monad typeclass.
In short, it provides a way to override the behavior 
of function *composition* so that additional data and
behavior can be overlaid on top of ordinary function
composition, just as the applicative functor let us
overlay extra data and behavior on ordinary function
*application*.

Composition is a super-power because because it lets 
us decompose complex computations into compositions
of simple computations.

As an example, suppose we want to get a dog but not
one that will make our house all furry. So we go to
the animal shelter. There are two dogs there, polly
and fido. Polly is a poodle and fido is a husky.

We don't want a dog that will mess up our house by
leaving lots of fur around. What we need then is a 
function that given a particular dog as input tells
us whether that dog is messy. For each dog we'll want 
a yes/no answer: is is this dog *messy* or not?

messy : dogs → yesno

How should we implement messy? The trick is to see 
that we can break it into a composition of simpler
functions. (1) We note that whether a dog is messy
if and only if it sheds. Whether it sheds depends 
on its coat: if it has hair it doesn't shed, but if 
it has fur, it does shed.  Whether a dog has fur or 
hair depends, in turn, on its breed. Poodles have 
hair. Husky's have fur. 

So we can now see how to solve the problem. Given
one of the dogs as input, compute its breed (husky
or poodle); then use that "output" as the input to
a second function that takes a breed as input and
outputs its coat type (fur or hair); next use that
output as the input to a function that indicates
whether that kind of coat sheds or not (yes/no).
We will take the answer to the last question as 
the answer to the overall question of whether a
given dog is *messy*.

Suppose we have functions to solve each of these
smaller problems.

breed : dogs → breeds
coat : breeds → coats
sheds : coats → yesno

Having broken our problem up into these parts, we
now need a way to compose them into the function 
we seek, messy : dogs → yesno.
-/

namespace hidden

-- Data types
inductive dogs | fido | polly
inductive breeds | poodle | husky
inductive coats | fur | hair
inductive yesno | yes | no
  
open dogs breeds coats yesno

-- Component functions
def breed : dogs → breeds
| polly := poodle
| fido := husky

def coat : breeds → coats
| poodle := hair
| husky := fur

def sheds : coats → yesno 
| fur := yes
| hair := no

/-
Composition is the operation of "connecting" 
the output of one function to the input of a
next one to produce a new function from initial
input to final output. We can thus chain together
our three functions to get our desired overall
solution.
-/

def messy := sheds ∘ coat ∘ breed

/-
We pronounce (sheds ∘ coat ∘ breed) as 
"sheds after coat after breed." When applied
to a dog, d, this function first applies breed,
then feeds the result to coat, then feeds that
result to sheds and finally returns the desired
yes/no result. Note that the argument on the 
right sort of flows right to left through this
function composition.
-/

#check messy  -- isMessy : dogs → messy
#reduce messy -- λ (x : dogs), sheds (breed x)

example : messy polly = no := rfl   
example : messy fido = yes := rfl

/-
Function composition is associative.
-/

theorem comp_assoc : 
  ∀ {α β γ δ : Type } 
    (k : γ → δ) 
    (g : β → γ) 
    (f : α → β),
  (k ∘ g) ∘ f = k ∘ (g ∘ f) :=
sorry

-- hint
#check @funext

/-
Let's unpack one of these examples. We know now that 
(messy polly) reduces to no. We also know that it
applies (λ d, (sheds (coat (breed d)))) to (polly).
It binds d to polly, then applies breed then coat
and then sheds. 

What we see is that ordinary function composition 
notation gives us a sort of "backwards" or inside out
sequential notation: the last operation to be applied 
is the leftmost one in the expression. On the other
hand, we can think of this sequence in a more usual
(for English speakers) left to right or top to bottom
sequence. 

With a simple notational change we can express the 
same composition of functions in a more natural manner.  
The secret is to use binding operations. First we bind
b to the result of applying breed to polly, then we
bind c to the result of applying coat to b then we
bind m to the result of apply sheds to c, and finally
we "return" (reduce to) m. What we end up with looks
a lot more like typical "sequential" code of the kind
we find in imperative languages.
-/

def isPollyMessy :=
  (let 
    b := (breed polly) in let
    c := (coat b) in let
    m := (sheds c) in
    m
  )


/-
If we generalize the choice of polly as the dog in
this case (replacing it with a parameter) then we
get our messy function back.
-/
def messy' (d : dogs) :=
(let 
  b := (breed d) in let   -- bind b, call rest
  c := (coat b)  in let   -- bind c, call rest
  m := (sheds c) in       -- bind m, call rest
        m                 -- "return" m
)

-- It's exactly the same as sheds ∘ coat ∘ breed
example : messy' = messy := rfl

/-
One of the things that a "monad" does is to allow
us to write compositions of a richer kind in this
sort of sequential style. But we don't need monad
to understand this idea. We can easily define a 
new notation that allows us to write the program
we've written here in a left-to-right sequential
style.
-/

/-
The easy trick is to define a notation for function
application where the argument is on the left and 
the function is on the right. We can then think of
"feeding" each argument into the function on the 
right. Let's use >> as an infix notation of this
style of function application.
-/

local notation v ` >> ` f :120 := f v

#reduce 
  polly >>  -- a pure argument bound as argument of rest
  breed >>  -- apply bread to incoing, pass result to rest
  coat >>   -- apply coat to incoming, pass result to rest
  sheds     -- apply sheds to incoming, return final result

/-
Function application is *left* associative, so what we
have here is polly being fed to breed reducing to some
breed, which is fed to coat, reducing to some coat, which
is fed to sheds, reducing to a yes/no value. It's still
just ordinary everyday function composition/application.
-/

#reduce (((polly >> breed) >> coat) >> sheds)     

  
/-
So now we have an abstraction of a sequential pipeline
that works by taking an argument (in general the result
of a preceding computation), and passes that value as 
the argument to "the rest of the pipeline."
-/

/-
Let's look at another way we can write this code,
starting with just (polly >> breed). 
-/

#reduce  
    (λ d, breed d)  -- bind d and compute (breed d)
    polly           -- argument bound to d


#reduce 
  (λ b, coat b)     -- bind b to result of the rest then compute (coat b)
    ((λ d, breed d) -- argument ("the rest")
      polly
    )

#reduce polly >> breed >> coat >> sheds
#reduce 
  (λ c, sheds c)  -- bind c to result of rest then compute (sheds c)
    ((λ b, coat b) -- argument (rest)
      ((λ d, breed d)
          polly
      )
  )

/-
Yet another way to write the same code, then, is as
a sequence of binding operation. Here we bind c to
the result of "running the rest of the computation"
then we process c. And the rest of the computation
is structured in the same way. We present this style
again to demystify some of the syntactic constructs
we'll see next, when we turn to monads, which simply
provide a way to compose functions, let's call them
"monadic functions" that return not pure results, of
some type β, but "enriched" results, of type (m β),
where m is a type constructor such as list, option,
either, pair, etc.
-/

/-
With this discussion of composition in mind, and now
understanding that a monad is a typeclass that enables
composition of monadic functions, please continue to
the monad.lean file. 
-/

end hidden
