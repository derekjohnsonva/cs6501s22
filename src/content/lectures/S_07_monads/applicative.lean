/-
We now introduce the applicative typeclass. Here
it is as copied mostly verbatim from Lean's library
(credit DeMoura and Ulrich). 
-/

import .functor 

namespace hidden

open function   -- for definition of "const" used at end of file
universes u v

/-
Now suppose that we want to generalize functors, which allow
for mapping of *one-argument* functions, such as inc, over 
functorial values, to enable mapping of n-argument functions
over functorial values for any natural number, n.

As a special case, we have the usual functor mapping function, 
which works as follows: (α → β) → f α → f β. In plain English,
it takes a pure one-argument function from (α → β) and applies
it to each value in the functorial value of type f α. 

Now consider a function of type α → β → γ (think of addition
of nats, of type nat → nat → nat, for example). Here what we
will want is a mapping function that takes a pure function of
type α → β → γ then a functor of α values *then a functor of 
β values* to produce a functor of γ values.

So suppose our pure function is nat addition and that we 
want to map this two-argument function. We'll need a list
of natural numbers as first arguments. We'll map add over 
it, but of course we won't get a list of resulting nats;
rather we'll get a list of partially evaluated functions.
-/

#reduce nat.add <$> [1,2,3] -- remember <$> is functor.map

/-
We will then want to apply each of these functions to each
of their second arguments.
-/

/-
Now consider mapping a pure function with three arguments.
We take our pure function, map it over the list of first
arguments, getting a list of partially evaluate functions
that expect two more arguments. We then want to apply each
of these to their second arguments in a second list to get
a list of further partially evaluate functions expecting 
their last arguments. We apply them to their arguments in
the third list to finally get a list of the values of the
function applied to all of its arguments, which come from
the given lists. 
-/

/-
So what we're seeing here is that once we bootstrap the
process given a pure function, what we've now got is a
situation in which we have a *list* of functions each of
which takes some number of arguments, and that many lists
of arguments. 
-/


/-
Bootstrap
-/
class has_pure (f : Type u → Type v) :=
(pure {α : Type u} : α → f α)

/-
Apply next step. Given a context (list, tree, option)
of functions of type (α → β), *where β can itself be a
function type*, and given a context of argument values
(of type α), compute and return a corresponding context 
of result values (of type β). Understand that if β is 
itself a function type, then what's returned here is
"another collection of functions." The seq function is
thus a means to apply a context containing functions
to a context containing arguments to get a context of
results, each of which itself could be a function of
one fewer arguments. 
-/
class has_seq (f : Type u → Type v) : Type (max (u+1) v) :=
(seq  : Π {α β : Type u}, f (α → β) → f α → f β)

-- infix notation for seq (** instead of * to not conflict)
infixl ` <**> `:60 := has_seq.seq

/-
And finally, the applicative functor typeclass. Note that
this typeclass (1) extends functor, thus inheriting its map
field; (2) it also extends has_pure and has_seq, as defined
just above, thus gaining pure and seq fields, each of the
requisite type. 

Finally, note that we implement the "map" function once and 
for all, for all instances of this typeclass. What does it 
do? It takes a function of type α → β, uses pure to turn it
into a (singleton) container of functions, and then uses the
seq (<*>) operator to map this container of functions (x)
over a container of argument values (y).
-/
class applicative (f : Type u → Type v) extends functor f, has_pure f, has_seq f :=
(map       := λ _ _ x y, pure x <**> y)

/-
The "applicative option" instance implements failure propagation.
-/

def pure_option {α : Type u} : α → option α 
| a := some a

def seq_option : Π {α β : Type u}, option (α → β) → option α → option β
| α β none _ := none
| α β (some func) oa := functor.map func oa  -- Use's functor's option_map!

instance : has_pure option := ⟨ @pure_option ⟩  
instance : has_seq option := ⟨ @seq_option ⟩ 
instance : applicative option := ⟨ ⟩ 

-- examples with one-argument functions
#reduce pure (nat.succ) <**> none
#reduce none <**> some 1
#reduce pure (nat.succ) <**> (some 1)
#eval pure (λ s, s++"!") <**> (some "Hello")

-- examples with multi-argument functions
#reduce pure (nat.mul) <**> some 3 
#reduce pure (nat.mul) <**> some 3 <**> some 4
#reduce pure (nat.mul) <**> none <**> some 4
#reduce pure (nat.mul) <**> some 3 <**> none

/-
Think of "none" as indicating a failure to compute
a function argument. What we've thus produced here,
in the form of the (applicative option) instance is 
a generalization of *function application,* where
a failure to produce the function to be applied, or
the failure to produce any of its arguments, yields
a failure return. In the case where the function and
all of its arguments are given, we just get ordinary
function application. 

Another way to think about this is that <**> handles
any error propagation "under the hood", leaving us as 
programmers with an notion of function application
that appears works pretty much as usual. This is an
example that shows how, by overloading applicative 
for option we obtain a new programming abstraction:
of ordinary function application (on the surface)
but with additional effects handling (in this case
error handling) being taken care of under the hood.
-/


/-
The applicative list typeclass instance.

In the preceding example, we had either zero or one
functions in an option and zero or one arguments in 
a second option. In the "normal" case, where both the
function and the argument are provided, we just apply
the function to the argument and return the result in
a "some _" option value. 

Now we turn to (applicative list) type. Here the seq
operator will take a list of zero or more functions and
a list of zero or more arguments and will return a list
containing the values obtained by applying each function 
in the function list to each value in the argument list.

The way to think about this is that we are implementing
a kind of non-deterministic, multi-valued computation. 
-/

def pure_list {α : Type u} : α → list α | a := [a]
def seq_list : Π {α β : Type u}, list (α → β) → list α → list β
| α β list.nil _ := list.nil
| α β (hf::tf) l := list.append (functor.map hf l) (seq_list tf l)
 
instance : has_pure list := ⟨ @pure_list ⟩  
instance : has_seq list := ⟨ @seq_list ⟩ 
instance : applicative list := ⟨ ⟩ 

-- tests with one-argument functions
#reduce seq_list [] [1,2,3] -- apply empty list of functions
#reduce [] <**> [1,2,3]      -- same thing using infix operator

#reduce seq_list [nat.succ] []
#reduce [nat.succ] <**> []

#reduce seq_list [nat.succ] [1,2,3]
#reduce [nat.succ] <**> [1,2,3]

#reduce seq_list (pure nat.succ) [1,2,3]
#reduce (pure nat.succ) <**> [1,2,3]

#reduce [nat.succ, nat.pred] <**> []
#reduce [nat.succ, nat.pred] <**> [1,2,3]

-- tests with two-argument functions!
#reduce (pure nat.add) <*> [1,2,3] 
#reduce (pure nat.add) <**> [1,2,3] <**> [2,4,6]
#reduce [nat.add, nat.mul] <**> [1,2,3] <**> [2,4,6]

/-
In practice we usually don't explicitly apply lists of
multiple functions directly to argument lists. Rather,
again in practice, we're usually interesting in applying
a single function to mult-valued arguments, so we use
"pure" to lift the function value into the list context
and then everything else is done by <**>, which, as we
have just seen, does tend to produce lists of functions
as intermediate results that get "applied" by <**> to
downstream argument lists (multi-valued arguments).
-/

end hidden


