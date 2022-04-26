universes u v

/-
We define a simple "binary tree of α values" data type
for use later in this file. Tuck it away in memory for now. 
-/

inductive tree (α : Type u)
| empty : tree
| node (a : α) (left right : tree) : tree



def aTree :=
  tree.node 0 
  (tree.node 1 tree.empty tree.empty) 
  (tree.node 2 tree.empty tree.empty)


namespace hidden

/-
We've seen a function for mapping a (different) function over a list.
-/

def list_map {α : Type u} {β : Type v} : (α → β) → list α → list β
| f []      := []
| f (h::t)  := (f h)::(list_map f t) 

/-
But we can imagine analogous functions over any kind of structure that
contains objects of some arbitrary other type. For example, here is a
function for mapping a function, f, over an object of type (option α),
for any type α. 
-/

def option_map {α : Type u} {β : Type v} : (α → β) → option α → option β
| f none      := none
| f (some a)  := some (f a) 

/-
As a third example, consider mapping over trees.
-/

/-
We can also write a function for mapping trees of α 
values to trees of β values in an analogous manner.
-/

def tree_map {α : Type u} {β : Type v} : (α → β) → (tree α) → (tree β)
| f tree.empty := tree.empty
| f (tree.node a l r) := tree.node (f a) (tree_map f l) (tree_map f r)


/-
What we're seeing are different implementations of "the same idea"
for mapping an element-level mapping function over a various types
of data structures containing such elements. The implementations of
these functions differ significantly; but look at their types. What
we see is that they're identical but for the types of containers we
envision transforming by the application  of element-level functions
to their contents.

def list_map    {α : Type u} {β : Type v} : (α → β) →   (list α)    → (list β)
def option_map  {α : Type u} {β : Type v} : (α → β) →   (option α)  → (option β)
def tree_map    {α : Type u} {β : Type v} : (α → β) →   (tree α)    → (tree β)

As usual, we can generalize by introducing a new parameter. 
But what is its type? Well, question: What is the type of list? Of option? Of tree? 
Answer: Each is Type u → Type u
We can't just add a parameter, m : Type u → Type u: the *implementations* differ
We have a common abstraction but with different implementations for different types

Ad hoc polymorphism, aka, overloading, aka generics, to the rescue! The new
pattern that we see here is that the parameter of the typeclass is no longer
a concrete type (such as bool or nat), but a polymorphic type builder, i.e.,
a value such as list α, option α, or tree α (each of type, Type → Type)
-/

class functor (m : Type u → Type v) :=
(map : ∀ {α β : Type u}, (α → β) → m α → m β)
-- (law1 : _)    -- how mapping identify function works
-- (law2 : _)    -- how mapping composition works

/-
As a shorthand notaton, we enable the developer to write
f<$>l as an expression that reduces to f mapped over l.
-/
local infixr ` <$> `:100 := functor.map

/-
Finally, we instantiate the typeclass once for each "type builder,"
such as list, option, or tree, over which we want to be able to map
functions using this notation. 
-/

instance list_mapper : functor list := ⟨ @list_map ⟩ 
instance option_mapper : functor option := ⟨ @option_map ⟩ 
instance tree_mapper : functor tree := ⟨ @tree_map ⟩

/-
We now have an overloaded map operator (in Haskell it's called fmap)
that can be used to map functions over lists, options, and trees. We
can now view lists, options, and trees as "functors" in the functional
programming (rather than category theory) sense of the term: that is,
as structured containers for objects of some source type that can be
"mapped" to corresponding structured containers for objects of some
destination type.
-/

#reduce nat.succ <$> [] 
#reduce nat.succ <$> [1,2,3]

#reduce string.length <$> ["Hello", "Lean!!!"]

#reduce nat.succ <$> option.none
#reduce nat.succ <$> option.some 0

#reduce nat.succ <$> (tree.empty)
#reduce nat.succ <$> aTree


#check @functor
/-
What we've done is to make list, option, and tree
into "members of the functor typeclass," thereby
overloading the operator that the typeclass defines
for each of these otherwise unrelated types.
-/

end hidden

/-
Now let's have a quick look at Lean's functor typeclass.
It's just like ours but it adds a second function that is
to be overloaded for each type (such as list or option) 
in the functor typeclass. 
-/

#check @functor
#print functor
/-
class functor (f : Type u → Type v) : Type (max (u+1) v) :=
(map : Π {α β : Type u}, (α → β) → f α → f β)
(map_const : Π {α β : Type u}, α → f β → f α := λ α β, map ∘ const β)

The const function (polymorphic in α and β) takes a value, a, of type
α, and yields a function that takes any value of type β and returns a.

The function, map ∘ const β, thus takes any value, a, of type α, and
returns a function that converts a list of β values into a list of a
values (not just α values, but constant a values).

def const (β : Sort u₂) (a : α) : β → α := λ x, a
-/


#check @list.map

instance : functor list := ⟨ @list.map, _ ⟩

def list_map_const 
  {α β : Type u} :
    α → list β → list α 
| a [] := []
| a (h::t) := a::list_map_const a t

-- E.g., replace each natural number in list with tt
#eval list_map_const tt [1,2,3]

instance list_functor : functor list := ⟨ @list.map, @list_map_const ⟩

#check @option.map

def option_map_const 
  {α β : Type u} :
  α → option β → option α 
| a option.none := option.none
| a (option.some b) := option.some a

instance : functor option := ⟨ @option.map, @option_map_const ⟩ 


#reduce nat.succ <$> [1,2,3]
#reduce ff <$ [1,2,3]
#reduce [1,2,3] $> ff


/-
One of the ways in which we can use the functor typeclass
is in defining generic versions of concrete functions. For
example, consider the simple increment function on natural
numbers. 
-/

def inc := 
  λ (n : nat), 
    n + 1

/-
We've seen how we can map such functions over lists of 
natural numbers. And, with this capability, we can define
a new function, here called inc_list_nat, that maps the
inc function over lists of nats. We can say that we have
lifted the inc function to be applicable to lists of nats.
-/

def inc_list_nat ( l : list nat) := list.map inc l

/-
Challenge: Generalize from this idea to write a generic
(ad hoc polymorphic) function, inc', that lifts inc 
to be be applicable to objects of any "functorial" type
over int. Given what we've got so far, for example, you  
should be able to apply inc_m_nat not only to objects of
type list nat, but also option nat, tree nat, and so on,
for any type constructor parameterized by the type, nat.
-/

def inc' {f : Type → Type} [functor f] (i : f nat) : f nat := 
  functor.map inc i

-- a generic increment operation on functorial data structures containing nats
example : inc' [1,2,3] = [2,3,4] := rfl 
example : inc' (some 1) = some 2 := rfl
instance : functor tree := ⟨ @hidden.tree_map, _ ⟩  -- you can fill in second field
example : inc' aTree =
            tree.node 
              1 
              (tree.node 2 tree.empty tree.empty) 
              (tree.node 3 tree.empty tree.empty) := rfl

/-
Generalize this function, from mapping *inc* over any functorial context
(data structure!) over values of type nat, to mapping *any function* of 
type α → β over any functorial context/container over values of type, α.
-/

def map_f {α β : Type u} {f : Type u → Type v} [functor f] : (α → β) → f α → f β  
| h i :=  functor.map h i


/-
Examples:
-/

def l_str := ["Hello", " Lean!"]
def o_str := some "Hello"
def t_str := tree.node "Hello" (tree.node " There!" tree.empty tree.empty) tree.empty

#reduce map_f string.length l_str
#reduce map_f string.length o_str
#reduce map_f string.length t_str

/-
Finally, let's look at the type of map_f to get a set of its nature.
In particular, look at this: (α → β) → f α → f β. What we've done is
to lift a "pure" function, h : α → β to one that takes a "functorial"
object, i : f α, and returns a functorial object of type f β. And by
the magic of typeclass resolution, we've overloaded this function for
three functorial types, namely list, option, and tree.  
-/