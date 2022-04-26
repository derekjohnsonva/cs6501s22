-- 
namespace hidden 

/-
In this lecture we solve the problem of ensuring that
argument values to foldr are properly coordinated. In the 
process we introduce *ad hoc* polymorphism (also called
"operator overloading") as distinct from the *parametric*
polymorphism (also called generics in Java and template
classes in C++) that we've been using all semester long. 

- We introduce a new mechanism, typeclasses, which support 
ad hoc polymorphism
- We see how instances of a given typeclass provide the
information needed to implement an overloaded operator for
a specified type of element
- We see how Lean's support for typeclasss enables lookup
and passing of typeclass *instances* as implicit arguments
- We then see how these ideas support the representation
of abstract algebraic structures.
- As an example, we formalize the abstract algebraic 
structure known as a "monoid," as a typeclass, and we 
define a typeclasses instance to establish the monoid
comprising the natural numbers under addition with 0 
as a proven identity element. 
-/


/-
As a first motivating example, suppose that we want
to abstract the concept of being an inhabited type.
A type is inhabited if it has at least one value, so
one way to show that a type is inhabited it to give
a particular value of that type.

For example, we could show that the bool, nat, and
string types are inhabited by creating instances of
the following polymorphic type, with bool, nat, and
string as values of α. 

What this type says is that you can have an instance
of this type by applying the mk constructor to some
specific value of the α type.
-/
inductive inhabited''' (α : Type)
| mk (a : α) : inhabited'''

/-
We can thus "show" that bool, nat, and string are
all inhabited types by creating one instance of this
polymorphic type for each of the type values, bool,
nat, and string.
-/
example : inhabited''' bool := inhabited'''.mk tt
example : inhabited''' nat := inhabited'''.mk 0
example : inhabited''' string := inhabited'''.mk ""


/-
The next concept in line is new syntax for defining
a new type in the special case where the type has
just one constructor. In this case, we can use the
"structure" keyword instead of inductive. Then any
type arguments followed (in this example) by a :=
and then the definition of the *one* constructor 
that is allowed when using "structure." First the
name is given, then :: then the *named fields* of
the type are listed. The essential benefit of using
"structure" is that Lean converts the field names
into "accessor" functions to retrieve the field
values from an instance of such a structure (a.k.a.,
"struct" in C and C++ or "record" in a relational
database). Here then is an example equivalent to
the preceding example except that "a" can now be
used as the name of a function that takes an
instance and returns the value of its "a" field. 
-/
structure inhabited'' (α : Type)  :=
mk  :: (a : α)

def bool_inhab'' : inhabited'' bool := inhabited''.mk tt
def nat_inhab'' : inhabited'' nat := inhabited''.mk 0
def string_inhab'' : inhabited'' string := inhabited''.mk ""

open inhabited''

#eval a string_inhab''

/-
Lean also provides a nice "dot" notation for applying a
function to an object, so we can also write the following
equivalent expression
-/

#eval bool_inhab''.a    -- expect tt
#eval nat_inhab''.a     -- expect 0
#eval string_inhab''.a  -- expect ""


/-
Our next step is easy: When defining a structure type, you
can leave out the constructor name and :: and Lean will use
"mk" as a default constructor name
-/
example : inhabited'' bool := inhabited''.mk tt
structure inhabited' (α : Type) := (a : α)
example : inhabited' bool := inhabited'.mk tt


/-
With what we've done already, we can now write a
(parametrically) polymorphic function, "default,""
that returns a defaul value for any *type*. A type
is the argument to "default" and its return value 
is a *value* of that type. 

Of course not every type is inhabited, so not every
type can have a default value. We need a way to limit
the application of the default function to types for
which some value shows that the type is inhabited.

One way to impose this constraint on the type that
can be passed to the "default" function is to have
it take, as a second argument, an instance of the
type, (inhabited α), for whatever type, α, is given
as its first argument.
-/

def default''' (α : Type) (i : inhabited'' α): α := i.a

#reduce default''' bool bool_inhab''
#reduce default''' nat nat_inhab''
#reduce default''' string string_inhab''

/-
We can make these function applications expressions even
easier to read by making the first type argument implicit,
letting it be inferred from the second inhabited' argument.
-/
def default'' {α : Type} (i : inhabited'' α): α := i.a

#reduce default'' bool_inhab''
#reduce default'' nat_inhab''
#reduce default'' string_inhab''



/-
Now we turn the world on its head. What if we wanted to
keep the first *type* argument explicit and have the value
of the second, instance, argument implicit? How could a
value argument be passed implicitly? What we'd need is
a mechanism that could find an instance value based on 
the type argument. Voila, typeclasses!
-/


/-
A typeclass is an ordinary structure type that supports
this kind of lookup operation. The mechanism allows us
to associate typeclass instances with types and to look
them up based on these types so that they can be passed
implicitly to functions that require them. 

The following example continues our running example. We
append _ to the typename only to distinguish it from our
final solution, following this example.
-/

/-
The verbose way to tell Lean that a structure type should
support instance lookup is to annotate the "structure"
definition with @[class], as seen next.

-/
@[class] structure inhabited_ (α : Type) :=
(a : α)

/-
With inhabited_ defined as a class, we can now create
values of this type -- instances -- while also having
them entered into Lean's database of available instances
of this class.
-/
instance bool_inhab_ : inhabited_ bool := inhabited_.mk tt
instance nat_inhab_ : inhabited_ nat := inhabited_.mk 0
instance string_inhab_ : inhabited_ string := inhabited_.mk ""

/-
Finally now we can rewrite default so that it takes a
type argument explicitly and *implicitly* finds and
passes instances, if they've been defined, for the given
type argument values. 
-/
def default (α : Type) [i : inhabited_ α] := i.a
/-
You can see here that α is an explicit type argument. The
square brackets ask Lean to find an implicitly pass an
instance of type inhabited_ α. If not instance for α 
has been registered, then Lean will issue and error
message saying that it can't synthesize (find) the
required typeclass instance. 
-/

#eval default bool    -- implicitly receives bool_inhab_
#eval default nat     -- implicitly receives nat_inhab_
#eval default string  -- implicitly receives string_inhab_
#eval default empty   -- OOPS. No instance for empty type
#eval default int     -- OOPS. No instance for int type


/-
As a final syntactic sugar, you can write "class <name>"
rather than @[class] structure <name>.
-/
class inhabited (α : Type) :=
(a : α)

/-
You don't even have to give instances names, since
they will be looked up and passed implicitly.
-/
instance : inhabited bool := inhabited.mk tt
instance : inhabited nat := inhabited.mk 0
instance : inhabited string := inhabited.mk ""


/-
A takeaway message is that we can now use the type
system to enforce conditions on the type values that
are passed to a function, restricting them only to
those type values for which metadata *for that type*
have been registered as typeclass instances. 
-/

/-
We now show how these ideas can be used to solve the
problem we had with our initial type signature for 
the right fold function: it is possible for clients 
to pass inconsistent operator and identity element
arguments when they are passed separate. We can do
much better.

A key is to recognize that the same algebraic 
structure: a binary operator on values of a type
and a bona fide identity element for that operator.
Algebraists call such a structure a monoid. We've
already seen that the natural numbers along with
addition and 0 are a monoid; as are the natural
numbers along with multiplication and 1; as well
as Booleans with and and tt; along with strings,
the append operation, and "".  
-/

/-
Our solution is to define monoid as a typeclass,
with instances for each type of value on which 
we can impose a monoid structure by providing
a correspond binary operation, identity element,
and proof that it really is an identity element.
-/

class monoid (α : Type) :=
(op : α → α → α)
(id : α)
(pf : ∀ (a : α), op a id = a) 

instance add_monoid : monoid nat :=
monoid.mk 
  nat.add 
  0 
  nat.add_zero

instance and_monoid : monoid bool := 
monoid.mk 
  band 
  tt 
  begin 
    intros, cases a, repeat { apply rfl },  
  end 

instance append_monoid : monoid string := 
monoid.mk 
  append 
  "" 
  begin 
    sorry
  end 

/-
We are now completely positioned to write a
beautiful parametric and ad hoc polymorphic
foldr function that (1) takes a type (of list
value) implicitly, (2) looks up an instance,
if there is one for that type and passes it
implicitly, and (3) uses the field values
to access the operator and identity element
to be associated with that type.
-/


def foldr {α : Type} [m : monoid α] : list α → α 
| [] := m.id
| (h::t) := let x:= m.op in x h (foldr t)

#eval foldr [tt,ff,tt]
#eval foldr [tt,tt,tt]
#eval foldr [1,2,3,4,5]
#eval foldr ["Hello", ", ", "Lean", "!"]

/-
We've now understood ad hoc polymorphism,
its use to to define typeclasses and instances
that enable implicit instance lookup, and to use
these capabilities to impose *constraints* on
the values of arguments passed as types: in this
case that the type has an overloaded definition
of a monoid algebraic structure for that type.
You can now read the definition of foldr as 
saying "if you give me any type and if I can 
find a monoid instance for that type, then I
will return a function that takes a list of
values of that type and reduces it to a single
value of that type using the operator and the
identity element found in that type instance."
With all this machinery in place, we now get
an elegant, easy to use foldr function that is
in effect overloaded to apply to values of at
least three different types. If you want to do
foldr operations on lists of values of other
types, just define monoid type instances for
them. Yay! 
-/

end hidden