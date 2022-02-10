/-
The purpose of this assignment is to develop
and deepen your understanding of the concepts
we've covered so far: equality of values/terms 
of any type, and conjunction of propositions.
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
to embed ∧. To do this we'll need to talk about
the introduction and elimination rules for or.
-/

namespace hidden

inductive or (P Q : Prop) : Prop
| intro_left  (Q : Prop) (p : P) : or
| intro_right (P : Prop) (q : Q) : or

theorem foo : or (3=3) (3=4) :=
or.intro_left rfl (3=4)

example : or (4=3) (3=3) :=
or.intro_right (4=3) rfl

end hidden

#check @or.intro_right

example : 3 = 3 ∨ 1 = 0 :=
or.intro_left (1=0) rfl

example : 1 = 0 ∨ 3 = 3 :=
or.intro_right (1=0) rfl

/-
#2. Let's using an inductive family to 
specify the successor relationship between
pairs of natural numbers. For any natural
numbers, n and m, (n, m) ∈ succ_rel if and
only if m = n + 1. Once you've done this,
state and prove the lemma, (0,1) ∈ succ_rel.
-/
-- Computation definitions of increment relation --
def incr (n : ℕ): ℕ := n + 1
#reduce incr 5

def incr' : ℕ → ℕ := 
λ (n : ℕ ),
n + 1
#reduce incr' 5

def incr'' : ℕ → ℕ := 
assume (n : ℕ),
n + 1
#reduce incr'' 5

def incr''' : ℕ → ℕ
| n := n + 1
#reduce incr''' 5

-- Declarative specification of the increment relation --
inductive succ_rel : ℕ → ℕ → Prop
| intro (n m : ℕ) (h : m = n + 1) : succ_rel n m

#check succ_rel 3 4
example : succ_rel 3 4 := succ_rel.intro 3 4 (eq.refl 4)
-- example : succ_rel 3 4 := succ_rel.intro 3 5 rfl -- This will produce an error

-- Proving that our computation definition satisfies the declarative specification
theorem def_equivalent : ∀ ( n m : ℕ), (m = incr n) ↔ succ_rel n m :=
begin
  intros,
  apply iff.intro _ _,
  assume h,
  exact succ_rel.intro n m h,
  -- solved the first goal, on to the the second
  assume h,
  cases h,
  unfold incr,
  exact h_h,
end

/- 
So then what is the point of this all? Why not always use computation?
Functions in lean are TOTAL. Meaning they assume they will work on
all values of the input data type.
Any relation can be a function if it is single valued. 
-/