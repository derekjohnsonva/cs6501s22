/-
- Data type -- inductive definition of a set of constructible terms
- Abstract data type (ADT) -- data type plus set of basic operations on values of this type
- Certified abstract data type (CADT) -- ADT with proofs of desired mathematical properties  

In this file, we see how to produce a CADT for Boolean algebra.
-/

namespace hidden

-- DATA TYPE

inductive boo
| ff 
| tt

open boo

-- OPERATIONS

-- unary operations

def id : boo → boo
| b := b

def not : boo → boo
| tt := ff
| ff := tt

def fals : boo → boo
| b := ff 

def troo : boo → boo
| b := tt 

-- binary operations

def and : boo → boo → boo
| ff ff := ff
| ff tt := ff
| tt ff := ff
| tt tt := tt

def or : boo → boo → boo
| ff ff := ff
| ff tt := tt
| tt ff := tt
| tt tt := tt

-- a ternary operation
def ite : boo → boo → boo → boo
|  ff t f := f
|  tt t f := t

-- PROOFS OF CRUCIAL PROPERTIES

-- example 

theorem demorgan1 : 
  ∀ (b1 b2 : boo), 
    not (and b1 b2) = or (not b1) (not b2) :=
  begin
    intros,
    -- case analysis on b1
    cases b1,
    -- for each case for b1, case analysis on b2
    repeat 
      { 
        cases b2,
        exact rfl,
        exact rfl
      }
  end

/-
As we saw during the lecture, bugs in our "code"
are revealed by an inability to prove that our
implementations of these operations have all the
key mathematical properties of the operations in
the Boolean algebra that we're trying to implement. 
Try slightly changing the definition of "and" or 
"or" for example, and see if, and if so how, the
changes break the proof(s).
-/

#reduce and tt ff

notation b1 * b2 := and b1 b2
notation b1 + b2 := or b1 b2
prefix ! := not

#reduce boo.tt * boo.ff
#reduce boo.tt + boo.ff
#reduce !(boo.tt + boo.ff)

-- infix `&`:10 := and
-- infix `|`:11 := or
-- prefix `!` := not

-- #reduce boo.tt & boo.tt
-- #reduce boo.tt | boo.ff
-- #reduce !boo.tt
end hidden