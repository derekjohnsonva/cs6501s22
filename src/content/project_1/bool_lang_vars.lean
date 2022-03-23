import .bool

namespace hidden 

-- DATA TYPE

/-
inductive bool_var 
| X
| Y 
| Z
-/

inductive bool_var 
| V (n : ℕ)

open bool_var

-- Test
def X := V 0
def Y := V 1
def Z := V 2

inductive bool_lang : Type
| TT : bool_lang
| FF : bool_lang
| var (v : bool_var) : bool_lang
| conj (e1 e2 : bool_lang) : bool_lang
| disj (e1 e2 : bool_lang) : bool_lang
| neg (e : bool_lang)


-- REFACTOR INTO TEST FILE
open bool_lang
def be1 := TT
def be2 := FF
def ve1 := var X
def be3 := conj be1 be2
def be4 := neg be3

open boo

def var_interp_1 : bool_var → boo
| v := boo.tt

/-
def var_interp_2 : bool_var → boo
| X := tt
| Y := ff
| Z := tt
-/

def var_interp_2 : bool_var → boo
| (V 0) := tt
| (V 1) := ff
| (V 2) := tt
| _ := tt

-- OPERATIONS
def eval : bool_lang → (bool_var → boo) → boo
| TT _ := tt
| FF _ := ff
| (var v) i := i v
| (conj e1 e2) i := and (eval e1 i) (eval e2 i)
| (disj e1 e2) i := or (eval e1 i) (eval e2 i)
| (neg e) i := not (eval e i)

-- NOTATIONS
notation b1 * b2 := conj b1 b2
notation b1 + b2 := disj b1 b2
prefix ! := neg

-- REFACTOR INTO TEST FILE
#reduce eval be4
#reduce eval (conj (disj be2 be4) be3)
#check X
#check (var X)
#reduce eval ((var X) * (var Y)) var_interp_1
#reduce eval ((var X) * (var Y)) var_interp_2

-- REFACTOR INTO TEST FILE
#reduce eval ((be2 + be4) * be3)

/-
How do we know that eval terminates?
-/

-- Non-terminating functions would be fatal
def bad : ℕ → false
| n := bad n    -- non-terminating recursion
#check (bad 3)  -- Yikes, a proof of false!

-- PROPERTIES?

/-
A property of an expression, e, is that e
evaluates to true. Let's call this property
evaluates_to_true.
-/
def evaluates_to_true : bool_lang → Prop 
| e := eval e = boo.tt
/-
This definition broke when we added an interpretation,
i, as a second argument to eval.
-/

example : evaluates_to_true TT :=
begin
  unfold evaluates_to_true,
  trivial,
end
--ditto last comment

example : evaluates_to_true (TT * FF) :=
begin
  unfold evaluates_to_true,
  simp [eval],
  apply rfl,  -- false
end
--ditto last comment

-- Property of an individual expression
example : evaluates_to_true (TT * TT) :=
begin
  unfold evaluates_to_true,
  simp [eval],
  apply rfl,  -- false
end
--ditto last comment


-- Property of the language as a whole: 
-- evaluation is deterministic.

-- HOMEWORK

/-
What deterministic means is that if you evaluate the same
expression twice (in the same environment) that you'll get
the same answer. A language with a statement that returns 
a truly random number wouldn't have this property. Show that
evaluation is deterministic for our "Bool" language.
-/

def eval_is_deterministic : 
  ∀ (e : bool_lang) (i : bool_var → boo) (b1 b2 : boo), 
  b1 = (eval e i) → 
  b2 = (eval e i) → 
  b1 = b2 := 
begin
  intros e i b1 b2 h1 h2,
  rw h1,
  rw h2,
end

def nat_eq : ℕ → ℕ → bool
| nat.zero nat.zero := bool.tt
| nat.zero _ := bool.ff
| _ nat.zero := bool.ff
| (nat.succ n') (nat.succ m') := nat_eq n' m'

def var_eq : bool_var → bool_var → bool
| (V n1) (V n2) := nat_eq n1 n2

def override : (bool_var → boo) → bool_var → boo → (bool_var → boo) :=
λ i v' b, 
  λ v, if (var_eq v v') then b else (i v) 


def init := var_interp_1
#reduce init X
#reduce init Y
#reduce init Z

def state_1 := override init X ff
#reduce state_1 X
#reduce state_1 Y
#reduce state_1 Z

def state_2 := override (override init X ff) Z ff
#reduce state_2 X
#reduce state_2 Y
#reduce state_2 Z


end hidden