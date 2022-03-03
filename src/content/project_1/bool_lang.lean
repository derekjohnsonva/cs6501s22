import .bool

namespace hidden

inductive bool_var : Type
| X 
| Y 
| Z
open bool_var
inductive bool_lang : Type 
| TT : bool_lang
| FF : bool_lang
| var (v : bool_var) : bool_lang
| conj (e1 e2 : bool_lang) : bool_lang
| disj (el e2 : bool_lang) : bool_lang
| neg (e : bool_lang) : bool_lang

open bool_lang

def be1 := TT
def be2 := FF
def ve1 := var X
def be3 := conj be1 be2 
def be4 := neg be3

open boo

def eval : bool_lang → boo
| TT := tt
| FF := ff
| (var v) := 
| (conj e1 e2) := and (eval e1) (eval e2)
| (disj e1 e2) := or (eval e1) (eval e2)
| (neg e1) := not (eval e1)

#reduce eval be4
#reduce eval (conj (disj be2 be4) be3)

-- Non terminating recursions will not compile
def bad : ℕ → false
| n := bad n

#check (bad 3) -- cant have this because it is a proof of false

-- To get around the recursion check, use meta (now we are turing complete)
meta def bad' : ℕ → false
| n := bad n

-- PROPERTIES?
-- Property of an expression, e, evaluating to true. 
def evaluates_to_true : bool_lang → Prop
| e := eval e = boo.tt

example : evaluates_to_true TT := 
begin
  unfold evaluates_to_true,
  trivial
end

example : evaluates_to_true (conj TT TT) := 
begin
  unfold evaluates_to_true,
  trivial,
end

-- Formalize the calim that our language with synt and sem is deterministic
-- Do this for homework
def lang_is_det : ∀ (e1 e2 : bool_lang), e1 = e2 → eval e1 = eval e2 :=
begin
  apply 
end

end hidden