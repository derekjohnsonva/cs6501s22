import .bool
import .arith_lang

namespace bool_namespace
open bool_namespace
open hidden
-- inductive bool_var : Type
-- | X 
-- | Y 
-- | Z

inductive bool_var
| V (n : ℕ)

open bool_var

def X := V 0
def Y := V 1
def Z := V 2

inductive bool_lang : Type 
| TT : bool_lang
| FF : bool_lang
| var (v : bool_var) : bool_lang
| conj (e1 e2 : bool_lang) : bool_lang
| disj (el e2 : bool_lang) : bool_lang
| neg (e : bool_lang) : bool_lang
| eql (e1 e2 : nt_lang)

open bool_lang

def be1 := TT
def be2 := FF
def ve1 := var X
def be3 := conj be1 be2 
def be4 := neg be3

open boo

def var_interp_1 : bool_var → boo
| v := tt


def var_interp_2 : bool_var → boo
| (V 0) := tt
| (V 1) := ff
| (V 2) := tt
| _ := tt

def eval : bool_lang → (bool_var → boo) → boo
| TT _ := tt
| FF _ := ff
| (var v) f := f v
| (conj e1 e2) i := and (eval e1 i) (eval e2 i)
| (disj e1 e2) i := or (eval e1 i) (eval e2 i)
| (neg e1) i := not (eval e1 i)
| (eql e1 e2) := if ()

#reduce eval be4 var_interp_1
#reduce eval (conj (disj be2 be4) be3) var_interp_1
#reduce eval (conj (var X) (var Y)) var_interp_1

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
| e := eval e var_interp_1 = boo.tt

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
  intros e1 e2 h,
  -- reflexive
  
end

end bool_namespace