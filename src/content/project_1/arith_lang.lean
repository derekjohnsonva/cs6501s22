import .nat

namespace hidden 

-- DATA TYPE

inductive nt_var 
| V (n : ℕ)

open nt_var

-- Test
def X := V 0
def Y := V 1
def Z := V 2

inductive nt_lang : Type
| lit (n : nt)
| var (v : nt_var) 
| dec (e : nt_lang) 
| inc (e : nt_lang) 
| add (e1 e2 : nt_lang)


-- REFACTOR INTO TEST FILE

def init : nt_var → nt
| v := nt.zero

-- prefer to apply an override function
def st_2 : nt_var → nt
| (V 0) := one
| _ := nt.zero

-- OPERATIONS
open nt_lang

/-
inductive nt_lang : Type
| lit (n : nt)
| var (v : nt_var) 
| dec (e : nt_lang) 
| inc (e : nt_lang) 
| add (e1 e2 : nt_lang)
-/

def eval : nt_lang → (nt_var → nt) → nt
| (lit n) _ := n
| (var v) i := i v
| (nt_lang.dec e) i := dec (eval e i)
| (nt_lang.inc e) i := inc (eval e i)
| (nt_lang.add e1 e2) i := add (eval e1 i) (eval e2 i)

-- NOTATIONS
notation e1 + e2 := add e1 e2


/-
def var_interp_1 : bool_var → boo
| v := boo.tt
-/

/-
-/

def override : (nt_var → nt) → nt_var → nt → (nt_var → nt) :=
λ i v n,
  λ x, if (var_eq x v) then n else i x

#reduce init X
#reduce init Y
#reduce init Z

def st_1 := override init X ff

#reduce st_1 X
#reduce st_1 Y
#reduce st_1 Z

def st_2 := override (st_1) Z ff

#reduce st_2 X
#reduce st_2 Y
#reduce st_2 Z


end hidden