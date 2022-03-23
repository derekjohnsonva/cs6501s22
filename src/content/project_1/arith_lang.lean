import .nat

namespace hidden

-- inductive bool_var : Type
-- | X 
-- | Y 
-- | Z

inductive nt_var
| V (n : ℕ)

open nt_var

def X := V 0
def Y := V 1
def Z := V 2

inductive nt_lang : Type 
| lit (n : nt)
| var (v : nt_var)
| dec (e : nt_lang) --evaluate e, decrement it, return the decremented val
| inc (e : nt_lang)
| add (e1 e2 : nt_lang)



def init : nt_var → nt
| v := nt.zero

-- prefer to apply an override function
def st_2 : nt_var → nt
| (V 0) := one
| _ := nt.zero

open nt_lang

def eval : nt_lang → (nt_var → nt) → nt
| (lit n) _ := n
| (var v) i := i v
| (nt_lang.dec e) i := dec (eval e i)
| (nt_lang.inc e) i := inc (eval e i)
| (nt_lang.add e1 e2) i := add (eval e1 i) (eval e2 i)

-- Notations
notation e1 + e2 := e1 e2



def override : (nt_var → nt) →  nt_var → nt → (nt_var → nt) :=
λ i v' b
  λ v, if (var_eq v v') then b else i v

end hidden