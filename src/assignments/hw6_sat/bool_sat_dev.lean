import .bool_expr
import .bool_var
import .bool_semantics
import .set_T

namespace bool_lang
open bool_lang.bool_expr
open bool_lang.bool_var

-- Workspace for top-down development

def reduce_or : list bool → bool
| list.nil := ff
| (h::t) := bor h (reduce_or t)

def get_interp_values : bool_expr → list interp → list bool
| _ list.nil := []
| e (h::t) := (eval e) h :: get_interp_values e t


-- Jack: returns list of interpretations for set of variables
def interps_of_vars : cset bool_var → list interp
| list.nil := [λ v, ff]
| (h::t) := 
  let l := interps_of_vars t in
    list.append 
      l 
      (list.map (λ i, override i h tt) l)

-- Returns set of all distinct variables in a given expr, e
def get_var_set : bool_expr → cset bool_var
| TT := []
| FF := []
| (var v) := [v]
| (conj e1 e2) := union var_eq (get_var_set e1) (get_var_set e2)
| (disj e1 e2) := union var_eq (get_var_set e1) (get_var_set e2)
| (not e) := get_var_set e

def is_satisfiable : bool_expr → bool
| e := reduce_or 
  (
    get_interp_values 
      e 
      (
        interps_of_vars 
          (
            get_var_set 
              e
          )
      )
  )

/-
Specification, existential quantification
-/
def satisfiable' (e : bool_expr) : Prop :=
  ∃ (i : interp), eval e i = tt

/-
Specification, computational case analysis
-/
def satisfiable (e : bool_expr) : Prop :=
  is_satisfiable e = tt

end bool_lang
