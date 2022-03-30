import .bool_var

namespace bool_lang
open bool_var

/-
We will represent an interpretation as a function
from Boolean variable (bool_var) to Boolean value.
We then provide an override function that takes a
given interpretation, i, a variable, v, and a new
value, t, and that returns a new interpretation, i',
equivalent to i except for the the new maplet from 
v to t.
-/

-- DATA TYPE

def interp := bool_var → bool

-- OPERATIONS

/-
Note that to make our code easier to read and 
understand, we're using our new type name here.
-/
def override : interp → bool_var → bool → interp :=
λ i v' b, 
  λ v, if (var_eq v v') then b else (i v)

end bool_lang
