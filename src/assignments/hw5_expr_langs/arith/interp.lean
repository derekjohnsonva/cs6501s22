import .var

namespace arith

-- type
def var_interp := var → nat

-- operations
def override : 
  var_interp → 
  var → nat → 
  var_interp :=
λ i v n,
  λ x, 
    if (var_eq x v) 
    then n 
    else i x


end arith