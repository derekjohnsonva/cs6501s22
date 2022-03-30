import .bool_expr
import .bool_var_test
namespace bool_lang 

-- some Boolean expressions
open bool_expr

def be0 := TT
def be1 := FF
def be2 := X * Y * X 
def be3 := be1 * be2
def be4 := !be3

end bool_lang