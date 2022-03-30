import .bool_interp
import .bool_expr_test

namespace bool_lang

open bool_var

-- some interpretations
def all_true : interp
| _ := tt

def all_false : interp
| _ := ff

def interp_0 : interp
| (V 0) := ff -- 0
| (V 1) := ff -- 0
| (V 2) := ff -- 0
| _ := tt

def interp_1 : interp
| (V 0) := ff -- 0
| (V 1) := ff -- 0
| (V 2) := tt -- 1
| _ := tt

def interp_2 : interp
| (V 0) := ff -- 0
| (V 1) := tt -- 1
| (V 2) := ff -- 0
| _ := tt

def interp_3 : interp
| (V 0) := ff
| (V 1) := tt -- 1
| (V 2) := tt -- 1
| _ := tt

def interp_4 : interp
| (V 0) := tt -- 1
| (V 1) := ff -- 0
| (V 2) := ff -- 0
| _ := tt

def interp_5 : interp
| (V 0) := tt -- 1
| (V 1) := ff -- 0
| (V 2) := tt -- 1
| _ := tt

def interp_6 : interp
| (V 0) := tt -- 1
| (V 1) := tt -- 1
| (V 2) := ff -- 0
| _ := tt

def interp_7 : interp
| (V 0) := tt -- 1
| (V 1) := tt -- 1
| (V 2) := tt -- 1
| _ := tt

end bool_lang