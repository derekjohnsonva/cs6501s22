import .bool_semantics
import .bool_expr_test
import .bool_interp_test
namespace bool_lang

-- evaluating expressions under given interpretations
open bool_expr
#reduce eval (X * Y) all_true            
#reduce eval (X * Y) interp_0
#reduce eval ((be2 + be4) * be3) interp_3 
#reduce eval ((be2 + be4) * be3) interp_1
#reduce eval ((be2 + be4) * be3) interp_7

end bool_lang