import .arith_expr

open nat_var
open nat_expr


-- variables

def X := Δ 0
def Y := Δ 1
def Z := Δ 2
def W := Δ 0  -- W and X are the same variable

-- an interpretation

def init : nat_var → nat
| v := nat.zero

-- test interpretation override 

example : init X = 0 := rfl
example : init Y = 0 := rfl
example : init Z = 0 := rfl

-- "assignment operation"
-- {X = 0, Y = 0, Z = 0}
def st_1 := override init X 2
-- {X = 2, Y = 0, Z = 0}

example : st_1 X = 2 := rfl
example : st_1 Y = 0 := rfl
example : st_1 Z = 0 := rfl

-- "assignment operation"
-- {X = 2, Y = 0, Z = 0}
def st_2 := override (st_1) Z 5
-- {X = 2, Y = 0, Z = 5}

example : st_2 X = 2 := rfl
example : st_2 Y = 0 := rfl
example : st_2 Z = 5 := rfl

-- example expressions

def e1 := [0] -- overloaded []: literal
def e2 := e1 + e1
def e3 := e2++
def e4 := [X] + [Y] + [Z]   -- []: "var" expression

-- test evaluation

example : eval e3 init = 1 := rfl
example : eval e4 st_2 = 7 := rfl