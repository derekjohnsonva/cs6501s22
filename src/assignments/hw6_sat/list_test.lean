/-
inductive list (T : Type u)
| nil : list
| cons (hd : T) (tl : list) : list
-/

#check @list

#check list nat
#check list bool

open list

def b_empty : list bool := nil
def one_list : list nat := 
    cons 
      0 
      nil
def two_list : list nat := 
    cons 
      1
      (
        cons
          0
          nil
      )

-- notation
def two_list' : list nat := 1::0::nil
def two_list'' := [1, 0]