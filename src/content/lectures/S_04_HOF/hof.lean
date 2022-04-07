
/-
Let's look at three functions, each transforming
one list into another by converting each element
in the argument list, through the application of
a function, into a corresponding element in the
resulting list. Try to see the commonalities and
the dimesions of variation. 
-/


-- map each n in argument list to n+1 in result
-- e.g., add_1 [1, 2, 3] = [2, 3, 4]
def add_1 : list nat → list nat
| [] := []
| (h::t) := (h+1)::add_1 t

example : add_1 [] = [] := rfl
example : add_1 [1, 2, 3] = [2, 3, 4] := rfl 


-- map each n in argument list to n+2 in result
-- e.g., add_2 [1, 2, 3] = [3, 4, 5] 
def add_2 : list nat → list nat
| [] := []
| (h::t) := (h+2)::add_2 t

#reduce add_2 []
#reduce add_2 [1, 2, 3]

def sqr_list : list nat → list nat
| [] := []
| (h::t) := (h * h)::sqr_list t

#reduce sqr_list []
#reduce sqr_list [1, 2, 3]

-- There is a lot of repeated code here.
-- We want a higher order function that will perform a nat → nat operation on every entry in a list
-- A higher order function is a function that takes a function as an argument
def f  : (nat → nat) → list nat → list nat
| _ [] := []
| fn (h::t) := (fn h)::(f fn t)
-- Test this code. This is essentially our add_1 function.
#reduce f (λ n, n + 1) [1, 2, 3]

-- This form is more general still. Instead of being tied to nats, we can now operate on any type in univers u
universe u 
def map {α β : Type u} : (α → β) → list α → list β
| fn [] := []
| fn (h::t) := (fn h)::(map fn t)
-- The more general 
#reduce map (λ n, n + 1) [1, 2, 3]
-- TODO: HW is to use map in our sat solver
-- Basically this is mapping interpretations to boolean values
-- map (eval e) l -- where e is an expression and l is a list of interpretations

#reduce map (λ n, n % 2) [1,2,3,4,5]  -- expect is [1,0,1,0,1]
-- mapping that will take a list of strings and return the length of the string
#reduce map (λ s, string.length s) ["Hello", "Lean"] -- expect [5, 4]

-- Now we will look at a similar higher order function, fold
-- We will first do the folding with a normal funciton
def sum_of_elems : list nat → nat 
| [] := 0
| (h::t) := h + (sum_of_elems t)

#reduce sum_of_elems [0,1,2,3,4,5] -- should be 15
--Folding with a different normal function. This shows that folding has an issue that map did not
-- We have to say what to do with the base case
def prod_of_elems : list nat → nat 
| [] := 1
| (h::t) := h * (prod_of_elems t)

#reduce prod_of_elems [0,1,2] -- should be 0
#reduce prod_of_elems [1,2,3] -- should be 6


-- How we will try to write this higher order function
-- Our arguments are a binary operator, a sigle value to return in the base case, and a list of nats
def reduce_elems : (nat → nat → nat) → nat → list nat → nat
| _ id [] := id
| f id (h::t)  := f h (reduce_elems f id t)

#reduce reduce_elems nat.add 0 [0,1,2,3] -- Should be the addition of all elements i.e. 6
#reduce reduce_elems nat.mul 1 [1,2,3] -- Should be the multiplication of all elements i.e. 6

-- Now lets try to generalize our reduce_elems to work with all types
-- we will need a reducer argument (often called `foldr`) 
-- This function could be called reduce
def reduce {α β : Type u} : (α → β → β) → β → list α → β
| _ id [] := id
| f id (h::t) := f h (reduce f id t)

-- should work on the `reduce_elems` examples
#reduce reduce nat.add 0 [0,1,2,3] -- Should be the addition of all elements i.e. 6
#reduce reduce nat.mul 1 [1,2,3]
-- More interesting example
#reduce reduce (λ s i, string.length s + i) 0 ["Hello", "lean"] -- Should be 5 + 4 = 9
#reduce reduce (λ s i, string.length s + i) 0 ["a", "man", "walked", "into", "a", "bar"] -- Should be 18


-- Write a function that computes the number of odd numbers in a list of natural numbers
#reduce reduce nat.add 0 (map (λ n, n%2) [1,2,3,4,5])

-- Write a map reduce function that is completely generic
-- args are reduce_op reduce_id map_fn list
def map_reduce {α β γ : Type u} : (β → γ → γ) → γ → (α → β) → list α → γ
| red_op id map_fn l := reduce red_op id (map map_fn l)

#reduce map_reduce nat.add 0 (λ n, n%2) [1,2,3,4,5] -- should be 3

/-
What does it mean for something to be an id for a reduction???
given...
```
γ : Type
op : γ → γ → γ 
id : γ
```
we want to construct a proof that `id` is the base case to `op`
```
pf : ∀ (a id : γ), op a id = a
```
One way to do this would be to provide a proof of pf as an argument to reduce
Another way is to see that this is the algebraic structure of a monoid
```
inductive monoid (α : Type u) (id : α) (∀ (b : α), op b id = b)

```
It would be much better if we could just pass one of these monoids to the reduce function
-- What we ultimately want is a way to 
-/
