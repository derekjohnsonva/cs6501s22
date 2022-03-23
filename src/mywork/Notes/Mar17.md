# Notes

Three domains of functions

## Math

examples of pure math functions: Mapping values to other values. $\{(0,0), (1,1), (2,2)\dots \}$

More simply, we would define the identity relationship as...
$$ \text{id} = {p: \N  \N | p.1 = p.2} $$

## Computational

$$\text{def  id}(n: nat) := n$$

## Logical/Declarative

```lean
inductive id_nat: nat -> nat -> Prop
| c: \all (n1 n2 : nat), n1 = n2 -> id_nat n1 n2
```

## What to do when we can't express a relationship with a function

Sometimes we will need to represent relations that do not fit in functions.
For example, the relation may not be *single valued*. In this case, use *Logical* definition.

For example, how would we express the mathmatical function $y = \pm \sqrt{x}$.
This function would include the sets $(9,3), (9,-3)$. This can not be represented with a computational function.

Using Logical definition we can define an inductive polymorphic type $sqrt$.

```lean
inductive sqrt : \Real -> \Real -> Prop
| constructor: \all(r1 r2: \Real), r1 = r2*r2 -> sqrt r1 r2
```

## Why Use Logical/Declarative

It looks like Logical defs are always more complicated. So why would we ever use them?

We use them because they allow us to do some of the things (like `while` loops) that we can not otherwise represent.
Imperative languages can not be expressed using pure computation.
