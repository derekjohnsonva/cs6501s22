/-
Things about the and operator
if P and Q are props
then it is true that (P ∧ Q) is a proposition
Thus to prove (P ∧ Q) we must prove P and Q (p: P, q: Q)
-/
axioms P Q : Prop
-- These two checks say the same thing
#check P ∧ Q
#check and P Q

axioms (p : P) (q : Q)

example : P ∧ Q := and.intro p q
/-
structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)
-/

