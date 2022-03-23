/-
The purpose of this assignment is to give you some
practice "pulling together all the pieces" that we've
covered in this class so far to produce examples of 
modular building blocks for the construction of "certified"
systems, by which we mean systems with proven properties.
In this homework, the properties that we care about have to 
do with correctness-of-implementation-of-basic-operations.
If you've made any mistakes, you won't be able to prove
the properties of these "algebras." If you prove all the
properties as required, you can be sure you've got them
right!

Develop certified abstract data types for (1) your own 
implementations of boolean algebra (build from our boo
type and its associated functions), and for (2) natural
number arithmetic (building from our nt type). 

Each of these "modules" must include the following:
- data type
- operations
- notations (make sure precedence and associativity are correct)
- NEW: test/demo cases represented as propositions with proofs
- proofs of essential properties as discussed in class
-/