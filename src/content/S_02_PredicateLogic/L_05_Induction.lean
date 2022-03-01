#check @nat.rec_on

/-
nat.rec_on :
  Π {motive : ℕ → Sort u_1} 
  (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n
-/

def fac : ℕ → ℕ :=
begin
  assume n,
  apply nat.rec_on n,
  
  -- first machine, base case
  exact 1,

  -- inductive case
  assume n' facn',
  exact facn' * (n'+1),
end

example : fac 0 = 1 := rfl
example : fac 5 = 120 := rfl

def fac' : ℕ → ℕ 
| 0 := 1
| (nat.succ n') := (nat.succ n') * (fac' n')

example : fac' 0 = 1 := rfl
example : fac' 5 = 120 := rfl

def sum_to : ℕ → ℕ 
| 0 := 0
| (nat.succ n') := (nat.succ n') + (sum_to n')

example : sum_to 0 = 0 := rfl
example : sum_to 10 = 55 := rfl
example : sum_to 11 = 66 := rfl

theorem sum_thm : 
∀ (n : ℕ), 2 * sum_to n = n * (nat.succ n) :=
begin
  assume n,
  apply nat.rec_on n,
  -- base case
  exact rfl,
  -- inductive
  assume n' h,
  --unfold sum_to,
  simp [sum_to],
end

/-
Let's looks at some induction principles
-/


#check @bool.rec_on

/-
inductive bool : Type
| tt 
| ff

 Π {motive : bool → Sort u_1} (n : bool), motive ff → motive tt → motive n
 -/

#print punit
#check @punit.rec_on

/-
Π {motive : punit → Sort u_1} (n : punit), motive punit.star → motive n
-/

#check empty

/-
inductive empty : Type

Π {motive : empty → Sort u_1} (n : empty), motive n
-/

#check @punit.rec_on

/-
 Π {motive : punit → Sort u_1} (n : punit), motive 
-/

axioms (e : empty) (purple : empty → Prop)

example : ∀ (e : empty), purple e :=
begin
  assume e,
  apply empty.rec_on,
end

/-
Case analysis vs induction
-/

example : ∀ (e : empty), purple e :=
begin
  assume e,
  cases e,
end

example : ∀ (b : bool), band b tt = b :=
begin
  assume b,
  cases b,
  repeat {exact rfl},
end 

theorem sum_thm' : 
∀ (n : ℕ), 2 * sum_to n = n * (nat.succ n) :=
begin
  assume n,
  cases n,
  exact rfl,
  apply linarith,
end 