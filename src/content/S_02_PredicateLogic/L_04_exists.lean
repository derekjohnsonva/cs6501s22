/-
Elimination rules for exists ∃
-/

-- Demorgan Laws
theorem demorgan_1 : ∀ (b1 b2 : bool), bnot (b1 && b2) = (bnot b1) || (bnot b2) :=
-- proof by caase analysis 
begin
  intros b1 b2,
  cases b1,
  -- b1 case 1, ff
  cases b2,
  exact rfl,
  exact rfl,
  -- b1 case 2, tt
  cases b2,
  exact rfl,
  exact rfl,
end


/-
bool.rec_on : Π {motive : bool → Sort u_1} (n : bool), motive ff → motive tt → motive n
-/
#check @bool.rec_on

theorem demorgan_1' : ∀ (b1 b2 : bool), bnot (b1 && b2) = (bnot b1) || (bnot b2) :=
begin
  intros,
  apply bool.rec_on b1,
  apply bool.rec_on b2,
  exact rfl,
  exact rfl,
  apply bool.rec_on b2,
  exact rfl,
  exact rfl,
end

-- rec.on is the induction principle for any value of a data type
-- ∴ we can replace rec_on with the induction tactic

theorem demorgan_1'' : ∀ (b1 b2 : bool), bnot (b1 && b2) = (bnot b1) || (bnot b2) :=
begin
  intros b1 b2,
  induction b1,
  induction b2,
  exact rfl,
  exact rfl,
  induction b2,
  exact rfl,
  exact rfl,
end

-- The law of the excluded middle allows us to do case analysis on (P ∧ Q)
example : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ (¬ P) ∨ (¬ Q) :=
begin
  intros,
  split,
  assume h,
  have pnp := classical.em P,
  have qnq := classical.em Q,
  cases pnp,
  cases qnq,
  have pq := and.intro pnp qnq,
  contradiction,
  apply or.inr qnq,
  apply or.inl pnp,

  assume h,
  cases h,
  repeat { assume paq, cases paq, contradiction,},
end

-- The constructive logic of lean is a weaker logic than classical logic
-- ex. Without the law of the excluded middle we would not have been able
-- to perform the proof above

-- Existential quantification
def ev (n : ℕ) := n%2 = 0
example : ∃ (n : ℕ), ev n := 
begin
  apply exists.intro 0,
  -- exact rfl,
  unfold ev,
  exact rfl,
end

example : (∃ (n : ℕ), ev n) → (∃ l, ev (l + 2)) :=
begin
  assume h,
  cases h with w k,
  apply exists.intro (w),
  unfold ev at k,
  unfold ev,
  simp,
  exact k,
end

example (h k : ℕ → Prop) :
  (∃ (n : ℕ), (h n) ∧ (k n)) → 
  (∃ (n : ℕ), (h n)) :=
begin
  assume a,
  cases a with w p,
  apply exists.intro w,
  apply and.elim_left p,
end


-- Diff between case analysis and induction for ℕ
/-
nat.rec_on :
  Π {motive : ℕ → Sort u_1}
    (n : ℕ), 
    motive 0 → 
    (Π (n : ℕ), 
    motive n → motive n.succ) →
    motive n
-/
#check @nat.rec_on 


