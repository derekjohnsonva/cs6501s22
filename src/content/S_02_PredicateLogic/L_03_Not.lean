/-
If P is a proposition then so is ¬P
ex. a proof of a = b implies a proof of a ≠ b

Law of the exclduded middle: if Q is a Prop, then ℚ ∨ ¬ℚ is true
-/

axiom excl_middle : ∀ (P : Prop), P ∨ ¬P

axiom KevinIsFromCville : Prop

example : KevinIsFromCville ∨ ¬KevinIsFromCville := excl_middle KevinIsFromCville

/-
to construct a proof of ∏ for some prop P, we
need to show that there can be no proof of P.
-/

namespace hidden
def not (P : Prop) : Prop := P → false
end hidden

example : ¬(0 = 1) := 
begin
  show not (0=1),
  assume h,
  cases h, -- could have used `trivial` if we wanted.
end

-- False implies everything: This is because if we
-- have a proof of false, our logic is inconsistent
-- and thus we just assume anything to be true.
example : false → KevinIsFromCville := 
begin
  intros f,
  trivial,
end

theorem exfalso : ∀ (P : Prop), false → P :=
begin
  intros p f,
  trivial,
end

theorem non_cont : ∀ (P : Prop), ¬ (P ∧ ¬P) :=
begin
  intros,
  assume P,
  cases P with left right,
  exact right left, -- Could have use `contradiction`
end

example : ∀ (P : Prop), ¬¬P → P :=
begin
  intros P,
  assume h,
  -- stuck!!! This is not a theorem in the constructive
  -- logic of Lean
end


#check @classical.em -- ∀ (p : Prop), p ∨ ¬p

example : ∀ (P : Prop), ¬¬P → P :=
begin
  intros P,
  assume h,
  have o := classical.em P,
  cases o,
  assumption,
  contradiction,
end

-- Proof by negation. I want to prove ¬P. Thus, assume P, show false.

-- Proof by contradiction. I want to show P. Thus, assueme ¬P, show false (ie a contradiction).
