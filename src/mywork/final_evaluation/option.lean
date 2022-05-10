import .functor
import .applicative
import .monad

universes u v w


namespace hidden

theorem option_map_id : 
  ∀ (T : Type u), option.map (@id T) = (@id (option T)) :=
begin
  assume T,
  apply funext,
  assume optionT,
  rw [id],
  induction optionT,
  simp [option.map_id],
  simp [option.map_id],
end

theorem option_comp_morphism :
  ∀ (α β γ : Type u) (func_f : α → β) (func_g : β → γ),
  option.map (func_g ∘ func_f) = option.map func_g ∘ option.map func_f :=
begin
  intros,
  apply funext,
  assume optionA,
  simp [option.map],
  induction optionA,
  simp [option.bind],
  simp [option.bind],
end

instance : functor option :=
⟨
  @option.map,
  option_map_id,
  option_comp_morphism,
⟩ 

----------------------------
-- APPLICATIVE FUNCTORS
----------------------------
-- Prove that an option is in the right type classes
def pure_option {α : Type u} : α → option α 
| a := some a
instance : has_pure option := ⟨ @pure_option ⟩ 
def seq_option : Π {α β : Type u}, option (α → β) → option α → option β
| α β none _ := none
| α β (some func) oa := functor.map func oa  -- Use's functor's option_map!
instance : has_seq option := ⟨ @seq_option ⟩ 

-- Prove the Applicative Functor Laws
theorem option_identity : ∀ (T : Type u), has_seq.seq (has_pure.pure (@id T)) = @id (option T) :=
begin
  intros t,
  apply funext,
  intro option_t,
  simp [has_seq.seq],
  simp [has_pure.pure],
  cases option_t,
  simp [pure_option],
  simp [seq_option],
  simp [functor.map],
  trivial,
  simp [pure_option],
  simp [seq_option],
  simp [functor.map],
  trivial,
end

theorem option_homomorphism : ∀ (α β: Type u) (x : α) (func : α → β), 
  (has_pure.pure func) <**> (has_pure.pure x) = (pure_option) (func x) := 
begin
  intros,
  simp [has_pure.pure],
  simp [has_seq.seq],
  simp [pure_option],
  simp [seq_option],
  simp [functor.map],
  simp [option.map],
  simp [option.bind],
end

theorem option_composition : ∀ (a b c : Type u) (u : option(a → b)) (v : option(b → c)) (w : option a),
  has_pure.pure (@function.comp a b c) <**> v <**> u <**> w = v <**> (u <**> w) :=
begin
  intros,
  simp [has_pure.pure],
  simp [has_seq.seq],
  simp [pure_option],
  simp [seq_option],
  simp [functor.map],
  cases v,
  simp [seq_option],
  trivial,
  cases u,
  simp [seq_option],
  trivial,
  cases w,
  simp [seq_option],
  trivial,
  simp [seq_option],
  trivial,
end

theorem option_interchange :  ∀ (a b : Type u) (x :  a) (u: option(a → b)), 
  u <**> (has_pure.pure x) =
  (has_pure.pure (λ an_F: (a → b), an_F x)) <**> u :=
begin
  intros,
  simp [has_pure.pure],
  simp [has_seq.seq],
  cases u,
  trivial,
  trivial,
end


instance : applicative option :=
⟨
  option_identity,
  option_homomorphism,
  option_composition,
  option_interchange,
⟩

-- MONAD STUFF
-- proving option is in the typeclass has_bind
def option_bind {α β : Type u}: option α → (α → option β) → option β :=
λ (ma : option α) a2mb, 
  match ma with
  | none := none
  | (some a) := a2mb a
  end

instance : has_bind option :=
⟨ 
  @option_bind
⟩

theorem option_left_identity : ∀ (α β : Type u) (x : α) (f : α → option β),
  has_bind.bind (has_pure.pure x) f = f x :=
begin
  intros,
  simp [has_pure.pure],
  simp [pure_option],
  simp [has_bind.bind],
  simp [option_bind],
end

theorem option_right_identity : ∀ (α : Type u) (x : option α),
  has_bind.bind x has_pure.pure = x :=
begin
  intros,
  simp [has_pure.pure],
  simp [has_bind.bind],
  simp [option_bind],
  cases x,
  simp [option_bind._match_1],
  simp [option_bind._match_1],
  simp [pure_option],
end 

theorem option_monad_associativity : ∀ (α β γ : Type u) (mon_a : option α) (f : α → option β) (g  :β → option γ),
  has_bind.bind (has_bind.bind mon_a f) g =
    has_bind.bind mon_a (λ (x : α), has_bind.bind (f x) g)
:=
begin
  intros,
  simp [has_bind.bind],
  simp [option_bind],
  cases mon_a,
  simp [option_bind._match_1],
  simp [option_bind._match_1],
end
-- Instance of Option for Monad Type Class
instance : monad option :=
⟨
  option_left_identity,
  option_right_identity,
  option_monad_associativity
⟩ 

end hidden