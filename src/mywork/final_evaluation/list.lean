import .functor
import .applicative

namespace hidden
open function

universes u v w

theorem list_map_id : 
  ∀ (T : Type u), list.map (@id T) = (@id (list T)) :=
begin
  assume T,
  apply funext,
  assume listT,
  rw [id],
  induction listT with d l h,
  simp [list.map],
  simp [list.map],
end

theorem list_comp_morphism :
  ∀ (α β γ : Type u) (func_f : α → β) (func_g : β → γ),
  list.map (func_g ∘ func_f) = list.map func_g ∘ list.map func_f :=
begin
  intros,
  apply funext,
  assume listA,
  simp [list.map],
end

instance : functor list :=
⟨
  @list.map,
  list_map_id,
  list_comp_morphism
⟩
----------------------------
-- APPLICATIVE FUNCTORS
----------------------------
def pure_list {α : Type u} : α → list α | a := [a]
instance : has_pure list := ⟨ @pure_list ⟩

def seq_list : Π {α β : Type u}, list (α → β) → list α → list β
| α β list.nil _ := list.nil
| α β (hf::tf) l := list.append (functor.map hf l) (seq_list tf l)
instance : has_seq list := ⟨ @seq_list ⟩ 

-- Prove the Applicative Functor Laws
theorem list_identity :  ∀ (T : Type u), has_seq.seq (has_pure.pure (@id T)) = @id (list T) :=
begin
  intros,
  apply funext,
  intro list_t,
  simp [has_seq.seq],
  simp [has_pure.pure],
  cases list_t with h t,
  simp [pure_list],
  simp [seq_list],
  simp [functor.map],
  
  simp [pure_list],
  simp [seq_list],
  simp [functor.map],
  apply list.append_nil,
end

theorem list_composition : ∀ (a b c : Type u) (u : list(a → b)) (v : list(b → c)) (w : list a),
  has_pure.pure (@function.comp a b c) <**> v <**> u <**> w = v <**> (u <**> w) :=
begin
  intros,
  simp [has_pure.pure],
  simp [has_seq.seq],
  simp [pure_list],
  simp [seq_list],
  simp [functor.map],
  sorry -- haven't figured this out
end




instance : applicative list :=
⟨⟩


end hidden