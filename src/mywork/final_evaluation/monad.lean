/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import .applicative
universes u v

namespace hidden

open function

class has_bind (m : Type u → Type v) :=
(bind : Π {α β : Type u}, m α → (α → m β) → m β)

export has_bind (bind)

@[inline] def has_bind.and_then {α β : Type u} {m : Type u → Type v} [has_bind m] (x : m α) (y : m β) : m β :=
do x, y

infixl ` >>= `:55 := bind
infixl ` >> `:55  := has_bind.and_then

class monad (m : Type u → Type v) extends applicative m, has_bind m : Type (max (u+1) v) :=
(map := λ α β f x, x >>= pure ∘ f)
(seq := λ α β f x, f >>= (<$> x))
 -- I will use pure here instead of `return` because `return` does not get created until the next line
(left_identity : ∀ (α β : Type u) (x : α) (f : α → m β),
  (pure x) >>= f = f x)
(right_identity : ∀ (α : Type u) (x : m α),
  x >>= pure = x)
(associativity : ∀ (α β γ : Type u) (mon_a : m α) (f : α → m β) (g  :β → m γ),
  (mon_a >>= f) >>= g = mon_a >>= (λ (x : α), f x >>= g))

@[reducible, inline] def return {m : Type u → Type v} [monad m] {α : Type u} : α → m α :=
pure

/- Identical to has_bind.and_then, but it is not inlined. -/
def has_bind.seq {α β : Type u} {m : Type u → Type v} [has_bind m] (x : m α) (y : m β) : m β :=
do x, y

end hidden