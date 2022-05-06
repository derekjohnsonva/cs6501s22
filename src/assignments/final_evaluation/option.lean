import .functor

namespace hidden

instance : functor option :=
⟨
  @option.map,
  _
⟩ 

end hidden