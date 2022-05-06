import .functor

namespace hidden

instance : functor list :=
⟨
  @list.map,
  _
⟩ 

end hidden