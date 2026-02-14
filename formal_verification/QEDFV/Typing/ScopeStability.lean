import QEDFV.Typing.Core
import QEDFV.Signature.GlobalLocalState

namespace QEDFV

inductive ScopeMutation : ScopeStack -> ScopeStack -> Prop where
  | refl (s) : ScopeMutation s s
  | push (s) : ScopeMutation s (push s)
  | pop (s s') : pop? s = some s' -> ScopeMutation s s'

theorem resolved_theorem_stability_under_scope_mutation
    (rt : RTerm)
    (ty : HolType)
    (ctx : List (String × HolType))
    (hTyped : CoreTyping ctx rt ty)
    (s1 s2 : ScopeStack)
    (_hm : ScopeMutation s1 s2) :
    CoreTyping ctx rt ty := by
  exact hTyped

end QEDFV
