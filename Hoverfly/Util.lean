module
public import Lean.Elab.Term

namespace Util

open Lean Elab Term SavedState

/--
Like `restoreState`, but *also* rewinds the name generator (and the macro-scope and
auxiliary-declaration generators) to the values captured in `s`.

`Core.SavedState.restore` deliberately restores only `env`/`messages`/`infoState` and
leaves `ngen` alone, because within a single elaboration thread the name generator only
ever moves forward, so it must not be rolled back. That assumption breaks for us: every
RPC request runs in a *fresh* `RequestM.runTermElabM` seeded from the `hoverfly`
snapshot's command state, so `ngen` is reset to the snapshot value on each call. Plain
`restoreState` then leaves `ngen` pointing *before* the `FVarId`/`MVarId`s that were
allocated (in a previous request) and baked into `s`'s metavariable context. The next
tactic re-issues those exact ids, clobbering the goal mvar and hypotheses in the restored
context — which surfaces as nonsense like `function expected ?α`. Restoring `ngen` makes
fresh allocations continue *past* everything already in `s`. -/
public def restoreStateFull (s : Lean.Elab.Term.SavedState) : Term.TermElabM Unit := do
  restoreState s
  modifyThe Core.State fun st => { st with
    ngen           := s.meta.core.ngen
    nextMacroScope := s.meta.core.nextMacroScope
    auxDeclNGen    := s.meta.core.auxDeclNGen }

end Util
