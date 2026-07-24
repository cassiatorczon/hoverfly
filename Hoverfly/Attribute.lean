module

public meta import Lean.Elab.Command
import Batteries.Linter.UnreachableTactic

public meta section

open Lean Elab Command

-- todo: this lets us add lemmas, not tactics

initialize hoverflyLemmaExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.flatten
  }

/-- Every `@[hoverfly]`-tagged lemma, in registration order. -/
def hoverflyLemmas (env : Environment) : Array Name := hoverflyLemmaExt.getState env

initialize registerBuiltinAttribute {
  name := `hoverflyLemma
  descr := "register a lemma for application in hoverfly"
  add := fun declName stx kind => do
    let info ← getConstInfo declName
    modifyEnv fun env => hoverflyLemmaExt.addEntry env declName
}

initialize hoverflyTacticExt : SimplePersistentEnvExtension
  (TSyntax `tactic) (Array (TSyntax `tactic)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.flatten
  }

def hoverflyTactics (env : Environment) : Array (TSyntax `tactic) :=
  hoverflyTacticExt.getState env

syntax tac_list := "[" tactic,+,? "]"

namespace TacList

def «elab» (stx : TSyntax `tac_list) : TermElabM (Array (TSyntax `tactic)) :=
  withRef stx do
    match stx with
    | `(tac_list | [$ts:tactic,*]) =>
      return ts
    | _ => throwUnsupportedSyntax

end TacList

open Lean.Elab.Command in
elab (name := addTacs)
    -- attrKind:attrKind
    "add_hoverfly_tactics " e:tac_list : command => do
  let tacArray ← liftTermElabM (TacList.elab e)
  tacArray.forM (fun tac => modifyEnv fun env => hoverflyTacticExt.addEntry env tac)

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addTacs
