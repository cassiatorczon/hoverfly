module

public meta import Aesop.Frontend.Extension
public meta import Lean.Elab.Command
import Aesop
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


/- Aesop tactic integration -/
def foobar : Syntax := Syntax.atom SourceInfo.none "need to implement this"

def addMode (stxM : CommandElabM (TSyntax `tactic)) (md : Meta.TransparencyMode) :
  CommandElabM (TSyntax `tactic) := do
  let stx ← stxM
  match md with
  | .all => `(tactic| with_unfolding_all $stx:tactic)
  | .default => return stx
  | .reducible =>
    `(tactic| with_reducible $stx:tactic)
  | .instances =>
    `(tactic| with_reducible_and_instances $stx:tactic)
  | .none => `(tactic| with_unfolding_none $stx:tactic)

open Aesop RuleTacDescr RuleTerm in
def ruleTacDescrToStx (descr : RuleTacDescr) : CommandElabM (Option Syntax) :=
  match descr with
  | apply t md =>
    match t with
      | const decl =>
        addMode (`(tactic | apply $(mkIdent decl):ident)) md
      | term tm =>
        addMode (`(tactic | apply $tm:term)) md
  | constructors (constructorNames : Array Name) md =>
    return foobar--none --TODO
  | forward (t : RuleTerm) (immediate : UnorderedArraySet PremiseIndex)
      (isDestruct : Bool) => return foobar--none --TODO
  | cases (target : CasesTarget) md
      (isRecursiveType : Bool) (ctorNames : Array CtorNames) => return foobar--none --TODO
  | tacticM (decl : Name) => return foobar--none --TODO
  | ruleTac (decl : Name) => return foobar--none --TODO
  | tacGen (decl : Name) => return foobar--none --TODO
  | singleRuleTac (decl : Name) => return foobar--none --TODO
  | tacticStx (stx : Syntax) => return (some stx)
  | preprocess => return foobar--none --TODO
  | forwardMatches (ms : Array ForwardRuleMatch) => return foobar--none --TODO

open Aesop Aesop.Frontend in
open Lean.Elab.Command in
elab (name := addAesopTacs)
    -- attrKind:attrKind
    "add_aesop_tactics_to_hoverfly ": command => do
  let aesopRuleSets ← liftCoreM getDeclaredGlobalRuleSets
  for (setName, ruleSet, simpExtName, simprocExtName) in aesopRuleSets do
    -- let forwardRules := (ruleSet.forwardRules.nameToRule.toList.map Prod.snd).map TODO
    let normRuleDescrs := ruleSet.normRules.fold (fun rules rule => rule.tac :: rules) []
    let safeRuleDescrs := ruleSet.safeRules.fold (fun rules rule => rule.tac :: rules) []
    let unsafeRuleDescrs := ruleSet.unsafeRules.fold (fun rules rule => rule.tac :: rules) []
    let ruleDescrs := normRuleDescrs ++ safeRuleDescrs ++ unsafeRuleDescrs
    let rules ← ruleDescrs.filterMapM ruleTacDescrToStx
    rules.forM (fun tac => modifyEnv fun env => hoverflyTacticExt.addEntry env {raw:=tac})

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addAesopTacs
