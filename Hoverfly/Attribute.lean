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

/-
-- -- Below is modified from Aesop :
namespace Attribute

namespace Parser

declare_syntax_cat Hoverfly.attr_tacs

declare_syntax_cat Hoverfly.tac_expr (behavior := symbol)

syntax term : Hoverfly.tac_expr -- TODO

-- syntax Aesop.rule_expr : Hoverfly.attr_tacs
-- syntax "[" Aesop.rule_expr,+,? "]" : Hoverfly.attr_tacs
syntax Hoverfly.tac_expr : Hoverfly.attr_tacs --TODO

syntax (name := hoverfly) "hoverfly " Hoverfly.attr_tacs : attr

end Parser

-- structure AttrConfig where
--   tacs : Array Syntax
--   deriving Inhabited

-- namespace AttrConfig

-- def «elab» (stx : Syntax) : Lean.Elab.Term.TermElabM AttrConfig :=
--   withRef stx do
--     match stx with
--     | `(attr| hoverfly $e:Hoverfly.attr_tacs) => do
--       let r ← RuleExpr.elab e |>.run $ ← ElabM.Context.forAdditionalGlobalRules
--       return { rules := #[r] }
--     | `(attr| hoverfly [ $es:Hoverfly.attr_tacs,* ]) => do
--       let ctx ← ElabM.Context.forAdditionalGlobalRules
--       let rs ← (es : Array Syntax).mapM λ e => RuleExpr.elab e |>.run ctx
--       return { rules := rs }
--     | _ => throwUnsupportedSyntax

-- end AttrConfig


-- initialize registerBuiltinAttribute {
--   name := `hoverfly
--   descr := "Register a declaration as a Hoverfly rule."
--   applicationTime := .afterCompilation
--   add := λ decl stx attrKind => withRef stx do
--     let rules ← runTermElabMAsCoreM do
--       let config ← AttrConfig.elab stx
--       return config.tacs
--     for rule in rules do
--       addGlobalRule rsName rule attrKind (checkNotExists := true)
--   erase := λ decl =>
--     let ruleFilter :=
--       { name := decl, scope := .global, builders := #[], phases := #[] }
--     eraseGlobalRules RuleSetNameFilter.all ruleFilter (checkExists := true)
-- }

end Attribute

-/
