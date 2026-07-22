module

public meta import Aesop.Frontend.Extension
public meta import Aesop.RuleTac
public meta import Aesop.Util.Tactic.Unfold
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

/-- Wraps a tactic `tac` so that it runs at a desired transparency mode. -/
def withTransparencyStx (md : Meta.TransparencyMode) (tac : TSyntax `tactic) :
    TSyntax `tactic :=
  match md with
  | .default   => tac
  -- `.none` (no unfolding at all) has no core tactic combinator; leave the tactic at default
  -- transparency as a best effort.
  | .none      => tac
  | .reducible => Unhygienic.run `(tactic| with_reducible $tac:tactic)
  | .instances => Unhygienic.run `(tactic| with_reducible_and_instances $tac:tactic)
  | .all       => Unhygienic.run `(tactic| with_unfolding_all $tac:tactic)

/-- The term an Aesop rule was built from, as it would appear in a tactic call. -/
def ruleTermToStx : Aesop.RuleTerm → TSyntax `term
  | .const decl => mkIdent decl
  | .term t => t

/-- A term `@d _ ⋯ _` (with one hole per argument of `d`'s type) that matches any fully-applied
occurrence of `d`. -/
def mkHeadPattern (d : Name) : CommandElabM (TSyntax `term) := do
  let info ← getConstInfo d
  let arity ← liftTermElabM <| Meta.forallTelescopeReducing info.type
    fun args _ => return args.size
  let holes ← (Array.range arity).mapM fun _ => `(_)
  return Syntax.mkApp (← `(@$(mkIdent d):ident)) holes

open Elab.Tactic Aesop in
/-- Runs the compiled Aesop rule tactic stored in declaration `decl`, which must have type
`TacticM Unit`, `Aesop.RuleTac`, `Aesop.SingleRuleTac`, or `Aesop.TacGen`. Aesop rules of these
kinds are metaprograms, so they have no tactic syntax of their own; this tactic makes them invocable
from a tactic block (classifying `decl` by its type exactly as Aesop's `RuleBuilder.tacticCore`
does). When the rule produces several alternative rule applications (e.g.
`Aesop.BuiltinRules.applyHyps` produces one per applicable hypothesis), the first one is used. -/
elab (name := aesopRuleTac) "aesop_rule_tac " decl:ident : tactic => do
  let declName ← realizeGlobalConstNoOverloadWithInfo decl
  let goal ← getMainGoal
  let type := (← getConstInfo declName).type
  let descr : RuleTacDescr ←
    if ← Meta.isDefEq (mkApp (mkConst ``TacticM) (mkConst ``Unit)) type then
      pure <| .tacticM declName
    else if ← Meta.isDefEq (mkConst ``SingleRuleTac) type then
      pure <| .singleRuleTac declName
    else if ← Meta.isDefEq (mkConst ``RuleTac) type then
      pure <| .ruleTac declName
    else if ← Meta.isDefEq (mkConst ``TacGen) type then
      pure <| .tacGen declName
    else
      throwError "aesop_rule_tac: expected {declName} to have one of the types\
        \n  TacticM Unit\n  Aesop.RuleTac\n  Aesop.SingleRuleTac\n  Aesop.TacGen\
        \nbut it has type{indentExpr type}"
  let input : RuleTacInput := {
    goal
    mvars := .ofHashSet (← goal.getMVarDependencies)
    indexMatchLocations := #[]
    patternSubsts? := none
    options := ← ({} : Aesop.Options).toOptions'
  }
  let (output, _) ← descr.run input |>.run
  let some app := output.applications[0]?
    | throwError "aesop_rule_tac: rule {declName} produced no rule applications"
  app.postState.restore
  replaceMainGoal (app.goals.map (·.mvarId)).toList

open Aesop RuleTacDescr in
/-- Best-effort translation of an Aesop rule into a standalone tactic. Returns `none` when the rule
has no reasonable syntactic counterpart.

Caveats on the cases that do translate:
- `constructors`: Aesop branches on every constructor that applies (`RuleTac.applyConsts`); as a
  single tactic we take the first that applies.
- `forward`: Aesop's `forward [r]` tactic (= `saturate 1 [r]`) rebuilds the rule with default
  immediate premises, no `destruct` clearing, and also fires the forward rules of the default rule
  sets — close, but not identical, to running the original rule alone.
- `cases`: Aesop repeatedly cases all hypotheses matching the target (up to defeq); we case just
  the first one found by `assumption` via `‹_›`, using the rule's stored constructor names as an
  `rcases` pattern like Aesop's script output does. Pattern-based cases targets are not supported.
- `tacticM`/`ruleTac`/`singleRuleTac`/`tacGen`: compiled metaprograms are run through the
  `aesop_rule_tac` bridge tactic, which takes the first rule application when the rule produces
  several alternatives.
-/
def ruleTacDescrToStx (descr : RuleTacDescr) : CommandElabM (Option Syntax) := do
  match descr with
  | apply t md =>
    let tac ← `(tactic| apply $(ruleTermToStx t))
    return some (withTransparencyStx md tac).raw
  | constructors ctors md =>
    let alts ← ctors.mapM fun c => `(tactic| apply $(mkIdent c):ident)
    let tac ← match alts with
      | #[tac] => pure tac
      | _ => `(tactic| first $[| $alts:tactic]*)
    return some (withTransparencyStx md tac).raw
  | forward t _immediate _isDestruct =>
    return some (← `(tactic| forward [$(ruleTermToStx t):term])).raw
  | cases target md _isRecursiveType ctorNames =>
    match target with
    | .decl d =>
      let hyp ← `(‹$(← mkHeadPattern d)›)
      let tac ←
        if ctorNames.isEmpty then
          `(tactic| cases $hyp:term)
        else
          `(tactic| rcases $hyp:term with $(ctorNamesToRCasesPats ctorNames):rcasesPatMed)
      return some (withTransparencyStx md tac).raw
    | .patterns _ => return none
  | tacticStx stx =>
    -- `(by tacs)` rules store a `tacticSeq`; parenthesize it into a single
    -- tactic, as Aesop's own `RuleTac.tacticStx` script builder does.
    if stx.isOfKind ``Lean.Parser.Tactic.tacticSeq then
      let seq : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx⟩
      return some (← `(tactic| ($seq:tacticSeq))).raw
    else
      return some stx
  -- Compiled metaprograms (`TacticM Unit`, `RuleTac`, `SingleRuleTac`, `TacGen`) have no
  -- syntax of their own; invoke them through the `aesop_rule_tac` bridge.
  | tacticM decl | ruleTac decl | tacGen decl | singleRuleTac decl =>
    return some (← `(tactic| aesop_rule_tac $(mkIdent decl):ident)).raw
  -- Aesop-internal rules.
  | preprocess | forwardMatches _ => return none

open Lean.Parser.Tactic in
/-- Renders one simp-theorem origin (declaration name plus its `post`/`inv` flags) as a `simp`
argument. -/
def mkSimpArgStx (decl : Name) (post inv : Bool) :
    CommandElabM (TSyntax ``Lean.Parser.Tactic.simpLemma) := do
  let i := mkIdent decl
  match post, inv with
  | true,  false => `(simpLemma| $i:term)
  | true,  true  => `(simpLemma| ← $i:term)
  | false, false => `(simpLemma| ↓ $i:term)
  | false, true  => `(simpLemma| ↓ ← $i:term)

open Aesop in
/-- The simp arguments contributed by a rule set's `@[aesop simp]` rules: its simp theorems
(minus erased ones), unfoldable definitions, and simprocs, each as `(name, post, inv)`. -/
def ruleSetSimpEntries (ruleSet : GlobalRuleSet) : Array (Name × Bool × Bool) := Id.run do
  let thms := ruleSet.simpTheorems
  let mut entries := #[]
  entries := thms.lemmaNames.fold (init := entries) fun entries origin =>
    match origin with
    | .decl n post inv => if thms.erased.contains origin then entries else
        entries.push (n, post, inv)
    | _ => entries
  entries := thms.toUnfold.fold (init := entries) fun entries n => entries.push (n, true, false)
  entries := thms.toUnfoldThms.foldl (init := entries) fun entries n _ => entries.push (n, true, false)
  entries := ruleSet.simprocs.simprocNames.fold (init := entries) fun entries n =>
    entries.push (n, true, false)
  return entries

open Aesop Aesop.Frontend in
open Lean.Elab.Command in
elab (name := addAesopTacs)
    -- attrKind:attrKind
    "add_aesop_tactics_to_hoverfly ": command => do
  let aesopRuleSets ← liftCoreM getDeclaredGlobalRuleSets
  let mut simpEntries : Std.HashSet (Name × Bool × Bool) := {}
  let mut unfoldNames : NameSet := {}
  for (_setName, ruleSet, _simpExtName, _simprocExtName) in aesopRuleSets do
    let normRuleDescrs := ruleSet.normRules.fold (fun rules rule => rule.tac :: rules) []
    let safeRuleDescrs := ruleSet.safeRules.fold (fun rules rule => rule.tac :: rules) []
    let unsafeRuleDescrs := ruleSet.unsafeRules.fold (fun rules rule => rule.tac :: rules) []
    let ruleDescrs := normRuleDescrs ++ safeRuleDescrs ++ unsafeRuleDescrs
    let rules ← ruleDescrs.filterMapM ruleTacDescrToStx
    rules.forM (fun tac => modifyEnv fun env => hoverflyTacticExt.addEntry env {raw:=tac})
    -- `@[aesop simp]` and `@[aesop unfold]` rules are not stored in the rule indices above but in
    -- dedicated simp-theorem/unfold structures; collect them across rule sets.
    simpEntries := simpEntries.insertMany (ruleSetSimpEntries ruleSet)
    unfoldNames := ruleSet.unfoldRules.foldl (init := unfoldNames) fun ns n _ => ns.insert n
  -- Aesop's norm simp runs `simp_all` with the default simp set (`useDefaultSimpSet` is on by
  -- default) plus the simp theorems of all rule sets in use (`mkLocalRuleSet`); mirror that as a
  -- single tactic.
  let sortedSimpEntries := simpEntries.toArray.qsort fun a b => a.1.toString < b.1.toString
  let simpArgs ← sortedSimpEntries.mapM fun (n, post, inv) => mkSimpArgStx n post inv
  let simpTac ←
    if simpArgs.isEmpty then `(tactic| simp_all)
    else `(tactic| simp_all [$simpArgs,*])
  modifyEnv fun env => hoverflyTacticExt.addEntry env simpTac
  -- Aesop applies unfold rules during normalization via its `aesop_unfold` tactic.
  unless unfoldNames.isEmpty do
    let ids := unfoldNames.toArray.qsort (·.toString < ·.toString) |>.map mkIdent
    let unfoldTac ← `(tactic| aesop_unfold $ids:ident*)
    modifyEnv fun env => hoverflyTacticExt.addEntry env unfoldTac

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
