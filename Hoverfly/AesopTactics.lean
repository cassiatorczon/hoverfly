module

public meta import Aesop.Frontend.Extension
public meta import Lean.Elab.Command
import Aesop
import Batteries.Linter.UnreachableTactic
public import Hoverfly.Attribute
public import Hoverfly.FunTac
public import Hoverfly.State

public meta section

open Lean Elab Command Meta

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

-- open Aesop RuleTac RuleTacDescr in
-- def ruleTacDescrToFunTac (descr : RuleTacDescr) : FunTac :=
--   fun {goal, savedState} => do
--     let _ := liftTermElabM (restoreStateFull savedState) -- TODO?
--     let ruleTac := descr.run
--     let mvarDeps ← liftM (goal.getMVarDependencies : MetaM (Std.HashSet MVarId))
--     let mvars := UnorderedArraySet.ofHashSet mvarDeps
--     let indexMatchLocations := #[] -- TODO
--     let patternSubsts? := none -- TODO
--     let options := {generateScript := false, forwardMaxDepth? := none}
--     let ruleTacInput := {goal,mvars, indexMatchLocations, patternSubsts?, options}
--     let {applications} ← ruleTac ruleTacInput
--     let appsList := applications.toList
--     let f (tacOutputs : List TacOutput) (ruleApp : RuleApplication)
--       : Aesop.BaseM (List TacOutput) :=
--       let {goals, postState, scriptSteps?, successProbability?} := ruleApp
--       let goals := goals.toList.map (fun g => g.mvarId)
--       let display := "TODO"
--       let isNoop := false -- TODO
--       let solvesGoal := false -- TODO
--       let tac : TacOutput := {goals, display, isNoop, solvesGoal}
--       return (tac :: tacOutputs)
--     List.foldlM f [] appsList
-- open Lean.Elab.Command in
-- elab (name := addAesopTacs)
--     -- attrKind:attrKind
--     "add_aesop_tactics_to_hoverfly ": command => do
--   let aesopRuleSets ← liftCoreM getDeclaredGlobalRuleSets
--   for (setName, ruleSet, simpExtName, simprocExtName) in aesopRuleSets do
--     -- let forwardRules := (ruleSet.forwardRules.nameToRule.toList.map Prod.snd).map TODO
--     let normRuleDescrs := ruleSet.normRules.fold (fun rules rule => rule.tac :: rules) []
--     let safeRuleDescrs := ruleSet.safeRules.fold (fun rules rule => rule.tac :: rules) []
--     let unsafeRuleDescrs := ruleSet.unsafeRules.fold (fun rules rule => rule.tac :: rules) []
--     let ruleDescrs := normRuleDescrs ++ safeRuleDescrs ++ unsafeRuleDescrs
--     let rules ← ruleDescrs.filterMapM ruleTacDescrToStx
--     rules.forM (fun tac => modifyEnv fun env => hoverflyTacticExt.addEntry env {raw:=tac})

-- initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addAesopTacs
