module

public meta import Aesop.Frontend.Extension
public meta import Aesop.RuleTac
import Batteries.Linter.UnreachableTactic
public import Hoverfly.Attribute
public meta import Hoverfly.Util
public meta import Lean.Elab.Command

public meta section

open Lean Elab Command Meta FunTac

open Aesop RuleTac RuleTacDescr in
def ruleTacDescrToFunTac (descr : RuleTacDescr) : FunTac :=
  fun {goal, savedState} => do
    let initialState ← saveState
    let _ := liftTermElabM (Util.restoreStateFull savedState) -- TODO?
    let ruleTac := descr.run
    let mvarDeps ← liftM (goal.getMVarDependencies : MetaM (Std.HashSet MVarId))
    let mvars := UnorderedArraySet.ofHashSet mvarDeps
    let indexMatchLocations := #[] -- TODO
    let patternSubsts? := none -- TODO
    let options := {generateScript := false, forwardMaxDepth? := none}
    let ruleTacInput := {goal,mvars, indexMatchLocations, patternSubsts?, options}
    let ({applications}, _) ← (ruleTac ruleTacInput).run
    let appsList := applications.toList
    let f (tacOutputs : List TacOutput) (ruleApp : RuleApplication)
      : TermElabM (List TacOutput) := do
      let {goals, postState, scriptSteps?, successProbability?} := ruleApp
      let termState : Term.State := ← get -- TODO
      let newState : Term.SavedState := { «meta» := postState, «elab» := termState}
      let goalList := goals.toList.map (fun g => g.mvarId)
      let display := "TODO"
      let assigned ← goal.isAssigned
      let isNoop := goalList == [goal] && !assigned
      let solvesGoal := goalList == [] && assigned
      let stx := Syntax.missing -- TODO
      let tac : TacOutput :=
        {stx, goals:=goalList, display, isNoop, solvesGoal, postState:=newState}
      return (tac :: tacOutputs)
    let _ := liftTermElabM (Util.restoreStateFull initialState) -- TODO?
    List.foldlM f [] appsList

open Lean.Elab.Command in
elab (name := addAesopTacs)
    -- attrKind:attrKind
    "add_aesop_tactics_to_hoverfly ": command => do
  let aesopRuleSets ← liftCoreM Aesop.Frontend.getDeclaredGlobalRuleSets
  for (_, ruleSet, _, _) in aesopRuleSets do
    -- let forwardRules := (ruleSet.forwardRules.nameToRule.toList.map Prod.snd).map TODO
    let normRuleDescrs := ruleSet.normRules.fold (fun rules rule => rule.tac :: rules) []
    let safeRuleDescrs := ruleSet.safeRules.fold (fun rules rule => rule.tac :: rules) []
    let unsafeRuleDescrs := ruleSet.unsafeRules.fold (fun rules rule => rule.tac :: rules) []
    let ruleDescrs := normRuleDescrs ++ safeRuleDescrs ++ unsafeRuleDescrs
    let rules := ruleDescrs.map ruleTacDescrToFunTac
    rules.forM (fun tac => modifyEnv fun env => hoverflyTacticExt.addEntry env tac)

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addAesopTacs
