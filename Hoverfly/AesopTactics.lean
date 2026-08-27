module

public meta import Aesop.Frontend.Extension
public meta import Aesop.RuleTac
import Batteries.Linter.UnreachableTactic
public import Hoverfly.Attribute
public meta import Hoverfly.Util
public meta import Lean.Elab.Command

public meta section

open Lean Elab Command Meta ProtoTactic Aesop RuleTac RuleTacDescr RuleTerm

def ppRuleTerm (t : RuleTerm) :=
  match t with
  | .const decl => s!"{decl}"
  | .term t => s!"{t}"

-- TODO
def ForwardRuleMatch.toString : ForwardRuleMatch → String :=
  fun m => s!"{m.rule.name}"

instance : ToString ForwardRuleMatch :=
  ⟨ForwardRuleMatch.toString⟩

-- TODO
def ppRuleTacDescr (descr : RuleTacDescr) : String :=
  match descr with
  | .apply t md =>
    "apply " ++ ppRuleTerm t
  | .constructors constructorNames md =>
    "constructor"
  | .forward t immediate isDestruct =>
    "forward " ++ ppRuleTerm t
  | .cases target md isRecursivetype ctorNames =>
    "cases " -- ++ s!"{target}"
  | .tacticM decl => s!"{decl}"
  | .ruleTac decl => s!"{decl}"
  | .tacGen decl => s!"{decl}"
  | .singleRuleTac decl => s!"{decl}"
  | .tacticStx stx => s!"{stx}"
  | .preprocess => "preprocess" -- TODO
  | .forwardMatches ms =>
    "forwardMatches " ++ s!"{ms.toList.toString}"

def ppScriptSteps (steps : Option (Array Script.LazyStep)) (default : String)
  : CoreM String :=
  match steps with
  | some steps => do
    let stepsRun ← steps.mapM (fun s => s.toStep.run)
    return s!"{stepsRun.map (fun (step, _) => step.uTactic)}"
  | none => return default

def ruleTacDescrToProtoTactic (descr : RuleTacDescr) : ProtoTactic :=
  fun {goal, savedState} => do
    let initialState ← saveState
    let _ := liftTermElabM (Util.restoreStateFull savedState) -- TODO?
    let ruleTac := descr.run
    let mvarDeps ← liftM (goal.getMVarDependencies : MetaM (Std.HashSet MVarId))
    let mvars := UnorderedArraySet.ofHashSet mvarDeps
    let indexMatchLocations : Array IndexMatchLocation := #[] -- TODO
    let patternSubsts? : Option (Array Substitution ):= none -- TODO
    let options : Options' :=
      {generateScript := true, forwardMaxDepth? := none}
    let ruleTacInput : RuleTacInput :=
      {goal, mvars, indexMatchLocations, patternSubsts?, options}
    try do
      let ({applications}, _) ← (ruleTac ruleTacInput).run
      let appsList := applications.toList
      let f (tacOutputs : List TacOutput) (ruleApp : RuleApplication)
        : TermElabM (List TacOutput) := do
        let _ := liftTermElabM (Util.restoreStateFull savedState) -- TODO?
        let {goals, postState, scriptSteps?, successProbability?} := ruleApp
        let termState : Term.State := ← get -- TODO
        let newState : Term.SavedState := { «meta» := postState, «elab» := termState}
        let goalList := goals.toList.map (fun g => g.mvarId)
        let display ← ppScriptSteps scriptSteps? (ppRuleTacDescr descr)
        let assigned ← goal.isAssigned
        let isNoop := goalList == [goal] && !assigned
        let solvesGoal := goalList == [] && assigned
        let stx := Syntax.missing -- TODO
        let tac : TacOutput :=
          {stx, goals:=goalList, display, isNoop, solvesGoal, postState:=newState}
        return (tac :: tacOutputs)
      let _ := liftTermElabM (Util.restoreStateFull initialState) -- TODO?
      List.foldlM f [] appsList
    catch e =>
      let display := ppRuleTacDescr descr
      let errString ← e.toMessageData.toString
      let errTac ← errTacOutput Syntax.missing display errString
      return [errTac]


elab (name := addAesopTacs)
    -- attrKind:attrKind
    "add_aesop_tactics_to_hoverfly ": command => do
  let aesopRuleSets ← liftCoreM Aesop.Frontend.getDeclaredGlobalRuleSets
  for (_, ruleSet, _, _) in aesopRuleSets do
    -- let forwardRules := (ruleSet.forwardRules.nameToRule.toList.map Prod.snd).map TODO
    let normRuleDescrs := ruleSet.normRules.fold (fun rules rule => rule.tac :: rules) []
    let safeRuleDescrs := ruleSet.safeRules.fold (fun rules rule => rule.tac :: rules) []
    let unsafeRuleDescrs := ruleSet.unsafeRules.fold (fun rules rule => rule.tac :: rules) []
    let ruleDescrs := normRuleDescrs ++ safeRuleDescrs ++ unsafeRuleDescrs -- ++ forwardRules
    let rules := ruleDescrs.map ruleTacDescrToProtoTactic
    rules.forM (fun tac => modifyEnv fun env => hoverflyTacticExt.addEntry env tac)

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``addAesopTacs
