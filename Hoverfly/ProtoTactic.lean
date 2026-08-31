module

public import Lean.Elab

open Lean Elab Term

namespace ProtoTactic

/-- Input for a tactic. -/
public structure TacInput where
  /-- The goal on which the tactic is run. -/
  goal : MVarId
  /-- The state in which the tactic is run. -/
  savedState : SavedState

/-- Output for a tactic. -/
public structure TacOutput where
  stx : Syntax -- syntax of the tactic
  goals : List MVarId -- goals resulting from the tactic application
  display : String -- pretty printed tactic
  isNoop : Bool -- whether the tactic is a no-op
  solvesGoal : Bool -- whether the tactic solves the goal
  postState : SavedState -- state after the tactic application
  error : Option String := none -- error thrown by tactic application

public def errTacOutput (stx : Syntax) (display : String) (err : String)
  : Elab.TermElabM TacOutput := do
  let postState ← saveState
  return {
    stx,
    goals := [],
    display,
    isNoop := false,
    solvesGoal := false,
    postState,
    error := some err}

public def isErrTacOutput (output : TacOutput) : Bool :=
  output.error.isSome --|| (output.goals == [] && !output.solvesGoal) TODO I think we don't need this part

@[expose]
public def ProtoTactic := TacInput → TermElabM (List TacOutput)

end ProtoTactic
