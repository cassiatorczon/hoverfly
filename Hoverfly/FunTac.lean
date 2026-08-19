module

public import Lean.Elab

open Lean Elab Term

namespace FunTac

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
  isNoop : Bool
  solvesGoal : Bool
  postState : SavedState
  error : Option String := none

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
  output.error.isSome || (output.goals == [] && !output.solvesGoal)

@[expose]
public def FunTac := TacInput → TermElabM (List TacOutput) -- TODO

end FunTac
