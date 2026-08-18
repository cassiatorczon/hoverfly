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

public def errTacOutput (s : String)
  : Elab.TermElabM TacOutput := do
  let postState ← saveState
  return {
    stx := Syntax.missing
    goals := [],
    display := s,
    isNoop := false,
    solvesGoal := false,
    postState}

-- TODO
public def isErrTacOutput (output : TacOutput) : Bool :=
  output.goals == [] && !output.solvesGoal

@[expose]
public def FunTac := TacInput → TermElabM (List TacOutput) -- TODO

end FunTac
