module

import Lean.Elab
import Aesop -- TODO

open Lean Elab


/-- Input for a tactic. -/
structure TacInput where
  /-- The goal on which the tactic is run. -/
  goal : MVarId
  /-- The state in which the tactic is run. -/
  savedState : Elab.Term.SavedState

/-- Output for a tactic. -/
structure TacOutput where
  goals : List MVarId
  display : String
  isNoop : Bool
  solvesGoal : Bool
deriving Inhabited

def FunTac := TacInput → Aesop.BaseM (List TacOutput) -- TODO
