module

public import Hoverfly.MVar
public import Hoverfly.Util
public import Lean.Elab

open Lean Elab Term FunTac Util

namespace TacticUtil

def matchesHyp (i : Syntax) : Bool :=
  Syntax.matchesIdent i (.str .anonymous "HYP")

-- gets all lists of length n composed from elements of xs, with repetition
def pickNWithRep (xs : List α) (n : Nat) : List (List α) :=
  match n with
  | 0 => [[]]
  | .succ n' =>
    xs.flatMap (fun x => (pickNWithRep xs n').map (fun ys => x :: ys))

def replaceHyps (xs : List Syntax) (s : Syntax) : Syntax :=
  let f := fun  (swapped, toSwapIn) arg =>
    match toSwapIn, matchesHyp arg with
    | x :: xs', true => (x :: swapped, xs')
    | _, _ => (arg :: swapped, toSwapIn)
  let newArgList := s.getArgs.foldl f ([], xs)
  s.setArgs newArgList.fst.toArray

-- converts a localDecl to a syntax
def declToSyntax (d : LocalDecl) : Syntax :=
  let val := d.userName
  let preresolved := [] -- TODO
  let rawVal := d.userName.toString.toRawSubstring -- TODO
  .ident SourceInfo.none rawVal val preresolved

def getTacsWithArgs (tac : Syntax) (lctx : LocalContext) : List Syntax :=
    -- let lctx ← liftM (Lean.LocalContext.sanitizeNames lctx : Elab.TermElabM LocalContext)
  let allDecls := lctx.decls.toList.filterMap id -- TODO is there actually no function for that
  let filteredDecls := allDecls.filter (fun d => !d.isAuxDecl && !d.isImplementationDetail)
  let filteredArgs := filteredDecls.map (fun d => declToSyntax d)
  let numArgs := tac.getArgs.countP matchesHyp
  let argLists := pickNWithRep filteredArgs numArgs
  argLists.map (fun argList => replaceHyps argList tac)

def runTac (t : Syntax) (mvarId : MVarId) (st : SavedState):
  Elab.TermElabM TacOutput := do
  -- restore state
  liftM (restoreStateFull st : Lean.Elab.TermElabM Unit)
  -- get existing messages before running the tactic
  let msgsBefore ←
    liftM ((do return (← getThe Core.State).messages.toList) : Elab.TermElabM _)
  try
    -- run the tactic
    let goals ← Elab.Term.withoutErrToSorry do
      Lean.Elab.Tactic.run mvarId do
        Lean.Elab.Tactic.evalTactic t
    -- get new messages
    let newMsgs ←
      liftM ((do return (← getThe Core.State).messages.toList.drop msgsBefore.length)
        : Elab.TermElabM _)
    match newMsgs.find? (fun m => m.severity matches .error) with
    | some err =>
      -- if the tactic "fails softly" (logs an error-severity message), record the error message
      errTacOutput t t.prettyPrint.pretty (← err.data.toString)
    | none =>
      -- if the tactic doesn't assign or change the goal, mark it noop
      -- if the tactic results in 0 goals and assigns the mvar, mark it as solving the goal
      let assigned ← liftM (mvarId.isAssigned : Lean.Elab.TermElabM Bool)
      let isNoop := goals == [mvarId] && !assigned
      let solvesGoal := goals == [] && assigned
      let display := t.prettyPrint.pretty
      let postState ← saveState
      return {stx:=t, goals, display, isNoop, solvesGoal, postState}
  catch e =>
    -- if the tactic throws, record the error message
    errTacOutput t t.prettyPrint.pretty (← e.toMessageData.toString)


public def tacticToFunTac
  (tac : Syntax) -- prototactic
  : FunTac :=
  fun {goal, savedState} => do
    liftM (restoreStateFull savedState : Lean.Elab.TermElabM Unit)
    let tacs := getTacsWithArgs tac (← liftM (goal.getDecl : Elab.TermElabM _)).lctx
    tacs.mapM (fun t => runTac t goal savedState)

end TacticUtil
