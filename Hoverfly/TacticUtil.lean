module

public import Hoverfly.MVar
public import Hoverfly.Util
public import Lean.Elab
public import Hoverfly.SyntaxUtil

open Lean Elab Term ProtoTactic Util SyntaxUtil

namespace TacticUtil

/-
Checks if a piece of syntax is the prototactic argument placeholder.
-/
def matchesHyp (i : Syntax) : Bool :=
  Syntax.matchesIdent i (.str .anonymous "HYP")

/-
Returns all lists of length n composed from elements of xs, with repetition.
-/
def pickNWithRep (xs : List α) (n : Nat) : List (List α) :=
  match n with
  | 0 => [[]]
  | .succ n' =>
    xs.flatMap (fun x => (pickNWithRep xs n').map (fun ys => x :: ys))

/-
Count instances of argument placeholders in a piece of syntax.
TODO the else case of this seems to cause the bug
-/
def countHyps (s : Syntax) : Nat := countSyntax matchesHyp s

/-
Replace each instance of an argument placeholder in a piece of syntax s with
the pieces of syntax xs, in depth-first order.

If xs has more elements than s has placeholders, the extra elements will be
ignored.
If xs has fewer elements than s has placeholders, the extra placeholders will
remain unchanged.
-/
def replaceHyps (xs : List Syntax) (s : Syntax) : Syntax :=
  let f : Array Syntax → Syntax → StateM (List Syntax) Syntax := fun acc s => do
    let toSwap ← get
    match toSwap, matchesHyp s with
    | _, false => return s.setArgs acc
    | [], _ => return s
    | x :: xs', true => do
      set xs'
      return x
  ((foldMSyntax' f s).run xs).fst

/-
Converts a LocalDecl to a Syntax.
TODO it seems like there should be a function for this. I'm not sure
this is the right way to do it.
-/
def localDeclToSyntax (d : LocalDecl) : Syntax :=
  let val := d.userName
  let preresolved := []
  let rawVal := d.userName.toString.toRawSubstring
  .ident SourceInfo.none rawVal val preresolved

/-
Replaces placeholder arguments in the given tactic with all (syntactically)
possible combinations of (non-auxiliary) declarations in the context,
including combinations with repetition of a single declaration.
-/
def instantiateArgs (tac : Syntax) (lctx : LocalContext) : List Syntax :=
  -- TODO do we want to sanitize names? -- let lctx ← liftM (Lean.LocalContext.sanitizeNames lctx : Elab.TermElabM LocalContext)
  let allDecls := lctx.decls.toList.filterMap id -- TODO is there actually no function for that
  let filteredDecls := allDecls.filter (fun d => !d.isAuxDecl && !d.isImplementationDetail)
  let filteredArgs := filteredDecls.map (fun d => localDeclToSyntax d)
  let numArgs := countHyps tac
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


public def syntaxToProtoTactic
  (tac : Syntax) -- prototactic
  : ProtoTactic :=
  fun {goal, savedState} => do
    liftM (restoreStateFull savedState : Lean.Elab.TermElabM Unit)
    let tacs := instantiateArgs tac (← liftM (goal.getDecl : Elab.TermElabM _)).lctx
    -- The `MonadExcept` instance for `TermElabM` rethrows timeouts, so we need to catch it again
    tacs.mapM fun t =>
      tryCatchRuntimeEx (runTac t goal savedState) fun e => do
        liftM (restoreStateFull savedState : Lean.Elab.TermElabM Unit)
        errTacOutput t t.prettyPrint.pretty (← e.toMessageData.toString)

end TacticUtil
