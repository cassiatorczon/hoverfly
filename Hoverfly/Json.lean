import ProofWidgets
import Hoverfly.Backend

namespace API
open Lean ProofWidgets

instance : ToJson String := inferInstanceAs (ToJson String)
instance : FromJson String := inferInstanceAs (FromJson String)

instance : ToJson MVarId := inferInstanceAs (ToJson MVarId)
instance : FromJson MVarId := inferInstanceAs (FromJson MVarId)

instance : ToJson (List MVarId) := inferInstanceAs (ToJson (List MVarId))
instance : FromJson (List MVarId) := inferInstanceAs (FromJson (List MVarId))

instance : ToJson Syntax := by sorry --TODO
instance : FromJson Syntax := by sorry--TODO

instance : ToJson Lean.Elab.Term.SyntheticMVarKind := by sorry --TODO
instance : FromJson Lean.Elab.Term.SyntheticMVarKind := by sorry--TODO

instance : ToJson (MVarIdMap Lean.Elab.Term.SyntheticMVarDecl) := by sorry
instance : FromJson (MVarIdMap Lean.Elab.Term.SyntheticMVarDecl) := by sorry

instance : ToJson (List Elab.Term.MVarErrorInfo) := by sorry
instance : FromJson (List Elab.Term.MVarErrorInfo) := by sorry

instance : ToJson (List Elab.Term.LevelMVarErrorInfo) := by sorry
instance : FromJson (List Elab.Term.LevelMVarErrorInfo) := by sorry

instance : ToJson (MVarIdMap Name) := by sorry
instance : FromJson (MVarIdMap Name) := by sorry

instance : ToJson (List Elab.Term.LetRecToLift) := by sorry
instance : FromJson (List Elab.Term.LetRecToLift) := by sorry

instance : ToJson Elab.Term.SavedState := by sorry
instance : FromJson Elab.Term.SavedState := by sorry


instance : ToJson Lean.Elab.Term.SyntheticMVarDecl where
  toJson s :=
    let stx_json := toJson s.stx
    let kind_json := toJson s.kind
    Json.mkObj [("stx", stx_json), ("kind", kind_json)]


instance : ToJson Lean.Elab.Tactic.State where
  toJson s :=
    let goals_json := toJson s.goals
    Json.mkObj [("goals", goals_json)]

instance : FromJson Lean.Elab.Tactic.State where
  fromJson? j := match j with
    | Json.obj kvs => match kvs.toList with
      | [("goals", l)] =>
        match fromJson? l with
        | Except.ok goals => Except.ok {goals := goals}
        | Except.error err => Except.error err
      | _ => Except.error s!"Unexpected fields for Lean.Elab.Tactic.State when parsing JSON." --TODO: better message
    | _ => Except.error s!"Unexpected JSON format for Lean.Elab.Tactic.State." --TODO: better message

instance : ToJson Lean.Elab.Term.State where
  toJson s :=
    let levelNames_json := toJson s.levelNames
    let syntheticMVars_json := toJson s.syntheticMVars
    let pendingMVars_json := toJson s.pendingMVars
    let mvarErrorInfos_json := toJson s.mvarErrorInfos
    let levelMVarErrorInfos_json := toJson s.levelMVarErrorInfos
    let mvarArgNames_json := toJson s.mvarArgNames
    let letRecsToLift_json := toJson s.letRecsToLift
    Json.mkObj [
      ("levelNames", levelNames_json),
      ("syntheticMVars", syntheticMVars_json),
      ("pendingMVars", pendingMVars_json),
      ("mvarErrorInfos", mvarErrorInfos_json),
      ("levelMVarErrorInfos", levelMVarErrorInfos_json),
      ("mvarArgNames", mvarArgNames_json),
      ("letRecsToLift", letRecsToLift_json)]
instance : FromJson Lean.Elab.Tactic.State where
  fromJson? j := match j with
    | Json.obj kvs => match kvs.toList with
      | [("goals", l)] =>
        match fromJson? l with
        | Except.ok goals => Except.ok {goals := goals}
        | Except.error err => Except.error err
      | _ => Except.error s!"Unexpected fields for Lean.Elab.Tactic.State when parsing JSON." --TODO: better message
    | _ => Except.error s!"Unexpected JSON format for Lean.Elab.Tactic.State." --TODO: better message

instance : ToJson Lean.Elab.Tactic.SavedState where
  toJson s :=
    let term_json := toJson s.term
    let tactic_json := toJson s.tactic
    Json.mkObj [("term", term_json), ("tactic", tactic_json)]
-- instance : FromJson Tactic.SavedState := inferInstanceAs (FromJson Tactic.SavedState)
