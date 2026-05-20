import Lean.Data.Json.Basic
import ProofWidgets

open Lean

instance : ToJson String := inferInstanceAs (ToJson String)
instance : FromJson String := inferInstanceAs (FromJson String)

instance : ToJson MVarId := inferInstanceAs (ToJson MVarId)
instance : FromJson MVarId := inferInstanceAs (FromJson MVarId)

/-
inductive Syntax where

  | missing : Syntax
  | node   (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom   (info : SourceInfo) (val : String) : Syntax
  | ident  (info : SourceInfo) (rawVal : Substring.Raw) (val : Name) (preresolved : List Syntax.Preresolved) : Syntax
-/

instance : ToJson Syntax := by sorry --TODO
instance : FromJson Syntax := by sorry--TODO

/-
inductive SyntheticMVarKind where
  | typeClass (extraErrorMsg? : Option MessageData)
  | coe (header? : Option String) (expectedType : Expr) (e : Expr) (f? : Option Expr)
      (mkErrorMsg? : Option (MVarId → Expr → Expr → MetaM MessageData))
  | tactic (tacticCode : Syntax) (ctx : SavedContext) (kind : TacticMVarKind) (delayOnMVars := false)
  | postponed (ctx : SavedContext)
-/

instance : ToJson Lean.Elab.Term.SyntheticMVarKind := by sorry --TODO
instance : FromJson Lean.Elab.Term.SyntheticMVarKind := by sorry--TODO


instance [ToJson α] : ToJson (MVarIdMap α) where
  toJson := by sorry

/--
protected def _root_.List.fromJson? [FromJson α] (j : Json) : Except String (List α) :=
  (fromJson? j (α := Array α)).map Array.toList

instance [FromJson α] : FromJson (List α) where
  fromJson? := List.fromJson?

protected def _root_.List.toJson [ToJson α] (a : List α) : Json :=
  toJson a.toArray

instance [ToJson α] : ToJson (List α) where
  toJson := List.toJson

protected def _root_.Option.fromJson? [FromJson α] : Json → Except String (Option α)
  | Json.null => Except.ok none
  | j         => some <$> fromJson? j

instance [FromJson α] : FromJson (Option α) where
  fromJson? := Option.fromJson?

protected def _root_.Option.toJson [ToJson α] : Option α → Json
  | none   => Json.null
  | some a => toJson a

instance [ToJson α] : ToJson (Option α) where
  toJson := Option.toJson

@[expose] def MVarIdMap (α : Type) := Std.TreeMap MVarId α (Name.quickCmp ·.name ·.name)
-/

instance : ToJson Lean.Elab.Term.SyntheticMVarDecl where
  toJson s :=
    let stx_json := toJson s.stx
    let kind_json := toJson s.kind
    Json.mkObj [("stx", stx_json), ("kind", kind_json)]
instance : FromJson Lean.Elab.Term.SyntheticMVarDecl := by sorry

/-
inductive MVarErrorKind where
  /-- Metavariable for implicit arguments. `ctx` is the parent application,
  `lctx` is a local context where it is valid (necessary for eta feature for named arguments). -/
  | implicitArg (lctx : LocalContext) (ctx : Expr)
  /-- Metavariable for explicit holes provided by the user (e.g., `_` and `?m`) -/
  | hole
  /-- "Custom", `msgData` stores the additional error messages. -/
  | custom (msgData : MessageData)
  deriving Inhabited

/--
When reporting unexpected universe level metavariables, it is useful to localize the errors
to particular terms, especially at `let` bindings and function binders,
where universe polymorphism is not permitted.
-/
structure LevelMVarErrorInfo where
  lctx      : LocalContext
  expr      : Expr
  ref       : Syntax
  msgData?  : Option MessageData := none
  deriving Inhabited
-/

instance : ToJson Lean.Elab.Term.MVarErrorKind := by sorry --TODO
instance : FromJson Lean.Elab.Term.MVarErrorKind := by sorry--TODO


instance : ToJson Elab.Term.MVarErrorInfo where
  toJson m :=
    let mvarId_json := toJson m.mvarId
    let ref_json := toJson m.ref
    let kind_json := toJson m.kind
    Json.mkObj [("mvarId", mvarId_json), ("ref", ref_json), ("kind", kind_json)]
instance : FromJson Elab.Term.MVarErrorInfo := by sorry

instance : ToJson Elab.Term.LevelMVarErrorInfo where
  toJson l :=
    let lctx_json := by sorry --toJson l.lctx
    let expr_json := by sorry --toJson l.expr
    let ref_json := toJson l.ref
    let kind_json := by sorry --toJson l.msgData?
    Json.mkObj [("lctx", lctx_json), ("expr", expr_json), ("ref", ref_json), ("kind", kind_json)]
instance : FromJson Elab.Term.LevelMVarErrorInfo := by sorry

instance : ToJson Elab.Term.LetRecToLift := by sorry
instance : FromJson Elab.Term.LetRecToLift := by sorry

instance : ToJson Elab.Term.SavedState := by sorry
instance : FromJson Elab.Term.SavedState := by sorry


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
