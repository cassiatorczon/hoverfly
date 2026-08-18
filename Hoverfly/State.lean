module

public import Hoverfly.FunTac
public import Lean.Data.Json.FromToJson.Basic
public import Lean.Elab.Term.TermElabM
public import Std.Data.HashMap.Basic

open Lean Elab FunTac

namespace State

@[expose]
public def StateId := Nat
  deriving OfNat, BEq, Hashable, ToJson, FromJson, HAdd, ToString

public structure ClusterInfo where
  members : List StateId
  sharedMVars : List MVarId

public structure State where
  allTactics : List FunTac
  nodeCounter : StateId := 0
  goalMap : Std.HashMap StateId (MVarId × Term.SavedState) := ∅
  tacticMap : Std.HashMap StateId (TacOutput × StateId) := ∅
  clusterMap : Std.HashMap StateId ClusterInfo := ∅
  deriving TypeName

end State
