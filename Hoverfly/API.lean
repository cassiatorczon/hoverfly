import ProofWidgets

-- TODO namespaces
open Lean ProofWidgets

-- TODO should these be the same
def GoalId := String
def TacticId := String

instance : ToJson GoalId := inferInstanceAs (ToJson String)
instance : FromJson GoalId := inferInstanceAs (FromJson String)

instance : ToJson TacticId := inferInstanceAs (ToJson String)
instance : FromJson TacticId := inferInstanceAs (FromJson String)

mutual
structure Goal where
  id : GoalId
  name : String
  -- status : Status
  children : List Tactic
  completed : Bool
  deriving ToJson, FromJson

structure Tactic where
  id : TacticId
  name : String
  -- status : Status
  children : List Goal
  deriving ToJson, FromJson
end

instance : Server.RpcEncodable Goal where
  rpcEncode goal := pure (toJson goal)
  rpcDecode json := fromJson? json |>.mapError (·)

instance : Server.RpcEncodable Tactic where
  rpcEncode tactic := pure (toJson tactic)
  rpcDecode json := fromJson? json |>.mapError (·)

open Lean ProofWidgets Server

-- TODO arg
@[server_rpc_method]
def getInitialState (_ : String) : RequestM (RequestTask Goal) :=
  -- TODO
  pure $ RequestTask.pure
    {
      id:= "g0",
      name:= "P /\\ Q", completed:= false, children:= [
        {
          id:= "t0",
          name:= "split", children:= [
            { id:= "g1", name:= "P", completed:= false, children:= []},
            { id:= "g2", name:= "Q", completed:= false, children:= []},
          ]
        }
      ]
    }

@[server_rpc_method]
def chooseTactic (_ : TacticId) : RequestM (RequestTask Goal) :=
  -- TODO
  pure $ RequestTask.pure
  {
    id:= "g0",
    name:= "P /\\ Q", completed:= false, children:= [
      {
        id:= "t0",
        name:= "split", children:= [
          { id:= "g1", name:= "P", completed:= false, children:= []},
          { id:= "g2", name:= "Q", completed:= false, children:= []},
        ]
      }
    ]
  }

@[widget_module]
def checkWidget : Widget.Module where
  javascript := include_str ".."/".lake"/"build"/"js"/"Hoverfly.js"

#widget checkWidget
