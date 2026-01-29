import ProofWidgets

-- TODO namespaces
open Lean ProofWidgets

-- -- TODO should these be the same
-- def GoalId := String
-- def String := String

instance : ToJson String := inferInstanceAs (ToJson String)
instance : FromJson String := inferInstanceAs (FromJson String)

instance : ToJson String := inferInstanceAs (ToJson String)
instance : FromJson String := inferInstanceAs (FromJson String)

mutual
structure Goal where
  id : String
  data : String
  children : List Tactic
  deriving ToJson, FromJson

structure Tactic where
  id : String
  data : String
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
  RequestM.asTask $ pure
    {
      id:= "g0",
      data:= "P /\\ Q", children:= [
        {
          id:= "t0",
          data:= "split", children:= [
            { id:= "g1", data:= "P", children:= []},
            { id:= "g2", data:= "Q", children:= []},
          ]
        }
      ]
    }

@[server_rpc_method]
def getSubgoals (t : Tactic) : RequestM (RequestTask (List Goal)) :=
  -- TODO
  RequestM.pureTask $
    if (t.id == "t0")
      then
        pure
          [
            {
            id:= "g0",
            data:= "P", children:= []},
            {
            id:= "g1",
            data:= "Q", children:= []}
            ]
      else
        if (t.id == "t1")
          then
            pure
              []
          else
            pure
              []


@[server_rpc_method]
def getApplicableTactics (g : Goal) : RequestM (RequestTask (List Tactic)) :=
  -- TODO
  RequestM.pureTask $
    if (g.id == "g0")
      then
        pure
          [
            {
            id:= "t0",
            data:= "split", children:= []}
            ]
      else
        if (g.id == "g1")
          then
            pure
              [
                {
                id:= "t1",
                data:= "exact P", children:= []}
              ]
          else
            pure
              [
                {
                id:= "t1",
                data:= "exact Q", children:= []}
              ]

@[widget_module]
def checkWidget : Widget.Module where
  javascript := include_str ".."/".lake"/"build"/"js"/"Hoverfly.js"

#widget checkWidget
