import ProofWidgets
namespace Step

namespace ProofTree

-- inductive Status : Type where
--   | selected -- status for current single node selected
--   | semiselected  -- status for all ancestors of selected node
--   | unselected -- status for all other visible nodes
--   -- | hidden -- status for hidden children
open Lean ProofWidgets

def ID := String

instance : ToJson ID := inferInstanceAs (ToJson String)
instance : FromJson ID := inferInstanceAs (FromJson String)

mutual
structure Goal where
  id : ID
  name : String
  -- status : Status
  children : List Tactic
  completed : Bool
  deriving ToJson, FromJson

structure Tactic where
  id : ID
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

end ProofTree

namespace API

/-
List of operations:

Change node selection status (selected, unselected, semiselected, hidden?)
Mark goal node and applicable ancestors as completed

Show applicable tactics for a goal
Show subgoals for a tactic
Hide and cache subtree rooted at goal
Hide and cache subtree rooted at tactic
Restore subtree rooted at goal
Restore subtree rooted at tactic
Hide unexplored neighboring tactics

-/


end API

end Step
