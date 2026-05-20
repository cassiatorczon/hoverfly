-- This module serves as the root of the `Persist` library.
-- Import modules here that should be built as part of the library.
import Scratch.IORefExample.StateExample0
import Lean
open Lean Widget


#eval show IO Nat from do
  let x ← myRef.get
  myRef.modify (· + 1)
  return x

structure IncrementParams where
  /-- Position of our widget instance in the Lean file. -/
  pos : Lsp.Position
  deriving FromJson, ToJson

open Server RequestM in
@[server_rpc_method]
def incrementCounter (params : IncrementParams) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
      -- increment the counter
      return "Done"


structure DecrementParams where
  /-- Position of our widget instance in the Lean file. -/
  pos : Lsp.Position
  deriving FromJson, ToJson

open Server RequestM in
@[server_rpc_method]
def decrementCounter (params : IncrementParams) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
      let oldval ← myRef.get
      let newval := oldval + 1
      myRef.set newval
      -- increment the counter
      return s!"{newval}"

open Server RequestM in
@[server_rpc_method]
def getTheCounter (params : IncrementParams) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
      return s!"{← myRef.get}"


@[widget_module]
def checkWidget : Widget.Module where
  javascript := "
import * as React from 'react';
const e = React.createElement;
import { useRpcSession, InteractiveCode, useAsync, mapRpcError } from '@leanprover/infoview';

export default function(props) {
  const rs = useRpcSession()
  const [count, setCount] = React.useState(null)

  React.useEffect(async () => {
    const initialCount = await rs.call('getTheCounter', { pos: props.pos })
    setCount(initialCount)
  }, [])

  const incr = async (event) => {
    const count = await rs.call('incrementCounter', { pos: props.pos })
    setCount(count)
  }

  const decr = async (event) => {
    const count = await rs.call('decrementCounter', { pos: props.pos })
    setCount(count)
  }

  if (count === null) { return 'Loading...'; }

  return e('div', null, count, e('button', { onClick: incr }, 'increment'), e('button', { onClick: decr }, 'decrement'))
}"

#widget checkWidget
