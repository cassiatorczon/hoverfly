import Lean
open Lean Widget Server
set_option doc.verso true

/-!
Our goal is to have a widget client that keeps a reference to data that is
managed on the server. The "increment" operation updates the value known to the
server, but the client can't access this value until they use the "update"
operation.

The client doesn't keep track of the current up-to-date counter value, the
client only keeps track of a {lean}`WithRpcRef Int`, an opaque value that represents
a pointer to the true counter value which lives on the server.

This is an obviously silly example, given that it would be just as easy for
the client to keep track of {name}`Int`. But if the server-side value was large
or difficult to seralize, this starts making sense.
-/

/-!
First: bookkeeping. We can only have {name}`WithRpcRef` values for types that have
a {name}`TypeName` instance.
-/

deriving instance TypeName for Int

/--
Stores an integer server-side and returns a reference to it.
-/
@[server_rpc_method]
def initializeCounter (initialValue : Int) : RequestM (RequestTask (WithRpcRef Int)) :=
  RequestM.asTask do
    WithRpcRef.mk initialValue

/--
Increments a server-side reference, and returns a reference to the updated value.
-/
@[server_rpc_method]
def incrementCounter (stateRef : (WithRpcRef Int)) : RequestM (RequestTask (WithRpcRef Int)) :=
  RequestM.asTask do
    let newRefVal := stateRef.val + 1
    return ← WithRpcRef.mk newRefVal

/--
Takes a server-side reference, and returns the value that this reference refers to.
-/
@[server_rpc_method]
def updateCounter (stateRef : (WithRpcRef Int)) : RequestM (RequestTask Int) :=
  RequestM.asTask do
    return stateRef.val

@[widget_module]
def stateWidget : Widget.Module where
  javascript := "
import * as React from 'react';
const e = React.createElement;
import { useRpcSession } from '@leanprover/infoview';

export default function() {
  const rs = useRpcSession()
  const [stateRef, setStateRef] = React.useState(null)
  const [count, setCount] = React.useState(null)
  const [error, setError] = React.useState(null)

  React.useEffect(() => {
    const INITIAL_VAL = 0;
    rs.call('initializeCounter', INITIAL_VAL)
      .then(newRef => {
        setStateRef(newRef);
        setCount(INITIAL_VAL);
      })
      .catch(err => {
        setError(`${err}`)
      })
  }, [])

  const incr = async (event) => {
    const newRef = await rs.call('incrementCounter', stateRef)
    setStateRef(newRef)
  }

  const upd = async (event) => {
    const count = await rs.call('updateCounter', stateRef)
    setCount(count);
  }

  if (error !== null) { return `Unexpected error: ${error}`}
  if (stateRef === null) { return 'Loading...'; }
  return e('div', null,
    count,
    e('button', { onClick: incr }, 'increment' ),
    e('button', { onClick: upd }, 'update'))
}"

#widget stateWidget

/-!

My first reaction when Wojciech was telling me about this style
was that it effectively represented a memory leak on the Lean side:
sure, Lean can recover all the memory used for counter values when the widget is unmounted,
but doesn't Lean need to keep track of every single value that's ever been sent
to a widget via {name}`WithRpcRef` just in case the widget held on to that ref?

But no, they thought of that: the widgets framework uses
[JavaScript finalizers](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/FinalizationRegistry#notes_on_cleanup_callbacks)
so that, when JavaScript garbage collects a widget-side {name}`WithRpcRef` value,
Lean gets a signal that the widget no longer holds a reference to the value.

-/
