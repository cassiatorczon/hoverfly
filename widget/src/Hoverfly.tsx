import { Fragment, useState } from 'react'
import { useRpcSession, useAsync, mapRpcError } from '@leanprover/infoview';
// import './App.css'

type Status = "selected" | "semiselected" | "unselected" | "hidden"

type Tactic = { id: string, name: string, children: Goal[], status: Status }

type Goal = { id: string, name: string, completed: boolean, children: Tactic[], status: Status }

function renderGoal(goal: Goal, onClick: (id: string) => void): React.ReactNode {
  return (
    <Fragment key={goal.id}>
      <li onClick={() => onClick(goal.id)}>{goal.name} [{goal.status}]</li>
      <ul> {goal.children.map((child: Tactic) => renderTactic(child, onClick))}</ul >
    </Fragment>)
}

function renderTactic(tactic: Tactic, onClick: (id: string) => void): React.ReactNode {
  return (
    <Fragment key={tactic.id}>
      <li onClick={() => onClick(tactic.id)}>{tactic.name} [{tactic.status}]</li>
      <ul>{tactic.children.map((child: Goal) => renderGoal(child, onClick))}</ul>
    </Fragment>)
}

function handleClick(goal: Goal, _: string): Goal {
  return goal
}

function HoverflyTree({ goal }: { goal: Goal }) {
  const [state, setState] = useState(goal)

  return (
    <>
      <ul>
        {renderGoal(state, (id) => {
          setState(handleClick(state, id))
        })}
      </ul>
    </>
  )
}

function Hoverfly() {
  const rs = useRpcSession()

  const st = useAsync(() =>
    rs.call('getInitialState', ""), [rs])

  return st.state === 'resolved' ? <HoverflyTree goal={st.value as Goal} />
    : st.state === 'rejected' ?
      <p>{mapRpcError(st.error).message}</p>
      : <p>Loading...</p>
}

export default Hoverfly
