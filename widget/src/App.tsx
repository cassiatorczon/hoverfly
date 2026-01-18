import { Fragment, useState } from 'react'
import './App.css'

type Status = "selected" | "semiselected" | "unselected" // | "hidden"

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

function App() {

  return (
    <>
      <HoverflyTree goal={{
        id: "g0",
        name: "P /\\ Q", completed: false, children: [
          {
            id: "t0",
            name: "split", children: [
              { id: "g1", name: "P", completed: false, children: [], status: "unselected" },
              { id: "g2", name: "Q", completed: false, children: [], status: "unselected" },
            ], status: "selected"
          }
        ], status: "semiselected"
      }} />
    </>
  )
}

export default App
