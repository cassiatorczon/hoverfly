# hoverfly
Hoverfly is a Lean 4 library for interactive exploration of proof search
spaces. Invoking the `hoverfly` tactic launches an interface in the Lean
Infoview that allows a user to interactively navigate the proof search space
for the given theorem.

This is research code and should be considered unstable.

## Requirements
The toolchain is pinned in `lean-toolchain`.
Dependencies are pinned in `lakefile.lean` (and `lake-manifest.json`).

## Building

```sh
lake build          # builds the library and examples
```

## Usage
First, import `Hoverfly`.

```lean4
import Hoverfly
```

There are then several ways to add tactics to Hoverfly, all modelled after
methods for adding tactics to `Aesop`.

As shown below, a list of
newline-separated tactics can be passed as an argument to the
`add_hoverfly_tactics` command. (As in `Aesop`, this addition is stateful, and
calling `add_hoverfly_tactics` several times in the same scope with different
lists will result in the union of those lists being added to Hoverfly.)

```lean4
add_hoverfly_tactics
  [
    assumption
    contradiction
    intro
    rfl
    rewrite [Eq.comm]
    induction HYP
    cases HYP
  ]
```

`HYP` here is a placeholder for a tactic argument that will be filled in as
Hoverfly runs. For example, `induction` takes one argument, so we add
`induction HYP` to Hoverfly; when generating lists of applicable tactics for
each goal, Hoverfly will then attempt to replace `HYP` with elements of the
goal context. If a tactic has multiple arguments, all arguments get `HYP` as a
placeholder (e.g., `induction HYP generalizing HYP`); each argument gets filled
in independently from the context.

As with Aesop, `apply X` for some lemma `X` can be added to Hoverfly by
annotating `X` with `@[hoverfly]`.

Finally, to simply add all tactics that are currently available to Aesop to
Hoverfly, you can use the `add_aesop_tactics_to_hoverfly` command.


After adding tactics to Hoverfly, call the `hoverfly` tactic on a given
predicate.


```lean4
theorem rfl_example
  : 1 = 1 := by
  hoverfly
```



Note: the tactic only launches the Infoview interface; it does not solve the
goal directly, but rather `sorry`s it out while the user finds a proof via the
interface. Once the user has found a proof via the interface, they can use the
`Finalize proof` button to replace the `hoverfly` tactic in the Lean file with
the proof.

## Code organization
-