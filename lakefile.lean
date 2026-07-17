import Lake
open Lake DSL System

package "hoverfly" where
  version := v!"0.1.0"

require ProofWidgets4 from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.105"

require "leanprover-community" / "batteries" @ git "v4.32.0"

/-
The following config is inspired by https://github.com/leanprover-community/ProofWidgets4/blob/main/lakefile.lean.
-/

input_dir widgetSrcs where
  path := "widget" / "src"
  filter := .extension <| .mem #["ts", "tsx", "css"]
  text := true

input_file widgetPackageJson where
  path := "widget" / "package.json"
  text := true

input_file widgetTsconfig where
  path := "widget" / "tsconfig.json"
  text := true

input_file widgetRollupConfig where
  path := "widget" / "rollup.config.js"
  text := true

target widget pkg : Unit := do
  let srcs ← widgetSrcs.fetch
  let packageJson ← widgetPackageJson.fetch
  let tsconfig ← widgetTsconfig.fetch
  let rollupConfig ← widgetRollupConfig.fetch
  srcs.bindM (sync := true) fun _ =>
  packageJson.bindM (sync := true) fun _ =>
  tsconfig.bindM (sync := true) fun _ =>
  rollupConfig.mapM fun _ => do
    let traceFile := pkg.buildDir / "js" / "lake.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      if ← (pkg.dir / "widget" / "node_modules").pathExists then
        proc {
          cmd := "npm"
          args := #["run", "build"]
          cwd := some (pkg.dir / "widget")
        }
      else
        logInfo s!"Hoverfly: widget/node_modules not found; \
          using prebuilt JS in src/assets/js. \
          Run `npm install` in the widget/ directory to rebuild it from source."

lean_lib Hoverfly where
  needs := #[widget]

@[default_target]
lean_exe hoverfly where
  root := `Main
