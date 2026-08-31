module

public import Lean.Elab

open Lean Elab Term

namespace SyntaxUtil

/- Fold over a Syntax (viewed as a tree of Syntaxes). -/
public def foldSyntax
  (fMissing : β)
  (fNode : SourceInfo → SyntaxNodeKind → Array β → Syntax → β)
  (fAtom : SourceInfo → String → β)
  (fIdent : SourceInfo → Substring.Raw → Name → List Syntax.Preresolved → β)
  (s : Syntax) : β :=
  match s with
  | .missing => fMissing
  | .node info kind args =>
    fNode
      info
      kind
      (args.foldl (fun acc' arg =>
        acc' ++ #[foldSyntax fMissing fNode fAtom fIdent arg])
      #[]) s
  | .atom info val => fAtom info val
  | .ident info rawVal val preresolved => fIdent info rawVal val preresolved

/-
Fold over a Syntax (viewed as a tree of Syntaxes).
Streamlined version that uses the same combinator function for all
constructors.
-/
public def foldSyntax'
  (f : Array β → Syntax → β)
  (s : Syntax) : β :=
  match s with
  | .node _ _ args => f (args.foldl
    (fun acc' arg => acc' ++ #[foldSyntax' f arg]) #[]) s
  | _ => f #[] s

/-
Monadic fold over a Syntax (viewed as a tree of Syntaxes).

-/
public def foldMSyntax [Monad m]
  (fMissing : m β)
  (fNode : SourceInfo → SyntaxNodeKind → Array β → Syntax → m β)
  (fAtom : SourceInfo → String → m β)
  (fIdent : SourceInfo → Substring.Raw → Name → List Syntax.Preresolved → m β)
  (s : Syntax) : m β :=
  match s with
  | .missing => fMissing
  | .node info kind args => do
    let res ← args.foldlM
      (fun acc' arg =>
        do return acc' ++ #[← foldMSyntax fMissing fNode fAtom fIdent arg]) #[]
    fNode info kind res s
  | .atom info val => fAtom info val
  | .ident info rawVal val preresolved => fIdent info rawVal val preresolved

/-
Monadic fold over a Syntax (viewed as a tree of Syntaxes).

Streamlined version that uses the same combinator function for all
constructors.
-/
public def foldMSyntax' [Monad m]
  (f :  Array β → Syntax → m β)
  (s : Syntax) : m β :=
  match s with
  | .node _ _ args => do
    let res ← args.foldlM
      (fun acc' arg => do return acc' ++ #[← foldMSyntax' f arg]) #[]
    f res s
  | _ => f #[] s

/- Count the number of nodes in a Syntax (viewed as a tree of Syntaxes)
  satisfying p. -/
public def countSyntax (p : Syntax → Bool) (s : Syntax) : Nat :=
  let f acc s := if p s then Array.sum acc + 1 else Array.sum acc
  foldSyntax' f s

end SyntaxUtil
