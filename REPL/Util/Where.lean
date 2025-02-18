/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Elab.Command

/-! # `#where` command

The `#where` command prints information about the current location, including the namespace,
active `open`, `universe`, and `variable` commands, and any options set with `set_option`.
-/

open Lean Elab Command

namespace Batteries.Tactic.Where

private def describeOpenDecls (ds : List OpenDecl) : MessageData := Id.run do
  let mut lines := #[]
  let mut simple := #[]
  let flush (lines simple : Array MessageData) : Array MessageData × Array MessageData :=
    if simple.isEmpty then
      (lines, simple)
    else
      (lines.push ("open " ++ MessageData.joinSep simple.toList " "), #[])
  for d in ds do
    match d with
    | .explicit id decl =>
      (lines, simple) := flush lines simple
      lines := lines.push m!"open {id} → {decl}"
    | .simple ns ex =>
      if ex == [] then
        simple := simple.push ns
      else
        (lines, simple) := flush lines simple
        let ex' := ex.map toMessageData
        lines := lines.push m!"open {ns} hiding {MessageData.joinSep ex' ", "}"
  (lines, _) := flush lines simple
  return MessageData.joinSep lines.toList "\n"

private def describeOptions (opts : Options) : CommandElabM (Option MessageData) := do
  let mut lines := #[]
  let decls ← getOptionDecls
  for (name, val) in opts do
    match decls.find? name with
    | some decl =>
      if val != decl.defValue then
        lines := lines.push m!"set_option {name} {val}"
    | none =>
      lines := lines.push m!"-- set_option {name} {val}  -- unknown"
  if lines.isEmpty then
    return none
  else
    return MessageData.joinSep lines.toList "\n"

-- Edit(kmill): extracted this from `#where`
def mkWhere : CommandElabM MessageData := do
  let scope ← getScope
  let mut msg : Array MessageData := #[]
  -- Noncomputable
  if scope.isNoncomputable then
    msg := msg.push m!"noncomputable section"
  -- Namespace
  if !scope.currNamespace.isAnonymous then
    msg := msg.push m!"namespace {scope.currNamespace}"
  -- Open namespaces
  if !scope.openDecls.isEmpty then
    msg := msg.push <| describeOpenDecls scope.openDecls.reverse
  -- Universe levels
  if !scope.levelNames.isEmpty then
    let levels := scope.levelNames.reverse.map toMessageData
    msg := msg.push <| "universe " ++ MessageData.joinSep levels " "
  -- Variables
  if !scope.varDecls.isEmpty then
    msg := msg.push <| ← `(command| variable $scope.varDecls*)
  -- Options
  if let some m ← describeOptions scope.opts then
    msg := msg.push m
  if msg.isEmpty then
    msg := #[m!"-- In root namespace with initial scope"]
  return m!"{MessageData.joinSep msg.toList "\n\n"}"

/-- `#where` gives a description of the global scope at this point in the module.
This includes the namespace, `open` namespaces, `universe` and `variable` commands,
and options set with `set_option`. -/
elab "#where" : command => do
  logInfo <| ← mkWhere
