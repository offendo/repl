/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend
import REPL.Timeout
import REPL.JSON
import REPL.Lean.InfoTree
import REPL.Lean.InfoTree.ToJson
import REPL.Lean.ContextInfo
import REPL.Lean.Environment
import REPL.Util.Path

open Lean Elab REPL
open Lean.Elab Json

namespace Lean.Elab.IO

/--
Wrapper for `IO.processCommands` that enables info states, and returns
* the new command state
* messages
* info trees
-/
def processCommandsWithInfoTrees
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO (Command.State × List Message × List InfoTree) := do
  let commandState := { commandState with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState
  pure (s, s.messages.toList, s.infoState.trees.toList)

/--
Process some text input, with or without an existing command state.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.

Returns:
1. The header-only command state (only useful when cmdState? is none)
2. The resulting command state after processing the entire input
3. List of messages
4. List of info trees
-/
def processInput (input : String) (cmdState? : Option Command.State)
    (opts : Options := {}) (fileName : Option String := none) :
    IO (Command.State × Command.State × List Message × List InfoTree) := unsafe do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName

  match cmdState? with
  | none => do
    -- Split the processing into two phases to prevent self-reference in proofs in tactic mode
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header opts messages inputCtx
    let headerOnlyState := Command.mkState env messages opts
    let (cmdState, messages, trees) ← processCommandsWithInfoTrees inputCtx parserState headerOnlyState
    return (headerOnlyState, cmdState, messages, trees)

  | some cmdStateBefore => do
    let parserState : Parser.ModuleParserState := {}
    let (cmdStateAfter, messages, trees) ← processCommandsWithInfoTrees inputCtx parserState cmdStateBefore
    return (cmdStateBefore, cmdStateAfter, messages, trees)

def processInputWithTimeout (timeout : UInt32) (input : String) (cmdState? : Option Command.State)
    (opts : Options := {}) (fileName : Option String := none) :
    IO ((Command.State × Command.State × List Message × List InfoTree) ⊕ IO.Error) :=
    do
      let func := fun () => processInput input cmdState? opts fileName
      let result <- runWithTimeout func timeout Task.Priority.dedicated
      return result

@[export do_init]
def doInit := unsafe do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution

structure PyResponse where
  state : Command.State
  msgs : String
  tree : String

@[export process_input_empty_state]
def processInputEmptyState (input : String) : IO PyResponse := unsafe do
  doInit
  let opts : Options := {}
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  -- Split the processing into two phases to prevent self-reference in proofs in tactic mode
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  let headerOnlyState := Command.mkState env messages opts

  let (cmdState, messages, trees) ←  processCommandsWithInfoTrees inputCtx parserState headerOnlyState
  let tree := Json.arr (←  trees.toArray.mapM fun t => t.toJson none)
  let msgs := Json.arr (<- messages.toArray.mapM fun m => m.toJson)
  return ⟨cmdState, toString msgs, toString tree⟩

@[export process_input_from_state]
def processInputFromState (input : String) (cmdState : Command.State) : IO PyResponse := unsafe do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName

  let parserState : Parser.ModuleParserState := {}
  let (cmdStateAfter, messages, trees) ← processCommandsWithInfoTrees inputCtx parserState cmdState
  let tree := Json.arr (←  trees.toArray.mapM fun t => t.toJson none)
  let msgs := Json.arr (<- messages.toArray.mapM fun m => m.toJson)
  return ⟨cmdStateAfter, toString msgs, toString tree⟩

@[export process_input_with_timeout]
def processInputWithTimeoutEmptyState (timeout : UInt32) (input : String):
    IO PyResponse :=
    unsafe do
      let func := fun () => processInputEmptyState input
      match <- runWithTimeout func timeout Task.Priority.dedicated with
        | .inl val => return val
        | .inr err => throw err

@[export process_input_with_timeout_from_state]
def processInputWithTimeoutFromState (timeout : UInt32) (input : String) (cmdState : Command.State) :
    IO PyResponse :=
    unsafe do
      Lean.initSearchPath (← Lean.findSysroot)
      enableInitializersExecution
      let func := fun () => processInputFromState input cmdState
      match <- runWithTimeout func timeout Task.Priority.dedicated with
        | .inl val => return val
        | .inr err => throw err
