import REPL.Main
import REPL.JSON
import REPL.Snapshots
import REPL.Frontend
import REPL.Lean.InfoTree
import REPL.Lean.InfoTree.ToJson
import REPL.Lean.ContextInfo
import REPL.Lean.Environment
import REPL.Util.Path

import Cli
import Socket

open Lean Elab
open Cli
open REPL
open Socket

/-- Get lines from stdin until a blank line is entered. -/
partial def getLines : IO String := do
  let stdout <- IO.getStdout
  stdout.putStr "λ "
  let line ← (← IO.getStdin).getLine
  if line.trim.isEmpty then
    return line
  else
    return line ++ (← getLines)

/-- Commands accepted by the REPL. -/
inductive Input
| command : REPL.Command → Input
| file : REPL.File → Input
| proofStep : REPL.ProofStep → Input
| pickleEnvironment : REPL.PickleEnvironment → Input
| unpickleEnvironment : REPL.UnpickleEnvironment → Input
| pickleProofSnapshot : REPL.PickleProofState → Input
| unpickleProofSnapshot : REPL.UnpickleProofState → Input

/-- Parse a user input string to an input command. -/
def parse (query : String) : IO Input := do
  let json := Json.parse query
  match json with
  | .error e => throw <| IO.userError <| toString <| toJson <|
      (⟨"Could not parse JSON:\n" ++ e⟩ : Error)
  | .ok j => match fromJson? j with
    | .ok (r : REPL.ProofStep) => return .proofStep r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.PickleEnvironment) => return .pickleEnvironment r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.UnpickleEnvironment) => return .unpickleEnvironment r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.PickleProofState) => return .pickleProofSnapshot r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.UnpickleProofState) => return .unpickleProofSnapshot r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.Command) => return .command r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.File) => return .file r
    | .error e => throw <| IO.userError <| toString <| toJson <|
        (⟨"Could not parse as a valid JSON command:\n" ++ e⟩ : Error)

/-- Avoid buffering the output. -/
def printFlush [ToString α] (s : α) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (toString s)
  out.flush -- Flush the output

/-- Read-eval-print loop for Lean. -/
unsafe def repl : IO Unit := do
  -- Print a little header
  let version := List.getLast! <| String.splitOn ((<- IO.getEnv "ELAN_TOOLCHAIN").getD "unknown:unknown") ":"
  let header := s!"Lean REPL ({version})"
  let underline := String.map (fun _ => '=') header
  let stdout <- IO.getStdout
  stdout.putStrLn $ s!"{header}\n{underline}"
  -- Now do the loop
  StateT.run' loop {}
where
  loop : M IO Unit := do
  let query ← getLines
  if query = "" then
    return ()
  if query.startsWith "#" || query.startsWith "--" then loop else
  IO.println <| toString <| ← match ← parse query with
  | .command r => return toJson (← runCommandWithTimeout r)
  | .file r => return toJson (← processFile r)
  | .proofStep r => return toJson (← runProofStep r)
  | .pickleEnvironment r => return toJson (← pickleCommandSnapshot r)
  | .unpickleEnvironment r => return toJson (← unpickleCommandSnapshot r)
  | .pickleProofSnapshot r => return toJson (← pickleProofSnapshot r)
  | .unpickleProofSnapshot r => return toJson (← unpickleProofSnapshot r)
  printFlush "\n" -- easier to parse the output if there are blank lines
  loop

partial def tcpRepl (port : Nat) : IO Unit := do
    let address ←  SockAddr.mk "localhost" (toString port) AddressFamily.inet SockType.stream
    let socket ← Socket.mk AddressFamily.inet SockType.stream
    socket.bind address
    socket.listen 5
    IO.println s!"Started TCP server; listening on port {port}"
    serve socket
  where
    communicate (addr : SockAddr) (socket' : Socket) : M IO Unit := do
      let query <- String.fromUTF8! <$> socket'.recv 65536
      let tid ←  IO.getTID
      match query.length with
      -- End the server
        | Nat.zero => do
          let host := addr.host.getD "??"
          let port := addr.port.getD 0
          IO.println s!"Closing connection to {host}:{port}; ending thread {tid}"
          socket'.close
          return ()
      -- Loop the server
        | _ => do
          let response := toString <| ← match (← parse query) with
            | .command r => return toJson (← runCommandWithTimeout r)
            | .file r => return toJson (← processFile r)
            | .proofStep r => return toJson (← runProofStep r)
            | .pickleEnvironment r => return toJson (← pickleCommandSnapshot r)
            | .unpickleEnvironment r => return toJson (← unpickleCommandSnapshot r)
            | .pickleProofSnapshot r => return toJson (← pickleProofSnapshot r)
            | .unpickleProofSnapshot r => return toJson (← unpickleProofSnapshot r)
          let bytesSend ← socket'.send response.toUTF8
          IO.println s!"Sent back {bytesSend} bytes"
          communicate addr socket'
    serve (socket : Socket) : IO Unit := do
      repeat do
        let (remoteAddr, socket') ←  socket.accept
        IO.println s!"Connected to {remoteAddr}"
        let _ ←  IO.asTask (StateT.run' (communicate remoteAddr socket') {}) (Task.Priority.dedicated)

unsafe def replCmd : Cmd := `[Cli|
  replCmd VIA runReplCmd; ["0.0.1"]
  "This string denotes the description of `exampleCmd`."

  FLAGS:
    t, tcp : Nat;                     "Serve REPL via TCP at port `tcp`. If 0, then default to stdio."

  EXTENSIONS:
    defaultValues! #[("tcp", "0")]
]
  where
    runReplCmd (args : Parsed) : IO UInt32 := do
      Lean.initSearchPath (← Lean.findSysroot)
      match (args.flag! "tcp").as! Nat with
       | Nat.zero => do repl
       | port => do tcpRepl port
      return 0

/-- Main executable function, run as `lake exe repl`. -/
-- def main (_ : List String) : IO Unit := do
--   initSearchPath (← Lean.findSysroot)
--   repl

unsafe def main (args : List String) : IO UInt32 := replCmd.validate args
