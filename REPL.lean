import REPL.Frontend
import REPL.Lean.InfoTree
import REPL.JSON
import REPL.Main
import Cli

open Cli


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
