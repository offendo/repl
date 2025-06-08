import Lake
open System Lake DSL

package repl

require "mathlib" 
  from git "https://github.com/leanprover-community/mathlib4" @ "v4.20.0-rc5"

require "Socket" 
  from git "https://github.com/offendo/Socket.lean" @ "v4.20.0-rc5"

require "leanprover" / "Cli"

@[default_target]
lean_lib REPL where
  defaultFacets := #[LeanLib.sharedFacet]
  buildType := Lake.BuildType.release
  moreLeancArgs := #["-O3"]

lean_exe repl where
  root := `REPL
  supportInterpreter := true
  buildType := Lake.BuildType.release
