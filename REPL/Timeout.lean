import Init.Prelude
import Lean

open Task Lean.Elab

abbrev Seconds := Nat

def runWithTimeout
  (func : Unit → IO β)
  (timeout : Seconds)
  (prio : Task.Priority := Task.Priority.default) : BaseIO (β ⊕ IO.Error) :=
  do
    -- Launch a timer function to run in a separate thread
    let timerFunc: IO (β ⊕ IO.Error) := do
        IO.sleep $ timeout * 1000
        return Sum.inr $ IO.userError s!"error: lean server timeout after {timeout} seconds"
    let timer <- IO.asTask timerFunc

    -- Launch the main task
    let funcWrapper: IO (β ⊕ IO.Error) := func () >>= fun b => return Sum.inl b
    let job <- IO.asTask funcWrapper prio

    -- Wait for whichever finishes first
    let result <- IO.waitAny [timer, job]

    -- Cancel the timer manually if it's still going
    let timerDone <- IO.hasFinished timer
    if not timerDone then IO.cancel timer

    -- Return the result
    match result with
      | Except.ok val => return val
        -- TODO: Not sure how to throw error here properly; should basically never happen
      | Except.error err => return Sum.inr err.toString

def fast := fun () => IO.lazyPure (fun () => 5 + 5)
def slow (a : Unit) := do
   let x := (IO.sleep 10000)
   BaseIO.toIO x

#eval runWithTimeout slow 4
