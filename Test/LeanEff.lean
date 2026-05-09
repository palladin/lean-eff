import LeanEff

open LeanEff

def readerProgram : Eff [Reader Nat] Nat := do
  let n ← ask
  pure (n + 1)

#guard run (runReader 41 readerProgram) == 42

def writerProgram : Eff [Writer String] Nat := do
  tell "begin"
  tell "end"
  pure 7

#guard run (runWriter writerProgram) == (7, ["begin", "end"])

def mixedProgram : Eff [Reader Nat, Writer String, State Nat] Nat := do
  let env ← ask
  let state ← get
  tell s!"env={env}"
  put (state + env)
  pure (state + 1)

#guard
  run (runState (σ := Nat) 10 (runWriter (runReader 5 mixedProgram))) ==
    ((11, ["env=5"]), 15)

def exceptProgram : Eff [ExceptE String, State Nat] Nat := do
  put (σ := Nat) 5
  throw "boom"
  pure 99

#guard
  match run (runState (σ := Nat) 0 (runExcept (ε := String) exceptProgram)) with
  | (Except.error "boom", 5) => true
  | _ => false

#guard
  match run (runExcept (ε := String) (runState (σ := Nat) 0 exceptProgram)) with
  | Except.error "boom" => true
  | _ => false

def caughtProgram : Eff [ExceptE String, State Nat] Nat :=
  tryCatch (ε := String) exceptProgram fun _ => do
    let n ← get (σ := Nat)
    pure (n + 1)

#guard
  match run (runState (σ := Nat) 0 (runExcept (ε := String) caughtProgram)) with
  | (Except.ok 6, 5) => true
  | _ => false

inductive Prompt : Effect where
  | confirm : String → Prompt Bool

def confirm {r : List Effect} [Member Prompt r] (message : String) : Eff r Bool :=
  send (Prompt.confirm message)

def runPrompt {α : Type} {r r' : List Effect} [Remove Prompt r r'] [Inhabited α]
    (answer : Bool) (m : Eff r α) : Eff r' α :=
  handleRelay (t := Prompt)
    (ret := fun x => pure x)
    (handle := fun request k =>
      match request with
      | Prompt.confirm _ => k answer)
    m

def customProgram : Eff [Writer String, Prompt] Nat := do
  if (← confirm "continue?") then
    tell "yes"
    pure 1
  else
    tell "no"
    pure 0

#guard run (runWriter (runPrompt true customProgram)) == (1, ["yes"])
#guard run (runWriter (runPrompt false customProgram)) == (0, ["no"])

def addGet (x : Nat) : Eff [Reader Nat] Nat := do
  let env ← ask
  pure (env + x)

def addN : Nat → Eff [Reader Nat] Nat
  | 0 => pure 0
  | n + 1 => addN n >>= addGet

#guard run (runReader 10 (addN 1000)) == 10000

def ioProgram : Eff [LiftIO] String := do
  let n ← liftIO (pure 7)
  pure s!"io={n}"

def main : IO Unit := do
  let result ← runLiftIO ioProgram
  if result == "io=7" then
    pure ()
  else
    throw (IO.userError s!"unexpected LiftIO result: {result}")
