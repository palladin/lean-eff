import LeanEff
import Examples.ScopedReader

open LeanEff

def readerProgram : Eff [Reader Nat] Nat := do
  let n ← ask
  pure (n + 1)

#guard
  (readerProgram
    |> runReader 41
    |> run) == 42

def writerProgram : Eff [Writer String] Nat := do
  tell "begin"
  tell "end"
  pure 7

#guard
  (writerProgram
    |> runWriter
    |> run) == (7, ["begin", "end"])

def mixedProgram : Eff [Reader Nat, Writer String, State Nat] Nat := do
  let env ← ask
  let state ← get
  tell s!"env={env}"
  put (state + env)
  pure (state + 1)

#guard
  (mixedProgram
    |> runReader 5
    |> runWriter
    |> runState (σ := Nat) 10
    |> run) ==
    ((11, ["env=5"]), 15)

def exceptProgram : Eff [ExceptE String, State Nat] Nat := do
  put (σ := Nat) 5
  throw "boom"
  pure 99

#guard
  match
      exceptProgram
        |> runExcept (ε := String)
        |> runState (σ := Nat) 0
        |> run
    with
  | (Except.error "boom", 5) => true
  | _ => false

#guard
  match
      exceptProgram
        |> runState (σ := Nat) 0
        |> runExcept (ε := String)
        |> run
    with
  | Except.error "boom" => true
  | _ => false

def caughtProgram : Eff [ExceptE String, State Nat] Nat :=
  tryCatch (ε := String) exceptProgram fun _ => do
    let n ← get (σ := Nat)
    pure (n + 1)

#guard
  match
      caughtProgram
        |> runExcept (ε := String)
        |> runState (σ := Nat) 0
        |> run
    with
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

instance : SnapshotCodec Prompt where
  effectName := "Prompt"
  encodeRequest
    | Prompt.confirm message =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "confirm")
          , ("message", Lean.Json.str message)
          ]
  encodeResponse
    | Prompt.confirm _, answer => Lean.toJson answer
  decodeResponse?
    | Prompt.confirm _, value => (Lean.fromJson? value : Except String Bool).toOption

def customProgram : Eff [Writer String, Prompt] Nat := do
  if (← confirm "continue?") then
    tell "yes"
    pure 1
  else
    tell "no"
    pure 0

#guard
  (customProgram
    |> runPrompt true
    |> runWriter
    |> run) == (1, ["yes"])

#guard
  (customProgram
    |> runPrompt false
    |> runWriter
    |> run) == (0, ["no"])

def promptTrueEvent : SnapshotEvent :=
  { effect := "Prompt"
    request :=
      Lean.Json.mkObj
        [ ("op", Lean.Json.str "confirm")
        , ("message", Lean.Json.str "continue?")
        ]
    response := Lean.Json.bool true }

def promptFalseEvent : SnapshotEvent :=
  { effect := "Prompt"
    request :=
      Lean.Json.mkObj
        [ ("op", Lean.Json.str "confirm")
        , ("message", Lean.Json.str "continue?")
        ]
    response := Lean.Json.bool false }

def writerYesEvent : SnapshotEvent :=
  { effect := "Writer"
    request :=
      Lean.Json.mkObj
        [ ("op", Lean.Json.str "tell")
        , ("value", Lean.Json.str "yes")
        ]
    response := Lean.Json.null }

def writerNoEvent : SnapshotEvent :=
  { effect := "Writer"
    request :=
      Lean.Json.mkObj
        [ ("op", Lean.Json.str "tell")
        , ("value", Lean.Json.str "no")
        ]
    response := Lean.Json.null }

def customSnapshotTrue : Snapshot :=
  [promptTrueEvent, writerYesEvent]

def customSnapshotFalse : Snapshot :=
  [promptFalseEvent, writerNoEvent]

def customSnapshotOutputMismatch : Snapshot :=
  [promptTrueEvent, writerNoEvent]

#guard
  (customProgram
    |> recordSnapshot
    |> runPrompt true
    |> runWriter (ω := String)
    |> runWriter (ω := SnapshotEvent)
    |> run) == ((1, ["yes"]), customSnapshotTrue)

#guard
  match customProgram |> replaySnapshot customSnapshotTrue with
  | Except.ok 1 => true
  | _ => false

#guard
  match customProgram |> checkSnapshot customSnapshotTrue with
  | Except.ok 1 => true
  | _ => false

#guard
  match customProgram |> checkSnapshot customSnapshotOutputMismatch with
  | Except.error (SnapshotReplayError.assertionMismatch 1 recorded actual) =>
      recorded == writerNoEvent &&
        actual == SnapshotEvent.toRequest writerYesEvent
  | _ => false

#guard
  match customProgram |> replaySnapshot customSnapshotFalse with
  | Except.ok 0 => true
  | _ => false

#guard
  compareSnapshots customSnapshotTrue customSnapshotFalse ==
    some (SnapshotDivergence.eventMismatch 0 promptTrueEvent promptFalseEvent)

#guard
  match Snapshot.fromJsonString (Snapshot.toJsonString customSnapshotTrue) with
  | Except.ok snapshot => snapshot == customSnapshotTrue
  | Except.error _ => false

#guard
  match customProgram |> replaySnapshot [writerYesEvent] with
  | Except.error (SnapshotReplayError.eventMismatch 0 recorded actual) =>
      recorded == writerYesEvent &&
        actual ==
          { effect := "Prompt"
            request :=
              Lean.Json.mkObj
                [ ("op", Lean.Json.str "confirm")
                , ("message", Lean.Json.str "continue?")
                ] }
  | _ => false

def randomProgram : Eff [Random] (Nat × Nat × Bool) := do
  let low ← randNat 0 6
  let high ← randNat 10 12
  let coin ← randBool
  pure (low, high, coin)

#guard
  match randomProgram |> evalRandom 123 |> run with
  | (low, high, _) =>
      decide (low <= 6) && decide (10 <= high) && decide (high <= 12)

#guard
  (randomProgram
    |> evalRandom 123
    |> run) == (1, 10, true)

def randomSnapshot123 : Snapshot :=
  [ { effect := "Random"
      request :=
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "nat")
          , ("lo", Lean.toJson 0)
          , ("hi", Lean.toJson 6)
          ]
      response := Lean.toJson 1 }
  , { effect := "Random"
      request :=
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "nat")
          , ("lo", Lean.toJson 10)
          , ("hi", Lean.toJson 12)
          ]
      response := Lean.toJson 10 }
  , { effect := "Random"
      request := Lean.Json.mkObj [("op", Lean.Json.str "bool")]
      response := Lean.toJson true }
  ]

#guard
  (randomProgram
    |> recordSnapshot
    |> evalRandom 123
    |> runWriter (ω := SnapshotEvent)
    |> run) == ((1, 10, true), randomSnapshot123)

#guard
  match randomProgram |> replaySnapshot randomSnapshot123 with
  | Except.ok (1, 10, true) => true
  | _ => false

def addGet (x : Nat) : Eff [Reader Nat] Nat := do
  let env ← ask
  pure (env + x)

def addN : Nat → Eff [Reader Nat] Nat
  | 0 => pure 0
  | n + 1 => addN n >>= addGet

#guard
  (addN 1000
    |> runReader 10
    |> run) == 10000

def ioProgram : Eff [LiftIO] String := do
  let n ← liftIO (pure 7)
  pure s!"io={n}"

def main : IO Unit := do
  let result ← runLiftIO ioProgram
  if result == "io=7" then
    pure ()
  else
    throw (IO.userError s!"unexpected LiftIO result: {result}")

namespace Test.EffF

-- A direct family need not use EffectRequest or live in Type 1.
inductive Tick : Type → Type where
  | tick : Tick Unit

private partial def countTicks [Inhabited α]
    (program : EffF Tick α) (count : Nat := 0) : α × Nat :=
  match program with
  | .pure value => (value, count)
  | .impure .tick continuation =>
      countTicks (ArrsF.apply continuation ()) (count + 1)

private def ticks : Nat → EffF Tick Nat
  | 0 => pure 0
  | n + 1 => do
      let previous ← ticks n
      EffF.send Tick.tick
      pure (previous + 1)

#guard countTicks (pure "done") == ("done", 0)
#guard countTicks (ticks 1000) == (1000, 1000)

private def mixedResults : EffF Tick (Nat × String) := do
  let n ← ticks 3
  EffF.send Tick.tick
  pure (n + 1, s!"ticks={n}")

#guard countTicks mixedResults == ((4, "ticks=3"), 4)

-- The higher-order handler restores the caller's environment after every nested body.
open Examples.ScopedReader in
#guard run 10 scopedProgram == (10, 60, 10)

open Examples.ScopedReader in
#guard run 3 scopedProgram == (3, 18, 3)

private def stringScope : Examples.ScopedReader.Program String := do
  let number ← Examples.ScopedReader.locally (fun _ => 7) Examples.ScopedReader.ask
  let text ← Examples.ScopedReader.locally (· + number) do
    pure s!"inside={← Examples.ScopedReader.ask}"
  pure s!"{text},outside={← Examples.ScopedReader.ask}"

#guard Examples.ScopedReader.run 5 stringScope == "inside=12,outside=5"

-- Existing qualified row constructors, queue views, and helpers remain usable.
private def resumeRow (queue : Arrs [] Nat Nat) (value : Nat) : Nat :=
  match Arrs.viewL queue with
  | Arrs.ViewL.one k => LeanEff.run (k value)
  | Arrs.ViewL.cons k rest => LeanEff.run (Eff.bindArrs (k value) rest)

#guard resumeRow
  (Arrs.append (Arrs.one fun n => Eff.pure (n + 1))
    (Arrs.one fun n => Eff.pure (n * 2))) 20 == 42

-- These are the bounds used when clients recurse over the rest of a row queue.
example {r : List Effect} (q : Arrs r α β) (k : α → Eff r γ)
    (rest : Arrs r γ β) (h : Arrs.viewL q = .cons k rest) :
    sizeOf rest < sizeOf q := by
  simpa only [h] using Arrs.viewL_rest_lt q

example {r : List Effect} (q : Arrs r α β) (rest : Arrs r β γ)
    (k : α → Eff r δ) (remaining : Arrs r δ γ)
    (h : Arrs.viewLAppend q rest = .cons k remaining) :
    sizeOf remaining < sizeOf (Arrs.append q rest) := by
  simpa only [h] using Arrs.viewLAppend_rest_lt q rest

end Test.EffF
