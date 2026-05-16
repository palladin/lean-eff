# LeanEff

LeanEff is a small Lean 4 extensible-effects library inspired by
“Freer Monads, More Extensible Effects,” and shaped for practical Lean
programming.

The intended user-facing style is concrete effect rows:

```lean
import LeanEff

open LeanEff

def program : Eff [Reader Nat, Writer String] Nat := do
  let n ← ask
  tell s!"n = {n}"
  pure (n + 1)

#eval program
  |> runReader 41
  |> runWriter
  |> run
```

Effect rows are treated as set-like lists for handler lookup. A handler removes
its effect wherever it appears and preserves the remaining row order; the order
in which handlers are called controls effect interaction.

## Included Effects

- `Reader ρ`: `ask`, `runReader`
- `Writer ω`: `tell`, `runWriter`
- `State σ`: `get`, `put`, `modify`, `runState`, `evalState`, `execState`
- `ExceptE ε`: `throw`, `tryCatch`, `runExcept`
- `Random`: `randNat`, `randBool`, `runRandom`, `evalRandom`
- `LiftIO`: `liftIO`, `runLiftIO`
- `Clock τ`: `now`, `runClockAt`
- `Console`: `printLine`, `readLine`, `runConsoleIO`
- `Display frame`: `drawFrame`, `runDisplayIO`
- `Input ι`: `pollInput`
- `Sleep`: `sleepMs`, `runSleepIO`

## Debug Snapshots

`recordSnapshot` records request/response effect interactions into a
`Snapshot`. A snapshot can later replay the same responses with
`replaySnapshot`, or be compared against another run with `compareSnapshots`.
Use `Snapshot.toJsonString` and `Snapshot.fromJsonString` to persist traces as
JSON.

```lean
def recorded :=
  program
    |> recordSnapshot
    |> runReader 41
    |> runWriter (ω := String)
    |> runWriter (ω := SnapshotEvent)
    |> run

def replayed :=
  program
    |> replaySnapshot recorded.2

def divergence :=
  compareSnapshots recorded.2 anotherSnapshot
```

Effects opt into snapshots through `SnapshotCodec`, which encodes effect
requests and responses as structured `Lean.Json` values. LeanEff includes
codecs for the built-in resumable effects.
Snapshots are request/response traces, so an effect operation that never resumes
does not produce an event through this middleware.

## Examples

- `Examples.AsciiTetris`: an animated terminal Tetris clone with nonblocking
  controls, ANSI colors, and a next-piece preview. It uses `Reader` for
  configuration, `State` for the board, `Writer` for game events, `ExceptE` for
  quit/game-over exits, `Random` for piece generation, `Display String` for
  drawing, `Input Command` for controls, and `Sleep` for frame pacing.

Run it with:

```sh
lake exe ascii_tetris
```

Record a JSON snapshot for deterministic debugging with:

```sh
lake exe ascii_tetris --record trace.json
```

Animate a JSON snapshot by replaying the recorded keys with:

```sh
lake exe ascii_tetris --replay trace.json
```

Strictly verify a JSON snapshot without animation with:

```sh
lake exe ascii_tetris --check trace.json
```

Run it in a real terminal because it temporarily switches terminal input mode.

- `Examples.VideoRental`: a small "Palladin's Video Rental" shop. The business
  logic uses `Clock` for the current rental day, `RentalRepo` for customers,
  movies, and rentals, and `Writer String` as a notification outbox. The demo
  interpreter backs the repository with an initialized in-memory SQLite database
  through `leanprover/leansqlite`, then runs an interactive menu until quit.

Run it with:

```sh
lake exe video_rental_shop
```

- `Examples.AgentSnake`: a concurrent multi-agent snake arena. The arena uses
  an `AgentHost` effect to spawn AI agents, publish world snapshots, and gather
  agent moves. Each AI snake is an independent `AgentEff` program that observes
  snapshots and chooses moves. `Random` drives agent jitter and food placement,
  and the same effects can run with either a threaded host interpreter or a
  single-threaded cooperative interpreter.

Run it with:

```sh
lake exe agent_snake_arena
```

Use the single-threaded cooperative interpreter with:

```sh
lake exe agent_snake_arena --cooperative
```

## V1 Notes

- Duplicate effect labels are unsupported. Wrap labels in distinct types if two
  effects have the same payload type.
- The core uses a Lean-friendly mutual `Eff` / `Arrs` continuation queue with
  a `ViewL` operation, so continuations are consumed from the front instead of
  repeatedly walking a left spine.
- Recursive handlers are executable `partial def`s; v1 handlers therefore
  require inhabited result types.
