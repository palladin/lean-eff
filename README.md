# LeanEff

LeanEff is a small Lean 4 extensible-effects library inspired by
“Freer Monads, More Extensible Effects,” and shaped for practical Lean
programming.

The project uses Lean **4.34.1**, pinned in `lean-toolchain`.

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

## Direct Effect Families

The shared computation core is `EffF e μ α`, where `e : Type → Type u` is a
request family and `μ : Type` is an application-defined metadata type.
`ArrsF e μ α β` is its typed continuation queue. The ordinary row
API specializes the same implementation:

```lean
abbrev Eff (r : List Effect) := EffF (EffectRequest r) Empty
abbrev Arrs (r : List Effect) := ArrsF (EffectRequest r) Empty
```

Use `EffF.send` to send a direct request; `send` continues to inject a request
into a row through `Member`. Both forms use the same bind and queue operations.

A direct family can contain nested computations. For example, a scoped reader
operation passes a body to its handler:

```lean
inductive Scope : Effect where
  | ask : Scope Nat
  | local {α : Type} (modify : Nat → Nat) : EffF Scope Empty α → Scope α

abbrev Program := EffF Scope Empty
```

The complete [scoped-reader example](Examples/ScopedReader.lean) interprets the
body in a modified environment and resumes its caller in the original one.
Recursive constructor fields name the actual inductive `EffF` directly; the
convenience alias is declared afterwards. The family can vary its request
universe; computation results remain in `Type`. The direct core avoids the
extra universe level of the row-indexed `EffectRequest` when defining such
nested algebras.

Existing row handlers and snapshot functions continue to operate on `Eff r`.
They do not automatically traverse nested computations in arbitrary higher-order
effects; the corresponding handler defines those semantics.

Row signatures, qualified constructor patterns, queue views, and queue helper
names are retained through aliases. Compiler-generated declaration names now
belong to `EffF` and `ArrsF`; clients using generated recursors or inspecting
names must migrate. This is source compatibility for the ordinary row API,
not full compatibility with every generated declaration from the old datatypes.

## Node metadata

Both constructors carry `Option μ`; ordinary `pure` and `send` use `none`:

```lean
EffF.pure   : Option μ → α → EffF e μ α
EffF.impure : Option μ → e x → ArrsF e μ x α → EffF e μ α
```

Use `EffM row Metadata` for annotated effect rows, or `EffF Requests Metadata`
for a direct family. Existing `Eff row` uses `Empty` and needs no annotations.
The library's handlers and snapshot functions accept either form.

`EffF.withMetadata info program` fills missing annotations throughout that
computation's continuation spine. Explicit inner annotations win. It wraps future
continuations without calling them, and does not annotate a continuation bound
*after* this call. A terminal `pure` can carry metadata, but bind consumes an
intermediate pure node and its annotation. Metadata is diagnostic context, not an
extra effect or an execution event.

The generic core cannot inspect computations inside an opaque effect request.
Higher-order libraries propagate metadata into their own child computations.
Handlers retain annotations on forwarded requests; consumed requests follow the
handler's normal semantics. Terminal interpreters may ignore metadata.

`mapMetadata`, `metadata`, and `eraseMetadata` provide inspection and transformation.
[Metadata laws](LeanEff/Metadata.lean) prove identity, composition, compatibility
with bind, and that erasing added metadata recovers the original unannotated spine.

Migration for direct-core users: supply the metadata parameter (`Empty` to opt out),
and add an annotation argument when matching or constructing `EffF.pure` and
`EffF.impure`. Row helpers such as `Eff.pure`, `Eff.impure`, and `Eff r` retain their
existing unannotated interface.

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
`replaySnapshot`, run a deterministic check with `checkSnapshot`, or be compared
against another run with `compareSnapshots`. Use `Snapshot.toJsonString` and
`Snapshot.fromJsonString` to persist traces as JSON.

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

def checked :=
  program
    |> checkSnapshot recorded.2

def divergence :=
  compareSnapshots recorded.2 anotherSnapshot
```

Effects opt into snapshots through `SnapshotCodec`, which encodes effect
requests and responses as structured `Lean.Json` values. LeanEff includes
codecs for the built-in resumable effects.
Snapshots are request/response traces, so an effect operation that never resumes
does not produce an event through this middleware. During a check, recorded
responses drive input-like effects such as `Random` and `Input`, while
output-like effect requests such as `Display.draw` frames must match the
recorded snapshot. `SnapshotCodec.checkMode` controls whether a request replays
its recorded response or asserts the generated request.

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
  snakes render as colored `*` cells, and the same effects can run with either a
  threaded host interpreter or a single-threaded cooperative interpreter.

Run it with:

```sh
lake exe agent_snake_arena
```

Use the single-threaded cooperative interpreter with:

```sh
lake exe agent_snake_arena --cooperative
```

Record a JSON snapshot of the arena with:

```sh
lake exe agent_snake_arena --record trace.json
```

Replay the recorded snake animation with:

```sh
lake exe agent_snake_arena --replay trace.json
```

Strictly verify the snapshot without animation with:

```sh
lake exe agent_snake_arena --check trace.json
```

## V1 Notes

- Duplicate effect labels are unsupported. Wrap labels in distinct types if two
  effects have the same payload type.
- The core uses a Lean-friendly mutual `EffF` / `ArrsF` continuation queue with
  a `ViewL` operation, so continuations are consumed from the front instead of
  repeatedly walking a left spine.
- Recursive handlers are executable `partial def`s; v1 handlers therefore
  require inhabited result types.
