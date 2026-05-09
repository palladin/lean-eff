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

#eval run (runWriter (runReader 41 program))
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

## Examples

- `Examples.AsciiTetris`: an animated terminal Tetris clone with nonblocking
  controls, ANSI colors, and a next-piece preview. It uses `Reader` for
  configuration, `State` for the board, `Writer` for game events, `ExceptE` for
  quit/game-over exits, `Random` for piece generation, and an example-specific
  `Terminal` effect for terminal input/output.

Run it with:

```sh
lake exe ascii_tetris
```

Run it in a real terminal because it temporarily switches terminal input mode.

## V1 Notes

- Duplicate effect labels are unsupported. Wrap labels in distinct types if two
  effects have the same payload type.
- The core uses a Lean-friendly mutual `Eff` / `Arrs` continuation queue with
  a `ViewL` operation, so continuations are consumed from the front instead of
  repeatedly walking a left spine.
- Recursive handlers are executable `partial def`s; v1 handlers therefore
  require inhabited result types.
