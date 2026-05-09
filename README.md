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
- `LiftIO`: `liftIO`, `runLiftIO`

## V1 Notes

- Duplicate effect labels are unsupported. Wrap labels in distinct types if two
  effects have the same payload type.
- The core uses a Lean-friendly mutual `Eff` / `Arrs` continuation queue with
  a `ViewL` operation, so continuations are consumed from the front instead of
  repeatedly walking a left spine.
- Recursive handlers are executable `partial def`s; v1 handlers therefore
  require inhabited result types.
