import LeanEff.Core

namespace LeanEff

inductive State (σ : Type) : Effect where
  | get : State σ σ
  | put : σ → State σ Unit

def get {σ : Type} {r : List Effect} [Member (State σ) r] : Eff r σ :=
  send State.get

def put {σ : Type} {r : List Effect} [Member (State σ) r]
    (value : σ) : Eff r Unit :=
  send (State.put value)

def modify {σ : Type} {r : List Effect} [Member (State σ) r]
    (f : σ → σ) : Eff r Unit := do
  let current ← get (σ := σ)
  put (f current)

private partial def runStateLoop {σ α : Type} {r r' : List Effect}
    [Remove (State σ) r r'] [Inhabited σ] [Inhabited α]
    (state : σ) : Eff r α → Eff r' (α × σ)
  | Eff.pure x => pure (x, state)
  | Eff.impure u q =>
      match Remove.decomp (t := State σ) (r := r) (r' := r') u with
      | Sum.inl request =>
          match request with
          | State.get => runStateLoop state (Arrs.apply q state)
          | State.put next => runStateLoop next (Arrs.apply q ())
      | Sum.inr rest =>
          Eff.impure rest (Arrs.one (qComp q (runStateLoop state)))

def runState {σ α : Type} {r r' : List Effect} [Remove (State σ) r r']
    [Inhabited σ] [Inhabited α]
    (initial : σ) (m : Eff r α) : Eff r' (α × σ) :=
  runStateLoop initial m

def evalState {σ α : Type} {r r' : List Effect} [Remove (State σ) r r']
    [Inhabited σ] [Inhabited α]
    (initial : σ) (m : Eff r α) : Eff r' α := do
  let result ← runState initial m
  pure result.1

def execState {σ α : Type} {r r' : List Effect} [Remove (State σ) r r']
    [Inhabited σ] [Inhabited α]
    (initial : σ) (m : Eff r α) : Eff r' σ := do
  let result ← runState initial m
  pure result.2

end LeanEff
