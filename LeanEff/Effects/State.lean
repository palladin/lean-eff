import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive State (σ : Type) : Effect where
  | get : State σ σ
  | put : σ → State σ Unit

def get {σ : Type} {r : List Effect} [Member (State σ) r] : EffM r μ σ :=
  send State.get

def put {σ : Type} {r : List Effect} [Member (State σ) r]
    (value : σ) : EffM r μ Unit :=
  send (State.put value)

def modify {σ : Type} {r : List Effect} [Member (State σ) r]
    (f : σ → σ) : EffM r μ Unit := do
  let current ← get (σ := σ)
  put (f current)

private partial def runStateLoop {σ α : Type} {r r' : List Effect}
    [Remove (State σ) r r'] [Inhabited σ] [Inhabited α]
    (state : σ) : EffM r μ α → EffM r' μ (α × σ)
  | EffF.pure info x => EffF.pure info (x, state)
  | EffF.impure info u q =>
      match Remove.decomp (t := State σ) (r := r) (r' := r') u with
      | Sum.inl request =>
          match request with
          | State.get => runStateLoop state (Arrs.apply q state)
          | State.put next => runStateLoop next (Arrs.apply q ())
      | Sum.inr rest =>
          EffF.impure info rest (Arrs.one (qComp q (runStateLoop state)))

def runState {σ α : Type} {r r' : List Effect} [Remove (State σ) r r']
    [Inhabited σ] [Inhabited α]
    (initial : σ) (m : EffM r μ α) : EffM r' μ (α × σ) :=
  runStateLoop initial m

def evalState {σ α : Type} {r r' : List Effect} [Remove (State σ) r r']
    [Inhabited σ] [Inhabited α]
    (initial : σ) (m : EffM r μ α) : EffM r' μ α := do
  let result ← runState initial m
  pure result.1

def execState {σ α : Type} {r r' : List Effect} [Remove (State σ) r r']
    [Inhabited σ] [Inhabited α]
    (initial : σ) (m : EffM r μ α) : EffM r' μ σ := do
  let result ← runState initial m
  pure result.2

end LeanEff
