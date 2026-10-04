import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Clock (τ : Type) : Effect where
  | now : Clock τ τ

def now {τ : Type} {r : List Effect} [Member (Clock τ) r] : EffM r μ τ :=
  send Clock.now

def runClockAt {τ α : Type} {r r' : List Effect} [Remove (Clock τ) r r']
    [Inhabited α]
    (value : τ) : EffM r μ α → EffM r' μ α :=
  handleRelay (t := Clock τ)
    (ret := fun x => pure x)
    (handle := fun request k =>
      match request with
      | Clock.now => k value)

end LeanEff
