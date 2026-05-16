import LeanEff.Core

namespace LeanEff

inductive Clock (τ : Type) : Effect where
  | now : Clock τ τ

def now {τ : Type} {r : List Effect} [Member (Clock τ) r] : Eff r τ :=
  send Clock.now

def runClockAt {τ α : Type} {r r' : List Effect} [Remove (Clock τ) r r']
    [Inhabited α]
    (value : τ) : Eff r α → Eff r' α :=
  handleRelay (t := Clock τ)
    (ret := fun x => pure x)
    (handle := fun request k =>
      match request with
      | Clock.now => k value)

end LeanEff
