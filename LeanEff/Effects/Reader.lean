import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Reader (ρ : Type) : Effect where
  | ask : Reader ρ ρ

def ask {ρ : Type} {r : List Effect} [Member (Reader ρ) r] : EffM r μ ρ :=
  send Reader.ask

def runReader {ρ α : Type} {r r' : List Effect} [Remove (Reader ρ) r r']
    [Inhabited α]
    (env : ρ) : EffM r μ α → EffM r' μ α :=
  handleRelay (t := Reader ρ)
    (ret := fun x => pure x)
    (handle := fun request k =>
      match request with
      | Reader.ask => k env)

end LeanEff
