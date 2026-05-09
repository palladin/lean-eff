import LeanEff.Core

namespace LeanEff

inductive Reader (ρ : Type) : Effect where
  | ask : Reader ρ ρ

def ask {ρ : Type} {r : List Effect} [Member (Reader ρ) r] : Eff r ρ :=
  send Reader.ask

def runReader {ρ α : Type} {r r' : List Effect} [Remove (Reader ρ) r r']
    [Inhabited α]
    (env : ρ) : Eff r α → Eff r' α :=
  handleRelay (t := Reader ρ)
    (ret := fun x => pure x)
    (handle := fun request k =>
      match request with
      | Reader.ask => k env)

end LeanEff
