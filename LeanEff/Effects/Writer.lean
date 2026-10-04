import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Writer (ω : Type) : Effect where
  | tell : ω → Writer ω Unit

def tell {ω : Type} {r : List Effect} [Member (Writer ω) r]
    (value : ω) : EffM r μ Unit :=
  send (Writer.tell value)

def runWriter {ω α : Type} {r r' : List Effect} [Remove (Writer ω) r r']
    [Inhabited α]
    (m : EffM r μ α) : EffM r' μ (α × List ω) :=
  handleRelay (t := Writer ω)
    (ret := fun x => pure (x, []))
    (handle := fun request k =>
      match request with
      | Writer.tell value => do
          let result ← k ()
          pure (result.1, value :: result.2))
    m

end LeanEff
