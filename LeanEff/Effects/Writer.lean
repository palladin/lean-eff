import LeanEff.Core

namespace LeanEff

inductive Writer (ω : Type) : Effect where
  | tell : ω → Writer ω Unit

def tell {ω : Type} {r : List Effect} [Member (Writer ω) r]
    (value : ω) : Eff r Unit :=
  send (Writer.tell value)

def runWriter {ω α : Type} {r r' : List Effect} [Remove (Writer ω) r r']
    [Inhabited α]
    (m : Eff r α) : Eff r' (α × List ω) :=
  handleRelay (t := Writer ω)
    (ret := fun x => pure (x, []))
    (handle := fun request k =>
      match request with
      | Writer.tell value => do
          let result ← k ()
          pure (result.1, value :: result.2))
    m

end LeanEff
