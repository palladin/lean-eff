import LeanEff.Core

namespace LeanEff

inductive Input (ι : Type) : Effect where
  | poll : Input ι ι

def pollInput {ι : Type} {r : List Effect} [Member (Input ι) r] : Eff r ι :=
  send Input.poll

end LeanEff
