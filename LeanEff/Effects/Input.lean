import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Input (ι : Type) : Effect where
  | poll : Input ι ι

def pollInput {ι : Type} {r : List Effect} [Member (Input ι) r] : EffM r μ ι :=
  send Input.poll

end LeanEff
