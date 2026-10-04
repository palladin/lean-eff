import LeanEff.Core

/- A higher-order effect can carry a computation for its handler to interpret. -/
namespace Examples.ScopedReader
open LeanEff

inductive Scope : Effect where
  | ask : Scope Nat
  | local {α : Type} (modify : Nat → Nat) : EffF Scope Empty α → Scope α

abbrev Program := EffF Scope Empty

def ask : Program Nat := EffF.send .ask

def locally (modify : Nat → Nat) (body : Program α) : Program α :=
  EffF.send (.local modify body)

/-- The nested body sees its modified environment; the caller resumes with the original one. -/
private partial def interpret [Inhabited β] (environment : Nat)
    (program : Program α) (ret : α → β) : β :=
  match program with
  | .pure _ value => ret value
  | .impure _ request continuation =>
      match request with
      | .ask => interpret environment (ArrsF.apply continuation environment) ret
      | .local modify body =>
          interpret (modify environment) body fun value =>
            interpret environment (ArrsF.apply continuation value) ret

def run [Inhabited α] (environment : Nat) (program : Program α) : α :=
  interpret environment program id

def scopedProgram : Program (Nat × Nat × Nat) := do
  let before ← ask
  let inside ← locally (fun environment => environment + before) do
    let outer ← ask
    let inner ← locally (· * 2) ask
    pure (outer + inner)
  let after ← ask
  pure (before, inside, after)

end Examples.ScopedReader
