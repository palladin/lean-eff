import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive LiftIO : Effect where
  | lift {α : Type} : IO α → LiftIO α

def liftIO {α : Type} {r : List Effect} [Member LiftIO r]
    (action : IO α) : EffM r μ α :=
  send (LiftIO.lift action)

partial def runLiftIO {α : Type} : EffM [LiftIO] μ α → IO α
  | EffF.pure _ x => pure x
  | EffF.impure _ u q =>
      match u with
      | EffectRequest.here request =>
          match request with
          | LiftIO.lift action => do
              let x ← action
              runLiftIO (Arrs.apply q x)
      | EffectRequest.there rest => EffectRequest.absurd rest

end LeanEff
