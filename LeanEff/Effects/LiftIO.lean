import LeanEff.Core

namespace LeanEff

inductive LiftIO : Effect where
  | lift {α : Type} : IO α → LiftIO α

def liftIO {α : Type} {r : List Effect} [Member LiftIO r]
    (action : IO α) : Eff r α :=
  send (LiftIO.lift action)

partial def runLiftIO {α : Type} : Eff [LiftIO] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | LiftIO.lift action => do
              let x ← action
              runLiftIO (Arrs.apply q x)
      | OpenUnion.there rest => OpenUnion.absurd rest

end LeanEff
