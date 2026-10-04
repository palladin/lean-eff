import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Display (frame : Type) : Effect where
  | draw : frame → Display frame Unit

def drawFrame {frame : Type} {r : List Effect} [Member (Display frame) r]
    (value : frame) : EffM r μ Unit :=
  send (Display.draw value)

partial def runDisplayIO {frame α : Type}
    (render : frame → String) : EffM [Display frame] μ α → IO α
  | EffF.pure _ x => pure x
  | EffF.impure _ u q =>
      match u with
      | EffectRequest.here request =>
          match request with
          | Display.draw frame => do
              IO.print (render frame)
              runDisplayIO render (Arrs.apply q ())
      | EffectRequest.there rest => EffectRequest.absurd rest

end LeanEff
