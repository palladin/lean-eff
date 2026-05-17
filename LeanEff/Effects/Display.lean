import LeanEff.Core

namespace LeanEff

inductive Display (frame : Type) : Effect where
  | draw : frame → Display frame Unit

def drawFrame {frame : Type} {r : List Effect} [Member (Display frame) r]
    (value : frame) : Eff r Unit :=
  send (Display.draw value)

partial def runDisplayIO {frame α : Type}
    (render : frame → String) : Eff [Display frame] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | EffectRequest.here request =>
          match request with
          | Display.draw frame => do
              IO.print (render frame)
              runDisplayIO render (Arrs.apply q ())
      | EffectRequest.there rest => EffectRequest.absurd rest

end LeanEff
