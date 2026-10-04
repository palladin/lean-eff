import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Sleep : Effect where
  | sleepMs : Nat → Sleep Unit

def sleepMs {r : List Effect} [Member Sleep r] (ms : Nat) : EffM r μ Unit :=
  send (Sleep.sleepMs ms)

partial def runSleepIO {α : Type} : EffM [Sleep] μ α → IO α
  | EffF.pure _ x => pure x
  | EffF.impure _ u q =>
      match u with
      | EffectRequest.here request =>
          match request with
          | Sleep.sleepMs ms => do
              IO.sleep (UInt32.ofNat ms)
              runSleepIO (Arrs.apply q ())
      | EffectRequest.there rest => EffectRequest.absurd rest

end LeanEff
