import LeanEff.Core

namespace LeanEff

inductive Sleep : Effect where
  | sleepMs : Nat → Sleep Unit

def sleepMs {r : List Effect} [Member Sleep r] (ms : Nat) : Eff r Unit :=
  send (Sleep.sleepMs ms)

partial def runSleepIO {α : Type} : Eff [Sleep] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | EffectRequest.here request =>
          match request with
          | Sleep.sleepMs ms => do
              IO.sleep (UInt32.ofNat ms)
              runSleepIO (Arrs.apply q ())
      | EffectRequest.there rest => EffectRequest.absurd rest

end LeanEff
