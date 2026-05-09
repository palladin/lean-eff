import LeanEff.Core

namespace LeanEff

inductive Random : Effect where
  | nat : Nat → Nat → Random Nat
  | bool : Random Bool

def randNat {r : List Effect} [Member Random r] (lo hi : Nat) : Eff r Nat :=
  send (Random.nat lo hi)

def randBool {r : List Effect} [Member Random r] : Eff r Bool :=
  send Random.bool

private partial def runRandomLoop {α : Type} {r r' : List Effect}
    [Remove Random r r'] [Inhabited α]
    (gen : StdGen) : Eff r α → Eff r' (α × StdGen)
  | Eff.pure x => pure (x, gen)
  | Eff.impure u q =>
      match Remove.decomp (t := Random) (r := r) (r' := r') u with
      | Sum.inl request =>
          match request with
          | Random.nat lo hi =>
              let (value, nextGen) := _root_.randNat gen lo hi
              runRandomLoop nextGen (Arrs.apply q value)
          | Random.bool =>
              let (value, nextGen) := _root_.randBool gen
              runRandomLoop nextGen (Arrs.apply q value)
      | Sum.inr rest =>
          Eff.impure rest (Arrs.one (qComp q (runRandomLoop gen)))

def runRandom {α : Type} {r r' : List Effect} [Remove Random r r']
    [Inhabited α]
    (seed : Nat) (m : Eff r α) : Eff r' (α × StdGen) :=
  runRandomLoop (mkStdGen seed) m

def evalRandom {α : Type} {r r' : List Effect} [Remove Random r r']
    [Inhabited α]
    (seed : Nat) (m : Eff r α) : Eff r' α := do
  let result ← runRandom seed m
  pure result.1

end LeanEff
