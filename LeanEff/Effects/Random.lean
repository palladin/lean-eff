import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Random : Effect where
  | nat : Nat → Nat → Random Nat
  | bool : Random Bool

def randNat {r : List Effect} [Member Random r] (lo hi : Nat) : EffM r μ Nat :=
  send (Random.nat lo hi)

def randBool {r : List Effect} [Member Random r] : EffM r μ Bool :=
  send Random.bool

private partial def runRandomLoop {α : Type} {r r' : List Effect}
    [Remove Random r r'] [Inhabited α]
    (gen : StdGen) : EffM r μ α → EffM r' μ (α × StdGen)
  | EffF.pure info x => EffF.pure info (x, gen)
  | EffF.impure info u q =>
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
          EffF.impure info rest (Arrs.one (qComp q (runRandomLoop gen)))

def runRandom {α : Type} {r r' : List Effect} [Remove Random r r']
    [Inhabited α]
    (seed : Nat) (m : EffM r μ α) : EffM r' μ (α × StdGen) :=
  runRandomLoop (mkStdGen seed) m

def evalRandom {α : Type} {r r' : List Effect} [Remove Random r r']
    [Inhabited α]
    (seed : Nat) (m : EffM r μ α) : EffM r' μ α := do
  let result ← runRandom seed m
  pure result.1

end LeanEff
