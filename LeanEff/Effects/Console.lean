import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive Console : Effect where
  | printLine : String → Console Unit
  | readLine : Console String

def printLine {r : List Effect} [Member Console r]
    (line : String) : EffM r μ Unit :=
  send (Console.printLine line)

def readLine {r : List Effect} [Member Console r] : EffM r μ String :=
  send Console.readLine

partial def runConsoleIO {α : Type} : EffM [Console] μ α → IO α
  | EffF.pure _ x => pure x
  | EffF.impure _ u q =>
      match u with
      | EffectRequest.here request =>
          match request with
          | Console.printLine line => do
              IO.println line
              runConsoleIO (Arrs.apply q ())
          | Console.readLine => do
              let stdin ← IO.getStdin
              let line ← stdin.getLine
              runConsoleIO (Arrs.apply q (line.trimAscii.toString))
      | EffectRequest.there rest => EffectRequest.absurd rest

end LeanEff
