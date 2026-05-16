import LeanEff.Core

namespace LeanEff

inductive Console : Effect where
  | printLine : String → Console Unit
  | readLine : Console String

def printLine {r : List Effect} [Member Console r]
    (line : String) : Eff r Unit :=
  send (Console.printLine line)

def readLine {r : List Effect} [Member Console r] : Eff r String :=
  send Console.readLine

partial def runConsoleIO {α : Type} : Eff [Console] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | Console.printLine line => do
              IO.println line
              runConsoleIO (Arrs.apply q ())
          | Console.readLine => do
              let stdin ← IO.getStdin
              let line ← stdin.getLine
              runConsoleIO (Arrs.apply q (line.trimAscii.toString))
      | OpenUnion.there rest => OpenUnion.absurd rest

end LeanEff
