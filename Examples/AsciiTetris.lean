import LeanEff

open LeanEff

namespace Examples.AsciiTetris

structure Point where
  x : Int
  y : Int
deriving BEq, Inhabited, Repr

structure Block where
  pos : Point
  piece : String
deriving Inhabited, Repr

structure Piece where
  name : String
  shape : List Point
  pos : Point
deriving Inhabited, Repr

structure Config where
  width : Nat
  height : Nat
  maxTurns : Nat
  tickMs : Nat
  framesPerDrop : Nat
deriving Inhabited, Repr

structure Game where
  occupied : List Block
  piece : Piece
  nextPiece : Piece
  score : Nat
  lines : Nat
  turns : Nat
deriving Inhabited, Repr

inductive Exit where
  | quit
  | gameOver
  | turnLimit
deriving Inhabited, Repr

inductive Command where
  | left
  | right
  | down
  | rotate
  | drop
  | quit
  | wait
deriving BEq, Inhabited, Repr

inductive Terminal : Effect where
  | draw : String → Terminal Unit
  | poll : Terminal Command
  | sleep : Nat → Terminal Unit

abbrev GameEff (α : Type) :=
  Eff [Reader Config, State Game, Writer String, ExceptE Exit, Random, Terminal] α

def drawFrame {r : List Effect} [Member Terminal r] (frame : String) : Eff r Unit :=
  send (Terminal.draw frame)

def pollInput {r : List Effect} [Member Terminal r] : Eff r Command :=
  send Terminal.poll

def sleepFrame {r : List Effect} [Member Terminal r] (ms : Nat) : Eff r Unit :=
  send (Terminal.sleep ms)

def p (x y : Int) : Point :=
  { x, y }

def spawnPos (cfg : Config) : Point :=
  p (Int.ofNat (cfg.width / 2) - 1) 0

def shape (idx : Nat) : String × List Point :=
  match idx % 7 with
  | 0 => ("I", [p (-1) 0, p 0 0, p 1 0, p 2 0])
  | 1 => ("O", [p 0 0, p 1 0, p 0 1, p 1 1])
  | 2 => ("T", [p (-1) 0, p 0 0, p 1 0, p 0 1])
  | 3 => ("L", [p (-1) 0, p 0 0, p 1 0, p 1 1])
  | 4 => ("J", [p (-1) 0, p 0 0, p 1 0, p (-1) 1])
  | 5 => ("S", [p 0 0, p 1 0, p (-1) 1, p 0 1])
  | _ => ("Z", [p (-1) 0, p 0 0, p 0 1, p 1 1])

def spawnPiece (cfg : Config) (idx : Nat) : Piece :=
  let (name, cells) := shape idx
  { name, shape := cells, pos := spawnPos cfg }

def randomPiece {r : List Effect} [Member Random r] (cfg : Config) : Eff r Piece := do
  let idx ← randNat 0 6
  pure (spawnPiece cfg idx)

def defaultConfig : Config :=
  { width := 10, height := 20, maxTurns := 10000, tickMs := 90, framesPerDrop := 7 }

def initialGame (first next : Piece) : Game :=
  { occupied := []
    piece := first
    nextPiece := next
    score := 0
    lines := 0
    turns := 0 }

def movePoint (pt : Point) (dx dy : Int) : Point :=
  { pt with x := pt.x + dx, y := pt.y + dy }

def activeCells (piece : Piece) : List Point :=
  piece.shape.map fun cell => movePoint piece.pos cell.x cell.y

def occupiedAt (cells : List Point) (pt : Point) : Bool :=
  cells.any fun cell => cell == pt

def blockAt? : List Block → Point → Option Block
  | [], _ => none
  | block :: rest, pt =>
      if block.pos == pt then
        some block
      else
        blockAt? rest pt

def blockedAt (blocks : List Block) (pt : Point) : Bool :=
  match blockAt? blocks pt with
  | some _ => true
  | none => false

def lockPiece (piece : Piece) : List Block :=
  (activeCells piece).map fun cell => { pos := cell, piece := piece.name }

def rotateCell (cell : Point) : Point :=
  p (-cell.y) cell.x

def rotatePiece (piece : Piece) : Piece :=
  { piece with shape := piece.shape.map rotateCell }

def movePiece (piece : Piece) (dx dy : Int) : Piece :=
  { piece with pos := movePoint piece.pos dx dy }

def outside (cfg : Config) (pt : Point) : Bool :=
  pt.x < 0 ||
  pt.x >= Int.ofNat cfg.width ||
  pt.y < 0 ||
  pt.y >= Int.ofNat cfg.height

def collides (cfg : Config) (occupied : List Block) (piece : Piece) : Bool :=
  (activeCells piece).any fun cell =>
    outside cfg cell || blockedAt occupied cell

def rowCount (blocks : List Block) (y : Int) : Nat :=
  (blocks.filter fun block => block.pos.y == y).length

def fullRows (cfg : Config) (blocks : List Block) : List Nat :=
  (List.range cfg.height).filter fun y =>
    decide (rowCount blocks (Int.ofNat y) >= cfg.width)

def clearedBelow (rows : List Nat) (y : Int) : Nat :=
  (rows.filter fun row => decide (Int.ofNat row > y)).length

def rowCleared (rows : List Nat) (cell : Point) : Bool :=
  rows.any fun row => cell.y == Int.ofNat row

def clearLines (cfg : Config) (blocks : List Block) : List Block × Nat :=
  let rows := fullRows cfg blocks
  let shifted :=
    blocks.filterMap fun block =>
      if rowCleared rows block.pos then
        none
      else
        some { block with pos := { block.pos with y := block.pos.y + Int.ofNat (clearedBelow rows block.pos.y) } }
  (shifted, rows.length)

def repeatString (s : String) (n : Nat) : String :=
  String.intercalate "" ((List.range n).map fun _ => s)

def ansi (code text : String) : String :=
  "\x1b[" ++ code ++ "m" ++ text ++ "\x1b[0m"

def enterScreen : String :=
  "\x1b[?1049h\x1b[?25l"

def exitScreen : String :=
  "\x1b[?25h\x1b[?1049l"

def framePrefix : String :=
  "\x1b[H\x1b[J"

def pieceColor (name : String) : String :=
  match name with
  | "I" => "36"
  | "O" => "33"
  | "T" => "35"
  | "L" => "91"
  | "J" => "34"
  | "S" => "32"
  | "Z" => "31"
  | _ => "37"

def cellText (game : Game) (pt : Point) : String :=
  if occupiedAt (activeCells game.piece) pt then
    ansi (pieceColor game.piece.name) "@@"
  else
    match blockAt? game.occupied pt with
    | some block => ansi (pieceColor block.piece) "@@"
    | none => "  "

def renderRow (cfg : Config) (game : Game) (y : Nat) : String :=
  let cells :=
    (List.range cfg.width).map fun x =>
      cellText game (p (Int.ofNat x) (Int.ofNat y))
  "|" ++ String.intercalate "" cells ++ "|"

def previewCell (piece : Piece) (x y : Nat) : String :=
  let pt := p (Int.ofNat x - 1) (Int.ofNat y)
  if occupiedAt piece.shape pt then
    ansi (pieceColor piece.name) "@@"
  else
    "  "

def renderPreviewRow (piece : Piece) (y : Nat) : String :=
  String.intercalate "" ((List.range 4).map fun x => previewCell piece x y)

def sidePanel (game : Game) : List String :=
  [s!"next: {game.nextPiece.name}",
   renderPreviewRow game.nextPiece 0,
   renderPreviewRow game.nextPiece 1,
   renderPreviewRow game.nextPiece 2,
   renderPreviewRow game.nextPiece 3,
   "",
   s!"score: {game.score}",
   s!"lines: {game.lines}",
   s!"turn:  {game.turns}",
   "",
   "a/d or arrows: move",
   "w/up: rotate",
   "s/down: soft drop",
   "space: hard drop",
   "q: quit"]

def attachPanel (board panel : List String) : List String :=
  board.zipIdx.map fun (line, idx) =>
    line ++ "  " ++ panel.getD idx ""

def render (cfg : Config) (game : Game) : String :=
  let border := "+" ++ repeatString "--" cfg.width ++ "+"
  let board := [border] ++ (List.range cfg.height).map (renderRow cfg game) ++ [border]
  let rows := attachPanel board (sidePanel game)
  String.intercalate "\n" <|
    [framePrefix, ansi "1;96" s!"ASCII Tetris  piece={game.piece.name}"] ++ rows

def byteAt? (bytes : ByteArray) (idx : Nat) : Option Nat :=
  if idx < bytes.size then
    some ((bytes.get! idx).toNat)
  else
    none

def parseCommand (bytes : ByteArray) : Command :=
  match byteAt? bytes 0, byteAt? bytes 1, byteAt? bytes 2 with
  | some 27, some 91, some 65 => .rotate
  | some 27, some 91, some 66 => .down
  | some 27, some 91, some 67 => .right
  | some 27, some 91, some 68 => .left
  | some 97, _, _ => .left
  | some 100, _, _ => .right
  | some 115, _, _ => .down
  | some 119, _, _ => .rotate
  | some 32, _, _ => .drop
  | some 113, _, _ => .quit
  | some 81, _, _ => .quit
  | _, _, _ => .wait

def testBytes (values : List Nat) : ByteArray :=
  values.foldl (fun bytes value => bytes.push (UInt8.ofNat value)) ByteArray.empty

#guard parseCommand (testBytes [27, 91, 68]) == .left
#guard parseCommand (testBytes [27, 91, 67]) == .right
#guard parseCommand (testBytes [68]) == .wait
#guard parseCommand (testBytes [100]) == .right

def draw : GameEff Unit := do
  let cfg ← ask (ρ := Config)
  let game ← get (σ := Game)
  drawFrame (render cfg game)

def pollCommand : GameEff Command := do
  pollInput

def tryMove (dx dy : Int) : GameEff Bool := do
  let cfg ← ask (ρ := Config)
  let game ← get (σ := Game)
  let candidate := movePiece game.piece dx dy
  if collides cfg game.occupied candidate then
    pure false
  else
    put { game with piece := candidate }
    pure true

def tryRotate : GameEff Bool := do
  let cfg ← ask (ρ := Config)
  let game ← get (σ := Game)
  let candidate := rotatePiece game.piece
  if collides cfg game.occupied candidate then
    pure false
  else
    put { game with piece := candidate }
    pure true

def addScore (delta : Nat) : GameEff Unit := do
  modify (σ := Game) fun game => { game with score := game.score + delta }

def lockAndSpawn : GameEff Unit := do
  let cfg ← ask (ρ := Config)
  let game ← get (σ := Game)
  let locked := game.occupied ++ lockPiece game.piece
  let (newCells, cleared) := clearLines cfg locked
  let nextPiece := game.nextPiece
  let newPreview ← randomPiece cfg
  let nextGame :=
    { game with
      occupied := newCells
      piece := nextPiece
      nextPiece := newPreview
      score := game.score + 10 + cleared * cleared * 100
      lines := game.lines + cleared }
  put nextGame
  if cleared > 0 then
    tell s!"cleared {cleared} line(s)"
  if collides cfg newCells nextPiece then
    tell s!"game over at score {nextGame.score}"
    LeanEff.throw Exit.gameOver

def stepDown : GameEff Unit := do
  let moved ← tryMove 0 1
  if moved then
    addScore 1
  else
    lockAndSpawn

def hardDropLoop : Nat → GameEff Nat
  | 0 => pure 0
  | fuel + 1 => do
      let moved ← tryMove 0 1
      if moved then
        let rest ← hardDropLoop fuel
        pure (rest + 1)
      else
        pure 0

def hardDrop : GameEff Unit := do
  let cfg ← ask (ρ := Config)
  let dropped ← hardDropLoop (cfg.height + 2)
  addScore (dropped * 2)
  tell s!"hard drop by {dropped}"
  lockAndSpawn

def applyCommand : Command → GameEff Unit
  | .left => do
      discard <| tryMove (-1) 0
  | .right => do
      discard <| tryMove 1 0
  | .down => stepDown
  | .rotate => do
      discard tryRotate
  | .drop => hardDrop
  | .quit => LeanEff.throw Exit.quit
  | .wait => pure ()

def shouldDrop (cfg : Config) (turns : Nat) : Bool :=
  if cfg.framesPerDrop == 0 then
    true
  else
    turns % cfg.framesPerDrop == 0

def frame : GameEff Unit := do
  draw
  let command ← pollCommand
  applyCommand command
  let cfg ← ask (ρ := Config)
  let game ← get (σ := Game)
  let nextTurn := game.turns + 1
  if shouldDrop cfg nextTurn then
    stepDown
  modify (σ := Game) fun game => { game with turns := nextTurn }
  sleepFrame cfg.tickMs

def gameLoop : Nat → GameEff Unit
  | 0 => LeanEff.throw Exit.turnLimit
  | fuel + 1 => do
      frame
      gameLoop fuel

def exitMessage : Exit → String
  | .quit => "quit"
  | .gameOver => "game over"
  | .turnLimit => "turn limit reached"

def buildGame (cfg : Config) : Eff [Random, Terminal] ((Except Exit Unit × Game) × List String) := do
  let first ← randomPiece cfg
  let next ← randomPiece cfg
  runWriter <|
    runState (initialGame first next) <|
      runExcept (ε := Exit) <|
        runReader cfg (gameLoop cfg.maxTurns)

def runGameLogic (cfg : Config) (seed : Nat) : Eff [Terminal] ((Except Exit Unit × Game) × List String) :=
  evalRandom seed (buildGame cfg)

partial def runTerminalIO {α : Type} : Eff [Terminal] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | Terminal.draw frame => do
              IO.println frame
              runTerminalIO (Arrs.apply q ())
          | Terminal.poll => do
              let stdin ← IO.getStdin
              let bytes ← stdin.read 8
              runTerminalIO (Arrs.apply q (parseCommand bytes))
          | Terminal.sleep ms => do
              IO.sleep (UInt32.ofNat ms)
              runTerminalIO (Arrs.apply q ())
      | OpenUnion.there rest => OpenUnion.absurd rest

def runGame (cfg : Config) : IO ((Except Exit Unit × Game) × List String) := do
  let seed ← IO.rand 0 1000000000
  runTerminalIO (runGameLogic cfg seed)

def printEvents (events : List String) : IO Unit := do
  if events.isEmpty then
    IO.println "No events recorded."
  else
    IO.println "Events:"
    for event in events do
      IO.println s!"- {event}"

def shellOutput (script : String) : IO String := do
  let out ← IO.Process.output { cmd := "sh", args := #["-c", script] }
  if out.exitCode == 0 then
    pure out.stdout
  else
    throw (IO.userError out.stderr)

def restoreTerminal (saved : String) : IO Unit := do
  IO.print exitScreen
  if saved.isEmpty then
    pure ()
  else
    discard <| IO.Process.output { cmd := "sh", args := #["-c", "stty " ++ saved ++ " < /dev/tty"] }

def withRawTerminal (body : IO α) : IO α := do
  let saved ← shellOutput "stty -g < /dev/tty"
  let saved := saved.trimAscii.toString
  discard <| shellOutput "stty -icanon -echo min 0 time 0 < /dev/tty"
  IO.print enterScreen
  try
    let result ← body
    restoreTerminal saved
    pure result
  catch e =>
    restoreTerminal saved
    throw e

def main : IO Unit := do
  let cfg := defaultConfig
  IO.println "ASCII Tetris"
  IO.println "Immediate controls: a/d/s/w, arrow keys, space, q."
  let ((outcome, finalGame), events) ← withRawTerminal (runGame cfg)
  match outcome with
  | Except.ok _ => IO.println "Finished."
  | Except.error reason => IO.println s!"Stopped: {exitMessage reason}"
  IO.println s!"Final score: {finalGame.score}, lines: {finalGame.lines}"
  printEvents events

end Examples.AsciiTetris

def main : IO Unit :=
  Examples.AsciiTetris.main
