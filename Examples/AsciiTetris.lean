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

def Command.label : Command → String
  | .left => "left"
  | .right => "right"
  | .down => "down"
  | .rotate => "rotate"
  | .drop => "drop"
  | .quit => "quit"
  | .wait => "wait"

def Command.parse? : String → Option Command
  | "left" => some .left
  | "right" => some .right
  | "down" => some .down
  | "rotate" => some .rotate
  | "drop" => some .drop
  | "quit" => some .quit
  | "wait" => some .wait
  | _ => none

instance : ToString Command where
  toString := Command.label

instance : Lean.ToJson Command where
  toJson command := Lean.Json.str (toString command)

instance : Lean.FromJson Command where
  fromJson? json := do
    let value ← json.getStr?
    match Command.parse? value with
    | some command => pure command
    | none => Except.error s!"unknown command: {value}"

abbrev GameEff (α : Type) :=
  Eff [Reader Config, State Game, Writer String, ExceptE Exit, Random,
    Display String, Input Command, Sleep] α

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

structure SnapshotProgress where
  current : Nat
  total : Nat

structure RenderInfo where
  mode : String
  snapshot? : Option SnapshotProgress := none
  json? : Option String := none

def snapshotProgressBarWidth : Nat := 16

def SnapshotProgress.bar (progress : SnapshotProgress) : String :=
  let filled :=
    if progress.total == 0 then
      0
    else
      Nat.min snapshotProgressBarWidth
        ((progress.current * snapshotProgressBarWidth) / progress.total)
  if filled >= snapshotProgressBarWidth then
    repeatString "=" snapshotProgressBarWidth
  else
    repeatString "=" filled ++ ">" ++
      repeatString "." (snapshotProgressBarWidth - filled - 1)

def SnapshotProgress.display (progress : SnapshotProgress) : String :=
  s!"snap [{progress.bar}] {progress.current}/{progress.total}"

def RenderInfo.footer (info : RenderInfo) : String :=
  let snapshot :=
    match info.snapshot? with
    | none => []
    | some progress => [progress.display]
  let json :=
    match info.json? with
    | none => []
    | some path => [s!"json: {path}"]
  String.intercalate " | " (["mode: " ++ info.mode] ++ snapshot ++ json)

def renderFrame (info : RenderInfo) (frame : String) : String :=
  frame ++ "\n\n" ++ info.footer

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
  sleepMs cfg.tickMs

def gameLoop : Nat → GameEff Unit
  | 0 => LeanEff.throw Exit.turnLimit
  | fuel + 1 => do
      frame
      gameLoop fuel

def exitMessage : Exit → String
  | .quit => "quit"
  | .gameOver => "game over"
  | .turnLimit => "turn limit reached"

def buildGame (cfg : Config) :
    Eff [Random, Display String, Input Command, Sleep]
      ((Except Exit Unit × Game) × List String) := do
  let first ← randomPiece cfg
  let next ← randomPiece cfg
  gameLoop cfg.maxTurns
    |> runReader cfg
    |> runExcept (ε := Exit)
    |> runState (initialGame first next)
    |> runWriter

def runGameLogic (cfg : Config) (seed : Nat) :
    Eff [Display String, Input Command, Sleep]
      ((Except Exit Unit × Game) × List String) :=
  evalRandom seed (buildGame cfg)

abbrev GameResult :=
  (Except Exit Unit × Game) × List String

partial def runTerminalIO {α : Type} (info : RenderInfo) :
    Eff [Display String, Input Command, Sleep] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | EffectRequest.here request =>
          match request with
          | Display.draw frame => do
              IO.println (renderFrame info frame)
              runTerminalIO info (Arrs.apply q ())
      | EffectRequest.there inputUnion =>
          match inputUnion with
          | EffectRequest.here request =>
              match request with
              | Input.poll => do
                  let stdin ← IO.getStdin
                  let bytes ← stdin.read 8
                  runTerminalIO info (Arrs.apply q (parseCommand bytes))
          | EffectRequest.there sleepUnion =>
              match sleepUnion with
              | EffectRequest.here request =>
                  match request with
                  | Sleep.sleepMs ms => do
                      IO.sleep (UInt32.ofNat ms)
                      runTerminalIO info (Arrs.apply q ())
              | EffectRequest.there rest => EffectRequest.absurd rest

def runGame (cfg : Config) : IO ((Except Exit Unit × Game) × List String) := do
  let seed ← IO.rand 0 1000000000
  runTerminalIO { mode := "play" } (runGameLogic cfg seed)

def runGameRecording (info : RenderInfo) (cfg : Config) : IO (GameResult × Snapshot) := do
  let seed ← IO.rand 0 1000000000
  buildGame cfg
    |> recordSnapshot
    |> runWriter (ω := SnapshotEvent)
    |> evalRandom seed
    |> runTerminalIO info

def checkGameSnapshot (cfg : Config) (snapshot : Snapshot) :
    Except SnapshotReplayError GameResult :=
  buildGame cfg
    |> checkSnapshot snapshot

structure ReplayState where
  index : Nat
  remaining : Snapshot

def snapshotOp? (event : SnapshotEvent) : Option String :=
  (event.request.getObjVal? "op").toOption.bind fun opJson =>
    opJson.getStr?.toOption

def isReplayDisplayEvent (event : SnapshotEvent) : Bool :=
  (event.effect == "Display" && snapshotOp? event == some "draw") ||
    (event.effect == "Sleep" && snapshotOp? event == some "sleep")

def eventHasOp (effect op : String) (event : SnapshotEvent) : Bool :=
  event.effect == effect && snapshotOp? event == some op

partial def ReplayState.dropDisplayEvents (state : ReplayState) : ReplayState :=
  match state.remaining with
  | event :: rest =>
      if isReplayDisplayEvent event then
        ReplayState.dropDisplayEvents
          { index := state.index + 1, remaining := rest }
      else
        state
  | [] => state

def ReplayState.consumeOptionalEvent (state : ReplayState)
    (effect op : String) : Option (Nat × SnapshotEvent) × ReplayState :=
  match state.remaining with
  | event :: rest =>
      if eventHasOp effect op event then
        (some (state.index, event), { index := state.index + 1, remaining := rest })
      else
        (none, state)
  | [] => (none, state)

def consumeSnapshotResponse {t : Effect} [SnapshotCodec t] {α : Type}
    (request : t α) (state : ReplayState) :
    Except SnapshotReplayError (α × ReplayState) :=
  let state := state.dropDisplayEvents
  let actual := SnapshotCodec.requestOf request
  match state.remaining with
  | [] => Except.error (SnapshotReplayError.snapshotEnded state.index actual)
      | event :: rest =>
      if SnapshotCodec.matchesRequest request event then
        match SnapshotCodec.decodeResponse? request event.response with
        | some response =>
            Except.ok (response, { index := state.index + 1, remaining := rest })
        | none =>
            Except.error
              (SnapshotReplayError.responseDecodeFailed state.index event actual)
      else
        Except.error (SnapshotReplayError.eventMismatch state.index event actual)

partial def replayGameAnimatedLoop {α : Type} [Inhabited α]
    (jsonName : String) (totalSnapshots : Nat) (state : ReplayState) :
    Eff [Random, Display String, Input Command, Sleep] α →
    IO (Except SnapshotReplayError (α × ReplayState))
  | Eff.pure x =>
      let state := state.dropDisplayEvents
      match state.remaining with
      | [] => pure (Except.ok (x, state))
      | _ => pure (Except.error (SnapshotReplayError.unusedEvents state.index state.remaining))
  | Eff.impure u q =>
      match u with
      | EffectRequest.here request =>
          match consumeSnapshotResponse request state with
          | Except.ok (response, state) =>
              replayGameAnimatedLoop jsonName totalSnapshots state (Arrs.apply q response)
          | Except.error error => pure (Except.error error)
      | EffectRequest.there terminalUnion =>
          match terminalUnion with
          | EffectRequest.here request =>
              match request with
              | Display.draw frame => do
                  let (event?, state) := state.consumeOptionalEvent "Display" "draw"
                  let info : RenderInfo :=
                    { mode := "replay"
                      snapshot? :=
                        event?.map fun (index, _) =>
                          { current := index + 1
                            total := totalSnapshots }
                      json? := some jsonName }
                  IO.println (renderFrame info frame)
                  replayGameAnimatedLoop jsonName totalSnapshots state (Arrs.apply q ())
          | EffectRequest.there inputUnion =>
              match inputUnion with
              | EffectRequest.here request =>
                  match request with
                  | Input.poll =>
                    match consumeSnapshotResponse (Input.poll (ι := Command)) state with
                    | Except.ok (response, state) =>
                        replayGameAnimatedLoop jsonName totalSnapshots state (Arrs.apply q response)
                    | Except.error error => pure (Except.error error)
              | EffectRequest.there sleepUnion =>
                  match sleepUnion with
                  | EffectRequest.here request =>
                      match request with
                      | Sleep.sleepMs ms => do
                          let (_, state) := state.consumeOptionalEvent "Sleep" "sleep"
                          IO.sleep (UInt32.ofNat ms)
                          replayGameAnimatedLoop jsonName totalSnapshots state (Arrs.apply q ())
                  | EffectRequest.there rest => EffectRequest.absurd rest

def replayGameAnimated (jsonName : String) (cfg : Config) (snapshot : Snapshot) :
    IO (Except SnapshotReplayError GameResult) := do
  let result ←
    replayGameAnimatedLoop
      jsonName
      snapshot.length
      { index := 0, remaining := snapshot }
      (buildGame cfg)
  match result with
  | Except.ok (result, _) => pure (Except.ok result)
  | Except.error error => pure (Except.error error)

def writeSnapshotJson (path : String) (snapshot : Snapshot) : IO Unit :=
  IO.FS.writeFile (System.FilePath.mk path) (Snapshot.toJsonString snapshot ++ "\n")

def readSnapshotJson (path : String) : IO Snapshot := do
  let contents ← IO.FS.readFile (System.FilePath.mk path)
  match Snapshot.fromJsonString contents with
  | Except.ok snapshot => pure snapshot
  | Except.error error =>
      throw (IO.userError s!"could not read snapshot JSON from {path}: {error}")

def jsonDisplayName (path : String) : String :=
  match (System.FilePath.mk path).fileName with
  | some name => name
  | none => path

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

def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  lake exe ascii_tetris"
    , "  lake exe ascii_tetris --record trace.json"
    , "  lake exe ascii_tetris --replay trace.json"
    , "  lake exe ascii_tetris --check trace.json"
    ]

inductive RunMode where
  | play
  | record (path : String)
  | replay (path : String)
  | check (path : String)
  | help

def parseRunMode : List String → Except String RunMode
  | [] => Except.ok .play
  | ["--record", path] => Except.ok (.record path)
  | ["--replay", path] => Except.ok (.replay path)
  | ["--check", path] => Except.ok (.check path)
  | ["--help"] => Except.ok .help
  | _ => Except.error usage

def printSummary (result : GameResult) : IO Unit := do
  let ((outcome, finalGame), _) := result
  match outcome with
  | Except.ok _ => IO.println "Finished."
  | Except.error reason => IO.println s!"Stopped: {exitMessage reason}"
  IO.println s!"Final score: {finalGame.score}, lines: {finalGame.lines}"

def printIntro : IO Unit := do
  IO.println "ASCII Tetris"
  IO.println "Immediate controls: a/d/s/w, arrow keys, space, q."

def main (args : List String) : IO Unit := do
  let cfg := defaultConfig
  let mode ←
    match parseRunMode args with
    | Except.ok mode => pure mode
    | Except.error message => throw (IO.userError message)
  match mode with
  | RunMode.play => do
      printIntro
      let result ← withRawTerminal (runGame cfg)
      printSummary result
  | RunMode.record path => do
      printIntro
      IO.println s!"Recording snapshot to {path}"
      let info : RenderInfo :=
        { mode := "record", json? := some (jsonDisplayName path) }
      let (result, snapshot) ← withRawTerminal (runGameRecording info cfg)
      writeSnapshotJson path snapshot
      IO.println s!"Recorded {snapshot.length} effect events."
      printSummary result
  | RunMode.replay path => do
      let snapshot ← readSnapshotJson path
      let result ← withRawTerminal (replayGameAnimated (jsonDisplayName path) cfg snapshot)
      match result with
      | Except.ok result => do
          IO.println s!"Replay animation consumed {snapshot.length} snapshot events from {path}."
          printSummary result
      | Except.error error =>
          throw (IO.userError s!"Replay diverged: {repr error}")
  | RunMode.check path => do
      let snapshot ← readSnapshotJson path
      match checkGameSnapshot cfg snapshot with
      | Except.ok result => do
          IO.println s!"Snapshot check replayed inputs and matched {snapshot.length} events from {path}."
          printSummary result
      | Except.error error =>
          throw (IO.userError s!"Snapshot check diverged: {repr error}")
  | RunMode.help =>
      IO.println usage

end Examples.AsciiTetris

def main (args : List String) : IO Unit :=
  Examples.AsciiTetris.main args
