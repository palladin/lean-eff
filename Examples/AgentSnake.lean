import LeanEff
import Std.Sync.Channel

open LeanEff

namespace Examples.AgentSnake

structure Point where
  x : Int
  y : Int
deriving BEq, Inhabited, Repr

def p (x y : Int) : Point :=
  { x, y }

inductive Direction where
  | up
  | down
  | left
  | right
deriving BEq, Inhabited, Repr

namespace Direction

def all : List Direction :=
  [.up, .down, .left, .right]

def delta : Direction → Point
  | .up => p 0 (-1)
  | .down => p 0 1
  | .left => p (-1) 0
  | .right => p 1 0

def opposite : Direction → Direction
  | .up => .down
  | .down => .up
  | .left => .right
  | .right => .left

def name : Direction → String
  | .up => "up"
  | .down => "down"
  | .left => "left"
  | .right => "right"

end Direction

instance : ToString Direction where
  toString := Direction.name

structure AgentProfile where
  id : Nat
  name : String
  headMark : String
  bodyMark : String
  seed : Nat
deriving Inhabited, Repr

structure Snake where
  id : Nat
  name : String
  headMark : String
  bodyMark : String
  body : List Point
  dir : Direction
  alive : Bool
  score : Nat
deriving Inhabited, Repr

structure AgentMove where
  agentId : Nat
  dir : Direction
deriving Inhabited, Repr

structure World where
  width : Nat
  height : Nat
  tick : Nat
  food : Point
  snakes : List Snake
  events : List String
deriving Inhabited, Repr

structure WorldView where
  tick : Nat
  width : Nat
  height : Nat
  food : Point
  you : Snake
  snakes : List Snake
deriving Inhabited, Repr

structure ArenaConfig where
  maxTicks : Nat
  tickMs : Nat
  thinkMs : Nat
  agents : List AgentProfile
deriving Inhabited, Repr

inductive AgentRuntime : Effect where
  | observe : AgentRuntime WorldView
  | move : Direction → AgentRuntime Unit

def viewWorld {r : List Effect} [Member AgentRuntime r] : Eff r WorldView :=
  send AgentRuntime.observe

def chooseMove {r : List Effect} [Member AgentRuntime r]
    (dir : Direction) : Eff r Unit :=
  send (AgentRuntime.move dir)

inductive AgentHost : Effect where
  | spawn : AgentProfile → Nat → AgentHost Unit
  | snapshot : World → AgentHost Unit
  | moves : AgentHost (List AgentMove)

def spawnAgent {r : List Effect} [Member AgentHost r]
    (profile : AgentProfile) (turns : Nat) : Eff r Unit :=
  send (AgentHost.spawn profile turns)

def publishWorld {r : List Effect} [Member AgentHost r]
    (world : World) : Eff r Unit :=
  send (AgentHost.snapshot world)

def agentMoves {r : List Effect} [Member AgentHost r] :
    Eff r (List AgentMove) :=
  send AgentHost.moves

inductive ArenaRuntime : Effect where
  | draw : World → ArenaRuntime Unit
  | sleep : Nat → ArenaRuntime Unit

def drawWorld {r : List Effect} [Member ArenaRuntime r]
    (world : World) : Eff r Unit :=
  send (ArenaRuntime.draw world)

def sleepMs {r : List Effect} [Member ArenaRuntime r] (ms : Nat) : Eff r Unit :=
  send (ArenaRuntime.sleep ms)

abbrev AgentEff (α : Type) :=
  Eff [Reader AgentProfile, AgentRuntime, Random, Writer String] α

abbrev ArenaEff (α : Type) :=
  Eff [Reader ArenaConfig, State World, AgentHost, ArenaRuntime, Random, Writer String] α

def move (pt : Point) (dir : Direction) : Point :=
  let d := dir.delta
  { x := pt.x + d.x, y := pt.y + d.y }

def inside (width height : Nat) (pt : Point) : Bool :=
  0 <= pt.x && pt.x < Int.ofNat width &&
    0 <= pt.y && pt.y < Int.ofNat height

def absDiff (a b : Int) : Nat :=
  if a < b then
    (b - a).toNat
  else
    (a - b).toNat

def distance (a b : Point) : Nat :=
  absDiff a.x b.x + absDiff a.y b.y

def dropLast : List α → List α
  | [] => []
  | _ :: [] => []
  | x :: xs => x :: dropLast xs

def Snake.head? (snake : Snake) : Option Point :=
  snake.body.head?

def Snake.head (snake : Snake) : Point :=
  snake.head?.getD default

def occupiedCells (snakes : List Snake) : List Point :=
  snakes.foldr (fun snake cells => snake.body ++ cells) []

def cellOccupied (snakes : List Snake) (pt : Point) : Bool :=
  (occupiedCells snakes).any fun cell => cell == pt

def findSnake? (world : World) (agentId : Nat) : Option Snake :=
  world.snakes.find? fun snake => snake.id == agentId

def deadSnake (profile : AgentProfile) : Snake :=
  { id := profile.id
    name := profile.name
    headMark := profile.headMark
    bodyMark := profile.bodyMark
    body := []
    dir := .right
    alive := false
    score := 0 }

def viewFor (world : World) (profile : AgentProfile) : WorldView :=
  { tick := world.tick
    width := world.width
    height := world.height
    food := world.food
    you := (findSnake? world profile.id).getD (deadSnake profile)
    snakes := world.snakes }

def safeDirections (view : WorldView) : List Direction :=
  Direction.all.filter fun dir =>
    let next := move view.you.head dir
    dir != view.you.dir.opposite &&
      inside view.width view.height next &&
        !cellOccupied view.snakes next

def pickDirection {r : List Effect} [Member Random r]
    (fallback : Direction) (choices : List Direction) : Eff r Direction := do
  match choices with
  | [] => pure fallback
  | _ =>
      let idx ← randNat 0 (choices.length - 1)
      pure (choices.getD idx fallback)

def minScore : List (Direction × Nat) → Nat
  | [] => 0
  | (_, score) :: rest =>
      rest.foldl (fun best item => Nat.min best item.2) score

def bestDirections (view : WorldView) (choices : List Direction) : List Direction :=
  let scored := choices.map fun dir => (dir, distance (move view.you.head dir) view.food)
  let best := minScore scored
  scored.filterMap fun item =>
    if item.2 == best then
      some item.1
    else
      none

def chooseDirection (view : WorldView) : AgentEff Direction := do
  let choices := safeDirections view
  let fallback := view.you.dir
  let jitter ← randNat 0 9
  if jitter == 0 then
    pickDirection fallback choices
  else
    pickDirection fallback (bestDirections view choices)

partial def agentLoop : Nat → AgentEff Unit
  | 0 => pure ()
  | n + 1 => do
      let profile ← ask (ρ := AgentProfile)
      let view ← viewWorld
      if view.you.alive then
        let dir ← chooseDirection view
        chooseMove dir
        tell s!"{profile.name} tick {view.tick}: {dir}"
      agentLoop n

def moveFor (moves : List AgentMove) (agentId : Nat) : Option Direction :=
  moves.foldl
    (fun found move =>
      if move.agentId == agentId then
        some move.dir
      else
        found)
    none

def steerSnake (moves : List AgentMove) (snake : Snake) : Snake :=
  if !snake.alive then
    snake
  else
    match moveFor moves snake.id with
    | none => snake
    | some dir =>
        if dir == snake.dir.opposite then
          snake
        else
          { snake with dir := dir }

def countPoint (points : List Point) (pt : Point) : Nat :=
  points.foldl (fun count point => if point == pt then count + 1 else count) 0

def proposedHeads (snakes : List Snake) : List Point :=
  snakes.filterMap fun snake =>
    if snake.alive then
      some (move snake.head snake.dir)
    else
      none

structure StepResult where
  snake : Snake
  event? : Option String
  ate : Bool
deriving Inhabited, Repr

def stepSnake (world : World) (steered : List Snake) (heads : List Point)
    (snake : Snake) : StepResult :=
  if !snake.alive then
    { snake, event? := none, ate := false }
  else
    let next := move snake.head snake.dir
    let crashed :=
      !inside world.width world.height next ||
        cellOccupied steered next ||
          countPoint heads next > 1
    if crashed then
      { snake := { snake with alive := false }
        event? := some s!"{snake.name} crashed at tick {world.tick}"
        ate := false }
    else
      let ate := next == world.food
      let body :=
        if ate then
          next :: snake.body
        else
          next :: dropLast snake.body
      let snake := { snake with body, score := snake.score + if ate then 1 else 0 }
      { snake
        event? := if ate then some s!"{snake.name} ate food at tick {world.tick}" else none
        ate }

def allPoints (width height : Nat) : List Point :=
  (List.range height).foldr
    (fun y points =>
      ((List.range width).map fun x => p (Int.ofNat x) (Int.ofNat y)) ++ points)
    []

def freeFoodCells (world : World) : List Point :=
  let blocked := occupiedCells world.snakes
  (allPoints world.width world.height).filter fun point =>
    !(blocked.any fun cell => cell == point)

def randomFood {r : List Effect} [Member Random r] (world : World) :
    Eff r Point := do
  let free := freeFoodCells world
  match free with
  | [] => pure world.food
  | _ =>
      let idx ← randNat 0 (free.length - 1)
      pure (free.getD idx world.food)

def foodEvent (food : Point) : String :=
  s!"food spawned at ({food.x}, {food.y})"

def advanceWorld (moves : List AgentMove) (world : World) : ArenaEff World := do
  let steered := world.snakes.map (steerSnake moves)
  let heads := proposedHeads steered
  let results := steered.map (stepSnake world steered heads)
  let snakes := results.map fun result => result.snake
  let newEvents := results.filterMap fun result => result.event?
  let ate := results.any fun result => result.ate
  let nextWorld :=
    { world with
      tick := world.tick + 1
      snakes
      events := (newEvents ++ world.events).take 7 }
  if ate then
    let food ← randomFood nextWorld
    pure { nextWorld with food, events := (foodEvent food :: nextWorld.events).take 7 }
  else
    pure nextWorld

partial def arenaLoop : Nat → ArenaEff Unit
  | 0 => do
      let world ← get (σ := World)
      drawWorld world
      tell s!"arena stopped at tick {world.tick}"
  | n + 1 => do
      let cfg ← ask (ρ := ArenaConfig)
      let world ← get (σ := World)
      drawWorld world
      publishWorld world
      sleepMs cfg.thinkMs
      let moves ← agentMoves
      tell s!"tick {world.tick}: collected {moves.length} move(s)"
      let nextWorld ← advanceWorld moves world
      put (σ := World) nextWorld
      sleepMs cfg.tickMs
      arenaLoop n

def arenaProgram : ArenaEff Unit := do
  let cfg ← ask (ρ := ArenaConfig)
  for profile in cfg.agents do
    spawnAgent profile cfg.maxTicks
    tell s!"spawned agent {profile.name}"
  let world ← get (σ := World)
  let food ← randomFood world
  put (σ := World) { world with food, events := [foodEvent food] }
  tell s!"initial {foodEvent food}"
  arenaLoop cfg.maxTicks

def repeatString (s : String) (n : Nat) : String :=
  String.intercalate "" ((List.range n).map fun _ => s)

def enterScreen : String :=
  "\x1b[?1049h\x1b[?25l"

def exitScreen : String :=
  "\x1b[?25h\x1b[?1049l"

def framePrefix : String :=
  "\x1b[H\x1b[J"

def snakeAt? (world : World) (pt : Point) : Option Snake :=
  world.snakes.find? fun snake => snake.body.any fun cell => cell == pt

def headAt? (world : World) (pt : Point) : Option Snake :=
  world.snakes.find? fun snake => snake.alive && snake.head? == some pt

def cellText (world : World) (pt : Point) : String :=
  if pt == world.food then
    "*"
  else
    match headAt? world pt with
    | some snake => snake.headMark
    | none =>
        match snakeAt? world pt with
        | some snake => snake.bodyMark
        | none => " "

def renderRow (world : World) (y : Nat) : String :=
  "|" ++
    String.intercalate ""
      ((List.range world.width).map fun x =>
        cellText world (p (Int.ofNat x) (Int.ofNat y))) ++
    "|"

def statusLine (snake : Snake) : String :=
  let state := if snake.alive then "alive" else "out"
  s!"{snake.headMark} {snake.name}: score {snake.score}, {state}"

def renderWorld (world : World) : String :=
  let border := "+" ++ repeatString "-" world.width ++ "+"
  let board := [border] ++
    ((List.range world.height).map fun y => renderRow world y) ++
    [border]
  let scores := world.snakes.map statusLine
  let events :=
    if world.events.isEmpty then
      ["events: none yet"]
    else
      ["events:"] ++ world.events.map (fun event => "  " ++ event)
  framePrefix ++
    String.intercalate "\n" (
    ["AGENT SNAKE ARENA",
     s!"tick {world.tick}    food at ({world.food.x}, {world.food.y})"] ++
    board ++ [""] ++ scores ++ [""] ++ events ++
    ["", "Each snake is a separate Eff agent running in its own Lean task."]) ++ "\n"

private structure AgentWire where
  profile : AgentProfile
  views : Std.Channel.Sync WorldView

private structure AgentHostIO where
  moveQueue : Std.Channel.Sync AgentMove
  wires : IO.Ref (List AgentWire)
  tasks : IO.Ref (List (Task (Except IO.Error (List String))))

private def newAgentHostIO : IO AgentHostIO := do
  let moveQueue ← Std.Channel.Sync.new (α := AgentMove) (some 128)
  let wires ← IO.mkRef ([] : List AgentWire)
  let tasks ← IO.mkRef ([] : List (Task (Except IO.Error (List String))))
  pure { moveQueue, wires, tasks }

private partial def drainMoves
    (ch : Std.Channel.Sync AgentMove) (acc : List AgentMove) :
    IO (List AgentMove) := do
  match (← Std.Channel.Sync.tryRecv ch) with
  | none => pure acc.reverse
  | some move => drainMoves ch (move :: acc)

private partial def runAgentRuntime {α : Type} (host : AgentHostIO) (wire : AgentWire) :
    Eff [AgentRuntime] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | AgentRuntime.observe => do
              let view ← Std.Channel.Sync.recv wire.views
              runAgentRuntime host wire (Arrs.apply q view)
          | AgentRuntime.move dir => do
              Std.Channel.Sync.send host.moveQueue { agentId := wire.profile.id, dir }
              runAgentRuntime host wire (Arrs.apply q ())
      | OpenUnion.there rest => OpenUnion.absurd rest

private def runAgent (turns : Nat) (host : AgentHostIO) (wire : AgentWire) :
    IO (List String) := do
  let ((_, _gen), thoughts) ←
    runAgentRuntime host wire <|
      runWriter <|
        runRandom wire.profile.seed <|
          runReader wire.profile (agentLoop turns)
  pure thoughts

private def spawnAgentIO (host : AgentHostIO) (profile : AgentProfile)
    (turns : Nat) : IO Unit := do
  let views ← Std.Channel.Sync.new (α := WorldView) (some 8)
  let wire : AgentWire := { profile, views }
  host.wires.modify fun wires => wires ++ [wire]
  let task ← IO.asTask (runAgent turns host wire)
  host.tasks.modify fun tasks => task :: tasks

private partial def runArenaIO {α : Type} (host : AgentHostIO) :
    Eff [AgentHost, ArenaRuntime] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | AgentHost.spawn profile turns => do
              spawnAgentIO host profile turns
              runArenaIO host (Arrs.apply q ())
          | AgentHost.snapshot world => do
              let wires ← host.wires.get
              for wire in wires do
                Std.Channel.Sync.send wire.views (viewFor world wire.profile)
              runArenaIO host (Arrs.apply q ())
          | AgentHost.moves => do
              let moves ← drainMoves host.moveQueue []
              runArenaIO host (Arrs.apply q moves)
      | OpenUnion.there rest =>
          match rest with
          | OpenUnion.here request =>
              match request with
              | ArenaRuntime.draw world => do
                  IO.print (renderWorld world)
                  runArenaIO host (Arrs.apply q ())
              | ArenaRuntime.sleep ms => do
                  IO.sleep (UInt32.ofNat ms)
                  runArenaIO host (Arrs.apply q ())
          | OpenUnion.there rest => OpenUnion.absurd rest

private def waitAgentLogs (host : AgentHostIO) : IO (List (List String)) := do
  let tasks ← host.tasks.get
  tasks.reverse.mapM fun task => IO.ofExcept task.get

private def runArena (cfg : ArenaConfig) (seed : Nat) (world : World) (host : AgentHostIO) :
    IO ((Unit × World) × List String) :=
  runArenaIO host <|
    runWriter <|
      evalRandom seed <|
        runState world <|
          runReader cfg arenaProgram

def withArenaScreen (body : IO α) : IO α := do
  IO.print enterScreen
  try
    let result ← body
    IO.print exitScreen
    pure result
  catch e =>
    IO.print exitScreen
    throw e

def mkSnake (profile : AgentProfile) (body : List Point)
    (dir : Direction) : Snake :=
  { id := profile.id
    name := profile.name
    headMark := profile.headMark
    bodyMark := profile.bodyMark
    body
    dir
    alive := true
    score := 0 }

def baseProfiles : List AgentProfile :=
  [{ id := 1, name := "Ada", headMark := "A", bodyMark := "a", seed := 11 },
   { id := 2, name := "Grace", headMark := "G", bodyMark := "g", seed := 29 },
   { id := 3, name := "Edsger", headMark := "E", bodyMark := "e", seed := 47 }]

def seedProfiles (seed : Nat) (profiles : List AgentProfile) : List AgentProfile :=
  profiles.zipIdx.map fun (profile, idx) =>
    { profile with seed := seed + idx * 7919 }

def initialWorld (profiles : List AgentProfile) : World :=
  let ada := profiles.getD 0 default
  let grace := profiles.getD 1 default
  let edsger := profiles.getD 2 default
  { width := 32
    height := 14
    tick := 0
    food := p 0 0
    snakes :=
      [mkSnake ada [p 2 2, p 1 2, p 0 2] .right,
       mkSnake grace [p 29 11, p 30 11, p 31 11] .left,
       mkSnake edsger [p 15 1, p 15 0] .down]
    events := [] }

def defaultConfig (profiles : List AgentProfile) : ArenaConfig :=
  { maxTicks := 90, tickMs := 75, thinkMs := 10, agents := profiles }

def printSummary (arenaLog : List String) (agentLogs : List (List String))
    (world : World) : IO Unit := do
  IO.println ""
  IO.println "Final scores"
  for snake in world.snakes do
    IO.println s!"- {snake.name}: {snake.score}"
  IO.println ""
  IO.println s!"Arena log entries: {arenaLog.length}"
  IO.println s!"Agent thought entries: {(agentLogs.map List.length).foldl (· + ·) 0}"

def main : IO Unit := do
  let arenaSeed ← IO.rand 0 1000000000
  let agentSeed ← IO.rand 0 1000000000
  let profiles := seedProfiles agentSeed baseProfiles
  let cfg := defaultConfig profiles
  let host ← newAgentHostIO
  let ((_, finalWorld), arenaLog) ←
    withArenaScreen (runArena cfg arenaSeed (initialWorld profiles) host)
  let agentLogs ← waitAgentLogs host
  printSummary arenaLog agentLogs finalWorld

end Examples.AgentSnake

def main : IO Unit :=
  Examples.AgentSnake.main
