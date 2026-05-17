import LeanEff
import Std.Sync.Channel

open LeanEff

namespace Examples.AgentSnake

structure Point where
  x : Int
  y : Int
deriving BEq, Inhabited, Repr, Lean.ToJson, Lean.FromJson

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

def parse? : String → Option Direction
  | "up" => some .up
  | "down" => some .down
  | "left" => some .left
  | "right" => some .right
  | _ => none

end Direction

instance : ToString Direction where
  toString := Direction.name

instance : Lean.ToJson Direction where
  toJson dir := Lean.Json.str (toString dir)

instance : Lean.FromJson Direction where
  fromJson? json := do
    let value ← json.getStr?
    match Direction.parse? value with
    | some dir => pure dir
    | none => Except.error s!"unknown direction: {value}"

structure AgentProfile where
  id : Nat
  name : String
  headMark : String
  bodyMark : String
  seed : Nat
deriving Inhabited, Repr, Lean.ToJson, Lean.FromJson

structure Snake where
  id : Nat
  name : String
  headMark : String
  bodyMark : String
  body : List Point
  dir : Direction
  alive : Bool
  score : Nat
deriving Inhabited, Repr, Lean.ToJson, Lean.FromJson

structure AgentMove where
  agentId : Nat
  dir : Direction
deriving Inhabited, Repr, Lean.ToJson, Lean.FromJson

structure World where
  width : Nat
  height : Nat
  tick : Nat
  food : Point
  snakes : List Snake
  events : List String
deriving Inhabited, Repr, Lean.ToJson, Lean.FromJson

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

def decodeUnitJson? : Lean.Json → Option Unit
  | Lean.Json.null => some ()
  | _ => none

instance : SnapshotCodec AgentHost where
  effectName := "AgentHost"
  encodeRequest
    | AgentHost.spawn profile turns =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "spawn")
          , ("profile", Lean.toJson profile)
          , ("turns", Lean.toJson turns)
          ]
    | AgentHost.snapshot world =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "snapshot")
          , ("world", Lean.toJson world)
          ]
    | AgentHost.moves =>
        Lean.Json.mkObj [("op", Lean.Json.str "moves")]
  encodeResponse
    | AgentHost.spawn _ _, () => Lean.Json.null
    | AgentHost.snapshot _, () => Lean.Json.null
    | AgentHost.moves, moves => Lean.toJson moves
  decodeResponse?
    | AgentHost.spawn _ _, value => decodeUnitJson? value
    | AgentHost.snapshot _, value => decodeUnitJson? value
    | AgentHost.moves, value =>
        (Lean.fromJson? value : Except String (List AgentMove)).toOption
  checkMode
    | AgentHost.spawn _ _ => .assertRequest
    | AgentHost.snapshot _ => .assertRequest
    | AgentHost.moves => .replayResponse

def spawnAgent {r : List Effect} [Member AgentHost r]
    (profile : AgentProfile) (turns : Nat) : Eff r Unit :=
  send (AgentHost.spawn profile turns)

def publishWorld {r : List Effect} [Member AgentHost r]
    (world : World) : Eff r Unit :=
  send (AgentHost.snapshot world)

def agentMoves {r : List Effect} [Member AgentHost r] :
    Eff r (List AgentMove) :=
  send AgentHost.moves

def drawWorld {r : List Effect} [Member (Display World) r]
    (world : World) : Eff r Unit :=
  drawFrame world

abbrev AgentEff (α : Type) :=
  Eff [Reader AgentProfile, AgentRuntime, Random, Writer String] α

abbrev ArenaEff (α : Type) :=
  Eff [Reader ArenaConfig, State World, AgentHost, Display World, Sleep, Random,
    Writer String] α

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

def ansi (code text : String) : String :=
  "\x1b[" ++ code ++ "m" ++ text ++ "\x1b[0m"

def snakeColor (id : Nat) : String :=
  match id % 6 with
  | 0 => "1;36"
  | 1 => "1;32"
  | 2 => "1;35"
  | 3 => "1;33"
  | 4 => "1;34"
  | _ => "1;91"

def snakeText (snake : Snake) (mark : String) : String :=
  ansi (snakeColor snake.id) mark

def snakeAt? (world : World) (pt : Point) : Option Snake :=
  world.snakes.find? fun snake => snake.body.any fun cell => cell == pt

def headAt? (world : World) (pt : Point) : Option Snake :=
  world.snakes.find? fun snake => snake.alive && snake.head? == some pt

def cellText (world : World) (pt : Point) : String :=
  if pt == world.food then
    ansi "1;31" "*"
  else
    match headAt? world pt with
    | some snake => snakeText snake "*"
    | none =>
        match snakeAt? world pt with
        | some snake => snakeText snake snake.bodyMark
        | none => " "

def renderRow (world : World) (y : Nat) : String :=
  "|" ++
    String.intercalate ""
      ((List.range world.width).map fun x =>
        cellText world (p (Int.ofNat x) (Int.ofNat y))) ++
    "|"

def statusLine (snake : Snake) : String :=
  let state := if snake.alive then "alive" else "out"
  s!"{snakeText snake "*"} {snake.name}: score {snake.score}, {state}"

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

def renderWorld (info : RenderInfo) (world : World) : String :=
  let border := "+" ++ repeatString "-" world.width ++ "+"
  let board := [border] ++
    ((List.range world.height).map fun y => renderRow world y) ++
    [border]
  let scores := world.snakes.map statusLine
  framePrefix ++
    String.intercalate "\n" (
    ["AGENT SNAKE ARENA",
     s!"tick {world.tick}    food at ({world.food.x}, {world.food.y})"] ++
    board ++ [""] ++ scores ++
    ["", info.footer]) ++ "\n"

private structure AgentWire where
  profile : AgentProfile
  views : Std.Channel.Sync WorldView

private abbrev AgentResult :=
  (Unit × StdGen) × List String

private def buildAgentProgram (profile : AgentProfile) (turns : Nat) :
    Eff [AgentRuntime] AgentResult :=
  agentLoop turns
    |> runReader profile
    |> runRandom profile.seed
    |> runWriter

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
  let result ← runAgentRuntime host wire (buildAgentProgram wire.profile turns)
  pure result.2

private def spawnAgentIO (host : AgentHostIO) (profile : AgentProfile)
    (turns : Nat) : IO Unit := do
  let views ← Std.Channel.Sync.new (α := WorldView) (some 8)
  let wire : AgentWire := { profile, views }
  host.wires.modify fun wires => wires ++ [wire]
  let task ← IO.asTask (runAgent turns host wire)
  host.tasks.modify fun tasks => task :: tasks

private partial def runArenaThreadedIO {α : Type} (info : RenderInfo)
    (host : AgentHostIO) :
    Eff [AgentHost, Display World, Sleep] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | AgentHost.spawn profile turns => do
              spawnAgentIO host profile turns
              runArenaThreadedIO info host (Arrs.apply q ())
          | AgentHost.snapshot world => do
              let wires ← host.wires.get
              for wire in wires do
                Std.Channel.Sync.send wire.views (viewFor world wire.profile)
              runArenaThreadedIO info host (Arrs.apply q ())
          | AgentHost.moves => do
              let moves ← drainMoves host.moveQueue []
              runArenaThreadedIO info host (Arrs.apply q moves)
      | OpenUnion.there rest =>
          match rest with
          | OpenUnion.here request =>
              match request with
              | Display.draw world => do
                  IO.print (renderWorld info world)
                  runArenaThreadedIO info host (Arrs.apply q ())
          | OpenUnion.there sleepUnion =>
              match sleepUnion with
              | OpenUnion.here request =>
                  match request with
                  | Sleep.sleepMs ms => do
                      IO.sleep (UInt32.ofNat ms)
                      runArenaThreadedIO info host (Arrs.apply q ())
              | OpenUnion.there rest => OpenUnion.absurd rest

private def waitAgentLogs (host : AgentHostIO) : IO (List (List String)) := do
  let tasks ← host.tasks.get
  tasks.reverse.mapM fun task => IO.ofExcept task.get

private abbrev ArenaResult :=
  (Unit × World) × List String

private abbrev AgentLogs :=
  List (List String)

private def buildArena (cfg : ArenaConfig) (world : World) :
    Eff [AgentHost, Display World, Sleep, Random] ArenaResult :=
  arenaProgram
    |> runReader cfg
    |> runState world
    |> runWriter

private def runArenaThreaded (info : RenderInfo) (cfg : ArenaConfig) (seed : Nat)
    (world : World) (host : AgentHostIO) :
    IO ArenaResult :=
  buildArena cfg world
    |> evalRandom seed
    |> runArenaThreadedIO info host

private def runArenaThreadedRecording (info : RenderInfo) (cfg : ArenaConfig)
    (seed : Nat) (world : World) (host : AgentHostIO) :
    IO (ArenaResult × Snapshot) :=
  buildArena cfg world
    |> recordSnapshot
    |> runWriter (ω := SnapshotEvent)
    |> evalRandom seed
    |> runArenaThreadedIO info host

private partial def runArenaDisplayIO {α : Type} (info : RenderInfo) :
    Eff [Display World, Sleep] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | Display.draw world => do
              IO.print (renderWorld info world)
              runArenaDisplayIO info (Arrs.apply q ())
      | OpenUnion.there sleepUnion =>
          match sleepUnion with
          | OpenUnion.here request =>
              match request with
              | Sleep.sleepMs ms => do
                  IO.sleep (UInt32.ofNat ms)
                  runArenaDisplayIO info (Arrs.apply q ())
          | OpenUnion.there rest => OpenUnion.absurd rest

private structure CoopAgent where
  profile : AgentProfile
  program : Eff [AgentRuntime] AgentResult
  logs? : Option (List String)

private structure CoopHost where
  agents : List CoopAgent
  pendingMoves : List AgentMove

private def CoopHost.empty : CoopHost :=
  { agents := [], pendingMoves := [] }

private def coopAgentLogs (host : CoopHost) : List (List String) :=
  host.agents.filterMap fun agent => agent.logs?

private structure ResumeResult where
  program : Eff [AgentRuntime] AgentResult
  moves : List AgentMove
  logs? : Option (List String)
deriving Inhabited

private partial def resumeAgentUntilNextView (profile : AgentProfile)
    (view : WorldView) (usedView : Bool)
    (program : Eff [AgentRuntime] AgentResult)
    (moves : List AgentMove) : ResumeResult :=
  match program with
  | Eff.pure result =>
      { program
        moves := moves.reverse
        logs? := some result.2 }
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | AgentRuntime.observe =>
              if usedView then
                { program
                  moves := moves.reverse
                  logs? := none }
              else
                resumeAgentUntilNextView profile view true (Arrs.apply q view) moves
          | AgentRuntime.move dir =>
              resumeAgentUntilNextView profile view usedView (Arrs.apply q ())
                ({ agentId := profile.id, dir } :: moves)
      | OpenUnion.there rest => OpenUnion.absurd rest

private def stepCoopAgent (world : World) (agent : CoopAgent) :
    CoopAgent × List AgentMove :=
  match agent.logs? with
  | some _ => (agent, [])
  | none =>
      let view := viewFor world agent.profile
      let result :=
        resumeAgentUntilNextView agent.profile view false agent.program []
      ({ agent with program := result.program, logs? := result.logs? }, result.moves)

private def stepCoopAgents (world : World) (agents : List CoopAgent) :
    List CoopAgent × List AgentMove :=
  agents.foldl
    (fun acc agent =>
      let (nextAgents, moves) := acc
      let (agent, newMoves) := stepCoopAgent world agent
      (nextAgents ++ [agent], moves ++ newMoves))
    (([] : List CoopAgent), ([] : List AgentMove))

private partial def runAgentHostCoop {α : Type} [Inhabited α] (host : CoopHost) :
    Eff [AgentHost, Display World, Sleep] α →
      Eff [Display World, Sleep] (α × List (List String))
  | Eff.pure x => pure (x, coopAgentLogs host)
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | AgentHost.spawn profile turns =>
              let agent :=
                { profile
                  program := buildAgentProgram profile turns
                  logs? := none }
              runAgentHostCoop
                { host with agents := host.agents ++ [agent] }
                (Arrs.apply q ())
          | AgentHost.snapshot world =>
              let (agents, moves) := stepCoopAgents world host.agents
              runAgentHostCoop
                { agents
                  pendingMoves := host.pendingMoves ++ moves }
                (Arrs.apply q ())
          | AgentHost.moves =>
              runAgentHostCoop
                { host with pendingMoves := [] }
                (Arrs.apply q host.pendingMoves)
      | OpenUnion.there rest =>
          match rest with
          | OpenUnion.here request =>
              Eff.impure (OpenUnion.here request)
                (Arrs.one fun x => runAgentHostCoop host (Arrs.apply q x))
          | OpenUnion.there sleepUnion =>
              match sleepUnion with
              | OpenUnion.here request =>
                  Eff.impure (OpenUnion.there (OpenUnion.here request))
                    (Arrs.one fun x => runAgentHostCoop host (Arrs.apply q x))
              | OpenUnion.there rest => OpenUnion.absurd rest

private def runArenaCoop (info : RenderInfo) (cfg : ArenaConfig) (seed : Nat)
    (world : World) :
    IO (ArenaResult × AgentLogs) :=
  buildArena cfg world
    |> evalRandom seed
    |> runAgentHostCoop CoopHost.empty
    |> runArenaDisplayIO info

private def runArenaCoopRecording (info : RenderInfo) (cfg : ArenaConfig)
    (seed : Nat) (world : World) :
    IO ((ArenaResult × Snapshot) × AgentLogs) :=
  buildArena cfg world
    |> recordSnapshot
    |> runWriter (ω := SnapshotEvent)
    |> evalRandom seed
    |> runAgentHostCoop CoopHost.empty
    |> runArenaDisplayIO info

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
  [{ id := 1, name := "Ada", headMark := "*", bodyMark := "*", seed := 11 },
   { id := 2, name := "Grace", headMark := "*", bodyMark := "*", seed := 29 },
   { id := 3, name := "Edsger", headMark := "*", bodyMark := "*", seed := 47 }]

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

def snapshotOp? (event : SnapshotEvent) : Option String :=
  (event.request.getObjVal? "op").toOption.bind fun opJson =>
    opJson.getStr?.toOption

def isReplayOptionalEvent (event : SnapshotEvent) : Bool :=
  (event.effect == "Display" && snapshotOp? event == some "draw") ||
    (event.effect == "Sleep" && snapshotOp? event == some "sleep") ||
      (event.effect == "AgentHost" &&
        (snapshotOp? event == some "spawn" || snapshotOp? event == some "snapshot"))

structure ReplayState where
  index : Nat
  remaining : Snapshot

def eventHasOp (effect op : String) (event : SnapshotEvent) : Bool :=
  event.effect == effect && snapshotOp? event == some op

def ReplayState.consumeOptionalEvent (state : ReplayState)
    (effect op : String) : Option (Nat × SnapshotEvent) × ReplayState :=
  match state.remaining with
  | event :: rest =>
      if eventHasOp effect op event then
        (some (state.index, event), { index := state.index + 1, remaining := rest })
      else
        (none, state)
  | [] => (none, state)

partial def ReplayState.dropOptionalEvents (state : ReplayState) : ReplayState :=
  match state.remaining with
  | event :: rest =>
      if isReplayOptionalEvent event then
        ReplayState.dropOptionalEvents
          { index := state.index + 1, remaining := rest }
      else
        state
  | [] => state

def consumeSnapshotResponse {t : Effect} [SnapshotCodec t] {α : Type}
    (request : t α) (state : ReplayState) :
    Except SnapshotReplayError (α × ReplayState) :=
  let state := state.dropOptionalEvents
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

partial def replayArenaAnimatedLoop {α : Type} [Inhabited α]
    (jsonName : String) (totalSnapshots : Nat) (state : ReplayState) :
    Eff [AgentHost, Display World, Sleep, Random] α →
    IO (Except SnapshotReplayError (α × ReplayState))
  | Eff.pure x =>
      let state := state.dropOptionalEvents
      match state.remaining with
      | [] => pure (Except.ok (x, state))
      | _ => pure (Except.error (SnapshotReplayError.unusedEvents state.index state.remaining))
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | AgentHost.spawn _ _ =>
              let (_, state) := state.consumeOptionalEvent "AgentHost" "spawn"
              replayArenaAnimatedLoop jsonName totalSnapshots state (Arrs.apply q ())
          | AgentHost.snapshot _ =>
              let (_, state) := state.consumeOptionalEvent "AgentHost" "snapshot"
              replayArenaAnimatedLoop jsonName totalSnapshots state (Arrs.apply q ())
          | AgentHost.moves =>
              match consumeSnapshotResponse AgentHost.moves state with
              | Except.ok (moves, state) =>
                  replayArenaAnimatedLoop jsonName totalSnapshots state (Arrs.apply q moves)
              | Except.error error => pure (Except.error error)
      | OpenUnion.there displayUnion =>
          match displayUnion with
          | OpenUnion.here request =>
              match request with
              | Display.draw world => do
                  let (event?, state) := state.consumeOptionalEvent "Display" "draw"
                  let info : RenderInfo :=
                    { mode := "replay"
                      snapshot? :=
                        event?.map fun (index, _) =>
                          { current := index + 1
                            total := totalSnapshots }
                      json? := some jsonName }
                  IO.print (renderWorld info world)
                  replayArenaAnimatedLoop jsonName totalSnapshots state (Arrs.apply q ())
          | OpenUnion.there sleepUnion =>
              match sleepUnion with
              | OpenUnion.here request =>
                  match request with
                  | Sleep.sleepMs ms => do
                      let (_, state) := state.consumeOptionalEvent "Sleep" "sleep"
                      IO.sleep (UInt32.ofNat ms)
                      replayArenaAnimatedLoop jsonName totalSnapshots state (Arrs.apply q ())
              | OpenUnion.there randomUnion =>
                  match randomUnion with
                  | OpenUnion.here request =>
                      match consumeSnapshotResponse request state with
                      | Except.ok (response, state) =>
                          replayArenaAnimatedLoop jsonName totalSnapshots state (Arrs.apply q response)
                      | Except.error error => pure (Except.error error)
                  | OpenUnion.there rest => OpenUnion.absurd rest

def replayArenaAnimated (jsonName : String) (cfg : ArenaConfig) (world : World)
    (snapshot : Snapshot) :
    IO (Except SnapshotReplayError ArenaResult) := do
  let result ←
    replayArenaAnimatedLoop
      jsonName
      snapshot.length
      { index := 0, remaining := snapshot }
      (buildArena cfg world)
  match result with
  | Except.ok (result, _) => pure (Except.ok result)
  | Except.error error => pure (Except.error error)

def checkArenaSnapshot (cfg : ArenaConfig) (world : World)
    (snapshot : Snapshot) : Except SnapshotReplayError ArenaResult :=
  buildArena cfg world
    |> checkSnapshot snapshot

def spawnProfile? (event : SnapshotEvent) : Option AgentProfile := do
  if event.effect == "AgentHost" && snapshotOp? event == some "spawn" then
    let profileJson ← (event.request.getObjVal? "profile").toOption
    (Lean.fromJson? profileJson : Except String AgentProfile).toOption
  else
    none

def profilesFromSnapshot (snapshot : Snapshot) : Except String (List AgentProfile) :=
  let profiles := snapshot.filterMap spawnProfile?
  if profiles.isEmpty then
    Except.error "snapshot has no AgentHost spawn events"
  else
    Except.ok profiles

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

inductive Runtime where
  | threaded
  | cooperative
deriving BEq, Inhabited

def Runtime.label : Runtime → String
  | .threaded => "threaded tasks"
  | .cooperative => "single-threaded cooperative"

inductive Action where
  | play
  | record (path : String)
  | replay (path : String)
  | check (path : String)
  | help

structure Cli where
  runtime : Runtime
  action : Action

def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  lake exe agent_snake_arena [--threaded|--cooperative]"
    , "  lake exe agent_snake_arena --record trace.json [--threaded|--cooperative]"
    , "  lake exe agent_snake_arena --replay trace.json"
    , "  lake exe agent_snake_arena --check trace.json"
    ]

def setRuntime (runtime : Runtime) (cli : Cli) : Cli :=
  { cli with runtime }

def setAction (action : Action) (cli : Cli) : Except String Cli :=
  match cli.action with
  | .play => Except.ok { cli with action }
  | .help => Except.error usage
  | .record _ => Except.error usage
  | .replay _ => Except.error usage
  | .check _ => Except.error usage

def parseCliLoop : List String → Cli → Except String Cli
  | [], cli => Except.ok cli
  | "--threaded" :: rest, cli =>
      parseCliLoop rest (setRuntime .threaded cli)
  | "--cooperative" :: rest, cli =>
      parseCliLoop rest (setRuntime .cooperative cli)
  | "--record" :: path :: rest, cli => do
      let cli ← setAction (.record path) cli
      parseCliLoop rest cli
  | "--replay" :: path :: rest, cli => do
      let cli ← setAction (.replay path) cli
      parseCliLoop rest cli
  | "--check" :: path :: rest, cli => do
      let cli ← setAction (.check path) cli
      parseCliLoop rest cli
  | "--help" :: [], cli =>
      setAction .help cli
  | _, _ => Except.error usage

def parseCli (args : List String) : Except String Cli :=
  parseCliLoop args { runtime := .threaded, action := .play }

private def runWithRuntime (runtime : Runtime) (cfg : ArenaConfig)
    (arenaSeed : Nat) (world : World) :
    IO (ArenaResult × AgentLogs) := do
  let info : RenderInfo := { mode := s!"play ({runtime.label})" }
  match runtime with
  | .threaded =>
      let host ← newAgentHostIO
      let result ← withArenaScreen (runArenaThreaded info cfg arenaSeed world host)
      let agentLogs ← waitAgentLogs host
      pure (result, agentLogs)
  | .cooperative =>
      withArenaScreen (runArenaCoop info cfg arenaSeed world)

private def runWithRuntimeRecording (runtime : Runtime) (cfg : ArenaConfig)
    (path : String) (arenaSeed : Nat) (world : World) :
    IO ((ArenaResult × Snapshot) × AgentLogs) := do
  let info : RenderInfo :=
    { mode := s!"record ({runtime.label})", json? := some (jsonDisplayName path) }
  match runtime with
  | .threaded =>
      let host ← newAgentHostIO
      let result ←
        withArenaScreen (runArenaThreadedRecording info cfg arenaSeed world host)
      let agentLogs ← waitAgentLogs host
      pure (result, agentLogs)
  | .cooperative =>
      withArenaScreen (runArenaCoopRecording info cfg arenaSeed world)

def printSummary (runtimeLabel : String) (arenaLog : List String)
    (agentLogs : AgentLogs)
    (world : World) : IO Unit := do
  IO.println ""
  IO.println s!"Runtime: {runtimeLabel}"
  IO.println "Final scores"
  for snake in world.snakes do
    IO.println s!"- {snake.name}: {snake.score}"
  IO.println ""
  IO.println s!"Arena log entries: {arenaLog.length}"
  IO.println s!"Agent thought entries: {(agentLogs.map List.length).foldl (· + ·) 0}"

def main (args : List String) : IO Unit := do
  let cli ←
    match parseCli args with
    | .ok cli => pure cli
    | .error message => throw (IO.userError message)
  match cli.action with
  | .help =>
      IO.println usage
  | .play => do
      let arenaSeed ← IO.rand 0 1000000000
      let agentSeed ← IO.rand 0 1000000000
      let profiles := seedProfiles agentSeed baseProfiles
      let cfg := defaultConfig profiles
      let (((_, finalWorld), arenaLog), agentLogs) ←
        runWithRuntime cli.runtime cfg arenaSeed (initialWorld profiles)
      printSummary cli.runtime.label arenaLog agentLogs finalWorld
  | .record path => do
      let arenaSeed ← IO.rand 0 1000000000
      let agentSeed ← IO.rand 0 1000000000
      let profiles := seedProfiles agentSeed baseProfiles
      let cfg := defaultConfig profiles
      let ((((_, finalWorld), arenaLog), snapshot), agentLogs) ←
        runWithRuntimeRecording cli.runtime cfg path arenaSeed (initialWorld profiles)
      writeSnapshotJson path snapshot
      IO.println s!"Recorded {snapshot.length} effect events to {path}."
      printSummary cli.runtime.label arenaLog agentLogs finalWorld
  | .replay path => do
      let snapshot ← readSnapshotJson path
      let profiles ←
        match profilesFromSnapshot snapshot with
        | .ok profiles => pure profiles
        | .error message => throw (IO.userError message)
      let cfg := defaultConfig profiles
      let result ←
        withArenaScreen
          (replayArenaAnimated (jsonDisplayName path) cfg (initialWorld profiles) snapshot)
      match result with
      | .ok ((_, finalWorld), arenaLog) => do
          IO.println s!"Replay animation consumed {snapshot.length} snapshot events from {path}."
          printSummary "snapshot replay" arenaLog [] finalWorld
      | .error error =>
          throw (IO.userError s!"Replay diverged: {repr error}")
  | .check path => do
      let snapshot ← readSnapshotJson path
      let profiles ←
        match profilesFromSnapshot snapshot with
        | .ok profiles => pure profiles
        | .error message => throw (IO.userError message)
      let cfg := defaultConfig profiles
      match checkArenaSnapshot cfg (initialWorld profiles) snapshot with
      | .ok ((_, finalWorld), arenaLog) => do
          IO.println s!"Snapshot check replayed inputs and matched {snapshot.length} events from {path}."
          printSummary "snapshot check" arenaLog [] finalWorld
      | .error error =>
          throw (IO.userError s!"Snapshot check diverged: {repr error}")

end Examples.AgentSnake

def main (args : List String) : IO Unit :=
  Examples.AgentSnake.main args
