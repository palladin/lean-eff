import Lean.Data.Json
import LeanEff.Effects.Reader
import LeanEff.Effects.Writer
import LeanEff.Effects.State
import LeanEff.Effects.Random
import LeanEff.Effects.Clock
import LeanEff.Effects.Console
import LeanEff.Effects.Display
import LeanEff.Effects.Input
import LeanEff.Effects.Sleep

deriving instance Repr for Lean.Json

namespace LeanEff

structure SnapshotRequest where
  effect : String
  request : Lean.Json
deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure SnapshotEvent where
  effect : String
  request : Lean.Json
  response : Lean.Json
deriving Repr, BEq, Lean.ToJson, Lean.FromJson

abbrev Snapshot := List SnapshotEvent

def Snapshot.toJsonString (snapshot : Snapshot) : String :=
  (Lean.toJson snapshot).pretty

def Snapshot.fromJsonString (contents : String) : Except String Snapshot := do
  let json ← Lean.Json.parse contents
  Lean.fromJson? json

namespace SnapshotEvent

def toRequest (event : SnapshotEvent) : SnapshotRequest :=
  { effect := event.effect, request := event.request }

end SnapshotEvent

inductive SnapshotCheckMode where
  | replayResponse
  | assertRequest
deriving Repr, BEq

class SnapshotCodec (t : Effect) where
  effectName : String
  encodeRequest : {α : Type} → t α → Lean.Json
  encodeResponse : {α : Type} → t α → α → Lean.Json
  decodeResponse? : {α : Type} → t α → Lean.Json → Option α
  checkMode : {α : Type} → t α → SnapshotCheckMode :=
    fun _ => .replayResponse

namespace SnapshotCodec

def requestOf {t : Effect} [SnapshotCodec t] {α : Type}
    (request : t α) : SnapshotRequest :=
  { effect := SnapshotCodec.effectName (t := t)
    request := SnapshotCodec.encodeRequest request }

def eventOf {t : Effect} [SnapshotCodec t] {α : Type}
    (request : t α) (response : α) : SnapshotEvent :=
  { effect := SnapshotCodec.effectName (t := t)
    request := SnapshotCodec.encodeRequest request
    response := SnapshotCodec.encodeResponse request response }

def matchesRequest {t : Effect} [SnapshotCodec t] {α : Type}
    (request : t α) (event : SnapshotEvent) : Bool :=
  event.effect == SnapshotCodec.effectName (t := t) &&
    event.request == SnapshotCodec.encodeRequest request

end SnapshotCodec

class SnapshotRow (r : List Effect) where
  requestOf : {α : Type} → EffectRequest r α → SnapshotRequest
  eventOf : {α : Type} → EffectRequest r α → α → SnapshotEvent
  matchesRequest : {α : Type} → EffectRequest r α → SnapshotEvent → Bool
  decodeResponse? : {α : Type} → EffectRequest r α → SnapshotEvent → Option α
  checkMode : {α : Type} → EffectRequest r α → SnapshotCheckMode

namespace SnapshotRow

instance : SnapshotRow [] where
  requestOf u := EffectRequest.absurd u
  eventOf u _ := EffectRequest.absurd u
  matchesRequest u _ := EffectRequest.absurd u
  decodeResponse? u _ := EffectRequest.absurd u
  checkMode u := EffectRequest.absurd u

instance {t : Effect} {r : List Effect} [SnapshotCodec t] [SnapshotRow r] :
    SnapshotRow (t :: r) where
  requestOf
    | EffectRequest.here request => SnapshotCodec.requestOf request
    | EffectRequest.there rest => SnapshotRow.requestOf rest
  eventOf
    | EffectRequest.here request, response => SnapshotCodec.eventOf request response
    | EffectRequest.there rest, response => SnapshotRow.eventOf rest response
  matchesRequest
    | EffectRequest.here request, event => SnapshotCodec.matchesRequest request event
    | EffectRequest.there rest, event => SnapshotRow.matchesRequest rest event
  decodeResponse?
    | EffectRequest.here request, event =>
        if SnapshotCodec.matchesRequest request event then
          SnapshotCodec.decodeResponse? request event.response
        else
          none
    | EffectRequest.there rest, event => SnapshotRow.decodeResponse? rest event
  checkMode
    | EffectRequest.here request => SnapshotCodec.checkMode request
    | EffectRequest.there rest => SnapshotRow.checkMode rest

end SnapshotRow

private def jsonOp (op : String) : Lean.Json :=
  Lean.Json.mkObj [("op", Lean.Json.str op)]

private def jsonUnit : Lean.Json :=
  Lean.Json.null

private def decodeJson? {α : Type} [Lean.FromJson α] (json : Lean.Json) : Option α :=
  (Lean.fromJson? json).toOption

private def decodeUnit? : Lean.Json → Option Unit
  | Lean.Json.null => some ()
  | _ => none

instance {ρ : Type} [Lean.ToJson ρ] [Lean.FromJson ρ] :
    SnapshotCodec (Reader ρ) where
  effectName := "Reader"
  encodeRequest
    | Reader.ask => jsonOp "ask"
  encodeResponse
    | Reader.ask, value => Lean.toJson value
  decodeResponse?
    | Reader.ask, value => decodeJson? value

instance {ω : Type} [Lean.ToJson ω] : SnapshotCodec (Writer ω) where
  effectName := "Writer"
  encodeRequest
    | Writer.tell value =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "tell")
          , ("value", Lean.toJson value)
          ]
  encodeResponse
    | Writer.tell _, () => jsonUnit
  decodeResponse?
    | Writer.tell _, value => decodeUnit? value
  checkMode
    | Writer.tell _ => .assertRequest

instance {σ : Type} [Lean.ToJson σ] [Lean.FromJson σ] :
    SnapshotCodec (State σ) where
  effectName := "State"
  encodeRequest
    | State.get => jsonOp "get"
    | State.put value =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "put")
          , ("value", Lean.toJson value)
          ]
  encodeResponse
    | State.get, value => Lean.toJson value
    | State.put _, () => jsonUnit
  decodeResponse?
    | State.get, value => decodeJson? value
    | State.put _, value => decodeUnit? value

instance : SnapshotCodec Random where
  effectName := "Random"
  encodeRequest
    | Random.nat lo hi =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "nat")
          , ("lo", Lean.toJson lo)
          , ("hi", Lean.toJson hi)
          ]
    | Random.bool => jsonOp "bool"
  encodeResponse
    | Random.nat _ _, value => Lean.toJson value
    | Random.bool, value => Lean.toJson value
  decodeResponse?
    | Random.nat _ _, value => decodeJson? (α := Nat) value
    | Random.bool, value => decodeJson? (α := Bool) value

instance {τ : Type} [Lean.ToJson τ] [Lean.FromJson τ] :
    SnapshotCodec (Clock τ) where
  effectName := "Clock"
  encodeRequest
    | Clock.now => jsonOp "now"
  encodeResponse
    | Clock.now, value => Lean.toJson value
  decodeResponse?
    | Clock.now, value => decodeJson? value

instance : SnapshotCodec Console where
  effectName := "Console"
  encodeRequest
    | Console.printLine line =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "printLine")
          , ("line", Lean.Json.str line)
          ]
    | Console.readLine => jsonOp "readLine"
  encodeResponse
    | Console.printLine _, () => jsonUnit
    | Console.readLine, value => Lean.Json.str value
  decodeResponse?
    | Console.printLine _, value => decodeUnit? value
    | Console.readLine, value => value.getStr?.toOption
  checkMode
    | Console.printLine _ => .assertRequest
    | Console.readLine => .replayResponse

instance {frame : Type} [Lean.ToJson frame] :
    SnapshotCodec (Display frame) where
  effectName := "Display"
  encodeRequest
    | Display.draw frame =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "draw")
          , ("frame", Lean.toJson frame)
          ]
  encodeResponse
    | Display.draw _, () => jsonUnit
  decodeResponse?
    | Display.draw _, value => decodeUnit? value
  checkMode
    | Display.draw _ => .assertRequest

instance {ι : Type} [Lean.ToJson ι] [Lean.FromJson ι] :
    SnapshotCodec (Input ι) where
  effectName := "Input"
  encodeRequest
    | Input.poll => jsonOp "poll"
  encodeResponse
    | Input.poll, value => Lean.toJson value
  decodeResponse?
    | Input.poll, value => decodeJson? value

instance : SnapshotCodec Sleep where
  effectName := "Sleep"
  encodeRequest
    | Sleep.sleepMs ms =>
        Lean.Json.mkObj
          [ ("op", Lean.Json.str "sleep")
          , ("ms", Lean.toJson ms)
          ]
  encodeResponse
    | Sleep.sleepMs _, () => jsonUnit
  decodeResponse?
    | Sleep.sleepMs _, value => decodeUnit? value
  checkMode
    | Sleep.sleepMs _ => .assertRequest

partial def recordSnapshot {r : List Effect} {α : Type} [SnapshotRow r]
    [Inhabited α] : Eff r α → Eff (Writer SnapshotEvent :: r) α
  | Eff.pure x => pure x
  | Eff.impure u q => do
      let response ← Eff.impure (EffectRequest.there u) (Arrs.one Eff.pure)
      tell (SnapshotRow.eventOf u response)
      recordSnapshot (Arrs.apply q response)

inductive SnapshotReplayError where
  | snapshotEnded (index : Nat) (request : SnapshotRequest)
  | eventMismatch (index : Nat) (recorded : SnapshotEvent)
      (actual : SnapshotRequest)
  | responseDecodeFailed (index : Nat) (recorded : SnapshotEvent)
      (actual : SnapshotRequest)
  | assertionMismatch (index : Nat) (recorded : SnapshotEvent)
      (actual : SnapshotRequest)
  | assertionResponseDecodeFailed (index : Nat) (recorded : SnapshotEvent)
      (actual : SnapshotRequest)
  | unusedEvents (index : Nat) (remaining : Snapshot)
deriving Repr, BEq

private partial def replaySnapshotLoop {r : List Effect} {α : Type}
    [SnapshotRow r] [Inhabited α]
    (index : Nat) (snapshot : Snapshot) : Eff r α → Except SnapshotReplayError α
  | Eff.pure x =>
      match snapshot with
      | [] => Except.ok x
      | _ => Except.error (SnapshotReplayError.unusedEvents index snapshot)
  | Eff.impure u q =>
      match snapshot with
      | [] =>
          Except.error
            (SnapshotReplayError.snapshotEnded index (SnapshotRow.requestOf u))
      | event :: rest =>
          let request := SnapshotRow.requestOf u
          if SnapshotRow.matchesRequest u event then
            match SnapshotRow.decodeResponse? u event with
            | some response =>
                replaySnapshotLoop (index + 1) rest (Arrs.apply q response)
            | none =>
                Except.error
                  (SnapshotReplayError.responseDecodeFailed index event request)
          else
            Except.error (SnapshotReplayError.eventMismatch index event request)

def replaySnapshot {r : List Effect} {α : Type} [SnapshotRow r] [Inhabited α]
    (snapshot : Snapshot) (m : Eff r α) : Except SnapshotReplayError α :=
  replaySnapshotLoop 0 snapshot m

private partial def checkSnapshotLoop {r : List Effect} {α : Type}
    [SnapshotRow r] [Inhabited α]
    (index : Nat) (snapshot : Snapshot) : Eff r α → Except SnapshotReplayError α
  | Eff.pure x =>
      match snapshot with
      | [] => Except.ok x
      | _ => Except.error (SnapshotReplayError.unusedEvents index snapshot)
  | Eff.impure u q =>
      match snapshot with
      | [] =>
          Except.error
            (SnapshotReplayError.snapshotEnded index (SnapshotRow.requestOf u))
      | event :: rest =>
          let request := SnapshotRow.requestOf u
          match SnapshotRow.checkMode u with
          | .replayResponse =>
              if SnapshotRow.matchesRequest u event then
                match SnapshotRow.decodeResponse? u event with
                | some response =>
                    checkSnapshotLoop (index + 1) rest (Arrs.apply q response)
                | none =>
                    Except.error
                      (SnapshotReplayError.responseDecodeFailed index event request)
              else
                Except.error (SnapshotReplayError.eventMismatch index event request)
          | .assertRequest =>
              if SnapshotRow.matchesRequest u event then
                match SnapshotRow.decodeResponse? u event with
                | some response =>
                    checkSnapshotLoop (index + 1) rest (Arrs.apply q response)
                | none =>
                    Except.error
                      (SnapshotReplayError.assertionResponseDecodeFailed index event request)
              else
                Except.error (SnapshotReplayError.assertionMismatch index event request)

/--
Runs a program against a recorded snapshot as a deterministic check.

Input-like effects such as `Random` and `Input` receive their recorded
responses. Output-like effects such as `Display.draw`, `Console.printLine`, or
`Writer.tell` must issue the same request as the snapshot before execution can
continue.
-/
def checkSnapshot {r : List Effect} {α : Type} [SnapshotRow r] [Inhabited α]
    (snapshot : Snapshot) (m : Eff r α) : Except SnapshotReplayError α :=
  checkSnapshotLoop 0 snapshot m

inductive SnapshotDivergence where
  | leftEnded (index : Nat) (right : SnapshotEvent)
  | rightEnded (index : Nat) (left : SnapshotEvent)
  | eventMismatch (index : Nat) (left right : SnapshotEvent)
deriving Repr, BEq

private def compareSnapshotsLoop :
    Nat → Snapshot → Snapshot → Option SnapshotDivergence
  | _, [], [] => none
  | index, [], right :: _ => some (SnapshotDivergence.leftEnded index right)
  | index, left :: _, [] => some (SnapshotDivergence.rightEnded index left)
  | index, left :: leftRest, right :: rightRest =>
      if left == right then
        compareSnapshotsLoop (index + 1) leftRest rightRest
      else
        some (SnapshotDivergence.eventMismatch index left right)

def compareSnapshots (left right : Snapshot) : Option SnapshotDivergence :=
  compareSnapshotsLoop 0 left right

end LeanEff
