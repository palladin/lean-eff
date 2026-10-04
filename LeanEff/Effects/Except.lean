import LeanEff.Core

namespace LeanEff

variable {μ : Type}

inductive ExceptE (ε : Type) : Effect where
  | throw {α : Type} : ε → ExceptE ε α

def throw {ε α : Type} {r : List Effect} [Member (ExceptE ε) r]
    (error : ε) : EffM r μ α :=
  send (ExceptE.throw error)

def runExcept {ε α : Type} {r r' : List Effect} [Remove (ExceptE ε) r r']
    [Inhabited α]
    (m : EffM r μ α) : EffM r' μ (Except ε α) :=
  handleRelay (t := ExceptE ε)
    (ret := fun x => pure (Except.ok x))
    (handle := fun request _ =>
      match request with
      | ExceptE.throw error => pure (Except.error error))
    m

partial def tryCatch {ε α : Type} {r r' : List Effect} [Remove (ExceptE ε) r r']
    [Inhabited α]
    (body : EffM r μ α) (handler : ε → EffM r μ α) : EffM r μ α :=
  let rec loop : EffM r μ α → EffM r μ α
    | EffF.pure info x => EffF.pure info x
    | EffF.impure info u q =>
        match Remove.decomp (t := ExceptE ε) (r := r) (r' := r') u with
        | Sum.inl request =>
            match request with
            | ExceptE.throw error => handler error
        | Sum.inr rest =>
            EffF.impure info
              (Remove.weaken (t := ExceptE ε) (r := r) (r' := r') rest)
              (Arrs.one (qComp q loop))
  loop body

abbrev «catch» {ε α : Type} {r r' : List Effect} [Remove (ExceptE ε) r r']
    [Inhabited α]
    (body : EffM r μ α) (handler : ε → EffM r μ α) : EffM r μ α :=
  tryCatch body handler

end LeanEff
