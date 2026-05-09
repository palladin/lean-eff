import LeanEff.Core

namespace LeanEff

inductive ExceptE (ε : Type) : Effect where
  | throw {α : Type} : ε → ExceptE ε α

def throw {ε α : Type} {r : List Effect} [Member (ExceptE ε) r]
    (error : ε) : Eff r α :=
  send (ExceptE.throw error)

def runExcept {ε α : Type} {r r' : List Effect} [Remove (ExceptE ε) r r']
    [Inhabited α]
    (m : Eff r α) : Eff r' (Except ε α) :=
  handleRelay (t := ExceptE ε)
    (ret := fun x => pure (Except.ok x))
    (handle := fun request _ =>
      match request with
      | ExceptE.throw error => pure (Except.error error))
    m

partial def tryCatch {ε α : Type} {r r' : List Effect} [Remove (ExceptE ε) r r']
    [Inhabited α]
    (body : Eff r α) (handler : ε → Eff r α) : Eff r α :=
  let rec loop : Eff r α → Eff r α
    | Eff.pure x => pure x
    | Eff.impure u q =>
        match Remove.decomp (t := ExceptE ε) (r := r) (r' := r') u with
        | Sum.inl request =>
            match request with
            | ExceptE.throw error => handler error
        | Sum.inr rest =>
            Eff.impure
              (Remove.weaken (t := ExceptE ε) (r := r) (r' := r') rest)
              (Arrs.one (qComp q loop))
  loop body

abbrev «catch» {ε α : Type} {r r' : List Effect} [Remove (ExceptE ε) r r']
    [Inhabited α]
    (body : Eff r α) (handler : ε → Eff r α) : Eff r α :=
  tryCatch body handler

end LeanEff
