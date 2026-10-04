import LeanEff.Internal.EffectRequest

namespace LeanEff

universe u

variable {μ : Type}

/- The computation core accepts any typed request family. Effect rows below
   specialize it to EffectRequest; higher-order algebras can use it directly. -/
mutual
  inductive EffF (e : Type → Type u) (μ : Type) : Type → Type _ where
    | pure {α : Type} : Option μ → α → EffF e μ α
    | impure {α x : Type} : Option μ → e x → ArrsF e μ x α → EffF e μ α

  inductive ArrsF (e : Type → Type u) (μ : Type) : Type → Type → Type _ where
    | one {α β : Type} : (α → EffF e μ β) → ArrsF e μ α β
    | append {α β γ : Type} : ArrsF e μ α β → ArrsF e μ β γ → ArrsF e μ α γ
end

inductive ArrsF.ViewL (e : Type → Type u) (μ : Type) : Type → Type → Type _ where
  | one {α β : Type} : (α → EffF e μ β) → ArrsF.ViewL e μ α β
  | cons {α β γ : Type} : (α → EffF e μ β) → ArrsF e μ β γ → ArrsF.ViewL e μ α γ

namespace EffF

def bind : EffF e μ α → (α → EffF e μ β) → EffF e μ β
  | EffF.pure _ x, k => k x
  | EffF.impure info u q, k => EffF.impure info u (ArrsF.append q (ArrsF.one k))

end EffF

namespace ArrsF

def viewLAppend : ArrsF e μ α β → ArrsF e μ β γ → ViewL e μ α γ
  | ArrsF.one k, q => ViewL.cons k q
  | ArrsF.append q q', rest => viewLAppend q (ArrsF.append q' rest)

def viewL : ArrsF e μ α β → ViewL e μ α β
  | ArrsF.one k => ViewL.one k
  | ArrsF.append q q' => viewLAppend q q'

-- Respect the request family's SizeOf instance in bounds used by downstream proofs.
theorem viewLAppend_rest_lt [∀ x, SizeOf (e x)] [SizeOf μ] :
    (q : ArrsF e μ α β) → (rest : ArrsF e μ β γ) →
    match viewLAppend q rest with
    | ViewL.one _ => True
    | ViewL.cons _ rest' => sizeOf rest' < sizeOf (ArrsF.append q rest)
  | ArrsF.one k, rest => by
      simp [viewLAppend]
  | ArrsF.append q q', rest => by
      simpa [viewLAppend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        viewLAppend_rest_lt q (ArrsF.append q' rest)
termination_by q => sizeOf q

theorem viewL_rest_lt [∀ x, SizeOf (e x)] [SizeOf μ] (q : ArrsF e μ α β) :
    match viewL q with
    | ViewL.one _ => True
    | ViewL.cons _ rest => sizeOf rest < sizeOf q := by
  cases q with
  | one k =>
      simp [viewL]
  | append q q' =>
      simpa [viewL] using viewLAppend_rest_lt q q'

set_option linter.unusedVariables false in
def apply : ArrsF e μ α β → α → EffF e μ β
  | q, x =>
      match h : viewL q with
      | ViewL.one k => k x
      | ViewL.cons k rest => EffF.bind (k x) (apply rest)
termination_by q => sizeOf q
decreasing_by
  simpa [h] using viewL_rest_lt q

end ArrsF

namespace EffF

def bindArrs (m : EffF e μ α) (q : ArrsF e μ α β) : EffF e μ β :=
  bind m (ArrsF.apply q)

end EffF

instance : Pure (EffF e μ) where
  pure := EffF.pure none

instance : Bind (EffF e μ) where
  bind := EffF.bind

instance : Monad (EffF e μ) where

instance [Inhabited α] : Inhabited (EffF e μ α) where
  default := EffF.pure none default

/-- Send a request directly to an effect family. -/
def EffF.send {e : Type → Type u} (request : e α) : EffF e μ α :=
  .impure none request (.one (.pure none))

mutual
  /-- Transform node annotations, including future nodes, without invoking continuations. -/
  def EffF.mapMetadata (f : Option μ → Option μ) : EffF e μ α → EffF e μ α
    | .pure info value => .pure (f info) value
    | .impure info request next => .impure (f info) request (ArrsF.mapMetadata f next)

  def ArrsF.mapMetadata (f : Option μ → Option μ) : ArrsF e μ α β → ArrsF e μ α β
    | .one k => .one fun value => EffF.mapMetadata f (k value)
    | .append first rest => .append (ArrsF.mapMetadata f first) (ArrsF.mapMetadata f rest)
end

/-- Fill missing annotations on this computation. Explicit inner annotations win.
Computations embedded in a request are opaque to the generic core. -/
def EffF.withMetadata? (info : Option μ) : EffF e μ α → EffF e μ α :=
  EffF.mapMetadata (fun existing => existing.orElse (fun _ => info))

def EffF.withMetadata (info : μ) : EffF e μ α → EffF e μ α :=
  EffF.withMetadata? (some info)

def EffF.metadata : EffF e μ α → Option μ
  | .pure info _ => info
  | .impure info _ _ => info

/-- Remove annotations from the continuation spine; requests are unchanged. -/
def EffF.eraseMetadata : EffF e μ α → EffF e μ α :=
  EffF.mapMetadata (fun _ => none)

/-- The row API specializes the shared core to the row's request union. -/
abbrev EffM (r : List Effect) (μ : Type) := EffF (EffectRequest r) μ
abbrev Eff (r : List Effect) := EffM r Empty
abbrev ArrsM (r : List Effect) (μ : Type) := ArrsF (EffectRequest r) μ
abbrev Arrs (r : List Effect) := ArrsM r Empty

namespace Eff
@[match_pattern] abbrev pure {r : List Effect} {α : Type} (x : α) : EffM r μ α := EffF.pure none x
@[match_pattern] abbrev impure {r : List Effect} {α x : Type}
    (request : EffectRequest r x) (q : ArrsM r μ x α) : EffM r μ α := EffF.impure none request q
abbrev bind {r : List Effect} {α β : Type} := @EffF.bind μ (EffectRequest r) α β
abbrev bindArrs {r : List Effect} {α β : Type} := @EffF.bindArrs μ (EffectRequest r) α β
end Eff

namespace Arrs
@[match_pattern] abbrev one {r : List Effect} {α β : Type}
    (k : α → EffM r μ β) : ArrsM r μ α β := ArrsF.one k
@[match_pattern] abbrev append {r : List Effect} {α β γ : Type}
    (q : ArrsM r μ α β) (rest : ArrsM r μ β γ) : ArrsM r μ α γ := ArrsF.append q rest
abbrev ViewL (r : List Effect) := ArrsF.ViewL (EffectRequest r) μ
@[match_pattern] abbrev ViewL.one {r : List Effect} {α β : Type}
    (k : α → EffM r μ β) : ViewL (μ := μ) r α β := ArrsF.ViewL.one k
@[match_pattern] abbrev ViewL.cons {r : List Effect} {α β γ : Type}
    (k : α → EffM r μ β) (rest : ArrsM r μ β γ) : ViewL (μ := μ) r α γ := ArrsF.ViewL.cons k rest
abbrev viewLAppend {r : List Effect} {α β γ : Type} := @ArrsF.viewLAppend μ (EffectRequest r) α β γ
abbrev viewL {r : List Effect} {α β : Type} := @ArrsF.viewL μ (EffectRequest r) α β
abbrev viewLAppend_rest_lt {r : List Effect} {α β γ : Type} :=
  ArrsF.viewLAppend_rest_lt (e := EffectRequest r) (μ := μ) (α := α) (β := β) (γ := γ)
abbrev viewL_rest_lt {r : List Effect} {α β : Type} :=
  ArrsF.viewL_rest_lt (e := EffectRequest r) (μ := μ) (α := α) (β := β)
abbrev apply {r : List Effect} {α β : Type} := @ArrsF.apply μ (EffectRequest r) α β
end Arrs

def send {t : Effect} {r : List Effect} [Member t r] {α : Type}
    (request : t α) : EffM r μ α :=
  Eff.impure (Member.inj (t := t) (r := r) request) (Arrs.one Eff.pure)

def qComp {r r' : List Effect} {α β γ : Type}
    (q : ArrsM r μ α β) (h : EffM r μ β → EffM r' μ γ) : α → EffM r' μ γ :=
  fun x => h (Arrs.apply q x)

partial def handleRelay {t : Effect} {r r' : List Effect} [Remove t r r']
    {α β : Type}
    [Inhabited β]
    (ret : α → EffM r' μ β)
    (handle : {x : Type} → t x → (x → EffM r' μ β) → EffM r' μ β) :
    EffM r μ α → EffM r' μ β
  | EffF.pure info x => EffF.withMetadata? info (ret x)
  | EffF.impure info u q =>
      match Remove.decomp (t := t) (r := r) (r' := r') u with
      | Sum.inl request =>
          handle request (qComp q (handleRelay ret handle))
      | Sum.inr rest =>
          EffF.impure info rest (Arrs.one (qComp q (handleRelay ret handle)))

def run {α : Type} : EffM [] μ α → α
  | EffF.pure _ x => x
  | EffF.impure _ u _ => EffectRequest.absurd u

end LeanEff
