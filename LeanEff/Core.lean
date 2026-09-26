import LeanEff.Internal.EffectRequest

namespace LeanEff

universe u

/- The computation core accepts any typed request family. Effect rows below
   specialize it to EffectRequest; higher-order algebras can use it directly. -/
mutual
  inductive EffF (e : Type → Type u) : Type → Type _ where
    | pure {α : Type} : α → EffF e α
    | impure {α x : Type} : e x → ArrsF e x α → EffF e α

  inductive ArrsF (e : Type → Type u) : Type → Type → Type _ where
    | one {α β : Type} : (α → EffF e β) → ArrsF e α β
    | append {α β γ : Type} : ArrsF e α β → ArrsF e β γ → ArrsF e α γ
end

inductive ArrsF.ViewL (e : Type → Type u) : Type → Type → Type _ where
  | one {α β : Type} : (α → EffF e β) → ArrsF.ViewL e α β
  | cons {α β γ : Type} : (α → EffF e β) → ArrsF e β γ → ArrsF.ViewL e α γ

namespace EffF

def bind : EffF e α → (α → EffF e β) → EffF e β
  | EffF.pure x, k => k x
  | EffF.impure u q, k => EffF.impure u (ArrsF.append q (ArrsF.one k))

end EffF

namespace ArrsF

def viewLAppend : ArrsF e α β → ArrsF e β γ → ViewL e α γ
  | ArrsF.one k, q => ViewL.cons k q
  | ArrsF.append q q', rest => viewLAppend q (ArrsF.append q' rest)

def viewL : ArrsF e α β → ViewL e α β
  | ArrsF.one k => ViewL.one k
  | ArrsF.append q q' => viewLAppend q q'

-- Respect the request family's SizeOf instance in bounds used by downstream proofs.
theorem viewLAppend_rest_lt [∀ x, SizeOf (e x)] :
    (q : ArrsF e α β) → (rest : ArrsF e β γ) →
    match viewLAppend q rest with
    | ViewL.one _ => True
    | ViewL.cons _ rest' => sizeOf rest' < sizeOf (ArrsF.append q rest)
  | ArrsF.one k, rest => by
      simp [viewLAppend]
  | ArrsF.append q q', rest => by
      simpa [viewLAppend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        viewLAppend_rest_lt q (ArrsF.append q' rest)
termination_by q => sizeOf q

theorem viewL_rest_lt [∀ x, SizeOf (e x)] (q : ArrsF e α β) :
    match viewL q with
    | ViewL.one _ => True
    | ViewL.cons _ rest => sizeOf rest < sizeOf q := by
  cases q with
  | one k =>
      simp [viewL]
  | append q q' =>
      simpa [viewL] using viewLAppend_rest_lt q q'

set_option linter.unusedVariables false in
def apply : ArrsF e α β → α → EffF e β
  | q, x =>
      match h : viewL q with
      | ViewL.one k => k x
      | ViewL.cons k rest => EffF.bind (k x) (apply rest)
termination_by q => sizeOf q
decreasing_by
  simpa [h] using viewL_rest_lt q

end ArrsF

namespace EffF

def bindArrs (m : EffF e α) (q : ArrsF e α β) : EffF e β :=
  bind m (ArrsF.apply q)

end EffF

instance : Pure (EffF e) where
  pure := EffF.pure

instance : Bind (EffF e) where
  bind := EffF.bind

instance : Monad (EffF e) where

instance [Inhabited α] : Inhabited (EffF e α) where
  default := EffF.pure default

/-- Send a request directly to an effect family. -/
def EffF.send {e : Type → Type u} (request : e α) : EffF e α :=
  .impure request (.one .pure)

/-- The row API specializes the shared core to the row's request union. -/
abbrev Eff (r : List Effect) := EffF (EffectRequest r)
abbrev Arrs (r : List Effect) := ArrsF (EffectRequest r)

namespace Eff
@[match_pattern] abbrev pure {r : List Effect} {α : Type} (x : α) : Eff r α := EffF.pure x
@[match_pattern] abbrev impure {r : List Effect} {α x : Type}
    (request : EffectRequest r x) (q : Arrs r x α) : Eff r α := EffF.impure request q
abbrev bind {r : List Effect} {α β : Type} := @EffF.bind (EffectRequest r) α β
abbrev bindArrs {r : List Effect} {α β : Type} := @EffF.bindArrs (EffectRequest r) α β
end Eff

namespace Arrs
@[match_pattern] abbrev one {r : List Effect} {α β : Type}
    (k : α → Eff r β) : Arrs r α β := ArrsF.one k
@[match_pattern] abbrev append {r : List Effect} {α β γ : Type}
    (q : Arrs r α β) (rest : Arrs r β γ) : Arrs r α γ := ArrsF.append q rest
abbrev ViewL (r : List Effect) := ArrsF.ViewL (EffectRequest r)
@[match_pattern] abbrev ViewL.one {r : List Effect} {α β : Type}
    (k : α → Eff r β) : ViewL r α β := ArrsF.ViewL.one k
@[match_pattern] abbrev ViewL.cons {r : List Effect} {α β γ : Type}
    (k : α → Eff r β) (rest : Arrs r β γ) : ViewL r α γ := ArrsF.ViewL.cons k rest
abbrev viewLAppend {r : List Effect} {α β γ : Type} := @ArrsF.viewLAppend (EffectRequest r) α β γ
abbrev viewL {r : List Effect} {α β : Type} := @ArrsF.viewL (EffectRequest r) α β
abbrev viewLAppend_rest_lt {r : List Effect} {α β γ : Type} :=
  ArrsF.viewLAppend_rest_lt (e := EffectRequest r) (α := α) (β := β) (γ := γ)
abbrev viewL_rest_lt {r : List Effect} {α β : Type} :=
  ArrsF.viewL_rest_lt (e := EffectRequest r) (α := α) (β := β)
abbrev apply {r : List Effect} {α β : Type} := @ArrsF.apply (EffectRequest r) α β
end Arrs

def send {t : Effect} {r : List Effect} [Member t r] {α : Type}
    (request : t α) : Eff r α :=
  Eff.impure (Member.inj (t := t) (r := r) request) (Arrs.one Eff.pure)

def qComp {r r' : List Effect} {α β γ : Type}
    (q : Arrs r α β) (h : Eff r β → Eff r' γ) : α → Eff r' γ :=
  fun x => h (Arrs.apply q x)

partial def handleRelay {t : Effect} {r r' : List Effect} [Remove t r r']
    {α β : Type}
    [Inhabited β]
    (ret : α → Eff r' β)
    (handle : {x : Type} → t x → (x → Eff r' β) → Eff r' β) :
    Eff r α → Eff r' β
  | Eff.pure x => ret x
  | Eff.impure u q =>
      match Remove.decomp (t := t) (r := r) (r' := r') u with
      | Sum.inl request =>
          handle request (qComp q (handleRelay ret handle))
      | Sum.inr rest =>
          Eff.impure rest (Arrs.one (qComp q (handleRelay ret handle)))

def run {α : Type} : Eff [] α → α
  | Eff.pure x => x
  | Eff.impure u _ => EffectRequest.absurd u

end LeanEff
