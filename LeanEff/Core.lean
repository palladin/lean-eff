import LeanEff.Internal.Union

namespace LeanEff

mutual
  inductive Eff (r : List Effect) : Type → Type 2 where
    | pure {α : Type} : α → Eff r α
    | impure {α x : Type} : OpenUnion r x → Arrs r x α → Eff r α

  inductive Arrs (r : List Effect) : Type → Type → Type 2 where
    | one {α β : Type} : (α → Eff r β) → Arrs r α β
    | append {α β γ : Type} : Arrs r α β → Arrs r β γ → Arrs r α γ
end

inductive Arrs.ViewL (r : List Effect) : Type → Type → Type 2 where
  | one {α β : Type} : (α → Eff r β) → Arrs.ViewL r α β
  | cons {α β γ : Type} : (α → Eff r β) → Arrs r β γ → Arrs.ViewL r α γ

namespace Eff

def bind : Eff r α → (α → Eff r β) → Eff r β
  | Eff.pure x, k => k x
  | Eff.impure u q, k => Eff.impure u (Arrs.append q (Arrs.one k))

end Eff

namespace Arrs

def viewLAppend : Arrs r α β → Arrs r β γ → ViewL r α γ
  | Arrs.one k, q => ViewL.cons k q
  | Arrs.append q q', rest => viewLAppend q (Arrs.append q' rest)

def viewL : Arrs r α β → ViewL r α β
  | Arrs.one k => ViewL.one k
  | Arrs.append q q' => viewLAppend q q'

theorem viewLAppend_rest_lt :
    (q : Arrs r α β) → (rest : Arrs r β γ) →
    match viewLAppend q rest with
    | ViewL.one _ => True
    | ViewL.cons _ rest' => sizeOf rest' < sizeOf (Arrs.append q rest)
  | Arrs.one k, rest => by
      simp [viewLAppend]
  | Arrs.append q q', rest => by
      simpa [viewLAppend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        viewLAppend_rest_lt q (Arrs.append q' rest)
termination_by q => sizeOf q

theorem viewL_rest_lt (q : Arrs r α β) :
    match viewL q with
    | ViewL.one _ => True
    | ViewL.cons _ rest => sizeOf rest < sizeOf q := by
  cases q with
  | one k =>
      simp [viewL]
  | append q q' =>
      simpa [viewL] using viewLAppend_rest_lt q q'

set_option linter.unusedVariables false in
def apply : Arrs r α β → α → Eff r β
  | q, x =>
      match h : viewL q with
      | ViewL.one k => k x
      | ViewL.cons k rest => Eff.bind (k x) (apply rest)
termination_by q => sizeOf q
decreasing_by
  simpa [h] using viewL_rest_lt q

end Arrs

namespace Eff

def bindArrs (m : Eff r α) (q : Arrs r α β) : Eff r β :=
  bind m (Arrs.apply q)

end Eff

instance : Pure (Eff r) where
  pure := Eff.pure

instance : Bind (Eff r) where
  bind := Eff.bind

instance : Monad (Eff r) where

instance [Inhabited α] : Inhabited (Eff r α) where
  default := Eff.pure default

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
  | Eff.impure u _ => OpenUnion.absurd u

end LeanEff
