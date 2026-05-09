namespace LeanEff

universe u

abbrev Effect := Type → Type 1

inductive OpenUnion : List Effect → Type → Type 2 where
  | here {t : Effect} {r : List Effect} {α : Type} :
      t α → OpenUnion (t :: r) α
  | there {t : Effect} {r : List Effect} {α : Type} :
      OpenUnion r α → OpenUnion (t :: r) α

namespace OpenUnion

def absurd {α : Type} {β : Sort u} : OpenUnion [] α → β
  | noUnion => nomatch noUnion

end OpenUnion

class Member (t : Effect) (r : List Effect) where
  inj {α : Type} : t α → OpenUnion r α

namespace Member

instance head {t : Effect} {r : List Effect} : Member t (t :: r) where
  inj x := OpenUnion.here x

instance tail {t h : Effect} {r : List Effect} [Member t r] :
    Member t (h :: r) where
  inj x := OpenUnion.there (Member.inj (t := t) (r := r) x)

end Member

class Remove (t : Effect) (r : List Effect) (r' : outParam (List Effect)) where
  decomp {α : Type} : OpenUnion r α → Sum (t α) (OpenUnion r' α)
  weaken {α : Type} : OpenUnion r' α → OpenUnion r α

namespace Remove

instance head {t : Effect} {r : List Effect} : Remove t (t :: r) r where
  decomp
    | OpenUnion.here x => Sum.inl x
    | OpenUnion.there u => Sum.inr u
  weaken u := OpenUnion.there u

instance tail {t h : Effect} {r r' : List Effect} [Remove t r r'] :
    Remove t (h :: r) (h :: r') where
  decomp
    | OpenUnion.here x => Sum.inr (OpenUnion.here x)
    | OpenUnion.there u =>
        match Remove.decomp (t := t) (r := r) (r' := r') u with
        | Sum.inl x => Sum.inl x
        | Sum.inr u' => Sum.inr (OpenUnion.there u')
  weaken
    | OpenUnion.here x => OpenUnion.here x
    | OpenUnion.there u => OpenUnion.there (Remove.weaken (t := t) (r := r) (r' := r') u)

end Remove

end LeanEff
