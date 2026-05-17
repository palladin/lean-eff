namespace LeanEff

universe u

abbrev Effect := Type → Type 1

inductive EffectRequest : List Effect → Type → Type _ where
  | here {t : Effect} {r : List Effect} {α : Type} :
      t α → EffectRequest (t :: r) α
  | there {t : Effect} {r : List Effect} {α : Type} :
      EffectRequest r α → EffectRequest (t :: r) α

namespace EffectRequest

def absurd {α : Type} {β : Sort u} : EffectRequest [] α → β
  | noRequest => nomatch noRequest

end EffectRequest

class Member (t : Effect) (r : List Effect) where
  inj {α : Type} : t α → EffectRequest r α

namespace Member

instance head {t : Effect} {r : List Effect} : Member t (t :: r) where
  inj x := EffectRequest.here x

instance tail {t h : Effect} {r : List Effect} [Member t r] :
    Member t (h :: r) where
  inj x := EffectRequest.there (Member.inj (t := t) (r := r) x)

end Member

class Remove (t : Effect) (r : List Effect) (r' : outParam (List Effect)) where
  decomp {α : Type} : EffectRequest r α → Sum (t α) (EffectRequest r' α)
  weaken {α : Type} : EffectRequest r' α → EffectRequest r α

namespace Remove

instance head {t : Effect} {r : List Effect} : Remove t (t :: r) r where
  decomp
    | EffectRequest.here x => Sum.inl x
    | EffectRequest.there u => Sum.inr u
  weaken u := EffectRequest.there u

instance tail {t h : Effect} {r r' : List Effect} [Remove t r r'] :
    Remove t (h :: r) (h :: r') where
  decomp
    | EffectRequest.here x => Sum.inr (EffectRequest.here x)
    | EffectRequest.there u =>
        match Remove.decomp (t := t) (r := r) (r' := r') u with
        | Sum.inl x => Sum.inl x
        | Sum.inr u' => Sum.inr (EffectRequest.there u')
  weaken
    | EffectRequest.here x => EffectRequest.here x
    | EffectRequest.there u => EffectRequest.there (Remove.weaken (t := t) (r := r) (r' := r') u)

end Remove

end LeanEff
