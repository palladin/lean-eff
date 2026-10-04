import LeanEff.Core

namespace LeanEff

mutual
  theorem EffF.mapMetadata_id {e : Type → Type u} {μ α : Type} (program : EffF e μ α) :
      EffF.mapMetadata id program = program :=
    match program with
    | .pure _ _ => rfl
    | .impure info request next =>
      congrArg (EffF.impure info request) (ArrsF.mapMetadata_id next)
  termination_by structural program

  theorem ArrsF.mapMetadata_id {e : Type → Type u} {μ α β : Type} (next : ArrsF e μ α β) :
      ArrsF.mapMetadata id next = next :=
    match next with
    | .one k => congrArg ArrsF.one (funext fun value => EffF.mapMetadata_id (k value))
    | .append first rest =>
      congr (congrArg ArrsF.append (ArrsF.mapMetadata_id first)) (ArrsF.mapMetadata_id rest)
  termination_by structural next
end

mutual
  theorem EffF.mapMetadata_comp {e : Type → Type u} {μ α : Type}
      (f g : Option μ → Option μ) (program : EffF e μ α) :
      EffF.mapMetadata f (EffF.mapMetadata g program) = EffF.mapMetadata (f ∘ g) program :=
    match program with
    | .pure _ _ => rfl
    | .impure info request next =>
      congrArg (EffF.impure (f (g info)) request) (ArrsF.mapMetadata_comp f g next)
  termination_by structural program

  theorem ArrsF.mapMetadata_comp {e : Type → Type u} {μ α β : Type}
      (f g : Option μ → Option μ) (next : ArrsF e μ α β) :
      ArrsF.mapMetadata f (ArrsF.mapMetadata g next) = ArrsF.mapMetadata (f ∘ g) next :=
    match next with
    | .one k => congrArg ArrsF.one (funext fun value => EffF.mapMetadata_comp f g (k value))
    | .append first rest =>
      by
      change ArrsF.append (ArrsF.mapMetadata f (ArrsF.mapMetadata g first))
        (ArrsF.mapMetadata f (ArrsF.mapMetadata g rest)) = _
      rw [ArrsF.mapMetadata_comp f g first, ArrsF.mapMetadata_comp f g rest]
      rfl
  termination_by structural next
end

/-- Metadata transformations preserve the original continuation boundary. -/
theorem EffF.mapMetadata_bind (f : Option μ → Option μ) (program : EffF e μ α)
    (next : α → EffF e μ β) :
    mapMetadata f (bind program next) =
      bind (mapMetadata f program) (fun value => mapMetadata f (next value)) := by
  cases program <;> rfl

theorem EffF.eraseMetadata_withMetadata (info : μ) (program : EffF e μ α) :
    eraseMetadata (withMetadata info program) = eraseMetadata program := by
  simp only [eraseMetadata, withMetadata, withMetadata?, mapMetadata_comp]
  rfl

end LeanEff
