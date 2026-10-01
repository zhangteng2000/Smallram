import ModifiedCartan.SpechtCharacterLabels
import ModifiedCartan.StandardPolytabloidBasis

open scoped Classical

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- The actual Specht representation on an arbitrary finite alphabet. -/
def spechtRepresentationOn {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) :
    Representation ℂ (Equiv.Perm A) (YoungSpechtModule μ) :=
  (spechtRepresentation μ).comp (Fintype.equivFinOfCardEq h).permCongrHom.toMonoidHom

theorem spechtRepresentationOn_character {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) :
    (spechtRepresentationOn μ h).character = spechtCharacterOn μ h := rfl

theorem spechtRepresentationOn_irreducible {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) :
    Representation.IsIrreducible (spechtRepresentationOn μ h) := by
  letI := spechtRepresentation_irreducible μ
  exact representation_irreducible_reindex (spechtRepresentation μ)
    (Fintype.equivFinOfCardEq h).permCongrHom

theorem spechtRepresentationOn_unitary {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) :
    IsUnitaryRepresentation (spechtRepresentationOn μ h) :=
  unitary_representation_reindex (spechtRepresentation μ)
    (Fintype.equivFinOfCardEq h).permCongrHom (spechtRepresentation_unitary μ)

theorem spechtCharacterOn_one_eq_tableaux {A : Type*} [Fintype A] (μ : YoungDiagram)
    (h : Fintype.card A = partitionSize μ) :
    spechtCharacterOn μ h 1 = (standardSkewTableauCount μ ⊥ : ℂ) := by
  rw [spechtCharacterOn_one, finrank_specht_eq_standardTableauCount]

end
end ModifiedCartan


