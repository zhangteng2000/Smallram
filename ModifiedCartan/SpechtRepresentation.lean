import ModifiedCartan.YoungSpechtIrreducible
import ModifiedCartan.RepresentationReindex

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

/-- A fixed numbering of the actual boxes; changing it only conjugates the group action. -/
def youngBoxNumbering (μ : YoungDiagram) : YoungBoxes μ ≃ Fin (partitionSize μ) :=
  μ.cells.equivFin

/-- The ordinary complex Specht representation on the numbered symmetric group. -/
def spechtRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Fin (partitionSize μ))) (YoungSpechtModule μ) :=
  (youngSpechtRepresentation μ).comp (youngBoxNumbering μ).symm.permCongrHom.toMonoidHom

theorem spechtRepresentation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (spechtRepresentation μ) := by
  letI := youngSpechtRepresentation_irreducible μ
  exact representation_irreducible_reindex (youngSpechtRepresentation μ)
    (youngBoxNumbering μ).symm.permCongrHom

theorem youngSpechtRepresentation_unitary (μ : YoungDiagram) :
    IsUnitaryRepresentation (youngSpechtRepresentation μ) := by
  intro g v w
  exact youngTabloidRepresentation_unitary μ g v.val w.val

theorem spechtRepresentation_unitary (μ : YoungDiagram) :
    IsUnitaryRepresentation (spechtRepresentation μ) :=
  unitary_representation_reindex (youngSpechtRepresentation μ)
    (youngBoxNumbering μ).symm.permCongrHom (youngSpechtRepresentation_unitary μ)

/-- The irreducible Specht character used in LaTeX `eq:KP-operators`. -/
def spechtCharacter (μ : YoungDiagram) : Equiv.Perm (Fin (partitionSize μ)) → ℂ :=
  (spechtRepresentation μ).character

theorem spechtCharacter_one (μ : YoungDiagram) :
    spechtCharacter μ 1 = Module.finrank ℂ (YoungSpechtModule μ) :=
  Representation.char_one (spechtRepresentation μ)

end
end ModifiedCartan


