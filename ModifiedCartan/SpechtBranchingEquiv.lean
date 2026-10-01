import ModifiedCartan.SpechtBranchingMap

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The action on the next row cutoff, written on the alphabet of the erased diagram. -/
def youngSpechtCornerSourceRepresentation (μ : YoungDiagram) (b : YoungCorner μ) :
    Representation ℂ (Equiv.Perm (YoungBoxes (removePartitionBox μ b)))
      (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule :=
  (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toRepresentation.comp
    (youngRemovalPermutationEquiv μ b).toMonoidHom

abbrev youngSpechtCornerPrevious (μ : YoungDiagram) (b : YoungCorner μ) :=
  ((youngSpechtRowFiltration μ b.val b.val.val.1).toSubmodule).comap
    (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule.subtype

theorem youngSpechtCornerPrevious_invariant (μ : YoungDiagram) (b : YoungCorner μ)
    (g : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) :
    youngSpechtCornerPrevious μ b ≤ (youngSpechtCornerPrevious μ b).comap
      (youngSpechtCornerSourceRepresentation μ b g) := by
  intro v hv
  exact (youngSpechtRowFiltration μ b.val b.val.val.1).apply_mem_toSubmodule
    (youngRemovalPermutationEquiv μ b g) hv

/-- The actual action on the successive row quotient. -/
def youngSpechtCornerQuotientRepresentation (μ : YoungDiagram) (b : YoungCorner μ) :
    Representation ℂ (Equiv.Perm (YoungBoxes (removePartitionBox μ b)))
      ((youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule ⧸
        youngSpechtCornerPrevious μ b) :=
  (youngSpechtCornerSourceRepresentation μ b).quotient (youngSpechtCornerPrevious μ b)
    (youngSpechtCornerPrevious_invariant μ b)

theorem youngSpechtCornerQuotient_action_mk (μ : YoungDiagram) (b : YoungCorner μ)
    (g : Equiv.Perm (YoungBoxes (removePartitionBox μ b)))
    (v : (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule) :
    youngSpechtCornerQuotientRepresentation μ b g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (youngSpechtCornerSourceRepresentation μ b g v) := rfl

/-- The corner quotient is isomorphic as a representation to the actual smaller Specht module. -/
def youngSpechtBranchingEquiv (μ : YoungDiagram) (b : YoungCorner μ) :
    (youngSpechtCornerQuotientRepresentation μ b).Equiv
      (youngSpechtRepresentation (removePartitionBox μ b)) :=
  Representation.Equiv.mk (youngSpechtCornerQuotientEquiv μ b) (by
    intro g
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on _ q ?_
    intro v
    change youngSpechtCornerQuotientEquiv μ b
        (youngSpechtCornerQuotientRepresentation μ b g (Submodule.Quotient.mk v)) =
      youngSpechtRepresentation (removePartitionBox μ b) g
        (youngSpechtCornerQuotientEquiv μ b (Submodule.Quotient.mk v))
    rw [youngSpechtCornerQuotient_action_mk, youngSpechtCornerQuotientEquiv_mk,
      youngSpechtCornerQuotientEquiv_mk]
    exact youngSpechtBranchingMap_action μ b g v)

theorem youngSpechtCornerQuotient_character (μ : YoungDiagram) (b : YoungCorner μ) :
    (youngSpechtCornerQuotientRepresentation μ b).character =
      (youngSpechtRepresentation (removePartitionBox μ b)).character :=
  Representation.char_iso (youngSpechtBranchingEquiv μ b)

end
end ModifiedCartan


