import ModifiedCartan.BranchingImageEquality

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The surjective corner-deletion map from the next Specht row cutoff to the
actual smaller Specht module. -/
def youngSpechtBranchingMap (μ : YoungDiagram) (b : YoungCorner μ) :
    (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule →ₗ[ℂ]
      YoungSpechtModule (removePartitionBox μ b) :=
  LinearMap.codRestrict (youngSpechtSubrepresentation (removePartitionBox μ b)).toSubmodule
    ((youngTabloidDeleteLinear μ b).domRestrict
      (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule) (by
        intro v
        have hv : youngTabloidDeleteLinear μ b v.val ∈
            youngDeletionImageSubrepresentation μ b (b.val.val.1 + 1) :=
          Submodule.mem_map.mpr ⟨v.val, v.property, rfl⟩
        rw [youngDeletionImage_eq_specht] at hv
        exact hv)

@[simp] theorem youngSpechtBranchingMap_val (μ : YoungDiagram) (b : YoungCorner μ)
    (v : (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule) :
    (youngSpechtBranchingMap μ b v).val = youngTabloidDeleteLinear μ b v.val := rfl

theorem youngSpechtBranchingMap_surjective (μ : YoungDiagram) (b : YoungCorner μ) :
    Function.Surjective (youngSpechtBranchingMap μ b) := by
  intro w
  have hw : w.val ∈ youngDeletionImageSubrepresentation μ b (b.val.val.1 + 1) := by
    rw [youngDeletionImage_eq_specht]
    exact w.property
  obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hw
  exact ⟨⟨v, hv⟩, Subtype.ext he⟩

theorem youngSpechtBranchingMap_ker (μ : YoungDiagram) (b : YoungCorner μ) :
    LinearMap.ker (youngSpechtBranchingMap μ b) =
      ((youngSpechtRowFiltration μ b.val b.val.val.1).toSubmodule).comap
        (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule.subtype := by
  ext v
  change youngSpechtBranchingMap μ b v = 0 ↔
    v.val ∈ youngSpechtRowFiltration μ b.val b.val.val.1
  have he : youngSpechtBranchingMap μ b v = 0 ↔ youngTabloidDeleteLinear μ b v.val = 0 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [he, youngTabloidDeleteLinear_kernel_cutoff μ b v.val v.property.2]
  exact ⟨fun h => ⟨v.property.1, h⟩, fun h => h.2⟩

theorem youngSpechtBranchingMap_action (μ : YoungDiagram) (b : YoungCorner μ)
    (g : Equiv.Perm (YoungBoxes (removePartitionBox μ b)))
    (v : (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule) :
    youngSpechtBranchingMap μ b
      ((youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toRepresentation
        (youngRemovalPermutationEquiv μ b g) v) =
      youngSpechtRepresentation (removePartitionBox μ b) g (youngSpechtBranchingMap μ b v) := by
  apply Subtype.ext
  exact youngTabloidDeleteLinear_action μ b g v.val

/-- An actual linear isomorphism from the successive row-filtration quotient
to the smaller Specht module. -/
def youngSpechtCornerQuotientEquiv (μ : YoungDiagram) (b : YoungCorner μ) :
    ((youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule ⧸
      ((youngSpechtRowFiltration μ b.val b.val.val.1).toSubmodule).comap
        (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule.subtype) ≃ₗ[ℂ]
      YoungSpechtModule (removePartitionBox μ b) :=
  (Submodule.quotEquivOfEq _ _ (youngSpechtBranchingMap_ker μ b).symm).trans
    ((youngSpechtBranchingMap μ b).quotKerEquivOfSurjective
      (youngSpechtBranchingMap_surjective μ b))

theorem youngSpechtCornerQuotientEquiv_mk (μ : YoungDiagram) (b : YoungCorner μ)
    (v : (youngSpechtRowFiltration μ b.val (b.val.val.1 + 1)).toSubmodule) :
    youngSpechtCornerQuotientEquiv μ b (Submodule.Quotient.mk v) = youngSpechtBranchingMap μ b v := by
  simp [youngSpechtCornerQuotientEquiv, Submodule.quotEquivOfEq_mk]

end
end ModifiedCartan


