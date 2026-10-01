import ModifiedCartan.PolytabloidDeletion
import ModifiedCartan.SpechtRowFiltration

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngPolytabloid_mem_corner_filtration (μ : YoungDiagram) (b : YoungCorner μ) :
    youngPolytabloid μ ∈ youngSpechtRowFiltration μ b.val (b.val.val.1 + 1) := by
  refine ⟨youngPolytabloid_mem_specht μ, ?_⟩
  intro t ht
  by_contra hn
  obtain ⟨c, rfl⟩ := youngPolytabloid_coefficient_support μ t hn
  have hh := youngCorner_column_row_le μ b c⁻¹
  change (c.val⁻¹ b.val).val.1 ≤ b.val.val.1 at hh
  change b.val.val.1 + 1 ≤ (c.val⁻¹ b.val).val.1 at ht
  omega

/-- The actual image of a restricted Specht row cutoff under corner deletion. -/
def youngDeletionImageSubrepresentation (μ : YoungDiagram) (b : YoungCorner μ) (r : ℕ) :
    Subrepresentation (youngTabloidRepresentation (removePartitionBox μ b)) where
  toSubmodule := ((youngSpechtRowFiltration μ b.val r).toSubmodule).map (youngTabloidDeleteLinear μ b)
  apply_mem_toSubmodule := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    apply Submodule.mem_map.mpr
    refine ⟨youngTabloidRepresentation μ (youngRemovalPermutationEquiv μ b g).val w, ?_, ?_⟩
    · exact (youngSpechtRowFiltration μ b.val r).apply_mem_toSubmodule
        (youngRemovalPermutationEquiv μ b g) hw
    · exact youngTabloidDeleteLinear_action μ b g w

/-- The smaller Specht module is contained in the deletion image. Equality
requires the later dimension argument and is not assumed here. -/
theorem youngSpecht_le_deletionImage (μ : YoungDiagram) (b : YoungCorner μ) :
    youngSpechtSubrepresentation (removePartitionBox μ b) ≤
      youngDeletionImageSubrepresentation μ b (b.val.val.1 + 1) := by
  apply (representationOrbitSpan_le_iff _ _ _).mpr
  apply Submodule.mem_map.mpr
  exact ⟨youngPolytabloid μ, youngPolytabloid_mem_corner_filtration μ b,
    youngTabloidDeleteLinear_polytabloid μ b⟩

theorem youngSpecht_finrank_le_deletionImage (μ : YoungDiagram) (b : YoungCorner μ) :
    Module.finrank ℂ (YoungSpechtModule (removePartitionBox μ b)) ≤
      Module.finrank ℂ (youngDeletionImageSubrepresentation μ b (b.val.val.1 + 1)).toSubmodule := by
  exact Submodule.finrank_mono (youngSpecht_le_deletionImage μ b)

end
end ModifiedCartan


