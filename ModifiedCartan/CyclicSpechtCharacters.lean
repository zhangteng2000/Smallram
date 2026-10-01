import ModifiedCartan.SpechtRepresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace ModifiedCartan
noncomputable section

theorem youngSpecht_eq_span_of_polytabloid_scalars (μ : YoungDiagram)
    (χ : Equiv.Perm (YoungBoxes μ) → ℂ)
    (hχ : ∀ g, youngTabloidRepresentation μ g (youngPolytabloid μ) = χ g • youngPolytabloid μ) :
    (youngSpechtSubrepresentation μ).toSubmodule = Submodule.span ℂ {youngPolytabloid μ} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨g, rfl⟩
    change youngTabloidRepresentation μ g (youngPolytabloid μ) ∈ Submodule.span ℂ {youngPolytabloid μ}
    rw [hχ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro v hv
    have he : v = youngPolytabloid μ := Set.mem_singleton_iff.mp hv
    rw [he]
    exact youngPolytabloid_mem_specht μ

theorem youngSpecht_finrank_of_polytabloid_scalars (μ : YoungDiagram)
    (χ : Equiv.Perm (YoungBoxes μ) → ℂ)
    (hχ : ∀ g, youngTabloidRepresentation μ g (youngPolytabloid μ) = χ g • youngPolytabloid μ) :
    Module.finrank ℂ (YoungSpechtModule μ) = 1 := by
  change Module.finrank ℂ (youngSpechtSubrepresentation μ).toSubmodule = 1
  rw [youngSpecht_eq_span_of_polytabloid_scalars μ χ hχ]
  exact finrank_span_singleton (youngPolytabloid_ne_zero μ)

theorem youngSpecht_action_of_polytabloid_scalars (μ : YoungDiagram)
    (χ : Equiv.Perm (YoungBoxes μ) → ℂ)
    (hχ : ∀ g, youngTabloidRepresentation μ g (youngPolytabloid μ) = χ g • youngPolytabloid μ)
    (g : Equiv.Perm (YoungBoxes μ)) : youngSpechtRepresentation μ g = χ g • 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change youngTabloidRepresentation μ g v.val = χ g • v.val
  have hv : v.val ∈ Submodule.span ℂ {youngPolytabloid μ} := by
    rw [← youngSpecht_eq_span_of_polytabloid_scalars μ χ hχ]
    exact v.property
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hv
  rw [← hz, map_smul, hχ, smul_smul, smul_smul, mul_comm z (χ g)]

theorem youngSpecht_character_of_polytabloid_scalars (μ : YoungDiagram)
    (χ : Equiv.Perm (YoungBoxes μ) → ℂ)
    (hχ : ∀ g, youngTabloidRepresentation μ g (youngPolytabloid μ) = χ g • youngPolytabloid μ)
    (g : Equiv.Perm (YoungBoxes μ)) : (youngSpechtRepresentation μ).character g = χ g := by
  unfold Representation.character
  rw [youngSpecht_action_of_polytabloid_scalars μ χ hχ, map_smul, LinearMap.trace_one,
    youngSpecht_finrank_of_polytabloid_scalars μ χ hχ]
  simp

end
end ModifiedCartan



