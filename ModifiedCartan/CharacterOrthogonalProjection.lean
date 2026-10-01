import ModifiedCartan.CharacterProjectorRange
import ModifiedCartan.CharacterOrthogonalInvariant

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem characterProjector_eq_zero_on_orthogonal (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (hσ : IsUnitaryRepresentation σ) {v : W}
    (hv : v ∈ (representationIsotypicSubmodule ρ σ)ᗮ) : characterProjector ρ σ v = 0 := by
  have hi := characterProjector_apply_mem_isotypic ρ σ v
  have ho := characterProjector_preserves_orthogonal ρ σ hσ hv
  exact inner_self_eq_zero.mp
    (((representationIsotypicSubmodule ρ σ).mem_orthogonal _).mp ho _ hi)

/-- Character projection onto the actual isotypic component, proved from Maschke and unitarity. -/
theorem characterProjector_eq_starProjection (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (hσ : IsUnitaryRepresentation σ) :
    characterProjector ρ σ =
      ((representationIsotypicSubmodule ρ σ).starProjection : W →ₗ[ℂ] W) := by
  apply LinearMap.ext
  intro v
  have hz := characterProjector_eq_zero_on_orthogonal ρ σ hσ
    ((representationIsotypicSubmodule ρ σ).sub_starProjection_mem_orthogonal v)
  rw [map_sub, characterProjector_fixed_on_isotypic ρ σ _
    ((representationIsotypicSubmodule ρ σ).starProjection_apply_mem v)] at hz
  exact sub_eq_zero.mp hz

theorem norm_characterProjector_apply_le (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (hσ : IsUnitaryRepresentation σ) (v : W) : ‖characterProjector ρ σ v‖ ≤ ‖v‖ := by
  rw [characterProjector_eq_starProjection ρ σ hσ]
  exact (representationIsotypicSubmodule ρ σ).norm_starProjection_apply_le v

end
end ModifiedCartan


