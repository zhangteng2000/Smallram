import ModifiedCartan.CharacterProjectorRange

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W U : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

omit [FiniteDimensional ℂ U] in
theorem isotypic_le_ker_characterProjector (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (τ : Representation ℂ G U)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hne : ¬ Nonempty (Representation.Equiv ρ σ)) :
    representationIsotypicSubmodule σ τ ≤ LinearMap.ker (characterProjector ρ τ) := by
  apply iSup_le
  intro f v hv
  obtain ⟨w, rfl⟩ := hv
  have h := congrArg (fun L : W →ₗ[ℂ] U => L w) (characterProjector_natural ρ σ τ f)
  rw [characterProjector_on_irreducible ρ σ, if_neg hne] at h
  simpa only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using h

theorem characterProjector_mul_eq_zero (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (τ : Representation ℂ G U)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hne : ¬ Nonempty (Representation.Equiv ρ σ)) :
    characterProjector ρ τ * characterProjector σ τ = 0 := by
  apply LinearMap.ext
  intro v
  exact isotypic_le_ker_characterProjector ρ σ τ hne
    (characterProjector_apply_mem_isotypic σ τ v)

end
end ModifiedCartan


