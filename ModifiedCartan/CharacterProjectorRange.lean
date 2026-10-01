import ModifiedCartan.CharacterIrreducibleImages
import ModifiedCartan.GroupSubmoduleIntertwiners

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

set_option backward.isDefEq.respectTransparency false in
theorem characterProjector_apply_mem_isotypic (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] (v : W) :
    characterProjector ρ σ v ∈ representationIsotypicSubmodule ρ σ := by
  let K : Submodule ℂ σ.asModule :=
    (representationIsotypicSubmodule ρ σ).comap
      ((characterProjector ρ σ).comp σ.asModuleEquiv.toLinearMap)
  have hk : K = ⊤ := by
    apply complex_submodule_eq_top_of_contains_group_simples (G := G)
    intro S hS w hw
    letI : IsSimpleModule ℂ[G] S := hS
    letI : FiniteDimensional ℂ (RestrictScalars ℂ ℂ[G] S) :=
      groupSubmoduleRepresentationFinite σ S
    letI : Representation.IsIrreducible (Representation.ofModule (k := ℂ) (G := G) S) :=
      groupSubmoduleRepresentationIrreducible σ S
    have hm := characterProjector_apply_irreducible_mem_isotypic ρ
      (Representation.ofModule (k := ℂ) (G := G) S) σ
      (groupSubmoduleIntertwiner σ S) ((RestrictScalars.addEquiv ℂ ℂ[G] S).symm ⟨w, hw⟩)
    exact hm
  have hv : σ.asModuleEquiv.symm v ∈ K := by rw [hk]; trivial
  change characterProjector ρ σ (σ.asModuleEquiv (σ.asModuleEquiv.symm v)) ∈
    representationIsotypicSubmodule ρ σ at hv
  simpa only [LinearEquiv.apply_symm_apply] using hv

/-- The character operator projects onto the actual sum of irreducible copies. -/
theorem characterProjector_range_eq_isotypic (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    LinearMap.range (characterProjector ρ σ) = representationIsotypicSubmodule ρ σ := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact characterProjector_apply_mem_isotypic ρ σ w
  · exact isotypic_le_characterProjector_range ρ σ

theorem characterProjector_idempotent (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    characterProjector ρ σ * characterProjector ρ σ = characterProjector ρ σ := by
  apply LinearMap.ext
  intro v
  exact characterProjector_fixed_on_isotypic ρ σ _
    (characterProjector_apply_mem_isotypic ρ σ v)

end
end ModifiedCartan


