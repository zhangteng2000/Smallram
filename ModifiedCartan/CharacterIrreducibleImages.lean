import ModifiedCartan.CharacterProjectorFixed

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W U : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem characterProjector_apply_irreducible_intertwiner (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (τ : Representation ℂ G U)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (f : Representation.IntertwiningMap σ τ) (v : W) :
    characterProjector ρ τ (f v) =
      if Nonempty (Representation.Equiv ρ σ) then f v else 0 := by
  have he := congrArg (fun L : W →ₗ[ℂ] U => L v) (characterProjector_natural ρ σ τ f)
  simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at he
  rw [he, characterProjector_on_irreducible]
  split_ifs <;> simp

theorem intertwiner_apply_mem_isotypic_of_equiv (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (τ : Representation ℂ G U)
    (e : Representation.Equiv ρ σ) (f : Representation.IntertwiningMap σ τ) (v : W) :
    f v ∈ representationIsotypicSubmodule ρ τ := by
  have hm := intertwiner_apply_mem_isotypic ρ τ
    (f.comp e.toIntertwiningMap) (e.symm v)
  change f (e (e.symm v)) ∈ representationIsotypicSubmodule ρ τ at hm
  simpa only [Representation.Equiv.apply_symm_apply] using hm

theorem characterProjector_apply_irreducible_mem_isotypic (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (τ : Representation ℂ G U)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (f : Representation.IntertwiningMap σ τ) (v : W) :
    characterProjector ρ τ (f v) ∈ representationIsotypicSubmodule ρ τ := by
  rw [characterProjector_apply_irreducible_intertwiner ρ σ τ f v]
  split_ifs with h
  · exact intertwiner_apply_mem_isotypic_of_equiv ρ σ τ (Classical.choice h) f v
  · exact (representationIsotypicSubmodule ρ τ).zero_mem

end
end ModifiedCartan


