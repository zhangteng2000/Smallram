import ModifiedCartan.CharacterProjectorRank
import ModifiedCartan.IsotypicCopies
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- A multiplicity-one isotypic subspace is the actual image of an injective
intertwiner from the irreducible representation. -/
theorem exists_intertwiner_range_of_isotypic_finrank (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (hd : Module.finrank ℂ (representationIsotypicSubmodule ρ σ) = Module.finrank ℂ V) :
    ∃ f : Representation.IntertwiningMap ρ σ, Function.Injective f ∧
      LinearMap.range f.toLinearMap = representationIsotypicSubmodule ρ σ := by
  have hex : ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 := by
    by_contra hn
    have hz (f : Representation.IntertwiningMap ρ σ) : f = 0 := by
      by_contra hf
      exact hn ⟨f, hf⟩
    have hbot : representationIsotypicSubmodule ρ σ = ⊥ := by
      apply bot_unique
      apply iSup_le
      intro f
      rw [hz f]
      simp [Representation.IntertwiningMap.zero_toLinearMap]
    have hs : Module.finrank ℂ (representationIsotypicSubmodule ρ σ) = 0 :=
      Submodule.finrank_eq_zero.mpr hbot
    have hv : Module.finrank ℂ V = 0 := hd.symm.trans hs
    exact irreducible_finrank_ne_zero ρ hv
  obtain ⟨f, hf⟩ := hex
  have hi : Function.Injective f := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  refine ⟨f, hi, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · exact le_iSup (fun g : Representation.IntertwiningMap ρ σ => LinearMap.range g.toLinearMap) f
  · exact (LinearMap.finrank_range_of_inj hi).trans hd.symm

end
end ModifiedCartan


