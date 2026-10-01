import ModifiedCartan.CharacterProjectorBasic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem intertwiner_apply_mem_isotypic (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (f : Representation.IntertwiningMap ρ σ) (v : V) :
    f v ∈ representationIsotypicSubmodule ρ σ := by
  exact (le_iSup (fun f : Representation.IntertwiningMap ρ σ =>
    LinearMap.range f.toLinearMap) f) ⟨v, rfl⟩

theorem characterProjector_fixed_on_isotypic (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (v : W) (hv : v ∈ representationIsotypicSubmodule ρ σ) :
    characterProjector ρ σ v = v := by
  have hk : representationIsotypicSubmodule ρ σ ≤
      LinearMap.ker (characterProjector ρ σ - (1 : Module.End ℂ W)) := by
    apply iSup_le
    intro f
    rintro w ⟨u, rfl⟩
    change characterProjector ρ σ (f.toLinearMap u) - f.toLinearMap u = 0
    rw [Representation.IntertwiningMap.toLinearMap_apply,
      characterProjector_apply_intertwiner ρ σ f u, sub_self]
  have hz := hk hv
  change characterProjector ρ σ v - v = 0 at hz
  exact sub_eq_zero.mp hz

theorem isotypic_le_characterProjector_range (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    representationIsotypicSubmodule ρ σ ≤ LinearMap.range (characterProjector ρ σ) := by
  intro v hv
  exact ⟨v, characterProjector_fixed_on_isotypic ρ σ v hv⟩

end
end ModifiedCartan


