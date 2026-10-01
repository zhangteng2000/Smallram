import ModifiedCartan.ClassFunctionScalarAction
import ModifiedCartan.CharacterProjectorRange

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem classFunctionOperator_on_isotypic (f : G → ℂ) (hf : IsConjugacyInvariant f)
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (v : W) (hv : v ∈ representationIsotypicSubmodule ρ σ) :
    classFunctionOperator f σ v = classFunctionScalar f ρ • v := by
  let K : Submodule ℂ W := LinearMap.ker
    (classFunctionOperator f σ - classFunctionScalar f ρ • (1 : Module.End ℂ W))
  have hK : representationIsotypicSubmodule ρ σ ≤ K := by
    apply iSup_le
    intro F w hw
    obtain ⟨u, rfl⟩ := hw
    have hn := congrArg (fun L : V →ₗ[ℂ] W => L u) (classFunctionOperator_natural f ρ σ F)
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at hn
    rw [classFunctionOperator_on_irreducible f hf ρ] at hn
    simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul] at hn
    change classFunctionOperator f σ (F u) - classFunctionScalar f ρ • F u = 0
    exact sub_eq_zero.mpr hn
  have h := hK hv
  change classFunctionOperator f σ v - classFunctionScalar f ρ • v = 0 at h
  exact sub_eq_zero.mp h

theorem classFunctionOperator_mul_characterProjector [FiniteDimensional ℂ W]
    (f : G → ℂ) (hf : IsConjugacyInvariant f) (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] :
    classFunctionOperator f σ * characterProjector ρ σ =
      classFunctionScalar f ρ • characterProjector ρ σ := by
  apply LinearMap.ext
  intro v
  exact classFunctionOperator_on_isotypic f hf ρ σ _
    (characterProjector_apply_mem_isotypic ρ σ v)

end
end ModifiedCartan

