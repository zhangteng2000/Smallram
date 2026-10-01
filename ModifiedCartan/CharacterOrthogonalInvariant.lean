import ModifiedCartan.CharacterProjectorFixed
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

section Invariance
variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem representationIsotypic_invariant (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (g : G) {v : W}
    (hv : v ∈ representationIsotypicSubmodule ρ σ) :
    σ g v ∈ representationIsotypicSubmodule ρ σ := by
  have hk : representationIsotypicSubmodule ρ σ ≤
      (representationIsotypicSubmodule ρ σ).comap (σ g) := by
    apply iSup_le
    intro f
    rintro w ⟨u, rfl⟩
    change σ g (f.toLinearMap u) ∈ representationIsotypicSubmodule ρ σ
    rw [Representation.IntertwiningMap.toLinearMap_apply,
      ← Representation.IntertwiningMap.isIntertwining ρ σ f g u]
    exact intertwiner_apply_mem_isotypic ρ σ f (ρ g u)
  exact hk hv

end Invariance

section Orthogonal
variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def IsUnitaryRepresentation (σ : Representation ℂ G W) : Prop :=
  ∀ (g : G) (v w : W), inner ℂ (σ g v) (σ g w) = inner ℂ v w

theorem invariant_orthogonal_of_unitary (σ : Representation ℂ G W)
    (hσ : IsUnitaryRepresentation σ) (K : Submodule ℂ W)
    (hK : ∀ (g : G) (v : W), v ∈ K → σ g v ∈ K)
    (g : G) {v : W} (hv : v ∈ Kᗮ) : σ g v ∈ Kᗮ := by
  apply (K.mem_orthogonal _).mpr
  intro w hw
  have hg : σ g (σ g⁻¹ w) = w := by
    change (σ g * σ g⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    inner ℂ w (σ g v) = inner ℂ (σ g (σ g⁻¹ w)) (σ g v) := by rw [hg]
    _ = inner ℂ (σ g⁻¹ w) v := hσ g _ _
    _ = 0 := (K.mem_orthogonal v).mp hv _ (hK g⁻¹ w hw)

theorem characterProjector_preserves_orthogonal (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hσ : IsUnitaryRepresentation σ)
    {v : W} (hv : v ∈ (representationIsotypicSubmodule ρ σ)ᗮ) :
    characterProjector ρ σ v ∈ (representationIsotypicSubmodule ρ σ)ᗮ := by
  simp only [characterProjector, characterWeightedOperator, LinearMap.smul_apply,
    LinearMap.sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro g _
  apply Submodule.smul_mem
  exact invariant_orthogonal_of_unitary σ hσ _
    (fun h w hw => representationIsotypic_invariant ρ σ h hw) g hv

end Orthogonal
end
end ModifiedCartan


