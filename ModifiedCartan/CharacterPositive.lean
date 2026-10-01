import ModifiedCartan.CharacterProjectionBound
import Mathlib.Analysis.InnerProductSpace.Positive

open scoped BigOperators Classical ComplexOrder

namespace ModifiedCartan
noncomputable section

theorem characterWeightedOperator_isPositive {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (hσ : IsUnitaryRepresentation σ) : (characterWeightedOperator ρ σ).IsPositive := by
  rw [characterWeightedOperator_eq_scaled_projector, characterProjector_eq_starProjection ρ σ hσ]
  apply (Submodule.isSymmetricProjection_starProjection _).isPositive.smul_of_nonneg
  positivity

theorem positive_operators_eq_zero_of_sum_eq_zero {ι W : Type*} [Fintype ι]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : ι → Module.End ℂ W) (hT : ∀ i, (T i).IsPositive) (h : ∑ i, T i = 0) (i : ι) :
    T i = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    (LinearMap.nonneg_iff_isPositive _).mpr (hT j))).mp h i (Finset.mem_univ i)

end
end ModifiedCartan


