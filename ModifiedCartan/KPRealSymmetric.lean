import ModifiedCartan.KPAlphaPositive
import ModifiedCartan.KPSubsetWeights

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem kpBeta_action_isSymmetric_of_real {A W : Type*} [Fintype A] [DecidableEq A]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Equiv.Perm A) W) (hρ : IsUnitaryRepresentation ρ)
    (μ : YoungDiagram) (z : A → ℝ) (a : ℝ) :
    (ρ.asAlgebraHom (kpBeta μ (fun i => (z i : ℂ)) (a : ℂ))).IsSymmetric := by
  rw [kpBeta_eq_sum_all_subsets, map_sum]
  apply LinearMap.isSymmetric_sum
  intro I hI
  rw [map_smul]
  apply LinearMap.IsSymmetric.smul
  · simp [kpWeight]
  · exact (kpAlpha_action_isPositive ρ hρ μ I).isSymmetric

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

theorem specht_kpBeta_isSymmetric_of_real {A : Type*} [Fintype A] [DecidableEq A]
    (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ)
    (μ : YoungDiagram) (z : A → ℝ) (a : ℝ) :
    ((spechtRepresentationOn τ h).asAlgebraHom
      (kpBeta μ (fun i => (z i : ℂ)) (a : ℂ))).IsSymmetric :=
  kpBeta_action_isSymmetric_of_real _ (spechtRepresentationOn_unitary τ h) μ z a

end
end ModifiedCartan


