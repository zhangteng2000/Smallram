import ModifiedCartan.KPRealSymmetric
import ModifiedCartan.KPJointEigenspace
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

open scoped Classical

namespace ModifiedCartan
noncomputable section

attribute [local instance] youngPermutationModuleNormed youngPermutationModuleInner

theorem kpJointEigenspaces_real_iSup {N : ℕ} (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℝ) :
    (⨆ χ : YoungDiagram → ℂ, kpJointEigenspace τ h (fun i => (z i : ℂ)) χ) = ⊤ := by
  apply LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
  · intro μ
    exact specht_kpBeta_isSymmetric_of_real τ h μ z 0
  · intro μ ν hne
    exact (kpBeta_commute (fun i => (z i : ℂ)) μ ν 0 0).map (spechtRepresentationOn τ h).asAlgebraHom

/-- Actual joint eigenspaces give a direct sum for every real parameter tuple,
including tuples with collisions. -/
theorem kpJointEigenspaces_real_isInternal {N : ℕ} (τ : YoungDiagram)
    (h : Fintype.card (Fin N) = partitionSize τ) (z : Fin N → ℝ) :
    DirectSum.IsInternal (kpJointEigenspace τ h (fun i => (z i : ℂ))) := by
  apply LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
  · intro μ
    exact specht_kpBeta_isSymmetric_of_real τ h μ z 0
  · intro μ ν hne
    exact (kpBeta_commute (fun i => (z i : ℂ)) μ ν 0 0).map (spechtRepresentationOn τ h).asAlgebraHom

end
end ModifiedCartan


