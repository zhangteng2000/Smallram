import ModifiedCartan.KPJointEigenspace
import ModifiedCartan.KPSpechtSupport
import ModifiedCartan.ScalarActionAdjoin

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem kpJointEigenspace_generated_scalar (τ : YoungDiagram)
    (h : Fintype.card A = partitionSize τ) (z : A → ℂ) (χ : YoungDiagram → ℂ)
    (x : kpGeneratedAlgebra z) : ∃ c : ℂ, ∀ v ∈ kpJointEigenspace τ h z χ,
      (spechtRepresentationOn τ h).asAlgebraHom x.val v = c • v := by
  apply scalar_action_of_mem_adjoin (spechtRepresentationOn τ h).asAlgebraHom
    (kpJointEigenspace τ h z χ) (Set.range fun μ => kpBeta μ z 0) _ x.val x.property
  rintro _ ⟨μ, rfl⟩
  refine ⟨χ μ, ?_⟩
  intro v hv
  exact (mem_kpJointEigenspace_iff τ h z χ v).mp hv μ

theorem kpJointEigenvalue_top (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ h z χ ≠ ⊥) :
    χ τ = ((partitionSize τ).factorial : ℂ) / (standardSkewTableauCount τ ⊥ : ℂ) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply smul_left_injective ℂ hv0
  have he := (mem_kpJointEigenspace_iff τ h z χ v).mp hv τ
  rw [specht_kpBeta_full_size τ h z 0, LinearMap.smul_apply, Module.End.one_apply] at he
  exact he.symm

theorem kpJointEigenvalue_eq_zero_of_not_le (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ h z χ ≠ ⊥)
    (μ : YoungDiagram) (hnot : ¬μ ≤ τ) : χ μ = 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply smul_left_injective ℂ hv0
  have he := (mem_kpJointEigenspace_iff τ h z χ v).mp hv μ
  rw [specht_kpBeta_eq_zero_of_not_le μ τ h hnot z 0, LinearMap.zero_apply] at he
  simpa only [zero_smul] using he.symm

theorem kpJointEigenvector_translation (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ) (v : YoungSpechtModule τ)
    (hv : v ∈ kpJointEigenspace τ h z χ) (μ : YoungDiagram) (a : ℂ) :
    (spechtRepresentationOn τ h).asAlgebraHom (kpBeta μ z a) v =
      (∑ ν : Subpartition (partitionSquare (Fintype.card A)),
        ((standardSkewTableauCount ν.val μ : ℂ) / ((partitionSize ν.val - partitionSize μ).factorial : ℂ) *
          a ^ (partitionSize ν.val - partitionSize μ)) * χ ν.val) • v := by
  have ht := kpBeta_translation μ z 0 a
  rw [zero_add] at ht
  rw [ht, map_sum, LinearMap.sum_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ν _
  rw [map_smul, LinearMap.smul_apply, (mem_kpJointEigenspace_iff τ h z χ v).mp hv ν.val, smul_smul]

end
end ModifiedCartan


