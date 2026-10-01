import ModifiedCartan.KPBetaFullSize
import ModifiedCartan.KPTranslation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem specht_kpAlpha_univ_eq_zero_of_ne (μ τ : YoungDiagram)
    (hτ : Fintype.card A = partitionSize τ) (hne : μ ≠ τ) :
    (spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ (Finset.univ : Finset A)) = 0 := by
  by_cases hμ : Fintype.card A = partitionSize μ
  · rw [kpAlpha_univ_eq_full μ hμ, kpFullCharacterSum_action_on_specht, ite_eq_right hne]
  · rw [kpAlpha_of_card_ne μ _ (by simpa using hμ), map_zero]

theorem kpBeta_zero_parameters_one (μ : YoungDiagram) :
    kpBeta μ (fun _ : A => 0) 1 = ∑ I : Finset A, kpAlpha μ I := by
  simp [kpBeta_eq_sum_all_subsets, kpWeight]

theorem specht_sum_kpAlpha_eq_zero_of_not_le (μ τ : YoungDiagram)
    (hτ : Fintype.card A = partitionSize τ) (hnot : ¬μ ≤ τ) :
    (∑ I : Finset A, (spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I)) = 0 := by
  rw [← map_sum, ← kpBeta_zero_parameters_one]
  have ht := kpBeta_translation μ (fun _ : A => 0) 0 1
  rw [zero_add] at ht
  rw [ht, map_sum]
  apply Finset.sum_eq_zero
  intro ν _
  by_cases he : ν.val = τ
  · rw [he, standardSkewTableauCount_of_not_le hnot]
    simp
  · rw [map_smul, kpBeta_zero_parameters, specht_kpAlpha_univ_eq_zero_of_ne ν.val τ hτ he,
      smul_zero]

end
end ModifiedCartan


