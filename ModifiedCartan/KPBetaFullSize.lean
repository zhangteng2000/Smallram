import ModifiedCartan.KPFullCharacterAction
import ModifiedCartan.KPSubsetWeights

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem kpBeta_zero_parameters (μ : YoungDiagram) :
    kpBeta μ (fun _ : A => 0) 0 = kpAlpha μ (Finset.univ : Finset A) := by
  rw [kpBeta_eq_sum_all_subsets, Finset.sum_eq_single (Finset.univ : Finset A)]
  · simp [kpWeight]
  · intro I _ hI
    have he : ∃ x : A, x ∉ I := by
      by_contra! hall
      apply hI
      ext x
      simp [hall x]
    obtain ⟨x, hx⟩ := he
    have hw : kpWeight (fun _ : A => 0) 0 I = 0 := by
      apply Finset.prod_eq_zero_iff.mpr
      exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩, by simp⟩
    rw [hw, zero_smul]
  · simp

theorem kpBeta_of_full_size (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (z : A → ℂ) (a : ℂ) : kpBeta μ z a = kpFullCharacterSum μ h := by
  rw [kpBeta_eq_sum_all_subsets, Finset.sum_eq_single (Finset.univ : Finset A)]
  · simp only [kpWeight, Finset.sdiff_self, Finset.prod_empty, one_smul, kpAlpha_univ_eq_full μ h]
  · intro I _ hI
    have hn : I.card ≠ partitionSize μ := fun hc => hI (I.eq_univ_of_card (hc.trans h.symm))
    rw [kpAlpha_of_card_ne μ I hn, smul_zero]
  · simp

theorem specht_kpBeta_full_size (τ : YoungDiagram) (h : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (a : ℂ) :
    (spechtRepresentationOn τ h).asAlgebraHom (kpBeta τ z a) =
      (((partitionSize τ).factorial : ℂ) / (standardSkewTableauCount τ ⊥ : ℂ)) •
        (1 : Module.End ℂ (YoungSpechtModule τ)) := by
  rw [kpBeta_of_full_size τ h, kpFullCharacterSum_action_on_specht, ite_eq_left rfl,
    h, finrank_specht_eq_standardTableauCount]

end
end ModifiedCartan


