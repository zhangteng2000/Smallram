import ModifiedCartan.KPOperators
import ModifiedCartan.FixedPointDeletion

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem subgroup_character_sum_coefficient {G : Type*} [Group G] [DecidableEq G]
    (H : Subgroup G) [Fintype H] (f : H → ℂ) (g : G) :
    (∑ h : H, MonoidAlgebra.single h.val (f h)).coeff g =
      if hg : g ∈ H then f ⟨g, hg⟩ else 0 := by
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hg : g ∈ H
  · rw [dif_pos hg, Finset.sum_eq_single (⟨g, hg⟩ : H)]
    · simp
    · intro h _ hh
      have hn : h.val ≠ g := fun he => hh (Subtype.ext he)
      simp [hn]
    · simp
  · rw [dif_neg hg]
    apply Finset.sum_eq_zero
    intro h _
    have hn : h.val ≠ g := fun he => hg (he ▸ h.property)
    simp [hn]

theorem kpAlpha_coefficient {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (I : Finset A) (hI : I.card = partitionSize μ) (g : Equiv.Perm A) :
    (kpAlpha μ I).coeff g = if hg : g ∈ supportedPermutationSubgroup I then
      spechtCharacterOn μ ((Fintype.card_coe I).trans hI)
        ((supportedPermutationEquiv I).symm ⟨g, hg⟩) else 0 := by
  rw [kpAlpha_of_card_eq μ I hI]
  have hs : (∑ p : Equiv.Perm I, MonoidAlgebra.single (supportedPermutationEquiv I p).val
      (spechtCharacterOn μ ((Fintype.card_coe I).trans hI) p)) =
      ∑ q : supportedPermutationSubgroup I, MonoidAlgebra.single q.val
        (spechtCharacterOn μ ((Fintype.card_coe I).trans hI) ((supportedPermutationEquiv I).symm q)) := by
    calc
      _ = ∑ p : Equiv.Perm I, MonoidAlgebra.single (supportedPermutationEquiv I p).val
          (spechtCharacterOn μ ((Fintype.card_coe I).trans hI)
            ((supportedPermutationEquiv I).symm (supportedPermutationEquiv I p))) := by
        simp only [MulEquiv.symm_apply_apply]
      _ = _ := (supportedPermutationEquiv I).toEquiv.sum_comp (fun q => MonoidAlgebra.single q.val
        (spechtCharacterOn μ ((Fintype.card_coe I).trans hI) ((supportedPermutationEquiv I).symm q)))
  rw [hs, subgroup_character_sum_coefficient]

theorem kpAlpha_erase_coefficient {A : Type*} [Fintype A] [DecidableEq A]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ + 1) (a : A) (g : Equiv.Perm A) :
    (kpAlpha μ (Finset.univ.erase a)).coeff g = if hg : g a = a then
      spechtCharacterOn μ (by
        rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, h]
        omega) (deleteFixedPoint a g hg) else 0 := by
  have hI : (Finset.univ.erase a).card = partitionSize μ := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, h]
    omega
  rw [kpAlpha_coefficient μ _ hI g]
  by_cases hg : g a = a
  · have hm : g ∈ supportedPermutationSubgroup (Finset.univ.erase a) :=
      (fixedPointStabilizerElement a g hg).property
    rw [dif_pos hm, dif_pos hg]
    rfl
  · have hm : g ∉ supportedPermutationSubgroup (Finset.univ.erase a) := fun hm => hg (hm a (by simp))
    rw [dif_neg hm, dif_neg hg]

end
end ModifiedCartan


