import ModifiedCartan.KPAlphaFullInduction
import ModifiedCartan.SpechtDistinctCharacters
import ModifiedCartan.SymmetricCharacterProjection

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def finsetUnivEquiv (A : Type*) [Fintype A] : ↥(Finset.univ : Finset A) ≃ A where
  toFun := Subtype.val
  invFun a := ⟨a, Finset.mem_univ a⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem supportedPermutation_univ (p : Equiv.Perm (↥(Finset.univ : Finset A))) :
    (supportedPermutationEquiv Finset.univ p).val = (finsetUnivEquiv A).permCongr p := by
  ext a
  exact supportedPermutationEquiv_apply_coe Finset.univ p ⟨a, Finset.mem_univ a⟩

theorem kpAlpha_univ_eq_full (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) :
    kpAlpha μ (Finset.univ : Finset A) = kpFullCharacterSum μ h := by
  rw [kpAlpha_of_card_eq μ _ (by simpa using h)]
  unfold kpFullCharacterSum
  calc
    _ = ∑ p : Equiv.Perm (↥(Finset.univ : Finset A)),
        MonoidAlgebra.single ((finsetUnivEquiv A).permCongr p)
          (spechtCharacterOn μ h ((finsetUnivEquiv A).permCongr p)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [supportedPermutation_univ, spechtCharacterOn_relabel μ _ h (finsetUnivEquiv A) p]
    _ = _ := (finsetUnivEquiv A).permCongr.sum_comp (fun g =>
      MonoidAlgebra.single g (spechtCharacterOn μ h g))

theorem kpFullCharacterSum_action {W : Type*} [AddCommGroup W] [Module ℂ W]
    (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (ρ : Representation ℂ (Equiv.Perm A) W) :
    ρ.asAlgebraHom (kpFullCharacterSum μ h) = characterWeightedOperator (spechtRepresentationOn μ h) ρ := by
  simp only [kpFullCharacterSum, map_sum, Representation.asAlgebraHom_single,
    characterWeightedOperator, permutation_character_inv, spechtRepresentationOn_character]

theorem kpFullCharacterSum_action_on_specht (μ τ : YoungDiagram)
    (hμ : Fintype.card A = partitionSize μ) (hτ : Fintype.card A = partitionSize τ) :
    (spechtRepresentationOn τ hτ).asAlgebraHom (kpFullCharacterSum μ hμ) =
      if μ = τ then (((Fintype.card A).factorial : ℂ) /
        (Module.finrank ℂ (YoungSpechtModule μ) : ℂ)) • (1 : Module.End ℂ (YoungSpechtModule τ)) else 0 := by
  letI := spechtRepresentationOn_irreducible μ hμ
  letI := spechtRepresentationOn_irreducible τ hτ
  rw [kpFullCharacterSum_action, characterWeightedOperator_on_irreducible,
    natCard_permutation_eq_factorial]
  by_cases he : μ = τ
  · subst τ
    simp only [ite_true, show Nonempty (Representation.Equiv (spechtRepresentationOn μ hμ)
      (spechtRepresentationOn μ hτ)) from ⟨Representation.Equiv.refl _⟩]
  · have hn : ¬Nonempty (Representation.Equiv (spechtRepresentationOn μ hμ)
        (spechtRepresentationOn τ hτ)) := by
      rintro ⟨e⟩
      exact he (spechtRepresentationOn_equiv_shape μ τ hμ hτ e)
    rw [ite_eq_right hn, ite_eq_right he]

end
end ModifiedCartan


