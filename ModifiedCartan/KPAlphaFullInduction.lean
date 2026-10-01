import ModifiedCartan.KPAlphaCoefficients
import ModifiedCartan.SpechtInductionCharacter

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def kpFullCharacterSum (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) : ℂ[Equiv.Perm A] :=
  ∑ g : Equiv.Perm A, MonoidAlgebra.single g (spechtCharacterOn μ h g)

theorem kpFullCharacterSum_coefficient (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (g : Equiv.Perm A) : (kpFullCharacterSum μ h).coeff g = spechtCharacterOn μ h g := by
  simp [kpFullCharacterSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- The one-box group-algebra induction identity on a whole finite alphabet.
This is the coefficient identity underlying LaTeX `eq:KP-translation`. -/
theorem kpAlpha_sum_erase (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ + 1) :
    (∑ a : A, kpAlpha μ (Finset.univ.erase a)) =
      ∑ ν : SizedYoungDiagram (Fintype.card A),
        if PartitionCovers ν.val μ then kpFullCharacterSum ν.val ν.property.symm else 0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, kpAlpha_erase_coefficient μ h]
  change inducedSpechtCharacter μ h g = _
  rw [inducedSpechtCharacter_eq_sum_covers]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases hc : PartitionCovers ν.val μ <;>
    simp only [hc, ite_true, ite_false, kpFullCharacterSum_coefficient,
      MonoidAlgebra.coeff_zero, Finsupp.zero_apply]

def kpSubsetExtension (J : Finset A) : ℂ[Equiv.Perm J] →ₗ[ℂ] ℂ[Equiv.Perm A] :=
  MonoidAlgebra.mapDomainLinearMap ℂ ℂ (fun p => (supportedPermutationEquiv J p).val)

theorem kpSubsetExtension_full (J : Finset A) (μ : YoungDiagram)
    (h : J.card = partitionSize μ) :
    kpSubsetExtension J (kpFullCharacterSum μ ((Fintype.card_coe J).trans h)) = kpAlpha μ J := by
  rw [kpAlpha_of_card_eq μ J h]
  simp only [kpSubsetExtension, kpFullCharacterSum, map_sum, MonoidAlgebra.mapDomainLinearMap_single]

end
end ModifiedCartan


