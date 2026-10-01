import ModifiedCartan.KPFullCharacterAction
import ModifiedCartan.CharacterPositive
import ModifiedCartan.SubsetRepresentationOperators

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem kpAlpha_action_isPositive {A W : Type*} [Fintype A] [DecidableEq A]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Equiv.Perm A) W) (hρ : IsUnitaryRepresentation ρ)
    (μ : YoungDiagram) (I : Finset A) : (ρ.asAlgebraHom (kpAlpha μ I)).IsPositive := by
  by_cases hI : I.card = partitionSize μ
  · rw [← kpSubsetExtension_full I μ hI, asAlgebraHom_subsetExtension, kpFullCharacterSum_action]
    letI := spechtRepresentationOn_irreducible μ ((Fintype.card_coe I).trans hI)
    exact characterWeightedOperator_isPositive _ _ (fun g v w => hρ (subsetPermutationInclusion I g) v w)
  · rw [kpAlpha_of_card_ne μ I hI, map_zero]
    exact LinearMap.isPositive_zero

end
end ModifiedCartan


