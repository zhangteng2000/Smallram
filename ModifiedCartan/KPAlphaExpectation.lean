import ModifiedCartan.KPAlphaPositive
import ModifiedCartan.CharacterProjectionBound

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- The exact factorial coefficient bound from LaTeX `eq:projectionbound`,
    for any finite unitary symmetric-group representation and any subset. -/
theorem kpAlpha_expectation_bound {A W : Type*} [Fintype A] [DecidableEq A]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Equiv.Perm A) W) (hρ : IsUnitaryRepresentation ρ)
    (μ : YoungDiagram) (I : Finset A) (v : W) (hv : ‖v‖ = 1) :
    ‖inner ℂ v (ρ.asAlgebraHom (kpAlpha μ I) v)‖ ≤ ((partitionSize μ).factorial : ℝ) := by
  by_cases hI : I.card = partitionSize μ
  · rw [← kpSubsetExtension_full I μ hI, asAlgebraHom_subsetExtension, kpFullCharacterSum_action]
    let := spechtRepresentationOn_irreducible μ ((Fintype.card_coe I).trans hI)
    have h := norm_characterWeightedOperator_expectation_le_card
      (spechtRepresentationOn μ ((Fintype.card_coe I).trans hI))
      (ρ.comp (subsetPermutationInclusion I))
      (fun g w u => hρ (subsetPermutationInclusion I g) w u) v hv
    simpa only [natCard_permutation_eq_factorial, Fintype.card_coe, hI] using h
  · rw [kpAlpha_of_card_ne μ I hI, map_zero, LinearMap.zero_apply, inner_zero_right, norm_zero]
    positivity

end
end ModifiedCartan

#print axioms ModifiedCartan.kpAlpha_expectation_bound