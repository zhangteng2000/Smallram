import ModifiedCartan.YoungRowDegrees
import ModifiedCartan.FrobeniusWeightVanishing

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem youngSpecht_weightColoring_intertwiner_zero_of_le_ne {m : ℕ} (μ : YoungDiagram)
    (d : Fin m →₀ ℕ) (hd : finiteColorWeight d ≤ partitionRowWeight μ)
    (hne : Finsupp.mapDomain Fin.val d ≠ partitionRowDegree μ)
    (F : Representation.IntertwiningMap (youngSpechtRepresentation μ)
      (weightColoringRepresentation (YoungBoxes μ) d)) : F = 0 := by
  apply youngSpechtIntertwiner_eq_zero_of_generator μ _ F
  ext f
  obtain ⟨a, b, hne, hcol, hc⟩ := weightColoring_column_collision_of_le_ne μ d hd hne f
  exact columnSignVector_collision_coeff μ d (F (youngSpechtGenerator μ))
    (youngSpechtIntertwiner_generator_column μ _ F) f a b hne hcol hc

theorem finiteFrobeniusPolynomial_coeff_zero_of_weight_le_ne {m : ℕ}
    (μ : YoungDiagram) (d : Fin m →₀ ℕ) (hd : finiteColorWeight d ≤ partitionRowWeight μ)
    (hne : Finsupp.mapDomain Fin.val d ≠ partitionRowDegree μ) :
    MvPolynomial.coeff d (finiteFrobeniusPolynomial (Fin m) μ) = 0 := by
  rw [finiteFrobeniusPolynomial_coeff_finrank_young,
    finrank_zero_iff_forall_zero.mpr
      (youngSpecht_weightColoring_intertwiner_zero_of_le_ne μ d hd hne)]
  simp

end
end ModifiedCartan


