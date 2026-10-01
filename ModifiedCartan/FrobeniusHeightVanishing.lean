import ModifiedCartan.YoungHeightCollision
import ModifiedCartan.YoungColoringVanishing
import ModifiedCartan.YoungFrobeniusCoefficients

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem youngSpecht_weightColoring_intertwiner_zero_of_height {m : ℕ}
    (μ : YoungDiagram) (hm : m < μ.colLen 0) (d : Fin m →₀ ℕ)
    (F : Representation.IntertwiningMap (youngSpechtRepresentation μ)
      (weightColoringRepresentation (YoungBoxes μ) d)) : F = 0 := by
  apply youngSpechtIntertwiner_eq_zero_of_generator μ _ F
  ext f
  obtain ⟨a, b, hne, hcol, hc⟩ := youngFirstColumn_color_collision μ hm f.val
  exact columnSignVector_collision_coeff μ d (F (youngSpechtGenerator μ))
    (youngSpechtIntertwiner_generator_column μ _ F) f a b hne hcol hc

/-- The actual Frobenius polynomial vanishes when its first column is longer
    than the alphabet. Auxiliary to the finite Schur formula in `lem:KP-correspondence`. -/
theorem finiteFrobeniusPolynomial_eq_zero_of_height {m : ℕ}
    (μ : YoungDiagram) (hm : m < μ.colLen 0) :
    finiteFrobeniusPolynomial (Fin m) μ = 0 := by
  apply MvPolynomial.eq_zero_iff.mpr
  intro d
  rw [finiteFrobeniusPolynomial_coeff_finrank_young,
    finrank_zero_iff_forall_zero.mpr (youngSpecht_weightColoring_intertwiner_zero_of_height μ hm d)]
  simp

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteFrobeniusPolynomial_eq_zero_of_height
