import ModifiedCartan.AmbientFactorizationLaurentSeries
import ModifiedCartan.ZFactorizationResidue

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- The residue vanishes for every pair of union and intersection supports,
including non-squarefree marker coefficients. KP Section 4.1.4; auxiliary to
LaTeX `lem:KP-correspondence`. -/
theorem ambientFactorizationLaurentSeries_residue {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (U Z : Finset A) :
    (finiteBernsteinLaurent B (ambientFactorizationLaurentSeries (Option B) θ U Z)).coeff (-1) = 0 := by
  by_cases hθ : θ ∈ supportedPermutationSubgroup U
  · by_cases hZ : Z ⊆ U
    · rw [ambientFactorizationLaurentSeries_restrict θ U Z hθ hZ]
      exact zFactorizationLaurentSeries_residue _ _
    · rw [ambientFactorizationLaurentSeries_zero_of_not_subset θ U Z hZ]
      simp [finiteBernsteinLaurent]
  · rw [ambientFactorizationLaurentSeries_zero_of_not_supported θ U Z hθ]
    simp [finiteBernsteinLaurent]

end
end ModifiedCartan

