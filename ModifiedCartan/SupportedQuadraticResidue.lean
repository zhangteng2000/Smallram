import ModifiedCartan.SupportedQuadraticMarkerCoefficients
import ModifiedCartan.AmbientFactorizationResidue

open scoped Classical

namespace ModifiedCartan
noncomputable section

/-- Every group-algebra and marker coefficient of KP's literal permutation
quadratic expression has zero finite Bernstein residue, with no restriction
on the marker exponent. KP Section 4.1.4, auxiliary to `lem:KP-correspondence`.
The character-to-Schur and Plucker interpretation is a separate obligation. -/
theorem supportedPowerSumQuadratic_residue {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (d : A →₀ ℕ) :
    (finiteBernsteinLaurent B
      (MvPolynomial.coeff d ((supportedPowerSumQuadratic A (Option B)).coeff θ))).coeff (-1) = 0 := by
  by_cases hd : ∀ a, d a ≤ 2
  · rw [← complementMarkerDegree_active_overlap d hd,
      supportedPowerSumQuadratic_union_inter_coeff θ (markerActiveSet d) (markerOverlapSet d)
        (markerOverlapSet_subset_active d)]
    exact ambientFactorizationLaurentSeries_residue θ _ _
  · rw [supportedPowerSumQuadratic_marker_coeff_zero θ d hd]
    simp [finiteBernsteinLaurent]

end
end ModifiedCartan

