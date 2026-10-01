import ModifiedCartan.EuclideanCoordinateNormalization
import ModifiedCartan.CanonicalGauge
import FewInflection.GaugeTranscendental
import FewInflection.ScalarGaugeRamification

open scoped Topology BigOperators
open Filter Set Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem characteristic_matrixGauge_of_euclidean_isometry {n : ℕ} (f : Curve n)
    (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x) :
    characteristic (f.matrixGauge A hA) = characteristic f := by
  have hn (z : ℂ) : euclideanNorm ((f.matrixGauge A hA).vector z) =
      euclideanNorm (f.vector z) := hAnorm (f.vector z)
  funext r
  simp only [characteristic, hn]

theorem canonicalCoefficient_curve_matrixGauge {n : ℕ} (f : Curve n)
    (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det) (i : Index n) :
    canonicalCoefficient n (f.matrixGauge A hA).coord i =
      canonicalCoefficient n f.coord i := by
  funext z
  apply canonicalCoefficient_matrix _ A hA.ne_zero i
  intro j
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)) z (mem_univ z)

/-- The fixed unitary coordinate change before `prop:representation`, used
in `prop:indices`. All coordinates at the origin become nonzero, while the
exact Euclidean characteristic and canonical coefficients are unchanged.
The original transcendence, ramification and nondegeneracy hypotheses are
preserved by proved invariances. -/
theorem exists_normalized_curve {n : ℕ} (f : Curve n) :
    ∃ g : Curve n, (∀ j, g.coord j 0 ≠ 0) ∧
      characteristic g = characteristic f ∧ ramification g = ramification f ∧
      (∀ i, canonicalCoefficient n g.coord i = canonicalCoefficient n f.coord i) ∧
      (g.linearlyNonDegenerate ↔ f.linearlyNonDegenerate) ∧
      (g.Transcendental ↔ f.Transcendental) ∧
      (SmallRamification g ↔ SmallRamification f) ∧
      (FiniteLowerOrder g ↔ FiniteLowerOrder f) := by
  obtain ⟨A, hA, hAnorm, hA0⟩ :=
    exists_euclidean_matrix_nonzero_coordinates (f.vector 0) (f.vector_ne_zero 0)
  have hT := characteristic_matrixGauge_of_euclidean_isometry f A hA hAnorm
  have hN := FewInflection.Curve.matrixGauge_ramification_eq f A hA
  refine ⟨f.matrixGauge A hA, hA0, hT, hN,
    canonicalCoefficient_curve_matrixGauge f A hA,
    (f.matrixGauge_linearlyNonDegenerate_iff A hA).symm,
    (f.matrixGauge_transcendental_iff A hA).symm, ?_, ?_⟩
  · simp only [SmallRamification, hT, hN]
  · have hratio : logGrowthRatio (f.matrixGauge A hA) = logGrowthRatio f := by
      funext r
      simp only [logGrowthRatio, hT]
    simp only [FiniteLowerOrder, lowerOrder, hratio]

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_normalized_curve
