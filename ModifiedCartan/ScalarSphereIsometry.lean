import ModifiedCartan.UnitaryNorm
import ModifiedCartan.ScalarSpherePotential
import ModifiedCartan.CurveCoordinateNormalization

open scoped Topology BigOperators Matrix
open Filter Set Metric MeasureTheory Matrix
set_option autoImplicit false
namespace ModifiedCartan

/-- A matrix preserving the exact Euclidean norm has determinant of norm one.
The proof uses the already checked finite-dimensional singular-value identity. -/
theorem norm_det_of_euclidean_matrix_isometry {n : ℕ}
    (A : Matrix (Index n) (Index n) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x) :
    ‖A.det‖ = 1 := by
  obtain ⟨V, σ, _, hσ, _, hprod⟩ := exists_unitary_positive_column_norms Aᵀ
    (by simpa only [Matrix.det_transpose] using hA.ne_zero)
  have hVgram : (V : Matrix (Index n) (Index n) ℂ)ᴴ *
      (V : Matrix (Index n) (Index n) ℂ) = Matrix.diagonal (fun _ => ((1 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_one, Matrix.diagonal_one, Matrix.star_eq_conjTranspose] using V.property.1
  have hσone (j : Index n) : σ j = 1 := by
    have hnorm := gram_diagonal_column_norms hVgram j
    have hmul : (fun k => (Aᵀ * (V : Matrix (Index n) (Index n) ℂ)) k j) =
        (fun i => ∑ k, (V : Matrix (Index n) (Index n) ℂ) k j * A k i) := by
      funext i
      simp only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
    rw [hσ j, hmul, hAnorm]
    have hn := euclideanNorm_nonneg (fun k => (V : Matrix (Index n) (Index n) ℂ) k j)
    nlinarith
  rw [Matrix.det_transpose] at hprod
  rw [← hprod]
  simp only [hσone, Finset.prod_const_one]

/-- The spherical log potential is exactly invariant under the actual fixed
Euclidean coordinate normalization, even at the chosen critical-point values. -/
theorem scalarSphericalLogPotential_matrixGauge (f : Curve 1)
    (A : Matrix (Index 1) (Index 1) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x) (z : ℂ) :
    scalarSphericalLogPotential (f.matrixGauge A hA).coord z =
      scalarSphericalLogPotential f.coord z := by
  have he : euclideanNorm (fun j => (f.matrixGauge A hA).coord j z) =
      euclideanNorm (fun j => f.coord j z) := hAnorm (fun j => f.coord j z)
  rw [scalarSphericalLogPotential, scalarSphericalLogPotential, he,
    FewInflection.Curve.matrixGauge_wronskian, norm_mul,
    norm_det_of_euclidean_matrix_isometry A hA hAnorm, mul_one]

theorem scalarNormalizedSpherePotential_matrixGauge (f : Curve 1)
    (A : Matrix (Index 1) (Index 1) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x) (t : ℝ) :
    scalarNormalizedSpherePotential (f.matrixGauge A hA) t = scalarNormalizedSpherePotential f t := by
  funext z
  rw [scalarNormalizedSpherePotential, scalarNormalizedSpherePotential,
    scalarSphericalLogPotential_matrixGauge f A hA hAnorm,
    characteristic_matrixGauge_of_euclidean_isometry f A hA hAnorm]

end ModifiedCartan
#print axioms ModifiedCartan.norm_det_of_euclidean_matrix_isometry
#print axioms ModifiedCartan.scalarSphericalLogPotential_matrixGauge
#print axioms ModifiedCartan.scalarNormalizedSpherePotential_matrixGauge

