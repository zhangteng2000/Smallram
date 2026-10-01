import ModifiedCartan.ScalarPhaseChoice
import ModifiedCartan.ScalarRectangleCrosses

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Exact spherical-speed invariance under the constructed fixed Euclidean
coordinate normalization, including critical points. -/
theorem scalarSphericalSpeed_matrixGauge (f : Curve 1)
    (A : Matrix (Index 1) (Index 1) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x) (z : ℂ) :
    scalarSphericalSpeed (f.matrixGauge A hA).coord z = scalarSphericalSpeed f.coord z := by
  have he : euclideanNorm (fun j => (f.matrixGauge A hA).coord j z) =
      euclideanNorm (fun j => f.coord j z) := hAnorm (fun j => f.coord j z)
  rw [scalarSphericalSpeed, scalarSphericalSpeed, he,
    FewInflection.Curve.matrixGauge_wronskian, norm_mul,
    norm_det_of_euclidean_matrix_isometry A hA hAnorm, mul_one]

theorem scalarProfileError_matrixGauge (f : Curve 1)
    (A : Matrix (Index 1) (Index 1) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x)
    (m : ℕ) (t : ℝ) (C : ℂ) :
    scalarProfileError (f.matrixGauge A hA) m t C = scalarProfileError f m t C := by
  unfold scalarProfileError
  rw [scalarNormalizedSpherePotential_matrixGauge f A hA hAnorm]

/-- The global minimizing coefficient itself is unchanged: its defining
predicate is exactly the same after the actual coordinate normalization. -/
theorem scalarPhaseCoefficient_matrixGauge (f : Curve 1)
    (A : Matrix (Index 1) (Index 1) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x)
    (m : ℕ) (t : ℝ) :
    scalarPhaseCoefficient (f.matrixGauge A hA) m t = scalarPhaseCoefficient f m t := by
  have hchoose {P Q : ℂ → Prop} (he : P = Q) (hP : ∃ x, P x) (hQ : ∃ x, Q x) :
      Classical.choose hP = Classical.choose hQ := by cases he; rfl
  apply hchoose
  funext C
  simp only [scalarProfileError_matrixGauge f A hA hAnorm]

/-- Actual rectangle paths obtained after normalization give exactly the same
speed bounds for the original physical curve. -/
theorem HasSmallRectangleCrosses.of_matrixGauge {f : Curve 1}
    (A : Matrix (Index 1) (Index 1) ℂ) (hA : IsUnit A.det)
    (hAnorm : ∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x)
    {r s : ℕ → ℝ} {Ω : Set ℂ} (h : HasSmallRectangleCrosses (f.matrixGauge A hA) r s Ω) :
    HasSmallRectangleCrosses f r s Ω := by
  simpa only [HasSmallRectangleCrosses, scalarSphericalSpeed_matrixGauge f A hA hAnorm] using h

end ModifiedCartan
#print axioms ModifiedCartan.scalarSphericalSpeed_matrixGauge
#print axioms ModifiedCartan.scalarPhaseCoefficient_matrixGauge
#print axioms ModifiedCartan.HasSmallRectangleCrosses.of_matrixGauge
