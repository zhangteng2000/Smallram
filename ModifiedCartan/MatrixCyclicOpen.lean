import ModifiedCartan.MatrixCyclic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Polynomial

open scoped BigOperators Classical Topology
open Matrix

namespace ModifiedCartan
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem polynomialOrbitColumns_continuous (p : ι → Polynomial ℂ) (v : ι → ℂ) :
    Continuous (polynomialOrbitColumns p v) := by
  apply continuous_matrix
  intro i j
  exact (continuous_apply i).comp ((p j).continuous_aeval.matrix_mulVec continuous_const)

/-- Cyclicity with a fixed vector persists under sufficiently small matrix perturbations. -/
theorem eventually_hasPolynomialCyclicVector_matrix (M : Matrix ι ι ℂ) (v : ι → ℂ)
    (h : HasPolynomialCyclicVector (Matrix.toLinAlgEquiv' M) v) :
    ∀ᶠ N in 𝓝 M, HasPolynomialCyclicVector (Matrix.toLinAlgEquiv' N) v := by
  choose p hp using (fun i : ι => h (Pi.single i 1))
  have hM : polynomialOrbitColumns p v M = 1 := by
    ext i j
    have hj := congrFun (hp j) i
    rw [matrix_polynomial_action] at hj
    simpa only [polynomialOrbitColumns, Matrix.one_apply, Pi.single_apply, eq_comm] using hj
  have hdet : (polynomialOrbitColumns p v M).det ≠ 0 := by rw [hM, Matrix.det_one]; exact one_ne_zero
  filter_upwards [(polynomialOrbitColumns_continuous p v).matrix_det.continuousAt.eventually_ne hdet]
    with N hN
  exact cyclic_of_polynomialOrbitColumns_det_ne_zero p v N hN

theorem eventually_hasPolynomialCyclicVector_of_matrix_continuousAt
    {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (T : X → Module.End ℂ V) (x : X) (v : V)
    (hc : ContinuousAt (fun y => LinearMap.toMatrixAlgEquiv b (T y)) x)
    (hv : HasPolynomialCyclicVector (T x) v) :
    ∀ᶠ y in 𝓝 x, HasPolynomialCyclicVector (T y) v := by
  have h := eventually_hasPolynomialCyclicVector_matrix (LinearMap.toMatrixAlgEquiv b (T x))
    (b.equivFun v) ((hasPolynomialCyclicVector_toMatrix_iff b (T x) v).mpr hv)
  filter_upwards [hc.eventually h] with y hy
  exact (hasPolynomialCyclicVector_toMatrix_iff b (T y) v).mp hy

end
end ModifiedCartan


