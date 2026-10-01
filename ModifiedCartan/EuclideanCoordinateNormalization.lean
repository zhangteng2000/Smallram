import ModifiedCartan.IsometryVectorTransport
import ModifiedCartan.NormComparison
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped Topology BigOperators
open Set Matrix
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem exists_euclidean_linearMap_nonzero_coordinates {n : ℕ}
    (v : Index n → ℂ) (hv : v ≠ 0) :
    ∃ B : (Index n → ℂ) →ₗ[ℂ] (Index n → ℂ), Function.Injective B ∧
      (∀ x, euclideanNorm (B x) = euclideanNorm x) ∧ ∀ j, B v j ≠ 0 := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Index n => ℂ)).symm
  have he (x : Index n → ℂ) : ‖e x‖ = euclideanNorm x := by
    rw [PiLp.norm_eq_of_L2]
    rfl
  let w := e (fun _ : Index n => (1 : ℂ))
  have hw : w ≠ 0 := by
    intro hz
    have hz' : (fun _ : Index n => (1 : ℂ)) = 0 := e.injective (by simpa only [map_zero] using hz)
    have hi := congrFun hz' (0 : Index n)
    norm_num at hi
  have hu : e v ≠ 0 := by
    intro hz
    exact hv (e.injective (by simpa only [map_zero] using hz))
  let c : ℝ := ‖e v‖ / ‖w‖
  have hc : 0 < c := div_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hw)
  have htarget : ‖e v‖ = ‖(c : ℂ) • w‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    exact (div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hw)).symm
  obtain ⟨L, hL⟩ := exists_linearIsometry_map_of_norm_eq hu htarget
  let B : (Index n → ℂ) →ₗ[ℂ] (Index n → ℂ) :=
    e.symm.toLinearMap.comp (L.toLinearMap.comp e.toLinearMap)
  have hBe (x : Index n → ℂ) : e (B x) = L (e x) := by
    change e (e.symm (L (e x))) = L (e x)
    exact e.apply_symm_apply _
  refine ⟨B, e.symm.injective.comp (L.injective.comp e.injective), ?_, ?_⟩
  · intro x
    rw [← he, hBe, L.norm_map, he]
  · intro j
    have hBv : B v = fun _ : Index n => (c : ℂ) := by
      apply e.injective
      rw [hBe, hL]
      change (c : ℂ) • e (fun _ : Index n => (1 : ℂ)) = e (fun _ : Index n => (c : ℂ))
      rw [← map_smul]
      congr 1
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [hBv]
    exact Complex.ofReal_ne_zero.mpr hc.ne'

/-- The matrix form of the manuscript's fixed unitary coordinate normalization.
It preserves the exact Euclidean norm and sends the prescribed nonzero vector
to a vector whose every coordinate is nonzero. -/
theorem exists_euclidean_matrix_nonzero_coordinates {n : ℕ}
    (v : Index n → ℂ) (hv : v ≠ 0) :
    ∃ A : Matrix (Index n) (Index n) ℂ, IsUnit A.det ∧
      (∀ x, euclideanNorm (fun j => ∑ k, x k * A k j) = euclideanNorm x) ∧
      ∀ j, (∑ k, v k * A k j) ≠ 0 := by
  classical
  obtain ⟨B, hBinj, hBnorm, hBv⟩ := exists_euclidean_linearMap_nonzero_coordinates v hv
  let M := LinearMap.toMatrix' B
  have hMapply (x : Index n → ℂ) : M *ᵥ x = B x := LinearMap.toMatrix'_mulVec B x
  have hMinj : Function.Injective M.mulVec := by
    intro x y hxy
    apply hBinj
    simpa only [hMapply] using hxy
  have hMunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hMinj)
  have hsum (x : Index n → ℂ) (j : Index n) : (∑ k, x k * Mᵀ k j) = B x j := by
    have hj := congrFun (hMapply x) j
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hj
  refine ⟨Mᵀ, by simpa only [Matrix.det_transpose] using hMunit, ?_, ?_⟩
  · intro x
    simpa only [hsum] using hBnorm x
  · intro j
    simpa only [hsum] using hBv j

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_euclidean_matrix_nonzero_coordinates
