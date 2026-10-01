import ModifiedCartan.CyclicCentralizer
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Classical
open Matrix

namespace ModifiedCartan
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_polynomial_action (M : Matrix ι ι ℂ) (v : ι → ℂ) (p : Polynomial ℂ) :
    (Polynomial.aeval (Matrix.toLinAlgEquiv' M) p) v =
      (Polynomial.aeval M p) *ᵥ v := by
  rw [Polynomial.aeval_algHom_apply]
  rfl

def polynomialOrbitColumns (p : ι → Polynomial ℂ) (v : ι → ℂ) (M : Matrix ι ι ℂ) :
    Matrix ι ι ℂ := fun i j => ((Polynomial.aeval M (p j)) *ᵥ v) i

theorem cyclic_of_polynomialOrbitColumns_det_ne_zero (p : ι → Polynomial ℂ)
    (v : ι → ℂ) (M : Matrix ι ι ℂ) (h : (polynomialOrbitColumns p v M).det ≠ 0) :
    HasPolynomialCyclicVector (Matrix.toLinAlgEquiv' M) v := by
  have hs : Function.Surjective (polynomialOrbitColumns p v M).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
  intro w
  obtain ⟨c, hc⟩ := hs w
  refine ⟨∑ j, c j • p j, ?_⟩
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, matrix_polynomial_action]
  ext i
  change (∑ j, c j • (Polynomial.aeval M (p j) *ᵥ v)) i = w i
  rw [Finset.sum_apply]
  simpa only [Pi.smul_apply, smul_eq_mul, polynomialOrbitColumns, Matrix.mulVec,
    dotProduct, mul_comm] using congrFun hc i

theorem matrix_polynomial_action_basis {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (T : Module.End ℂ V) (v : V) (p : Polynomial ℂ) :
    (Polynomial.aeval (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv b T)) p)
        (b.equivFun v) = b.equivFun ((Polynomial.aeval T p) v) := by
  rw [matrix_polynomial_action, Polynomial.aeval_algHom_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (Polynomial.aeval T p) v

theorem hasPolynomialCyclicVector_toMatrix_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (T : Module.End ℂ V) (v : V) :
    HasPolynomialCyclicVector (Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv b T))
      (b.equivFun v) ↔ HasPolynomialCyclicVector T v := by
  constructor
  · intro h w
    obtain ⟨p, hp⟩ := h (b.equivFun w)
    refine ⟨p, b.equivFun.injective ?_⟩
    rwa [matrix_polynomial_action_basis] at hp
  · intro h w
    obtain ⟨p, hp⟩ := h (b.equivFun.symm w)
    refine ⟨p, ?_⟩
    rw [matrix_polynomial_action_basis, hp, b.equivFun.apply_symm_apply]

end
end ModifiedCartan


