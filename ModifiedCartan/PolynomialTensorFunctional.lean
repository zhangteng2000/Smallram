import ModifiedCartan.PolynomialDeterminantCoefficients
import ModifiedCartan.FiniteAlternants
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.RingTheory.MvPolynomial.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Pair a multivariate polynomial with one univariate linear functional per
    variable. Auxiliary to the decomposition step of `lem:KP-correspondence`. -/
def polynomialTensorFunctional {m : ℕ}
    (v : Fin m → Module.Dual ℂ (Polynomial ℂ)) : MvPolynomial (Fin m) ℂ →ₗ[ℂ] ℂ :=
  (MvPolynomial.basisMonomials (Fin m) ℂ).constr ℂ
    (fun d => ∏ i : Fin m, v i (Polynomial.monomial (d i) 1))

theorem polynomialTensorFunctional_monomial_one {m : ℕ}
    (v : Fin m → Module.Dual ℂ (Polynomial ℂ)) (d : Fin m →₀ ℕ) :
    polynomialTensorFunctional v (MvPolynomial.monomial d 1) =
      ∏ i : Fin m, v i (Polynomial.monomial (d i) 1) :=
  (MvPolynomial.basisMonomials (Fin m) ℂ).constr_basis ℂ _ d

theorem polynomialTensorFunctional_C_mul {m : ℕ}
    (v : Fin m → Module.Dual ℂ (Polynomial ℂ)) (c : ℂ) (P : MvPolynomial (Fin m) ℂ) :
    polynomialTensorFunctional v (MvPolynomial.C c * P) = c * polynomialTensorFunctional v P := by
  rw [← MvPolynomial.smul_eq_C_mul]
  exact (polynomialTensorFunctional v).map_smul c P

def polynomialSeparateProduct (m : ℕ) :
    MultilinearMap ℂ (fun _ : Fin m => Polynomial ℂ) (MvPolynomial (Fin m) ℂ) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin m) (MvPolynomial (Fin m) ℂ)).compLinearMap
    (fun i => (Polynomial.aeval (MvPolynomial.X i)).toLinearMap)

theorem polynomialSeparateProduct_apply {m : ℕ} (p : Fin m → Polynomial ℂ) :
    polynomialSeparateProduct m p =
      ∏ i : Fin m, (p i).eval₂ MvPolynomial.C (MvPolynomial.X i) := rfl

theorem polynomialTensorFunctional_separateProduct {m : ℕ}
    (v : Fin m → Module.Dual ℂ (Polynomial ℂ)) (p : Fin m → Polynomial ℂ) :
    polynomialTensorFunctional v
      (∏ i : Fin m, (p i).eval₂ MvPolynomial.C (MvPolynomial.X i)) =
      ∏ i : Fin m, v i (p i) := by
  have h : (polynomialTensorFunctional v).compMultilinearMap (polynomialSeparateProduct m) =
      (MultilinearMap.mkPiAlgebra ℂ (Fin m) ℂ).compLinearMap v := by
    apply Module.Basis.ext_multilinear (fun _ => Polynomial.basisMonomials ℂ)
    intro e
    simp only [LinearMap.compMultilinearMap_apply, polynomialSeparateProduct_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      Polynomial.coe_basisMonomials, Polynomial.eval₂_monomial, map_one, one_mul]
    have hp : (∏ i : Fin m, (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^ e i) =
        MvPolynomial.monomial (finiteExponent e) 1 := by
      simpa only [map_one, one_mul] using (finiteExponent_monomial e (1 : ℂ)).symm
    rw [hp, polynomialTensorFunctional_monomial_one]
    rfl
  exact MultilinearMap.congr_fun h p

/-- Pairing the determinant polynomial gives the determinant of the pairings.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialTensorFunctional_alternant {m : ℕ}
    (v : Fin m → Module.Dual ℂ (Polynomial ℂ)) (p : Fin m → Polynomial ℂ) :
    polynomialTensorFunctional v (polynomialAlternant p) =
      Matrix.det (fun i j : Fin m => v i (p j)) := by
  unfold polynomialAlternant
  erw [Matrix.det_apply', Matrix.det_apply']
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin m) ℂ) =
      MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) := (map_intCast _ _).symm
  rw [hc, polynomialTensorFunctional_C_mul]
  congr 1
  calc
    _ = polynomialTensorFunctional v (∏ j : Fin m,
        (p (σ.symm j)).eval₂ MvPolynomial.C (MvPolynomial.X j)) := by
      apply congrArg (polynomialTensorFunctional v)
      simpa only [Equiv.symm_apply_apply] using Equiv.prod_comp σ
        (fun j => (p (σ.symm j)).eval₂ MvPolynomial.C (MvPolynomial.X j))
    _ = ∏ j : Fin m, v j (p (σ.symm j)) := polynomialTensorFunctional_separateProduct v _
    _ = _ := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ (fun j => v j (p (σ.symm j)))).symm

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialTensorFunctional_alternant
