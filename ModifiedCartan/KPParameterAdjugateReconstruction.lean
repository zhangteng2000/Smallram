import ModifiedCartan.KPParameterCharacters
import ModifiedCartan.SchubertAdjugateReconstruction

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators MonoidAlgebra IsMulCommutative
attribute [local instance] kpParameterBetheAlgebra_isMulCommutative

/-- The scalar polynomial determinant of the universal initial-value matrix. -/
def kpParameterODEDeterminant (N D : ℕ) : MvPolynomial (Fin N) ℂ :=
  ∏ r : Fin D, if r.val < N then 1 else
    (kpParameterWeight ∅).coeff 0 * (r.val.descFactorial N : MvPolynomial (Fin N) ℂ)

theorem kpParameterODEJetMatrix_det (N D : ℕ) :
    (polynomialODEJetMatrix N D (kpParameterDifferentialCoefficients N)).det =
      algebraMap (MvPolynomial (Fin N) ℂ) (kpParameterBetheAlgebra N)
        (kpParameterODEDeterminant N D) := by
  rw [polynomialODEJetMatrix_det, kpParameterDifferentialCoefficients_leading,
    Polynomial.coeff_map]
  unfold kpParameterODEDeterminant
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r _
  by_cases hr : r.val < N
  · simp only [hr, ite_true, map_one]
  · simp only [hr, ite_false, map_mul, map_natCast]

theorem kpParameterWeight_zero_eval {N : ℕ} (z : Fin N → ℂ) :
    MvPolynomial.eval z ((kpParameterWeight ∅).coeff 0) = ∏ i, z i := by
  have he := congrArg (fun p : Polynomial ℂ => p.coeff 0) (kpParameterWeight_map z ∅)
  rw [Polynomial.coeff_map] at he
  change MvPolynomial.eval z ((kpParameterWeight ∅).coeff 0) = _ at he
  rw [he]
  simp only [Polynomial.coeff_zero_eq_eval_zero, kpWeightPolynomial, Finset.sdiff_empty,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    zero_add]

theorem kpParameterODEDeterminant_eval {N D : ℕ} (z : Fin N → ℂ) :
    MvPolynomial.eval z (kpParameterODEDeterminant N D) =
      ∏ r : Fin D, if r.val < N then 1 else (∏ i, z i) * (r.val.descFactorial N : ℂ) := by
  unfold kpParameterODEDeterminant
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r _
  by_cases hr : r.val < N
  · simp only [hr, ite_true, map_one]
  · simp only [hr, ite_false, map_mul, map_natCast, kpParameterWeight_zero_eval]

theorem kpParameterODEDeterminant_eval_ne_zero {N D : ℕ} (z : Fin N → ℂ)
    (hz : (∏ i, z i) ≠ 0) :
    MvPolynomial.eval z (kpParameterODEDeterminant N D) ≠ 0 := by
  rw [kpParameterODEDeterminant_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  by_cases hr : r.val < N
  · rw [ite_eq_left hr]
    exact one_ne_zero
  · rw [ite_eq_right hr]
    apply mul_ne_zero hz
    have hpos : 0 < r.val.descFactorial N := Nat.descFactorial_pos.mpr (by omega)
    exact_mod_cast hpos.ne'

def kpParameterInitialVector (N D : ℕ) (j : Fin N) (r : Fin D) :
    kpParameterBetheAlgebra N :=
  algebraMap ℂ (kpParameterBetheAlgebra N)
    (if r.val = j.val then ((j.val.factorial : ℂ)⁻¹) else 0)

def kpParameterAdjugatePolynomial (N D : ℕ) (j : Fin N) :
    Polynomial (kpParameterBetheAlgebra N) :=
  polynomialODEAdjugatePolynomial N D (kpParameterDifferentialCoefficients N)
    (kpParameterInitialVector N D j)

theorem kpParameterBetheEvaluation_algebraMap {N : ℕ} (z : Fin N → ℂ)
    (r : MvPolynomial (Fin N) ℂ) :
    kpParameterBetheEvaluation z
      (algebraMap (MvPolynomial (Fin N) ℂ) (kpParameterBetheAlgebra N) r) =
        algebraMap ℂ (kpGeneratedAlgebra z) (MvPolynomial.eval z r) := by
  apply Subtype.ext
  change kpParameterEvaluation z
    ((algebraMap (MvPolynomial (Fin N) ℂ) (kpParameterBetheAlgebra N) r).val) = _
  rw [Subalgebra.coe_algebraMap, kpParameterEvaluation_algebraMap]
  rfl

theorem kpParameterODEJetMatrix_det_character {N D : ℕ} (z : Fin N → ℂ)
    (φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ) :
    (φ.comp (kpParameterBetheEvaluation z))
      (polynomialODEJetMatrix N D (kpParameterDifferentialCoefficients N)).det =
        MvPolynomial.eval z (kpParameterODEDeterminant N D) := by
  rw [kpParameterODEJetMatrix_det]
  change φ (kpParameterBetheEvaluation z _) = _
  rw [kpParameterBetheEvaluation_algebraMap, AlgHom.commutes]
  rfl

/-- Universal adjugate polynomials specialize to the scalar column-coordinate
    differential operator on an actual joint eigenspace. -/
theorem kpParameterAdjugatePolynomial_character {N D : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin N) = partitionSize τ)
    (z : Fin N → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ)
    (hφ : ∀ x : kpGeneratedAlgebra z, ∀ v ∈ kpJointEigenspace τ hτ z χ,
      (spechtRepresentationOn τ hτ).asAlgebraHom x.val v = φ x • v)
    (j : Fin N) :
    (kpParameterAdjugatePolynomial N D j).map
      (φ.comp (kpParameterBetheEvaluation z)).toRingHom =
      polynomialODEAdjugatePolynomial N D
        (partitionColumnDifferentialCoefficients N (kpJointValuePolynomial N χ))
        (fun r : Fin D => if r.val = j.val then ((j.val.factorial : ℂ)⁻¹) else 0) := by
  rw [kpParameterAdjugatePolynomial,
    polynomialODEAdjugatePolynomial_map (R := kpParameterBetheAlgebra N) (S := ℂ)]
  congr 1
  · funext i
    exact kpParameterDifferentialCoefficients_character τ hτ z χ hne φ hφ i
  · funext r
    exact (φ.comp (kpParameterBetheEvaluation z)).commutes _

theorem kpParameterScalarODEJetMatrix_det {N D : ℕ}
    (τ : YoungDiagram) (hτ : Fintype.card (Fin N) = partitionSize τ)
    (z : Fin N → ℂ) (χ : YoungDiagram → ℂ)
    (hne : kpJointEigenspace τ hτ z χ ≠ ⊥)
    (φ : kpGeneratedAlgebra z →ₐ[ℂ] ℂ)
    (hφ : ∀ x : kpGeneratedAlgebra z, ∀ v ∈ kpJointEigenspace τ hτ z χ,
      (spechtRepresentationOn τ hτ).asAlgebraHom x.val v = φ x • v) :
    (polynomialODEJetMatrix N D
      (partitionColumnDifferentialCoefficients N (kpJointValuePolynomial N χ))).det =
        MvPolynomial.eval z (kpParameterODEDeterminant N D) := by
  have hc : (fun i => (kpParameterDifferentialCoefficients N i).map
      (φ.comp (kpParameterBetheEvaluation z)).toRingHom) =
      partitionColumnDifferentialCoefficients N (kpJointValuePolynomial N χ) := by
    funext i
    exact kpParameterDifferentialCoefficients_character τ hτ z χ hne φ hφ i
  have he := (φ.comp (kpParameterBetheEvaluation z)).toRingHom.map_det
    (polynomialODEJetMatrix (R := kpParameterBetheAlgebra N) N D
      (kpParameterDifferentialCoefficients N))
  change (φ.comp (kpParameterBetheEvaluation z))
      (polynomialODEJetMatrix N D (kpParameterDifferentialCoefficients N)).det =
    ((polynomialODEJetMatrix N D (kpParameterDifferentialCoefficients N)).map
      (φ.comp (kpParameterBetheEvaluation z)).toRingHom).det at he
  rw [polynomialODEJetMatrix_map, hc, kpParameterODEJetMatrix_det_character] at he
  exact he.symm

end
end ModifiedCartan

#print axioms ModifiedCartan.kpParameterODEDeterminant_eval_ne_zero
#print axioms ModifiedCartan.kpParameterAdjugatePolynomial_character
#print axioms ModifiedCartan.kpParameterScalarODEJetMatrix_det
