import ModifiedCartan.PolynomialODEAdjugate

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

theorem polynomial_ofFn_map (f : R →+* S) (D : ℕ) (v : Fin D → R) :
    (Polynomial.ofFn D v).map f = Polynomial.ofFn D (fun k => f (v k)) := by
  ext k
  rw [Polynomial.coeff_map]
  by_cases hk : k < D
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk, Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),
      Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega), map_zero]

/-- Specialization of coefficients commutes with the finite ODE matrix. -/
theorem polynomialODEJetMatrix_map (f : R →+* S) (N D : ℕ)
    (c : Fin (N + 1) → Polynomial R) :
    (polynomialODEJetMatrix N D c).map f =
      polynomialODEJetMatrix N D (fun i => (c i).map f) := by
  funext r k
  change f (polynomialODEJetMatrix N D c r k) = _
  by_cases hr : r.val < N
  · simp [polynomialODEJetMatrix, hr]
  · simp only [polynomialODEJetMatrix, ite_eq_right hr]
    rw [← Polynomial.coeff_map]
    congr 1
    simp only [Polynomial.map_sum, Polynomial.map_mul, ← Polynomial.iterate_derivative_map,
      Polynomial.map_pow, Polynomial.map_X]

/-- The polynomial adjugate construction used to clear the nonzero initial
    determinant in the Bethe identification argument. -/
def polynomialODEAdjugatePolynomial (N D : ℕ)
    (c : Fin (N + 1) → Polynomial R) (v : Fin D → R) : Polynomial R :=
  Polynomial.ofFn D ((polynomialODEJetMatrix N D c).adjugate.mulVec v)

/-- Adjugate reconstruction is polynomial in the differential coefficients
    and commutes with every ring specialization. -/
theorem polynomialODEAdjugatePolynomial_map (f : R →+* S) (N D : ℕ)
    (c : Fin (N + 1) → Polynomial R) (v : Fin D → R) :
    (polynomialODEAdjugatePolynomial N D c v).map f =
      polynomialODEAdjugatePolynomial N D (fun i => (c i).map f) (fun k => f (v k)) := by
  unfold polynomialODEAdjugatePolynomial
  rw [polynomial_ofFn_map]
  congr 1
  funext k
  rw [f.map_mulVec]
  have hm : (polynomialODEJetMatrix N D c).adjugate.map f =
      ((polynomialODEJetMatrix N D c).map f).adjugate :=
    f.map_adjugate _
  rw [hm, polynomialODEJetMatrix_map]
  rfl

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialODEAdjugatePolynomial_map