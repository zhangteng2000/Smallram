import ModifiedCartan.GaudinDegenerationIdentity

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

variable {N : ℕ}

def kpPolynomialParameters (z : Fin N → ℂ) (s : ℂ) (i : Fin N) : ℂ :=
  z i + s ^ (i.val + 1)

theorem kpPolynomialParameters_zero (z : Fin N → ℂ) : kpPolynomialParameters z 0 = z := by
  ext i
  simp [kpPolynomialParameters]

theorem kpPolynomialParameters_inv (z : Fin N → ℂ) (t : ℂ) :
    kpPolynomialParameters z t⁻¹ = gaudinDeformedParameters z t := by
  ext i
  simp only [kpPolynomialParameters, gaudinDeformedParameters, inv_pow]

def kpCurveWeightPolynomial (z : Fin N → ℂ) (a : ℂ) (I : Finset (Fin N)) : Polynomial ℂ :=
  ∏ i ∈ Finset.univ \ I, (Polynomial.C (a + z i) + Polynomial.X ^ (i.val + 1))

theorem kpCurveWeightPolynomial_eval (z : Fin N → ℂ) (a s : ℂ) (I : Finset (Fin N)) :
    (kpCurveWeightPolynomial z a I).eval s = kpWeight (kpPolynomialParameters z s) a I := by
  simp only [kpCurveWeightPolynomial, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, kpWeight, kpPolynomialParameters,
    add_assoc]

end
end ModifiedCartan


