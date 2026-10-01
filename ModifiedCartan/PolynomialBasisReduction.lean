import ModifiedCartan.PolynomialMinorBasisChange
import Mathlib.LinearAlgebra.Transvection.Basic

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- An elementary column operation on an arbitrary basis. -/
theorem basis_exists_elementary_subtraction {ι W : Type*} [DecidableEq ι]
    [AddCommGroup W] [Module ℂ W] (b : Module.Basis ι ℂ W)
    (i j : ι) (hij : i ≠ j) (c : ℂ) :
    ∃ d : Module.Basis ι ℂ W, d i = b i - c • b j ∧ ∀ k, k ≠ i → d k = b k := by
  have hz : b.coord i ((-c) • b j) = 0 := by
    simp [Module.Basis.coord_apply, hij]
  let d := b.map (LinearEquiv.transvection hz)
  refine ⟨d, ?_, ?_⟩
  · simp [d, LinearMap.transvection.apply, Module.Basis.coord_apply, sub_eq_add_neg]
  · intro k hk
    simp [d, LinearMap.transvection.apply, Module.Basis.coord_apply, hk.symm]

/-- Cancelling two equal leading degrees strictly lowers the degree whenever
    the resulting polynomial is nonzero. -/
theorem polynomial_natDegree_cancel_leading_lt (p q : Polynomial ℂ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hd : p.natDegree = q.natDegree)
    (hr : p - (p.leadingCoeff / q.leadingCoeff) • q ≠ 0) :
    (p - (p.leadingCoeff / q.leadingCoeff) • q).natDegree < p.natDegree := by
  have hc : p.leadingCoeff / q.leadingCoeff ≠ 0 := div_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hq)
  apply Polynomial.natDegree_lt_natDegree hr
  apply Polynomial.degree_sub_lt_left ?_ hp ?_
  · rw [Polynomial.smul_eq_C_mul, Polynomial.degree_C_mul hc,
      Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, hd]
  · rw [Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hq)]

end
end ModifiedCartan

#print axioms ModifiedCartan.basis_exists_elementary_subtraction
#print axioms ModifiedCartan.polynomial_natDegree_cancel_leading_lt