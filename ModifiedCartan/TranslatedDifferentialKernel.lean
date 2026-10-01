import ModifiedCartan.MvPolynomialTranslationJets
import ModifiedCartan.KPJointShiftedContraction

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def polynomialFirstDifferential {m : ℕ} (N : ℕ) (c : ℕ → Polynomial ℂ)
    (p : Polynomial (MvPolynomial (Fin m) ℂ)) : Polynomial (MvPolynomial (Fin m) ℂ) :=
  ∑ k ∈ Finset.range (N + 1), (c k).map MvPolynomial.C * (Polynomial.derivative^[N - k] p)

theorem polynomialFirstDifferential_translated_eval {m : ℕ}
    (N : ℕ) (c : ℕ → Polynomial ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ) (a : ℂ) :
    mvPolynomialTranslate (Fin m) a
      ((polynomialFirstDifferential N c (MvPolynomial.finSuccEquiv ℂ m P)).eval (MvPolynomial.C a)) =
      ∑ k ∈ Finset.range (N + 1),
        MvPolynomial.C ((c k).eval a * ((N - k).factorial : ℂ)) *
          (MvPolynomial.finSuccEquiv ℂ m
            (mvPolynomialTranslate (Fin (m + 1)) a P)).coeff (N - k) := by
  simp only [polynomialFirstDifferential, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_map_apply, map_sum, map_mul, mvPolynomialTranslate_C]
  apply Finset.sum_congr rfl
  intro k _
  rw [← finSuccEquiv_translate_factorial_coeff]
  ring

theorem polynomialFirstDifferential_eq_zero_of_translated_contraction {m : ℕ}
    (N : ℕ) (c : ℕ → Polynomial ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (h : ∀ a : ℂ, (∑ k ∈ Finset.range (N + 1),
      MvPolynomial.C ((c k).eval a * ((N - k).factorial : ℂ)) *
        (MvPolynomial.finSuccEquiv ℂ m
          (mvPolynomialTranslate (Fin (m + 1)) a P)).coeff (N - k)) = 0) :
    polynomialFirstDifferential N c (MvPolynomial.finSuccEquiv ℂ m P) = 0 := by
  apply polynomial_mvCoefficients_eq_zero_of_scalar_eval
  intro a
  apply mvPolynomialTranslate_injective (Fin m) a
  rw [map_zero, polynomialFirstDifferential_translated_eval]
  exact h a

def kpJointDifferentialCoefficient (N : ℕ) (χ : YoungDiagram → ℂ) (k : ℕ) : Polynomial ℂ :=
  Polynomial.C ((-1 : ℂ) ^ k) * kpJointValuePolynomial N χ (columnPartition k)

/-- The actual nonzero divided alternating polynomial is annihilated in its
    first variable by the KP polynomial differential operator at every center.
    Auxiliary to manuscript `lem:KP-correspondence`, KP Section 4.2.3. -/
theorem kpJointDividedPolynomial_differential_eq_zero {A : Type*} [Fintype A]
    {m : ℕ} (hm : Fintype.card A = m + 1)
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ) (z : A → ℂ)
    (χ : YoungDiagram → ℂ) (hne : kpJointEigenspace τ hτ z χ ≠ ⊥) :
    polynomialFirstDifferential (Fintype.card A)
      (kpJointDifferentialCoefficient (Fintype.card A) χ)
      (MvPolynomial.finSuccEquiv ℂ m
        (finitePartitionDividedPolynomial (m + 1) (Fintype.card A) χ)) = 0 := by
  apply polynomialFirstDifferential_eq_zero_of_translated_contraction
  intro a
  have h := kpJointDividedPolynomial_translated_contraction hm τ hτ z χ hne a
  simpa only [hm, kpJointDifferentialCoefficient, Polynomial.eval_mul, Polynomial.eval_C] using h

end
end ModifiedCartan

#print axioms ModifiedCartan.kpJointDividedPolynomial_differential_eq_zero
