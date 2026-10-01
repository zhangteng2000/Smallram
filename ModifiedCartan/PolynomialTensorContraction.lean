import ModifiedCartan.PolynomialTensorFunctional
import ModifiedCartan.PolynomialCoefficientSpace

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialTensorFunctional_coeff {m : ℕ} (d : Fin m →₀ ℕ)
    (P : MvPolynomial (Fin m) ℂ) :
    polynomialTensorFunctional (fun i => Polynomial.lcoeff ℂ (d i)) P = MvPolynomial.coeff d P := by
  have h : polynomialTensorFunctional (fun i => Polynomial.lcoeff ℂ (d i)) =
      MvPolynomial.lcoeff ℂ d := by
    apply (MvPolynomial.basisMonomials (Fin m) ℂ).ext
    intro e
    change polynomialTensorFunctional _ (MvPolynomial.monomial e 1) =
      MvPolynomial.coeff d (MvPolynomial.monomial e 1)
    rw [polynomialTensorFunctional_monomial_one]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases he : e = d
    · subst e
      simp
    · rw [ite_eq_right he]
      obtain ⟨i, hi⟩ : ∃ i, e i ≠ d i := by
        by_contra hn
        push Not at hn
        exact he (Finsupp.ext hn)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  exact LinearMap.congr_fun h P

theorem polynomialLinearCoefficientMap_monomial {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (L : R →ₗ[ℂ] S) (k : ℕ) (c : R) :
    polynomialLinearCoefficientMap L (Polynomial.monomial k c) = Polynomial.monomial k (L c) := by
  ext j
  rw [polynomialLinearCoefficientMap_coeff]
  by_cases h : k = j <;> simp [Polynomial.coeff_monomial, h]

theorem finSuccEquiv_monomial_cons {m : ℕ} (d : Fin m →₀ ℕ) (k : ℕ) (c : ℂ) :
    MvPolynomial.finSuccEquiv ℂ m (MvPolynomial.monomial (d.cons k) c) =
      Polynomial.monomial k (MvPolynomial.monomial d c) := by
  ext j e
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  have hcons : d.cons k = e.cons j ↔ k = j ∧ d = e := by
    constructor
    · intro h
      exact ⟨congrArg (fun t => t 0) h, by simpa only [Finsupp.tail_cons] using congrArg Finsupp.tail h⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [MvPolynomial.coeff_monomial, Polynomial.coeff_monomial, hcons]
  by_cases hk : k = j <;> by_cases hd : d = e <;> simp [hk, hd]

/-- Pairing one variable first is the ordinary scalar coefficient contraction
    followed by its univariate functional. Auxiliary to `lem:KP-correspondence`. -/
theorem polynomialTensorFunctional_first {m : ℕ}
    (v : Fin (m + 1) → Module.Dual ℂ (Polynomial ℂ))
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    polynomialTensorFunctional v P = v 0
      (polynomialLinearCoefficientMap (polynomialTensorFunctional (v ∘ Fin.succ))
        (MvPolynomial.finSuccEquiv ℂ m P)) := by
  have h : polynomialTensorFunctional v = (v 0).comp
      ((polynomialLinearCoefficientMap (polynomialTensorFunctional (v ∘ Fin.succ))).comp
        (MvPolynomial.finSuccEquiv ℂ m).toLinearMap) := by
    apply (MvPolynomial.basisMonomials (Fin (m + 1)) ℂ).ext
    intro d
    change polynomialTensorFunctional v (MvPolynomial.monomial d 1) = v 0
      (polynomialLinearCoefficientMap (polynomialTensorFunctional (v ∘ Fin.succ))
        (MvPolynomial.finSuccEquiv ℂ m (MvPolynomial.monomial d 1)))
    rw [← Finsupp.cons_tail d, finSuccEquiv_monomial_cons,
      polynomialLinearCoefficientMap_monomial, polynomialTensorFunctional_monomial_one,
      polynomialTensorFunctional_monomial_one, Fin.prod_univ_succ]
    simp only [Finsupp.cons_zero, Finsupp.cons_succ, Finsupp.tail_apply, Function.comp_apply]
    have hm (c : ℂ) : Polynomial.monomial (d 0) c = c • Polynomial.monomial (d 0) (1 : ℂ) := by
      simp only [Polynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hm (∏ i : Fin m, v i.succ (Polynomial.monomial (d i.succ) 1)), map_smul]
    simp only [smul_eq_mul]
    ring
  exact LinearMap.congr_fun h P

theorem polynomialTensorFunctional_zero_of_annihilates_first {m : ℕ}
    (v : Fin (m + 1) → Module.Dual ℂ (Polynomial ℂ))
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (h : ∀ p ∈ polynomialCoefficientSpace (MvPolynomial.finSuccEquiv ℂ m P), v 0 p = 0) :
    polynomialTensorFunctional v P = 0 := by
  rw [polynomialTensorFunctional_first]
  exact h _ ⟨polynomialTensorFunctional (v ∘ Fin.succ), rfl⟩

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialTensorFunctional_first
