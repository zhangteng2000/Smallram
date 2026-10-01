import ModifiedCartan.PolynomialFourierKernel
import ModifiedCartan.FixedColoringInverse
import ModifiedCartan.FiniteColoringAverage
import ModifiedCartan.FiniteFrobeniusPolynomials

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialSpechtCoefficient_cycle {A B : Type*} [Fintype A] [Fintype B]
    (μ : SizedYoungDiagram (Fintype.card A)) :
    polynomialSpechtCoefficient (finiteCyclePolynomial B) μ = finiteFrobeniusPolynomial B μ.val :=
  finiteFrobeniusPolynomialOn_eq μ.val μ.property.symm

/-- Finite Cauchy identity for the actual Specht character transforms. Its
right side counts multisets on the product alphabet; no Schur formula is assumed. -/
theorem finiteFrobeniusPolynomial_cauchy {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] :
    (∑ μ : SizedYoungDiagram (Fintype.card A),
      MvPolynomial.rename Sum.inl (finiteFrobeniusPolynomial B μ.val) *
        MvPolynomial.rename Sum.inr (finiteFrobeniusPolynomial C μ.val)) =
      ∑ s : Sym (B × C) (Fintype.card A),
        (s.val.map (fun p => (MvPolynomial.X (Sum.inl p.1) : MvPolynomial (B ⊕ C) ℂ) *
          MvPolynomial.X (Sum.inr p.2))).prod := by
  have h := polynomial_specht_kernel
    (fun g : Equiv.Perm A => MvPolynomial.rename Sum.inl (finiteCyclePolynomial B g))
    (fun g : Equiv.Perm A => MvPolynomial.rename Sum.inr (finiteCyclePolynomial C g))
    (fun g h => congrArg (MvPolynomial.rename Sum.inl) (finiteCyclePolynomial_conjugate g h))
  simp only [polynomialSpechtCoefficient_rename, polynomialSpechtCoefficient_cycle,
    finiteCyclePolynomial_inv] at h
  rw [← h]
  simp only [finiteCyclePolynomial_rename, ← permutationFixedColoringSum_product]
  convert! permutationFixedColoringSum_average (A := A)
    (fun p : B × C => (MvPolynomial.X (Sum.inl p.1) : MvPolynomial (B ⊕ C) ℂ) *
      MvPolynomial.X (Sum.inr p.2)) using 1
  apply Finset.sum_congr (by ext; simp)
  intro s hs
  rfl

end
end ModifiedCartan


